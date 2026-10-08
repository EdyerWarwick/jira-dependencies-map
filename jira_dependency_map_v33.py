#!/usr/bin/env python3
"""Jira Dependency Map — standalone Flask application."""
import subprocess,sys,time,threading,webbrowser,os,base64,json,ctypes
from collections import defaultdict,deque
import requests as req
from flask import Flask,Response,jsonify,request

JIRA_BATCH_SIZE=1000
_loading_progress={"phase":"Idle","batch":0,"fetched":0,"total":None,"detail":""}
_loading_progress_lock=threading.Lock()

def _set_loading_progress(**values):
    with _loading_progress_lock:
        _loading_progress.update(values)

def _get_loading_progress():
    with _loading_progress_lock:
        return dict(_loading_progress)

JIRA_HTTP_SESSION=req.Session()

# Background cache for the slower full/completed-ticket load. The initial board
# can render from active tickets while this cache is populated.
_completed_loads={}
_completed_loads_lock=threading.Lock()

JIRA_BASE_URL="https://uow-idg.atlassian.net"
JQL_QUERY="project IN (OPD, WT) AND status NOT IN (Epics, Component) AND issuetype != Epic AND issuetype NOT IN subTaskIssueTypes() AND parent != OPD-457"
PORT=5001
STARTUP_MESSAGES_URL="https://sitebuilder.warwick.ac.uk/sitebuilder2/api/dataentry/entries.json?page=/services/marketing/teams/cds/opd/startup/"

# GitHub Actions patches APP_VERSION during the build. Updates are installed
# by jira_dependency_map_launcher.py, never by the running application.
APP_VERSION="1.0.0"
GITHUB_REPO=os.environ.get("JIRA_DEP_MAP_GITHUB_REPO","EdyerWarwick/jira-dependencies-map")
_update_restart_lock=threading.Lock()
_update_restart_started=False

def _launcher_path():
    """Return the stable launcher path supplied by the managed installation."""
    value=str(os.environ.get("JIRA_DEP_MAP_LAUNCHER") or "").strip().strip('"')
    if value and os.path.isfile(value):
        return os.path.abspath(value)
    return None

# Credentials are stored in the current Windows user's Credential Manager.
# Nothing sensitive is embedded in this source file or sent to the browser.
CREDENTIAL_TARGET="Jira Dependency Map"
CRED_TYPE_GENERIC=1
CRED_PERSIST_LOCAL_MACHINE=2

# Per-user application preferences are stored outside the browser profile.
# This survives browser cache/site-data cleanup and is scoped to the current
# Windows user. The file contains only non-sensitive UI/application settings.
PREFERENCES_DIR=os.path.join(os.environ.get("LOCALAPPDATA") or os.path.expanduser("~"),"JiraDependencyMap")
PREFERENCES_FILE=os.path.join(PREFERENCES_DIR,"preferences.txt")
DEFAULT_PREFERENCES={
    "showCompleted":False,"filterUser":"","filterDue":"all","includeWithRemarkable":True,
    "customJql":"","useJiraModal":False,"showMiniMap":True,"startingView":"default",
}
_preferences_lock=threading.Lock()

def _normalise_preferences(data):
    out=dict(DEFAULT_PREFERENCES)
    if isinstance(data,dict):
        out.update({k:data[k] for k in DEFAULT_PREFERENCES if k in data})
    out["showCompleted"]=out["showCompleted"] is True
    out["filterUser"]=str(out["filterUser"] or "")
    out["filterDue"]=out["filterDue"] if out["filterDue"] in {"all","next7","nextMonth","overdue","noDueDate"} else "all"
    out["includeWithRemarkable"]=out["includeWithRemarkable"] is not False
    out["customJql"]=str(out["customJql"] or "").strip()
    out["useJiraModal"]=out["useJiraModal"] is True
    out["showMiniMap"]=out["showMiniMap"] is not False
    out["startingView"]=out["startingView"] if out["startingView"] in {"default","dashboard","milestone"} else "default"
    return out

def _read_preferences():
    with _preferences_lock:
        try:
            with open(PREFERENCES_FILE,"r",encoding="utf-8") as fh:
                return _normalise_preferences(json.load(fh))
        except FileNotFoundError:
            return dict(DEFAULT_PREFERENCES)
        except Exception as e:
            print(f"  Preferences: could not read {PREFERENCES_FILE}: {e}")
            return dict(DEFAULT_PREFERENCES)

def _write_preferences(updates):
    if not isinstance(updates,dict):
        raise ValueError("Preferences must be an object.")
    with _preferences_lock:
        try:
            with open(PREFERENCES_FILE,"r",encoding="utf-8") as fh:
                data=_normalise_preferences(json.load(fh))
        except Exception:
            data=dict(DEFAULT_PREFERENCES)
        data.update({k:updates[k] for k in DEFAULT_PREFERENCES if k in updates})
        data=_normalise_preferences(data)
        os.makedirs(PREFERENCES_DIR,exist_ok=True)
        temp_file=PREFERENCES_FILE+".tmp"
        with open(temp_file,"w",encoding="utf-8") as fh:
            json.dump(data,fh,indent=2,ensure_ascii=False)
            fh.write("\n")
        os.replace(temp_file,PREFERENCES_FILE)
        return data

def resource_path(relative_path):
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, relative_path)

def _version_tuple(value):
    try:
        parts=str(value or "").strip().lstrip("vV").split(".")
        nums=[]
        for part in parts[:3]:
            digits="".join(ch for ch in part if ch.isdigit())
            nums.append(int(digits or 0))
        while len(nums)<3:
            nums.append(0)
        return tuple(nums[:3])
    except Exception:
        return (0,0,0)

def _get_latest_stable_release():
    """Return the highest published, non-draft, non-prerelease GitHub release."""
    api=f"https://api.github.com/repos/{GITHUB_REPO}/releases?per_page=100&t={int(time.time())}"
    resp=req.get(
        api,
        headers={
            "Accept":"application/vnd.github+json",
            "Cache-Control":"no-cache",
            "Pragma":"no-cache",
            "X-GitHub-Api-Version":"2022-11-28",
        },
        timeout=10,
    )
    resp.raise_for_status()
    releases=resp.json()
    if not isinstance(releases,list):
        return None

    candidates=[]
    for release in releases:
        if not isinstance(release,dict):
            continue
        # Ignore drafts and prereleases. Only published stable releases
        # should be candidates for automatic application updates.
        if release.get("draft") or release.get("prerelease"):
            continue
        tag=str(release.get("tag_name") or "").strip()
        version=_version_tuple(tag)
        if not tag or version <= (0,0,0):
            continue
        candidates.append((version,release))

    if not candidates:
        return None

    candidates.sort(key=lambda item:item[0],reverse=True)
    return candidates[0][1]

app=Flask(__name__)

if os.name == "nt":
    _advapi32=ctypes.WinDLL("advapi32", use_last_error=True)
    _CredWriteW=_advapi32.CredWriteW
    _CredWriteW.argtypes=[ctypes.c_void_p,ctypes.c_uint]
    _CredWriteW.restype=ctypes.c_bool
    _CredReadW=_advapi32.CredReadW
    _CredReadW.argtypes=[ctypes.c_wchar_p,ctypes.c_uint,ctypes.c_uint,ctypes.POINTER(ctypes.c_void_p)]
    _CredReadW.restype=ctypes.c_bool
    _CredDeleteW=_advapi32.CredDeleteW
    _CredDeleteW.argtypes=[ctypes.c_wchar_p,ctypes.c_uint,ctypes.c_uint]
    _CredDeleteW.restype=ctypes.c_bool
    _CredFree=_advapi32.CredFree
    _CredFree.argtypes=[ctypes.c_void_p]
    _CredFree.restype=ctypes.c_bool

    class _FILETIME(ctypes.Structure):
        _fields_=[
            ("dwLowDateTime",ctypes.c_uint32),
            ("dwHighDateTime",ctypes.c_uint32),
        ]

    class _CREDENTIALW(ctypes.Structure):
        _fields_=[
            ("Flags",ctypes.c_uint32),
            ("Type",ctypes.c_uint32),
            ("TargetName",ctypes.c_wchar_p),
            ("Comment",ctypes.c_wchar_p),
            ("LastWritten",_FILETIME),
            ("CredentialBlobSize",ctypes.c_uint32),
            ("CredentialBlob",ctypes.POINTER(ctypes.c_ubyte)),
            ("Persist",ctypes.c_uint32),
            ("AttributeCount",ctypes.c_uint32),
            ("Attributes",ctypes.c_void_p),
            ("TargetAlias",ctypes.c_wchar_p),
            ("UserName",ctypes.c_wchar_p),
        ]

def _credential_read():
    """Read the Jira email/API key from Windows Credential Manager."""
    if os.name != "nt":
        raise RuntimeError("This credential store requires Windows.")
    ptr=ctypes.c_void_p()
    if not _CredReadW(CREDENTIAL_TARGET,CRED_TYPE_GENERIC,0,ctypes.byref(ptr)):
        return None
    try:
        cred=ctypes.cast(ptr,ctypes.POINTER(_CREDENTIALW)).contents
        raw=ctypes.string_at(cred.CredentialBlob,cred.CredentialBlobSize)
        data=json.loads(raw.decode("utf-8"))
        email=str(data.get("email") or "").strip()
        api_key=str(data.get("apiKey") or "").strip()
        if not email or not api_key:
            return None
        return {"email":email,"apiKey":api_key}
    finally:
        _CredFree(ptr)

def _credential_write(email,api_key):
    """Store the Jira credentials in Windows Credential Manager."""
    if os.name != "nt":
        raise RuntimeError("This credential store requires Windows.")
    email=str(email or "").strip()
    api_key=str(api_key or "").strip()
    if not email or not api_key:
        raise ValueError("Email and API key are required.")
    payload=json.dumps({"email":email,"apiKey":api_key},separators=(",",":")).encode("utf-8")
    if len(payload)>5120:
        raise ValueError("The credential is too large for Windows Credential Manager.")

    blob=(ctypes.c_ubyte*len(payload)).from_buffer_copy(payload)
    cred=_CREDENTIALW()
    cred.Flags=0
    cred.Type=CRED_TYPE_GENERIC
    cred.TargetName=CREDENTIAL_TARGET
    cred.Comment="Jira Dependency Map credentials"
    cred.CredentialBlobSize=len(payload)
    cred.CredentialBlob=ctypes.cast(blob,ctypes.POINTER(ctypes.c_ubyte))
    cred.Persist=CRED_PERSIST_LOCAL_MACHINE
    cred.AttributeCount=0
    cred.Attributes=None
    cred.TargetAlias=None
    cred.UserName=email
    if not _CredWriteW(ctypes.byref(cred),0):
        err=ctypes.get_last_error()
        raise RuntimeError(f"Windows Credential Manager could not save the credential (error {err}).")

def _credential_delete():
    """Remove the Jira credentials from Windows Credential Manager."""
    if os.name != "nt":
        raise RuntimeError("This credential store requires Windows.")
    if not _CredDeleteW(CREDENTIAL_TARGET,CRED_TYPE_GENERIC,0):
        err=ctypes.get_last_error()
        # ERROR_NOT_FOUND = 1168. Treat it as already removed.
        if err != 1168:
            raise RuntimeError(f"Windows Credential Manager could not remove the credential (error {err}).")

def get_jira_headers():
    credential=_credential_read()
    if not credential:
        raise RuntimeError("No Jira credential is configured. Restart the app and enter your Jira email and API key.")
    # Jira Basic authentication is base64(email:api_key). The encoded value
    # is generated only in memory and is never stored in the source or browser.
    basic=base64.b64encode(f"{credential['email']}:{credential['apiKey']}".encode("utf-8")).decode("ascii")
    return {"Authorization":f"Basic {basic}","Content-Type":"application/json","Accept":"application/json"}


# ---------------------------------------------------------------------------
# Jira helpers
# ---------------------------------------------------------------------------

def jira_error(resp):
    try:
        data=resp.json(); return str(data.get("errorMessages") or data.get("errors") or data)
    except Exception: return resp.text or resp.reason

def _jira_search(jql, fields, label):
    """Run a paginated Jira JQL search and return all matching issues."""
    url=f"{JIRA_BASE_URL}/rest/api/3/search/jql"
    all_issues=[]; token=None; page=0; batch_size=JIRA_BATCH_SIZE
    _set_loading_progress(phase=f"Downloading batch {page} work items…",batch=0,fetched=0,total=None,detail="Connecting to Jira…")
    while True:
        page+=1
        body={"jql":jql,"maxResults":batch_size,"fields":fields}
        if token: body["nextPageToken"]=token
        _set_loading_progress(phase=f"Downloading batch {page} work items…",batch=page,fetched=len(all_issues),detail=f"Requesting batch {page}…")
        print(f"  -> Jira {label} page {page} (have {len(all_issues):,} so far; batch size {batch_size:,})")
        started=time.time()
        request_headers=get_jira_headers()
        request_headers.update({"Cache-Control":"no-cache","Pragma":"no-cache"})
        resp=JIRA_HTTP_SESSION.post(url,headers=request_headers,json=body,timeout=60)
        # Some Jira configurations enforce a smaller maxResults limit. Fall back once.
        if resp.status_code==400 and batch_size!=100:
            print(f"  <- Jira rejected batch size {batch_size}; retrying with 100")
            batch_size=100
            page-=1
            continue
        print(f"  <- HTTP {resp.status_code} ({len(resp.content):,} bytes, {time.time()-started:.2f}s)")
        if not resp.ok: raise RuntimeError(f"Jira API {resp.status_code}: {jira_error(resp)}")
        data=resp.json(); batch=data.get("issues",[]); all_issues.extend(batch); token=data.get("nextPageToken")
        total=data.get("total")
        _set_loading_progress(phase=f"Downloading batch {page} work items…",batch=page,fetched=len(all_issues),total=total,detail=f"Batch {page}: {len(batch):,} downloaded ({len(all_issues):,}" + (f" of {total:,}" if isinstance(total,int) else "") + ")")
        if not token or not batch: break
    _set_loading_progress(phase=f"Downloaded {label} work items",batch=page,fetched=len(all_issues),total=len(all_issues),detail=f"{len(all_issues):,} work items downloaded")
    due_dates=sum(1 for issue in all_issues if (issue.get("fields") or {}).get("duedate"))
    link_sets=sum(1 for issue in all_issues if (issue.get("fields") or {}).get("issuelinks"))
    print(f"  OK {label}: fetched {len(all_issues):,} issues ({due_dates:,} with due dates; {link_sets:,} with issue links)")
    return all_issues

def _external_blocker_keys(raw_issues):
    """Return linked blocker keys that were outside the main JQL result set."""
    in_scope={str(r.get("key") or "").strip() for r in raw_issues if r.get("key")}
    external=set()
    for r in raw_issues:
        source=r.get("key")
        if source not in in_scope: continue
        for link in (r.get("fields") or {}).get("issuelinks") or []:
            t=link.get("type") or {}
            inward=(t.get("inward") or "").strip().lower()
            outward=(t.get("outward") or "").strip().lower()
            blocker=blocked=None
            if outward=="blocks" and link.get("outwardIssue"):
                blocker=source; blocked=link["outwardIssue"].get("key")
            elif inward=="is blocked by" and link.get("inwardIssue"):
                blocker=link["inwardIssue"].get("key"); blocked=source
            if blocker and blocked and blocker!=blocked and blocker not in in_scope and blocked in in_scope:
                external.add(str(blocker).strip())
    return sorted(k for k in external if k)

def jira_fetch_external_issues(raw_issues, include_completed=True):
    """Recursively fetch external blockers until no new blocker keys are found."""
    fields=["summary","status","priority","assignee","duedate","issuelinks","parent","customfield_10014","labels"]
    # Jira can impose a limit on the number of values in an IN clause. Keep the
    # normal case to one JQL request, and only split unusually large sets.
    chunk_size=1000

    known={str(r.get("key")).strip() for r in raw_issues if r.get("key")}
    pending=set(_external_blocker_keys(raw_issues)) - known
    fetched=[]
    round_no=0

    while pending:
        round_no += 1
        current=sorted(pending)
        pending.clear()
        print(f"  External blockers: round {round_no}, {len(current):,} new ticket(s) to fetch")

        round_fetched=[]
        for start in range(0,len(current),chunk_size):
            chunk=current[start:start+chunk_size]
            key_list=", ".join(chunk)
            jql=f"key in ({key_list})"
            if not include_completed:
                jql=f"({jql}) AND statusCategory != Done"
            print(f"  External blockers: requesting {len(chunk):,} ticket(s) in one JQL")
            round_fetched.extend(_jira_search(jql,fields,"external blocker"))

        # Only successfully returned issues are candidates for another round.
        # This also prevents circular dependency chains from causing an endless loop.
        new_issues=[]
        for issue in round_fetched:
            key=str(issue.get("key") or "").strip()
            if key and key not in known:
                known.add(key)
                new_issues.append(issue)

        fetched.extend(new_issues)

        # Inspect the newly fetched issues for blockers that are still outside
        # the complete set we've already seen, then fetch those in the next round.
        if new_issues:
            pending.update(set(_external_blocker_keys(new_issues)) - known)

        print(f"  External blockers: round {round_no} found {len(new_issues):,} new issue(s); {len(pending):,} more blocker(s) queued")

    _set_loading_progress(phase="Processing dependencies…",batch=0,fetched=len(fetched),total=len(fetched),detail=f"{len(fetched):,} external blockers downloaded")
    print(f"  External blockers: recursively found {len(fetched):,} additional issue(s)")
    return fetched

def _base_issue_fields():
    return ["summary","status","priority","assignee","duedate","issuelinks","parent","customfield_10014","labels"]

def _completed_jql(jql):
    """Restrict a JQL query to Jira's Done status category."""
    base=str(jql or JQL_QUERY).strip() or JQL_QUERY
    return f"({base}) AND statusCategory = Done"

def _merge_issues(target, additions):
    existing={str(r.get("key") or "").strip() for r in target if r.get("key")}
    for issue in additions or []:
        key=str(issue.get("key") or "").strip()
        if key and key not in existing:
            target.append(issue)
            existing.add(key)
    return target

def jira_fetch_active_issues(jql=None):
    fields=_base_issue_fields()
    active_jql=_active_jql(jql)
    all_issues=_jira_search(active_jql,fields,"open")

    # First external-ticket pass: only after every open/main ticket has been
    # downloaded. This keeps the first board build focused on active work.
    _set_loading_progress(phase="Checking external blockers for open tickets…",batch=0,fetched=len(all_issues),total=len(all_issues),detail="Checking links from open tickets…")
    external_issues=jira_fetch_external_issues(all_issues, include_completed=True)
    _merge_issues(all_issues, external_issues)
    return all_issues

def jira_fetch_completed_issues(jql=None):
    fields=_base_issue_fields()
    completed_jql=_completed_jql(jql)
    completed=_jira_search(completed_jql,fields,"completed")

    # Second external-ticket pass: only after every completed ticket has been
    # downloaded, so blockers referenced solely by completed work are included.
    _set_loading_progress(phase="Checking external blockers for completed tickets…",batch=0,fetched=len(completed),total=len(completed),detail="Checking links from completed tickets…")
    external_issues=jira_fetch_external_issues(completed, include_completed=True)
    _merge_issues(completed, external_issues)
    return completed

def jira_fetch_all_issues(jql=None):
    """Load open tickets, check their externals, then completed tickets, then their externals."""
    active=jira_fetch_active_issues(jql)
    completed=jira_fetch_completed_issues(jql)
    all_issues=[]
    _merge_issues(all_issues,active)
    _merge_issues(all_issues,completed)
    _set_loading_progress(phase="Processing dependencies…",batch=0,fetched=len(all_issues),total=len(all_issues),detail=f"{len(all_issues):,} tickets ready")
    print(f"  OK fetched {len(all_issues):,} total issues after open/completed external checks")
    return all_issues

def _active_jql(jql):
    """Restrict a JQL query to Jira's non-Done status category."""
    base=str(jql or JQL_QUERY).strip() or JQL_QUERY
    return f"({base}) AND statusCategory != Done"

def _completed_cache_key(jql, generation=None):
    base=str(jql or JQL_QUERY).strip() or JQL_QUERY
    generation=str(generation or "").strip()
    return f"{base}\n__load_generation__={generation}" if generation else base

def _background_completed_load(jql, active_raw, generation=None):
    key=_completed_cache_key(jql,generation)
    try:
        with _completed_loads_lock:
            _completed_loads[key]={"status":"downloading","fetched":0,"detail":"Starting completed ticket download…","graph":None,"error":None}
        print(f"  Background completed load started for JQL generation {generation}: {jql}")
        completed=jira_fetch_completed_issues(jql)
        raw=[]
        _merge_issues(raw,active_raw)
        _merge_issues(raw,completed)
        graph=serialize_graph(raw,jql)
        with _completed_loads_lock:
            _completed_loads[key]={"status":"ready","fetched":len(raw),"detail":f"{len(raw):,} total tickets downloaded","graph":graph,"error":None}
        print(f"  Background completed load complete for generation {generation}: {len(raw):,} total tickets")
    except Exception as e:
        with _completed_loads_lock:
            _completed_loads[key]={"status":"error","fetched":0,"detail":"Completed ticket download failed","graph":None,"error":str(e)}
        print(f"  Background completed load failed for generation {generation}: {e}")

def _start_background_full_load(jql, active_raw, generation=None):
    key=_completed_cache_key(jql,generation)
    with _completed_loads_lock:
        existing=_completed_loads.get(key)
        if existing and existing.get("status") in {"downloading","ready"}:
            return
        _completed_loads[key]={"status":"queued","fetched":0,"detail":"Queued completed ticket download…","graph":None,"error":None}
    threading.Thread(target=_background_completed_load,args=(jql,active_raw,generation),daemon=True,name="jira-completed-loader").start()

def _extract_epic(fields):
    """Return {key, summary, url} for the parent epic, or None."""
    # Next-gen projects: epic is the direct parent with issuetype=Epic
    parent=fields.get("parent") or {}
    if parent.get("key"):
        pf=parent.get("fields") or {}
        if (pf.get("issuetype") or {}).get("name","").lower()=="epic":
            return {"key":parent["key"],"summary":pf.get("summary",""),"url":f"{JIRA_BASE_URL}/browse/{parent['key']}"}
    # Classic projects: customfield_10014 holds the epic key as a plain string
    epic_key=fields.get("customfield_10014")
    if epic_key and isinstance(epic_key,str):
        return {"key":epic_key,"summary":"","url":f"{JIRA_BASE_URL}/browse/{epic_key}"}
    return None

# ---------------------------------------------------------------------------
# Graph logic
# ---------------------------------------------------------------------------

def parse_dependency_graph(raw):
    # Hard-remove cancelled/archived; keep Done & Completed so the frontend toggle can show/hide them.
    HARD_REMOVE={"cancelled","canceled","archived"}
    issues={}
    for r in raw:
        key=r.get("key"); f=r.get("fields") or {}; s=f.get("status") or {}; name=s.get("name") or ""
        if not key or name.strip().lower() in HARD_REMOVE: continue
        issues[key]={
            "key":key,"summary":f.get("summary") or "","status":name,
            "priority":(f.get("priority") or {}).get("name"),
            "assignee":((f.get("assignee") or {}).get("displayName") or (f.get("assignee") or {}).get("name") or "Unassigned"),
            "assigneeAccountId":(f.get("assignee") or {}).get("accountId"),
            "dueDate":f.get("duedate") or None,
            "labels":f.get("labels") or [],
            "epic":_extract_epic(f),
            "url":f"{JIRA_BASE_URL}/browse/{key}",
            "blockers":set(),"blocked":set(),"externalBlockers":[]
        }
    edges=set(); external=defaultdict(dict)
    for r in raw:
        source=r.get("key")
        if source not in issues: continue
        for link in (r.get("fields") or {}).get("issuelinks") or []:
            t=link.get("type") or {}
            inward=(t.get("inward") or "").strip().lower()
            outward=(t.get("outward") or "").strip().lower()
            blocker=blocked=None
            if outward=="blocks" and link.get("outwardIssue"): blocker=source; blocked=link["outwardIssue"].get("key")
            elif inward=="is blocked by" and link.get("inwardIssue"): blocker=link["inwardIssue"].get("key"); blocked=source
            if not blocker or not blocked or blocker==blocked: continue
            if blocker in issues and blocked in issues:
                # Include all internal edges — frontend toggle handles done/completed visibility
                edges.add((blocker,blocked))
            elif blocked in issues and blocker not in issues:
                # External blocker (outside our JQL scope) — always include
                external[blocked][blocker]={"key":blocker,"url":f"{JIRA_BASE_URL}/browse/{blocker}"}
    for a,b in edges: issues[a]["blocked"].add(b); issues[b]["blockers"].add(a)
    for k,v in external.items(): issues[k]["externalBlockers"]=list(v.values())
    return issues,edges

def detect_cycles(keys,edges):
    """Iterative Tarjan-style cycle detection — avoids Python recursion limit."""
    graph=defaultdict(list)
    for a,b in edges: graph[a].append(b)
    # colour: 0=white, 1=grey (in stack), 2=black (done)
    colour={k:0 for k in keys}; cycles=set()
    for start in keys:
        if colour[start]!=0: continue
        # Each stack frame: (node, iterator-over-neighbours, path-index)
        path=[]; path_set=set(); call_stack=[(start,iter(graph[start]))]
        colour[start]=1; path.append(start); path_set.add(start)
        while call_stack:
            node,it=call_stack[-1]
            try:
                nxt=next(it)
                if colour[nxt]==0:
                    colour[nxt]=1; path.append(nxt); path_set.add(nxt)
                    call_stack.append((nxt,iter(graph[nxt])))
                elif colour[nxt]==1:
                    # Back-edge → everything from nxt to end of path is in a cycle
                    idx=path.index(nxt)
                    cycles.update(path[idx:])
            except StopIteration:
                colour[node]=2
                if path and path[-1]==node:
                    path.pop(); path_set.discard(node)
                call_stack.pop()
    return cycles

def calculate_levels(issues,edges):
    cycles=detect_cycles(issues.keys(),edges); graph=defaultdict(list); indegree=defaultdict(int)
    for a,b in edges:
        if a in cycles or b in cycles: continue
        graph[a].append(b); indegree[b]+=1
    level={k:0 for k in issues if k not in cycles}
    for k,v in issues.items():
        if k not in cycles and v["externalBlockers"]: level[k]=1
    q=deque(k for k in issues if k not in cycles and indegree[k]==0)
    while q:
        n=q.popleft()
        for nxt in graph[n]:
            level[nxt]=max(level.get(nxt,0),level[n]+1); indegree[nxt]-=1
            if indegree[nxt]==0: q.append(nxt)
    for k,v in issues.items():
        if k in cycles: level[k]=0
    return level,cycles

def serialize_graph(raw, jql=None):
    issues,edges=parse_dependency_graph(raw); levels,cycles=calculate_levels(issues,edges); out=[]
    for k,v in issues.items():
        out.append({
            "key":k,"summary":v["summary"],"status":v["status"],"priority":v["priority"],"assignee":v.get("assignee") or "Unassigned","assigneeAccountId":v.get("assigneeAccountId"),
            "labels":v.get("labels") or [],
            "dueDate":v.get("dueDate"),
            "epic":v.get("epic"),"url":v["url"],
            "blockers":sorted(v["blockers"]),"blocked":sorted(v["blocked"]),
            "externalBlockers":sorted(v["externalBlockers"],key=lambda x:x["key"]),
            "level":levels.get(k,0),"cycle":k in cycles
        })
    out.sort(key=lambda x:(x["level"],x["key"]))
    return {"issues":out,"edges":[{"from":a,"to":b} for a,b in sorted(edges)],
            "levels":max((i["level"] for i in out),default=0),
            "cycleKeys":sorted(cycles),"total":len(out),"jql":str(jql or JQL_QUERY).strip() or JQL_QUERY}

# ---------------------------------------------------------------------------
# Flask routes
# ---------------------------------------------------------------------------

@app.route("/api/loading-status")
def api_loading_status():
    return jsonify(_get_loading_progress())

@app.route("/api/dependencies")
def api_dependencies():
    try:
        jql=request.args.get("jql")
        if jql is not None and not str(jql).strip():
            jql=None
        active_jql=str(jql or JQL_QUERY).strip() or JQL_QUERY
        mode=(request.args.get("mode") or "all").strip().lower()
        generation=str(request.args.get("generation") or "").strip()
        if mode == "active":
            raw=jira_fetch_active_issues(active_jql)
            # Associate the slower completed-ticket load with the exact browser
            # refresh that requested it. An older refresh must never publish its
            # snapshot into a newer refresh.
            _start_background_full_load(active_jql, raw, generation)
            return jsonify(serialize_graph(raw,active_jql))
        return jsonify(serialize_graph(jira_fetch_all_issues(active_jql), active_jql))
    except RuntimeError as e: return jsonify({"error":str(e)}),502
    except Exception as e: return jsonify({"error":f"Unexpected error: {e}"}),500

@app.route("/api/completed-status")
def api_completed_status():
    jql=str(request.args.get("jql") or JQL_QUERY).strip() or JQL_QUERY
    generation=str(request.args.get("generation") or "").strip()
    with _completed_loads_lock:
        data=dict(_completed_loads.get(_completed_cache_key(jql,generation) or "", {"status":"not-started","fetched":0,"detail":"Completed tickets have not started downloading.","graph":None,"error":None}))
    data.pop("graph",None)
    return jsonify(data)

@app.route("/api/completed-data")
def api_completed_data():
    jql=str(request.args.get("jql") or JQL_QUERY).strip() or JQL_QUERY
    generation=str(request.args.get("generation") or "").strip()
    with _completed_loads_lock:
        data=_completed_loads.get(_completed_cache_key(jql,generation))
        if not data or data.get("status") != "ready":
            return jsonify({"status":(data or {}).get("status","not-started")}),202
        return jsonify(data.get("graph") or {}),200

@app.route("/api/links",methods=["POST"])
def api_links():
    try:
        body=request.get_json(force=True) or {}; links=body.get("links") or []
        if not isinstance(links,list) or not links: return jsonify({"ok":True,"saved":0})
        saved=0
        for link in links:
            source=str((link or {}).get("source") or "").strip()
            target=str((link or {}).get("target") or "").strip()
            if not source or not target or source==target: raise RuntimeError("Invalid dependency in save request.")
            # FIX: Jira GET shows outwardIssue=BLOCKED on the blocker's page.
            # POST must mirror this: outwardIssue=target(blocked), inwardIssue=source(blocker).
            payload={"type":{"name":"Blocks"},"outwardIssue":{"key":target},"inwardIssue":{"key":source}}
            resp=req.post(f"{JIRA_BASE_URL}/rest/api/3/issueLink",headers=get_jira_headers(),json=payload,timeout=30)
            if not resp.ok: raise RuntimeError(f"Jira API {resp.status_code}: {jira_error(resp)}")
            saved+=1
        return jsonify({"ok":True,"saved":saved})
    except RuntimeError as e: return jsonify({"error":str(e)}),502
    except Exception as e: return jsonify({"error":f"Unexpected error: {e}"}),500

@app.route("/api/issues",methods=["POST"])
def api_issues():
    try:
        body=request.get_json(force=True) or {}
        changes=body.get("changes") or []
        if not isinstance(changes,list): raise RuntimeError("Invalid issue changes payload.")
        saved=0
        for ch in changes:
            key=str((ch or {}).get("key") or "").strip()
            if not key: raise RuntimeError("Missing issue key.")
            fields={}
            if "priority" in ch:
                priority=str(ch.get("priority") or "").strip()
                if not priority: raise RuntimeError(f"Missing priority for {key}.")
                fields["priority"]={"name":priority}
            if "assigneeAccountId" in ch:
                aid=ch.get("assigneeAccountId")
                fields["assignee"]={"accountId":aid} if aid else None
            if "dueDate" in ch:
                due_date=ch.get("dueDate")
                if due_date is not None:
                    due_date=str(due_date).strip()
                    if due_date:
                        import datetime as _dt
                        try: _dt.date.fromisoformat(due_date)
                        except ValueError: raise RuntimeError(f"Invalid due date for {key}.")
                    else:
                        due_date=None
                fields["duedate"]=due_date
            if not fields: continue
            resp=req.put(f"{JIRA_BASE_URL}/rest/api/3/issue/{key}",headers=get_jira_headers(),json={"fields":fields},timeout=30)
            if not resp.ok: raise RuntimeError(f"Jira API {resp.status_code}: {jira_error(resp)}")
            saved+=1
        return jsonify({"ok":True,"saved":saved})
    except RuntimeError as e: return jsonify({"error":str(e)}),502
    except Exception as e: return jsonify({"error":f"Unexpected error: {e}"}),500

@app.route("/api/credential-status")
def api_credential_status():
    try:
        credential=_credential_read()
        return jsonify({"configured":bool(credential),"email":credential["email"] if credential else ""})
    except Exception as e:
        return jsonify({"configured":False,"error":str(e)}),500

@app.route("/api/startup-messages")
def api_startup_messages():
    print(f"[Startup Messages] Fetching Sitebuilder feed: {STARTUP_MESSAGES_URL}", flush=True)
    try:
        response=req.get(STARTUP_MESSAGES_URL,timeout=15,headers={"Accept":"application/json"})
        print(f"[Startup Messages] Sitebuilder response: HTTP {response.status_code}, content-type={response.headers.get('Content-Type','')}, bytes={len(response.content)}", flush=True)
        if not response.ok:
            print(f"[Startup Messages] Sitebuilder request failed: {response.text[:500]}", flush=True)
            return jsonify({"error":f"Sitebuilder returned HTTP {response.status_code}"}),502
        data=response.json()
        items=data.get("items",[]) if isinstance(data,dict) else []
        print(f"[Startup Messages] JSON parsed successfully. Raw item count: {len(items) if isinstance(items,list) else 'not a list'}", flush=True)
        messages=[]
        for index,item in enumerate(items if isinstance(items,list) else []):
            if not isinstance(item,dict):
                print(f"[Startup Messages] Item {index}: skipped because it is not an object", flush=True)
                continue
            title=str(item.get("title") or "").strip()
            body=str(item.get("parsedContentBody") or "").strip()
            print(f"[Startup Messages] Item {index}: title={title!r}, parsedContentBody length={len(body)}", flush=True)
            if title or body:
                messages.append({"title":title,"parsedContentBody":body})
        print(f"[Startup Messages] Returning {len(messages)} usable message(s) to browser", flush=True)
        return jsonify({"items":messages})
    except Exception as e:
        print(f"[Startup Messages] ERROR: {type(e).__name__}: {e}", flush=True)
        return jsonify({"error":f"Could not load startup messages: {e}"}),502

@app.route("/api/app-version")
def api_app_version():
    result={
        "current":APP_VERSION,
        "latest":APP_VERSION,
        "updateAvailable":False,
        "canInstall":bool(getattr(sys,"frozen",False) and _launcher_path()),
        "releaseUrl":f"https://github.com/{GITHUB_REPO}/releases/latest"
    }
    try:
        release=_get_latest_stable_release()
        if release:
            latest=str(release.get("tag_name") or "").strip()
            if latest:
                result["latest"]=latest.lstrip("vV")
                result["updateAvailable"]=_version_tuple(latest)>_version_tuple(APP_VERSION)
                result["releaseUrl"]=release.get("html_url") or result["releaseUrl"]
    except Exception:
        pass
    return jsonify(result)

@app.route("/api/credentials",methods=["POST"])
def api_credentials():
    try:
        body=request.get_json(force=True) or {}
        email=str(body.get("email") or "").strip()
        api_key=str(body.get("apiKey") or "").strip()
        if not email or not api_key:
            return jsonify({"error":"Email and API key are required."}),400
        if "@" not in email:
            return jsonify({"error":"Enter a valid email address."}),400
        _credential_write(email,api_key)
        # Validate immediately so a typo does not leave the app apparently configured.
        headers=get_jira_headers()
        test=req.get(f"{JIRA_BASE_URL}/rest/api/3/myself",headers=headers,timeout=30)
        if not test.ok:
            _credential_delete()
            return jsonify({"error":f"Jira authentication failed ({test.status_code}): {jira_error(test)}"}),401
        return jsonify({"ok":True,"email":email})
    except RuntimeError as e:
        return jsonify({"error":str(e)}),500
    except Exception as e:
        return jsonify({"error":f"Could not save credential: {e}"}),500

@app.route("/api/credentials/remove",methods=["POST"])
def api_credentials_remove():
    try:
        _credential_delete()
        # Start a completely new process rather than replacing the current
        # process in-place. Replacing the process while Flask is still serving
        # this request can leave the browser pointing at localhost before the
        # new server has started listening.
        def restart():
            time.sleep(0.8)
            if getattr(sys,"frozen",False):
                command=[sys.executable,*sys.argv[1:]]
            else:
                command=[sys.executable,os.path.abspath(sys.argv[0]),*sys.argv[1:]]
            env=os.environ.copy()
            env["JIRA_DEP_MAP_RESTART"]="1"
            subprocess.Popen(
                command,
                close_fds=True,
                env=env,
                creationflags=getattr(subprocess,"CREATE_NEW_PROCESS_GROUP",0) if os.name=="nt" else 0
            )
            os._exit(0)
        threading.Thread(target=restart,daemon=True).start()
        return jsonify({"ok":True,"restarting":True})
    except Exception as e:
        return jsonify({"error":f"Could not remove credential: {e}"}),500

@app.route("/api/install-update",methods=["POST"])
def api_install_update():
    """Restart through the stable launcher so it can install the latest release."""
    global _update_restart_started

    launcher=_launcher_path()
    if not getattr(sys,"frozen",False) or not launcher:
        return jsonify({
            "error":"Automatic updates are only available when the app is run from the installed launcher."
        }),409

    with _update_restart_lock:
        if _update_restart_started:
            return jsonify({"ok":True,"restarting":True,"pid":os.getpid()})
        try:
            env=os.environ.copy()
            # The launcher passes this to the replacement app so it reuses the
            # existing browser tab instead of opening another one.
            env["JIRA_DEP_MAP_RESTART"]="1"
            subprocess.Popen(
                [launcher],
                cwd=os.path.dirname(launcher) or None,
                env=env,
                close_fds=True,
                creationflags=getattr(subprocess,"CREATE_NEW_PROCESS_GROUP",0) if os.name=="nt" else 0
            )
            _update_restart_started=True
        except Exception as e:
            return jsonify({"error":f"Could not start the updater: {e}"}),500

    def stop_current_app():
        # Give Flask enough time to send the response before releasing port 5001.
        time.sleep(0.8)
        os._exit(0)

    threading.Thread(target=stop_current_app,daemon=True).start()
    return jsonify({"ok":True,"restarting":True,"pid":os.getpid()})


@app.route("/api/update-health")
def api_update_health():
    return jsonify({"ok":True,"version":APP_VERSION,"pid":os.getpid()})


@app.route("/api/preferences",methods=["GET"])
def api_preferences():
    try:
        return jsonify(_read_preferences())
    except Exception as e:
        return jsonify({"error":f"Could not read preferences: {e}"}),500

@app.route("/api/preferences",methods=["POST"])
def api_preferences_save():
    try:
        body=request.get_json(force=True) or {}
        return jsonify(_write_preferences(body))
    except Exception as e:
        return jsonify({"error":f"Could not save preferences: {e}"}),500

@app.route("/api/config")
def api_config():
    return jsonify({"jiraBaseUrl":JIRA_BASE_URL,"port":PORT,"jql":JQL_QUERY})

@app.route("/api/link",methods=["POST"])
def api_link():
    try:
        body=request.get_json(force=True) or {}
        source=str(body.get("source") or "").strip(); target=str(body.get("target") or "").strip()
        if not source or not target or source==target:
            return jsonify({"error":"A valid source and target issue are required."}),400
        # FIX: same direction correction as /api/links
        payload={"type":{"name":"Blocks"},"outwardIssue":{"key":target},"inwardIssue":{"key":source}}
        resp=req.post(f"{JIRA_BASE_URL}/rest/api/3/issueLink",headers=get_jira_headers(),json=payload,timeout=30)
        if not resp.ok: raise RuntimeError(f"Jira API {resp.status_code}: {jira_error(resp)}")
        return jsonify({"ok":True,"source":source,"target":target})
    except RuntimeError as e: return jsonify({"error":str(e)}),502
    except Exception as e: return jsonify({"error":f"Unexpected error: {e}"}),500

@app.route("/api/unlink",methods=["POST"])
def api_unlink():
    """Delete a single Jira issue link. Called during SAVE for staged deletions."""
    try:
        body=request.get_json(force=True) or {}
        source=str(body.get("source") or "").strip()  # blocker
        target=str(body.get("target") or "").strip()  # blocked
        if not source or not target:
            return jsonify({"error":"source and target are required"}),400
        link_id=None
        # Strategy 1: find link on blocker (source) page — outwardIssue=target after fix
        r=req.get(f"{JIRA_BASE_URL}/rest/api/3/issue/{source}?fields=issuelinks",headers=get_jira_headers(),timeout=30)
        if r.ok:
            for lk in (r.json().get("fields") or {}).get("issuelinks") or []:
                t=lk.get("type") or {}
                if t.get("outward","").strip().lower()=="blocks" and (lk.get("outwardIssue") or {}).get("key")==target:
                    link_id=lk.get("id"); break
        # Strategy 2: find link on blocked (target) page — inwardIssue=source
        if not link_id:
            r2=req.get(f"{JIRA_BASE_URL}/rest/api/3/issue/{target}?fields=issuelinks",headers=get_jira_headers(),timeout=30)
            if r2.ok:
                for lk in (r2.json().get("fields") or {}).get("issuelinks") or []:
                    t=lk.get("type") or {}
                    if t.get("inward","").strip().lower()=="is blocked by" and (lk.get("inwardIssue") or {}).get("key")==source:
                        link_id=lk.get("id"); break
        if not link_id:
            return jsonify({"error":f"Could not find Jira link between {source} and {target}"}),404
        r3=req.delete(f"{JIRA_BASE_URL}/rest/api/3/issueLink/{link_id}",headers=get_jira_headers(),timeout=30)
        if not r3.ok and r3.status_code!=204:
            raise RuntimeError(f"Jira API {r3.status_code}: {jira_error(r3)}")
        return jsonify({"ok":True})
    except RuntimeError as e: return jsonify({"error":str(e)}),502
    except Exception as e: return jsonify({"error":f"Unexpected error: {e}"}),500

@app.route("/")
def index(): return Response(build_html(),mimetype="text/html")

# ---------------------------------------------------------------------------
# HTML / CSS / JS
# ---------------------------------------------------------------------------

def build_html():
    return r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Jira Dependency Map</title>
<link rel="icon" type="image/png" href="https://warwick.ac.uk/services/marketing/teams/cds/opd/1486504840-cog-cogwheel-gear-repr-options-setting_81360.png">
<style>
*{box-sizing:border-box;margin:0;padding:0}
:root{
  --bg:#f1f5f9;--surface:#fff;--border:#dbe2ea;
  --text:#172033;--muted:#64748b;--accent:#6366f1;--line:#94a3b8;
}
html,body{height:100%;overflow:hidden}
body{font-family:system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;
     background:var(--bg);color:var(--text);font-size:14px}

/* ── Header ─────────────────────────────────────────────────────────────── */
#app-header{
  height:58px;background:linear-gradient(135deg,#0f172a,#1e293b);color:#fff;
  display:flex;align-items:center;gap:12px;padding:0 18px;
  box-shadow:0 2px 14px rgba(0,0,0,.25);
}
.brand{display:flex;align-items:center;gap:9px;font-weight:700;flex-shrink:0;cursor:pointer;border-radius:7px}
.brand:focus-visible{outline:2px solid #7dd3fc;outline-offset:4px}
.brand-icon{width:30px;height:30px;border-radius:50%;background:#fff;display:inline-flex;align-items:center;justify-content:center;flex:0 0 30px;overflow:hidden}
.brand-icon img{width:21px;height:21px;object-fit:contain;display:block}
.brand small{display:block;font-size:11px;color:#94a3b8;font-weight:400;margin-top:1px}
.header-center{flex:1;display:flex;align-items:center;gap:7px}
.search-wrap{width:100%;max-width:360px;position:relative}
.search-wrap svg{position:absolute;left:10px;top:50%;transform:translateY(-50%);pointer-events:none;opacity:.45}
#search{
  width:100%;background:rgba(255,255,255,.1);border:1px solid rgba(255,255,255,.2);
  color:#fff;border-radius:7px;padding:7px 34px 7px 32px;font-size:13px;
  outline:none;transition:background .15s,border-color .15s;
}
#search:focus{background:rgba(255,255,255,.16);border-color:rgba(255,255,255,.45)}
#search::placeholder{color:rgba(255,255,255,.38)}
#search-clear{
  position:absolute;right:7px;top:50%;transform:translateY(-50%);
  width:24px;height:24px;border:0;border-radius:50%;
  background:transparent;color:rgba(255,255,255,.62);cursor:pointer;
  font-size:18px;line-height:22px;padding:0;display:none;
}
#search-clear:hover,#search-clear:focus-visible{background:rgba(255,255,255,.14);color:#fff;outline:none}
#search-clear.visible{display:block}
.sr-only{position:absolute;width:1px;height:1px;padding:0;margin:-1px;overflow:hidden;clip:rect(0,0,0,0);white-space:nowrap;border:0}
.header-actions{display:flex;align-items:center;gap:8px;flex-shrink:0}
.filter-controls{display:flex;align-items:center;gap:7px;position:relative;flex-shrink:0}
.filter-menu{display:none;position:absolute;top:calc(100% + 8px);left:0;width:300px;background:#fff;color:#172033;border:1px solid #dbe2ea;border-radius:10px;box-shadow:0 12px 30px rgba(15,23,42,.2);padding:12px;z-index:10000}
.filter-menu.open{display:block}
.filter-menu-title{font-size:11px;font-weight:850;text-transform:uppercase;letter-spacing:.07em;color:#64748b;margin:0 0 10px}
.filter-option{display:flex;align-items:center;justify-content:space-between;gap:12px;padding:9px 4px;border-bottom:1px solid #eef2f7}
.filter-option:last-child{border-bottom:0}
.filter-option-label{font-size:13px;font-weight:650;color:#334155}
.filter-checkbox{width:17px;height:17px;accent-color:#6366f1}
.filter-user-select{width:100%;box-sizing:border-box;border:1px solid #cbd5e1;border-radius:6px;background:#fff;color:#334155;padding:7px 8px;font:inherit;font-size:13px}
.filter-clear{border-color:rgba(239,68,68,.3);background:rgba(239,68,68,.08);color:#fecaca}
.filter-clear:not(:disabled):hover{background:rgba(239,68,68,.16)}
.filter-clear:disabled{opacity:.45;cursor:default}
.btn{
  border:1px solid rgba(255,255,255,.15);background:rgba(255,255,255,.08);
  color:#e2e8f0;border-radius:7px;padding:7px 11px;cursor:pointer;font-size:13px;
  transition:background .12s;display:inline-flex;align-items:center;gap:5px;
}
.btn:hover{background:rgba(255,255,255,.17)}
.view-switcher{display:inline-flex;align-items:center;padding:2px;border:1px solid rgba(255,255,255,.15);background:rgba(255,255,255,.06);border-radius:8px;gap:2px}
.view-switch{border:0;background:transparent;color:#94a3b8;border-radius:6px;padding:6px 9px;font:inherit;font-size:12px;font-weight:700;cursor:pointer;white-space:nowrap}
.view-switch:hover{background:rgba(255,255,255,.09);color:#e2e8f0}
.view-switch.active{background:#fff;color:#172033;box-shadow:0 1px 2px rgba(0,0,0,.12)}
.btn-save{font-weight:800;min-width:36px;width:36px;height:32px;padding:0;justify-content:center}.btn-save[hidden],.btn-discard[hidden]{display:none!important}
.btn-save.unsaved{background:#f59e0b;color:#172033;border-color:#fbbf24;box-shadow:0 0 0 2px rgba(245,158,11,.25);opacity:1}
.btn-save:disabled{opacity:.45;cursor:default}
.btn-discard{font-weight:800;min-width:36px;width:36px;height:32px;padding:0;justify-content:center;background:rgba(239,68,68,.12);border-color:rgba(239,68,68,.45);color:#fecaca}
.btn-discard:hover{background:rgba(239,68,68,.24);border-color:rgba(248,113,113,.7);color:#fff}
.save-progress{position:fixed;right:18px;bottom:18px;z-index:20000;display:none;min-width:220px;max-width:320px;padding:11px 14px;background:#172033;color:#fff;border:1px solid #334155;border-radius:9px;box-shadow:0 10px 30px rgba(15,23,42,.28);font-size:12px;font-weight:750}
.save-progress.show{display:block}
.save-progress-text{display:flex;align-items:center;justify-content:space-between;gap:14px}
.save-progress-bar{height:4px;margin-top:8px;background:#334155;border-radius:999px;overflow:hidden}
.save-progress-fill{height:100%;width:0;background:#6366f1;border-radius:999px;transition:width .15s ease}
.header-divider{width:1px;height:22px;background:#334155;opacity:.45;margin:0 2px}
.btn-refresh{min-width:32px;padding-left:8px;padding-right:8px;font-size:16px}
.btn-settings{min-width:32px;width:32px;height:32px;padding:0;justify-content:center;font-size:18px;color:#cbd5e1}
.btn-settings:hover{color:#fff}
#deselect{display:none;border-color:rgba(99,102,241,.5);background:rgba(99,102,241,.18);color:#c7d2fe}
#deselect.visible{display:inline-flex}
/* ── Completed toggle ────────────────────────────────────────────────────── */
.btn-toggle-completed{gap:7px;padding-left:10px}
.toggle-track{
  display:inline-block;flex-shrink:0;
  width:28px;height:16px;border-radius:8px;
  background:#475569;position:relative;
  transition:background .18s;
}
.toggle-track::after{
  content:"";position:absolute;
  width:12px;height:12px;border-radius:50%;
  background:#fff;top:2px;left:2px;
  transition:transform .18s;
}
.btn-toggle-completed.active .toggle-track{background:#6366f1}
.btn-toggle-completed.active .toggle-track::after{transform:translateX(12px)}
.btn-toggle-milestones{padding-left:11px;padding-right:11px}
.btn-toggle-milestones.active{background:rgba(56,189,248,.16);border-color:rgba(56,189,248,.45);color:#bae6fd}
#board.milestone-board{display:block;width:max-content;min-width:100%;padding-bottom:10px;}
#board.milestone-board #lines{display:none!important}
.milestone-overview{width:max-content;min-width:100%;padding:0;display:flex;flex-direction:column;gap:18px}
.milestone-overview-header{display:flex;align-items:center;justify-content:space-between;padding:0 2px}
.milestone-overview-title{font-size:12px;text-transform:uppercase;letter-spacing:.08em;font-weight:800;color:var(--muted)}
.milestone-overview-count{font-size:12px;background:#e0f2fe;border-radius:999px;padding:3px 9px;color:#0369a1;font-weight:800}
.milestone-row{display:flex;gap:14px;overflow:visible;padding:2px 2px 14px}
.milestone-item{width:400px;min-width:400px;display:flex;flex-direction:column;gap:7px}
.milestone-item .card{width:100%;}
.milestone-blocked{border:1px solid var(--border);border-radius:9px;background:#fff;padding:9px 10px;box-shadow:0 1px 2px rgba(15,23,42,.04)}
.milestone-blocked-head{display:flex;align-items:center;justify-content:space-between;gap:8px;margin-bottom:7px}
.milestone-blocked-title{font-size:10px;text-transform:uppercase;letter-spacing:.05em;font-weight:800;color:#9a6700}
.milestone-blocked-count{font-size:10px;background:#fff7ed;border:1px solid #fed7aa;border-radius:999px;padding:2px 6px;color:#9a6700;font-weight:800}
.milestone-blocked-list{display:flex;flex-direction:column;gap:4px;max-height:calc(100vh - 335px);overflow-y:auto;overscroll-behavior:contain;padding-right:2px}
.milestone-blocked-group{display:flex;flex-direction:column;gap:4px}
.milestone-blocked-group + .milestone-blocked-group{margin-top:7px}
.milestone-blocked-level{font-size:9px;text-transform:uppercase;letter-spacing:.05em;font-weight:800;color:#94a3b8;padding:2px 1px}
/* ── Hover highlight lock ─────────────────────────────────────────────── */
.hover-lock-btn{
  border:1px solid #cbd5e1;background:#fff;color:#64748b;width:24px;height:22px;
  padding:0;margin:-1px 2px 0 0;border-radius:5px;cursor:pointer;
  font-size:12px;line-height:20px;text-align:center;opacity:1;
  box-shadow:0 1px 1px rgba(15,23,42,.06);
}
.hover-lock-btn:hover{background:#f8fafc;color:#334155}
.hover-lock-btn.active{
  background:#fff7ed;border-color:#f59e0b;color:#b45309;
  box-shadow:0 0 0 2px rgba(245,158,11,.16);
}
.card.selection-highlight{
  outline:2px solid #8b5cf6;
  outline-offset:-2px;
  box-shadow:0 0 0 3px rgba(139,92,246,.14);
}
.card.highlight-locked{
  outline:2px solid #f59e0b;
  outline-offset:-2px;
  box-shadow:0 0 0 3px rgba(245,158,11,.12);
}
.card.completed .key,
.card.completed .summary{
  text-decoration:line-through;
  text-decoration-thickness:1.5px;
  text-decoration-color:currentColor;
}
.milestone-blocked-item{display:flex;align-items:center;width:100%;box-sizing:border-box;border:1px solid #e2e8f0;border-radius:5px;background:#f8fafc;padding:5px 7px;text-align:left;cursor:pointer;font-size:12px;line-height:1.3;color:#475569;overflow:hidden;white-space:nowrap}
.milestone-blocked-content{display:block;min-width:0;flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.milestone-blocked-priority{display:inline-flex;align-items:center;vertical-align:middle;margin-right:6px;flex-shrink:0}
.milestone-blocked-assignee{display:inline-flex;flex:0 0 20px;align-items:center;justify-content:center;width:20px;height:20px;margin:-2px 0 -2px 6px;border-radius:50%;background:#e2e8f0;color:#475569;font-size:9px;font-weight:800;line-height:20px;vertical-align:middle}
.milestone-blocked-assignee.unassigned{background:#2563eb;color:#fff}
.milestone-blocked-item:hover{background:#fffaf0;border-color:#fed7aa}
.milestone-blocked-item a{color:inherit;text-decoration:none}
.milestone-blocked-item a:hover{text-decoration:underline}
.milestone-blocked-item.completed,
.milestone-blocked-item.completed .milestone-blocked-key{
  text-decoration:line-through;
  text-decoration-thickness:1.5px;
  text-decoration-color:currentColor;
}
.milestone-back{display:none;position:absolute;top:62px;left:18px;z-index:30;border:0;background:transparent;color:#64748b;font-size:12px;font-weight:700;padding:5px 7px;border-radius:5px;cursor:pointer}
.milestone-back:hover{background:#e2e8f0;color:#334155}
.milestone-back.visible{display:block}
.milestone-blocked-key{font-weight:800;color:#9a6700}
.milestone-blocked-empty{font-size:10px;color:#94a3b8;padding:3px 0}
.milestone-overview-card .card{cursor:pointer}
.milestone-overview-card .card:hover{transform:translateY(-1px)}
.milestone-overview-card .card .priority-trigger{cursor:default}
.milestone-flash{animation:milestoneFlash .9s ease-out}
.dependency-flash{animation:dependencyFlash .9s ease-out}
@keyframes milestoneFlash{0%{box-shadow:0 0 0 4px rgba(56,189,248,.75)}100%{box-shadow:0 0 0 0 rgba(56,189,248,0)}}
@keyframes dependencyFlash{0%{box-shadow:0 0 0 4px rgba(99,102,241,.75)}100%{box-shadow:0 0 0 0 rgba(99,102,241,0)}}
#status-text{font-size:12px;color:#fff;white-space:nowrap}

/* ── Jira ticket preview modal ─────────────────────────────────────────── */
.ticket-preview-backdrop{
  position:fixed;inset:0;z-index:10079;
  background:rgba(15,23,42,.22);
}
.ticket-preview-modal{
  position:fixed;left:50%;top:50%;transform:translate(-50%,-50%);
  width:min(1600px,calc(100vw - 48px));height:min(760px,calc(100vh - 48px));
  z-index:10080;display:flex;flex-direction:column;overflow:hidden;resize:none;
  background:#fff;border:1px solid #cbd5e1;border-radius:10px;
  box-shadow:0 24px 70px rgba(15,23,42,.28);
}
.ticket-preview-header{flex:0 0 auto;display:flex;align-items:center;justify-content:space-between;gap:12px;padding:9px 12px;background:#f8fafc;border-bottom:1px solid #e2e8f0}
.ticket-preview-title{min-width:0;font-size:12px;font-weight:700;color:#0f172a;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.ticket-preview-actions{display:flex;align-items:center;gap:6px;flex:0 0 auto}
.ticket-preview-open,.ticket-preview-close{
  width:108px;height:30px;padding:0 10px;border:1px solid #cbd5e1;
  background:#fff;color:#334155;border-radius:5px;font-size:11px;font-weight:700;
  line-height:1;cursor:pointer;text-decoration:none;
  display:inline-flex;align-items:center;justify-content:center;white-space:nowrap;
}
.ticket-preview-open:hover{background:#f1f5f9}
.ticket-preview-close{
  background:linear-gradient(135deg,#0f172a,#1e293b);
  border-color:#334155;color:#fff;
}
.ticket-preview-close:hover{background:#334155;border-color:#475569;color:#fff}
.ticket-preview-modal iframe{display:block;flex:1 1 auto;width:100%;min-height:0;border:0;background:#fff}

/* ── Error bar ───────────────────────────────────────────────────────────── */
#error{
  display:none;position:absolute;top:58px;left:0;right:0;
  background:#fef2f2;color:#991b1b;padding:10px 18px;
  border-bottom:1px solid #fecaca;z-index:40;font-size:13px;
}


.dashboard-ticket-controls{display:flex;align-items:center;gap:8px;margin-top:9px;flex-wrap:wrap}
.dashboard-assignee-select{max-width:180px}
.dashboard-ticket-key-wrap{display:flex;align-items:center;gap:5px;min-width:0}
.dashboard-ticket.chain-date-risk{border-color:#f59e0b;background:#fffbeb}
.dashboard-risk.chain-date-risk{color:#92400e;background:#fef3c7;border-color:#fcd34d}
/* ── App shell ───────────────────────────────────────────────────────────── */
#app{height:calc(100vh - 58px);overflow-x:auto;overflow-y:hidden;position:relative}
#app.locked{
  height:auto;
  min-height:calc(100vh - 58px);
  max-height:calc(100vh - 58px);
  overflow-x:auto;
  overflow-y:auto;
}
#app.locked #board{
  /* In a dependency chain, size the board only to the columns/cards that
     are actually rendered. This prevents an old SVG/board width from leaving
     a large empty scroll area to the right. */
  width:max-content;
  min-width:0;
  padding-bottom:20px;
}
#app.milestone-mode{overflow-x:auto;overflow-y:auto}
#app.milestone-mode #board-minimap{display:none!important}
#app.dashboard-mode{overflow-x:hidden;overflow-y:auto}
#app.dashboard-mode #board{min-width:0;display:block;overflow:visible}

/* ── Board mini-map ─────────────────────────────────────────────────────── */
#board-minimap{
  position:fixed;right:16px;bottom:16px;width:220px;height:142px;
  padding:10px;background:linear-gradient(135deg,#0f172a,#1e293b);
  border:1px solid #cbd5e1;border-radius:10px;
  box-shadow:0 8px 24px rgba(15,23,42,.16);
  z-index:35;display:none;box-sizing:border-box;user-select:none;
}
#board-minimap.visible{display:block}
#board-minimap-stage{
  position:relative;width:100%;height:100%;overflow:hidden;
  border-radius:6px;background:linear-gradient(135deg,#0f172a,#1e293b);
}
.minimap-board{
  position:absolute;left:0;top:0;transform-origin:top left;
}
.minimap-column{
  position:absolute;border:1px solid #d7dee8;border-radius:3px;
  background:#eef2f7;box-sizing:border-box;
}
.minimap-card{
  position:absolute;border:1px solid #b8c4d4;border-radius:2px;
  background:#fff;box-sizing:border-box;
}
.minimap-card.milestone{border-color:#2563eb;background:#60a5fa}
.minimap-card.selected{border-color:#7c3aed;background:#a78bfa}
.minimap-card.highlight-locked{border-color:#d97706;background:#f59e0b}
.minimap-card.dimmed{opacity:.5}
.minimap-card.overdue{border-color:#ef4444;background:#ef4444;box-shadow:0 0 0 1px #b91c1c}
#board-minimap-viewport{
  position:absolute;left:0;top:0;
  border:2px solid #6366f1;background:rgba(99,102,241,.10);
  border-radius:3px;box-sizing:border-box;cursor:grab;
  min-width:8px;min-height:8px;
}
#board-minimap-viewport.dragging{cursor:grabbing}
#board-minimap-hint{
  position:absolute;right:3px;bottom:3px;font-size:8px;line-height:1;
  color:#cbd5e1;background:rgba(15,23,42,.82);padding:2px 3px;
  border-radius:3px;pointer-events:none;
}
#board{
  min-width:max-content;position:relative;
  padding:26px 28px 80px;display:flex;gap:42px;align-items:flex-start;
}
#lines{position:absolute;inset:0;width:100%;height:100%;pointer-events:none;z-index:1;overflow:visible}

/* ── Columns ─────────────────────────────────────────────────────────────── */
.column{
  width:285px;flex:0 0 285px;position:relative;z-index:2;
  display:flex;flex-direction:column;
  height:calc(100vh - 110px);
}
/* When locked: column grows to fit its cards naturally */
.column.unlocked{height:auto}

.column-header{
  height:42px;display:flex;align-items:center;justify-content:space-between;
  padding:0 5px 9px;border-bottom:2px solid #cbd5e1;margin-bottom:10px;
  color:var(--muted);background:var(--bg);
  position:sticky;top:0;z-index:20;
}
.column-title{font-size:12px;text-transform:uppercase;letter-spacing:.08em;font-weight:800}
.column-count{
  font-size:12px;background:#e2e8f0;border-radius:999px;
  padding:2px 8px;color:#475569;font-weight:700;
}

/* ── Cards container ─────────────────────────────────────────────────────── */
/*
 * overflow-x:hidden  → no horizontal scrollbar ever
 * overflow-y:auto    → thin vertical scrollbar only when needed
 */
.cards{
  flex:1;min-height:0;
  display:flex;flex-direction:column;gap:9px;
  overflow-y:auto;overflow-x:hidden;
  padding:2px 20px 80px;
  scrollbar-width:thin;scrollbar-color:#cbd5e1 transparent;
}
/* When an item is locked the chain is short — let it expand, no scrollbar */
.cards.noscroll{overflow:visible;flex:none;padding-bottom:20px}

/* ── Cards ───────────────────────────────────────────────────────────────── */
.card{
  position:relative;background:var(--surface);border:1px solid var(--border);
  border-radius:9px;padding:11px 12px;cursor:pointer;
  box-shadow:0 1px 2px rgba(15,23,42,.05);
  transition:opacity .18s,filter .18s,box-shadow .18s,border-color .18s,transform .18s;
  z-index:3;
}
.card:hover{box-shadow:0 7px 20px rgba(15,23,42,.12);border-color:#aab7c7;transform:translateY(-1px)}
.card.cycle{border-color:#ef4444;box-shadow:0 0 0 2px rgba(239,68,68,.13)}
.card.external{border-left:3px solid #f59e0b}

/* ── Card header row ─────────────────────────────────────────────────────── */
.card-top{display:flex;align-items:flex-start;justify-content:space-between;gap:8px;margin-bottom:7px}
.card-top-left{display:flex;align-items:center;gap:6px;min-width:0}
.assignee-select{font:inherit;border:0;background:transparent;color:var(--muted);cursor:pointer;min-width:0;padding:0;outline:none}
.assignee-select{font-size:11px;max-width:100%;margin-top:7px}
.assignee-select.unassigned{background:#2563eb;color:#fff;border-radius:999px;padding:2px 7px;font-weight:700}
.assignee-select.unassigned option{background:#fff;color:#334155}
.priority-picker{position:relative;display:inline-flex;align-items:center;flex-shrink:0}
.priority-trigger{display:flex;align-items:center;justify-content:center;width:22px;height:22px;padding:0;border:0;background:transparent;border-radius:4px;cursor:pointer}
.priority-trigger:hover,.priority-picker.open .priority-trigger{background:#f1f5f9}
.priority-icon{width:16px;height:16px;display:block;flex-shrink:0;pointer-events:none}
.priority-menu{display:none;position:fixed;top:auto;left:auto;width:212px;padding:3px 0;background:#fff;border:1px solid #dbe3ec;border-radius:8px;box-shadow:0 8px 24px rgba(15,23,42,.16);z-index:80}
.priority-picker.open .priority-menu{display:block;z-index:9999}
.priority-option{width:100%;display:flex;align-items:center;gap:11px;padding:9px 14px;border:0;background:#fff;color:#334155;font:inherit;font-size:13px;text-align:left;cursor:pointer}
.priority-option:hover{background:#f1f5f9}
.priority-option.selected{background:#eef2ff;color:#1e293b;font-weight:700}
.priority-option .priority-icon{width:16px;height:16px}
.p-highest{background:#ef4444}.p-high{background:#f97316}
.p-medium{background:#eab308}.p-low{background:#3b82f6}.p-lowest{background:#cbd5e1}
.key{font-size:11px;font-weight:800;color:var(--accent);text-decoration:none;white-space:nowrap}
.key:hover{text-decoration:underline}

/* ── Epic badge ──────────────────────────────────────────────────────────── */
.epic-badge{
  display:inline-flex;align-items:center;gap:4px;margin-bottom:5px;
  font-size:10px;font-weight:700;color:#7c3aed;
  background:#f5f3ff;border:1px solid #ddd6fe;border-radius:4px;
  padding:2px 6px;max-width:100%;text-decoration:none;
  overflow:hidden;text-overflow:ellipsis;white-space:nowrap;
  transition:background .12s;
}
.epic-badge:hover{background:#ede9fe}
.epic-dot{font-size:8px;flex-shrink:0}

/* ── Summary & meta ──────────────────────────────────────────────────────── */
.summary{font-size:13px;line-height:1.4;color:#1e293b;overflow-wrap:anywhere}
mark{background:#fef08a;border-radius:2px;padding:0 1px;color:inherit}
.milestone-banner{
  display:flex;align-items:center;justify-content:center;
  height:15px;margin:-11px -12px 9px;
  background:#59c7f5;color:#172033;
  border-radius:8px 8px 0 0;
  font-size:9px;font-weight:800;letter-spacing:.08em;
  line-height:15px;
}
.status-badge{
  display:inline-block;font-size:11px;font-weight:600;
  border-radius:5px;padding:2px 7px;margin-top:0;flex-shrink:0;
}
.relations{display:flex;flex-wrap:wrap;gap:4px;margin-top:7px}
.relation-box{display:inline-flex;align-items:center;gap:3px;border:1px solid #dbe3ec;background:#f8fafc;border-radius:5px;padding:2px 5px;font-size:10px;line-height:1.35}
.relation-box.up{background:#fff7ed;border-color:#fed7aa}.relation-box.up .relation-key{color:#9a6700}
.relation-box.down{background:#f5f3ff;border-color:#ddd6fe}.relation-box.down .relation-key{color:#4338ca}
.relation-key{color:var(--accent);font-weight:800;text-decoration:none}
.relation-box.up:has(.relation-key.completed),.relation-box.down:has(.relation-key.completed){background:transparent}
a.relation-key.completed{text-decoration:line-through;text-decoration-thickness:2px}
.relation-key:hover{text-decoration:underline}
.relation-arrow{font-weight:900;color:#64748b;line-height:1}
.external-key{color:#9a6700}
.see-blocked-btn{margin-top:7px;padding:4px 8px;border:1px solid #cbd5e1;border-radius:4px;background:#f8fafc;color:#334155;font-size:11px;font-weight:600;cursor:pointer}.see-blocked-btn:hover{background:#e2e8f0}
.cycle-note{
  font-size:11px;color:#b91c1c;background:#fef2f2;
  border:1px solid #fecaca;border-radius:6px;padding:6px 7px;margin-top:8px;
}
.empty{
  color:#94a3b8;font-size:13px;padding:15px 8px;
  border:1px dashed #cbd5e1;border-radius:8px;text-align:center;
}
.no-active-user{width:min(520px,calc(100% - 40px));margin:70px auto 0;padding:24px;border:1px solid #dbe2ea;border-radius:12px;background:#fff;box-shadow:0 8px 24px rgba(15,23,42,.08);text-align:center;color:#475569}
.no-active-user-title{font-size:18px;font-weight:800;color:#172033;margin-bottom:7px}
.no-active-user-label{font-size:13px;color:#64748b;margin-bottom:16px}
.no-active-user-select-label{display:flex;align-items:center;justify-content:center;gap:9px;font-size:12px;font-weight:700;color:#475569;flex-wrap:wrap}
.no-active-user-select{min-width:210px;padding:7px 9px;border:1px solid #cbd5e1;border-radius:6px;background:#fff;color:#334155;font:inherit;font-weight:500}
.no-results{width:min(520px,calc(100% - 40px));margin:70px auto 0;padding:24px;border:1px solid #dbe2ea;border-radius:12px;background:#fff;box-shadow:0 8px 24px rgba(15,23,42,.08);text-align:center;color:#475569}
.no-results-title{font-size:18px;font-weight:800;color:#172033;margin-bottom:7px}
.no-results-message{font-size:13px;color:#64748b}
.completed-download-notice{position:fixed;left:50%;bottom:18px;transform:translateX(-50%);z-index:120;background:#fff7ed;border:1px solid #fed7aa;border-radius:9px;box-shadow:0 8px 24px rgba(15,23,42,.12);padding:10px 14px;min-width:min(420px,calc(100vw - 32px));text-align:center}
.completed-download-title{font-size:12px;font-weight:800;color:#9a6700;margin-bottom:3px}
.completed-download-message{font-size:11px;color:#7c5a17;line-height:1.4}


/* ── Dependency modal ─────────────────────────────────────────────────────── */
#dependency-modal{display:none;position:fixed;inset:0;background:rgba(15,23,42,.52);backdrop-filter:blur(2px);z-index:200;align-items:center;justify-content:center;padding:16px}
#dependency-modal.open{display:flex}
.modal-card{width:min(540px,calc(100vw - 32px));max-height:calc(100vh - 32px);overflow:auto;background:#fff;border-radius:14px;box-shadow:0 24px 70px rgba(15,23,42,.28);padding:22px}
.modal-head{display:flex;align-items:flex-start;justify-content:space-between;margin-bottom:18px}
.modal-head h2{font-size:18px;line-height:1.2;margin:0;color:#172033}
.modal-head::after{content:"Add or remove relationships for this issue";position:absolute;margin-top:25px;font-size:11px;color:#94a3b8}
.modal-close{border:0;background:#f1f5f9;color:#475569;border-radius:7px;width:30px;height:30px;cursor:pointer;font-size:18px}
.modal-close:hover{background:#e2e8f0;color:#172033}
.modal-field{margin-bottom:12px}
.modal-field label{display:block;font-size:10px;text-transform:uppercase;letter-spacing:.05em;font-weight:800;color:#64748b;margin-bottom:5px}
.modal-field select{width:100%;padding:10px;border:1px solid #cbd5e1;border-radius:7px;background:#fff;font:inherit}
.modal-field select:disabled{background:#f8fafc;color:#334155;border-color:#e2e8f0}
.issue-search{width:100%;box-sizing:border-box;padding:10px;border:1px solid #cbd5e1;border-radius:7px;background:#fff;font:inherit;margin-bottom:6px}
.issue-search:focus{outline:none;border-color:#818cf8;box-shadow:0 0 0 3px rgba(99,102,241,.12)}
.modal-direction{display:flex;align-items:center;justify-content:space-between;gap:12px;padding:12px;border-radius:8px;background:#f8fafc;border:1px solid #e2e8f0;font-size:13px;font-weight:800;margin:15px 0}
#dep-direction{display:flex;align-items:center;gap:7px;color:#4338ca}
#dep-direction::before{content:"→";display:inline-flex;align-items:center;justify-content:center;width:22px;height:22px;border-radius:5px;background:#f5f3ff;color:#4338ca;font-size:14px}
.direction-switch{display:inline-flex;align-items:center;gap:8px;flex-shrink:0}
.direction-switch input{position:absolute;opacity:0;pointer-events:none}
.switch-track{position:relative;width:38px;height:22px;border-radius:999px;background:#cbd5e1;cursor:pointer;transition:background .15s}
.switch-track::after{content:"";position:absolute;top:3px;left:3px;width:16px;height:16px;border-radius:50%;background:#fff;box-shadow:0 1px 3px rgba(15,23,42,.25);transition:transform .15s}
.direction-switch input:checked + .switch-track{background:#6366f1}
.direction-switch input:checked + .switch-track::after{transform:translateX(16px)}
.direction-switch-label{font-size:10px;color:#64748b;font-weight:700;white-space:nowrap}
.modal-existing{margin-top:18px;border-top:1px solid #e2e8f0;padding-top:15px}
.modal-existing h3{font-size:11px;text-transform:uppercase;letter-spacing:.05em;color:#64748b;margin:0 0 9px}
.dependency-section{margin-bottom:12px}
.dependency-section:last-child{margin-bottom:0}
.dependency-section-title{font-size:10px;text-transform:uppercase;letter-spacing:.05em;font-weight:800;margin-bottom:5px}
.dependency-section.blocked-by .dependency-section-title{color:#9a6700}
.dependency-section.blocks .dependency-section-title{color:#4338ca}
.dependency-row{display:flex;align-items:center;gap:8px;padding:8px 9px;border:1px solid #e2e8f0;border-left-width:3px;border-radius:6px;background:#f8fafc;margin-bottom:5px;font-size:11px}
.dependency-section.blocked-by .dependency-row{border-left-color:#f59e0b;background:#fffaf0}
.dependency-section.blocks .dependency-row{border-left-color:#6366f1;background:#f8f7ff}
.dependency-row-text{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;color:#334155}
.dependency-row-key{font-weight:800;color:#4338ca}
.dependency-section.blocked-by .dependency-row-key{color:#9a6700}
.dependency-remove{border:0;background:transparent;color:#64748b;font-size:11px;font-weight:700;cursor:pointer;padding:3px 5px;border-radius:4px}
.dependency-remove:hover{background:#fee2e2;color:#dc2626}
.dependency-empty{font-size:11px;color:#94a3b8;padding:4px 0}
.modal-actions{display:flex;justify-content:flex-end;gap:8px;margin-top:17px}
.modal-primary{border:0;background:#6366f1;color:#fff;border-radius:7px;padding:9px 14px;font-weight:800;cursor:pointer}
.modal-secondary{border:1px solid #cbd5e1;background:#fff;color:#334155;border-radius:7px;padding:9px 14px;cursor:pointer}
.modal-secondary:hover{background:#f8fafc}
.edit-dependency-btn{margin-top:8px;width:100%;border:1px dashed #cbd5e1;background:#f8fafc;color:#475569;border-radius:6px;padding:5px 8px;font-size:11px;font-weight:700;cursor:pointer}
.edit-dependency-btn:hover{background:#eef2ff;border-color:#a5b4fc;color:#4338ca}
/* ── Loading overlay ─────────────────────────────────────────────────────── */
#loading{
  position:fixed;inset:58px 0 0;
  background:radial-gradient(circle at 50% 42%,rgba(255,255,255,.98) 0,rgba(241,245,249,.96) 48%,rgba(226,232,240,.94) 100%);
  backdrop-filter:blur(7px);display:flex;flex-direction:column;
  align-items:center;justify-content:center;gap:15px;
  z-index:100;opacity:0;pointer-events:none;transition:opacity .2s;
}
#loading.show{opacity:1;pointer-events:auto}
/* dependency-status is earlier in the DOM than #loading, so it cannot be hidden with a following-sibling selector. */
#dependency-status.loading-hidden{display:none !important}
#dependency-status.view-hidden{display:none !important}
#loading::before{
  content:"";position:absolute;width:520px;height:520px;border-radius:50%;
  background:radial-gradient(circle,rgba(99,102,241,.08),transparent 68%);
  animation:loadingPulse 2.4s ease-in-out infinite;pointer-events:none;
}
.loading-favicon-wrap{
  position:relative;width:72px;height:72px;display:flex;align-items:center;justify-content:center;
  border-radius:50%;background:rgba(99,102,241,.08);box-shadow:0 8px 28px rgba(99,102,241,.16);
  animation:loadingPulse 2.4s ease-in-out infinite;
}
.loading-favicon{width:48px;height:48px;object-fit:contain;animation:loadingFaviconSpin 2.2s linear infinite}
@keyframes loadingFaviconSpin{to{transform:rotate(360deg)}}
@keyframes loadingPulse{0%,100%{transform:scale(.94);opacity:.78}50%{transform:scale(1.06);opacity:1}}
#loading-label{position:relative;font-size:18px;font-weight:850;color:#172033;letter-spacing:.1px;text-align:center}
#loading-status{position:relative;font-size:12px;font-weight:650;color:#64748b;text-align:center;min-height:18px}
.loading-progress{position:relative;width:min(420px,calc(100vw - 56px));height:8px;background:#dbe3ef;border-radius:999px;overflow:hidden;box-shadow:inset 0 1px 2px rgba(15,23,42,.08)}
#loading-progress-bar{height:100%;width:42%;background:linear-gradient(90deg,var(--accent),#818cf8);border-radius:999px;box-shadow:0 0 14px rgba(99,102,241,.32);animation:loadingProgress 1.35s ease-in-out infinite}
@keyframes loadingProgress{0%{transform:translateX(-130%)}50%{transform:translateX(85%)}100%{transform:translateX(230%)}}
.startup-message{
  position:relative;width:min(620px,calc(100vw - 40px));box-sizing:border-box;
  background:rgba(255,255,255,.98);border:1px solid #c7d2fe;border-radius:16px;
  padding:22px 28px;box-shadow:0 12px 38px rgba(15,23,42,.14),0 0 0 5px rgba(99,102,241,.05);
  color:#334155;font-size:16px;line-height:1.65;text-align:center;
  animation:startupMessageIn .45s ease-out, startupMessageGlow 2.8s ease-in-out infinite;
}
.startup-message::before{content:none;display:none}
.startup-message-title{font-size:21px;font-weight:850;line-height:1.25;color:#172033;margin-bottom:9px}
.startup-message-body{font-size:16px;color:#475569}
.startup-message-body p{margin:0 0 8px}.startup-message-body p:last-child{margin-bottom:0}
@keyframes startupMessageIn{from{opacity:0;transform:translateY(10px) scale(.98)}to{opacity:1;transform:translateY(0) scale(1)}}
@keyframes startupMessageGlow{0%,100%{box-shadow:0 12px 38px rgba(15,23,42,.14),0 0 0 5px rgba(99,102,241,.05)}50%{box-shadow:0 14px 42px rgba(15,23,42,.17),0 0 0 8px rgba(99,102,241,.07)}}

/* ── Legend ──────────────────────────────────────────────────────────────── */
.legend{
  position:fixed;bottom:16px;left:18px;z-index:20;
  background:rgba(255,255,255,.95);border:1px solid var(--border);
  box-shadow:0 3px 15px rgba(15,23,42,.1);border-radius:8px;
  padding:8px 12px;font-size:11px;color:#64748b;display:flex;gap:14px;
}
.legend span{display:flex;align-items:center;gap:5px}
.dot{width:9px;height:9px;border-radius:50%;display:inline-block}
.dot-orange{background:#f59e0b}.dot-red{background:#ef4444}

/* ── Selection highlight ─────────────────────────────────────────────────── */
.dimmed{opacity:.2;filter:grayscale(.6)}
.highlighted{box-shadow:0 0 0 2px rgba(99,102,241,.35);z-index:8!important}
.locked{box-shadow:0 0 0 3px rgba(99,102,241,.6)!important;border-color:#6366f1!important}
.line{fill:none;stroke:var(--line);stroke-width:1.6;opacity:.78;
      transition:stroke .2s,opacity .2s,stroke-width .2s}
.line.highlighted-line{stroke:#6366f1;stroke-width:2.5;opacity:1}
.line.faint{stroke:#b0bec9;stroke-width:1.3;opacity:.38}
.arrow{fill:var(--line)}
/* hover-chain dimming */
.card.hover-dimmed{opacity:.12!important;filter:grayscale(.8)!important;transition:opacity .2s,filter .2s}
.line.hover-dimmed{opacity:.04!important;transition:opacity .2s}


#dependency-status{
  position:fixed;top:66px;right:16px;z-index:120;
  display:flex;align-items:center;gap:5px;padding:4px 6px;
  background:rgba(255,255,255,.94);border:1px solid #e2e8f0;
  border-radius:7px;box-shadow:0 2px 8px rgba(15,23,42,.06);
  pointer-events:none;
}
#dependency-status .status-pill{
  display:inline-flex;align-items:center;gap:4px;padding:3px 6px;
  border-radius:5px;background:transparent;border:0;
  font-size:9px;font-weight:800;white-space:nowrap;color:#64748b;
}
#dependency-status .status-pill.blocked{color:#9a6700}
#dependency-status .status-pill.blocks{color:#4338ca}
#dependency-status .status-pill.external{color:#9a6700;background:#fff8eb}
#dependency-status .status-pill.cycle{color:#dc2626;background:#fff5f5}
#dependency-status .status-pill.locked{color:#4f46e5;background:#f0f3ff}
#dependency-status .status-dot{width:6px;height:6px;border-radius:50%;display:inline-block}
#dependency-status .external .status-dot{background:#f59e0b}
#dependency-status .cycle .status-dot{background:#ef4444}
#dependency-status .locked .status-dot{background:#6366f1}
#dependency-status .status-arrow{font-size:12px;line-height:1;font-weight:900}


.issue-combobox{position:relative}
.issue-options{
  position:absolute;left:0;right:0;top:100%;z-index:80;
  max-height:240px;overflow-y:auto;
  background:#fff;border:1px solid #cbd5e1;border-top:0;
  border-radius:0 0 7px 7px;box-shadow:0 6px 18px rgba(15,23,42,.14);
  display:none;
}
.issue-options.open{display:block}
.issue-option{
  padding:8px 10px;font-size:11px;line-height:1.35;cursor:pointer;
  border-bottom:1px solid #f1f5f9;color:#334155;
}
.issue-option:last-child{border-bottom:0}
.issue-option:hover,.issue-option.active{background:#eef2ff;color:#3730a3}
.issue-option-key{font-weight:800}
.issue-option-summary{color:#64748b}


/* ── Due dates ─────────────────────────────────────────────────────────── */
.card-meta{display:flex;align-items:center;gap:8px;flex-wrap:wrap;margin-top:8px}
.card-meta .assignee-select{margin-top:0;flex:0 1 auto;min-width:150px}
.due-date{display:inline-flex;align-items:center;gap:4px;border:1px solid #e2e8f0;background:#f8fafc;color:#475569;border-radius:5px;padding:4px 7px;font:inherit;font-size:11px;line-height:1.2;cursor:pointer;white-space:nowrap}
.due-date:hover{background:#eef2ff;border-color:#c7d2fe;color:#3730a3}
.due-date.overdue{color:#b91c1c;background:#fef2f2;border-color:#fecaca;font-weight:800}
.due-date.chain-date-risk{color:#9a3412;background:#fff7ed;border-color:#fb923c;font-weight:850;box-shadow:0 0 0 2px rgba(251,146,60,.22)}
.due-date.chain-date-risk:hover{color:#7c2d12;background:#ffedd5;border-color:#f97316}
.card.chain-date-risk-card{box-shadow:inset 0 0 0 2px rgba(249,115,22,.32)}
.card.overdue-card{outline:2px solid #ef4444;outline-offset:-2px}
.due-date-empty{color:#64748b}
.due-date-icon{font-size:11px}
#due-date-modal{display:none;position:fixed;inset:0;background:rgba(15,23,42,.42);backdrop-filter:blur(2px);z-index:10060;align-items:center;justify-content:center;padding:16px}
#due-date-modal.open{display:flex}
.due-date-card{width:min(330px,calc(100vw - 32px));background:#fff;border-radius:12px;box-shadow:0 24px 70px rgba(15,23,42,.28);padding:18px}
.due-date-head{display:flex;align-items:center;justify-content:space-between;margin-bottom:13px}
.due-date-title{font-size:14px;font-weight:800;color:#172033}
.due-date-key{font-size:11px;color:#64748b;margin-top:2px}
.due-date-input{width:100%;padding:9px 10px;border:1px solid #cbd5e1;border-radius:7px;background:#fff;color:#172033;font:inherit;font-size:13px}
.due-date-input:focus{outline:none;border-color:#818cf8;box-shadow:0 0 0 3px rgba(99,102,241,.12)}
.due-date-actions{display:flex;justify-content:space-between;gap:8px;margin-top:14px}
.due-date-actions-right{display:flex;gap:8px}
.due-date-button{border:1px solid #cbd5e1;background:#fff;color:#334155;border-radius:7px;padding:7px 11px;font:inherit;font-size:12px;font-weight:700;cursor:pointer}
.due-date-button:hover{background:#f8fafc}
.due-date-button.primary{background:#6366f1;border-color:#6366f1;color:#fff}
.due-date-button.danger{color:#b91c1c;border-color:#fecaca;background:#fef2f2}
#chain-date-warning-modal{display:none;position:fixed;inset:0;background:rgba(15,23,42,.5);backdrop-filter:blur(2px);z-index:10070;align-items:center;justify-content:center;padding:16px}
#chain-date-warning-modal.open{display:flex}
.chain-date-warning-card{width:min(720px,calc(100vw - 32px));max-height:calc(100vh - 32px);overflow:auto;background:#fff;border-radius:12px;box-shadow:0 24px 70px rgba(15,23,42,.32);padding:20px}
.chain-date-warning-title{font-size:16px;font-weight:850;color:#991b1b;margin:0 0 12px}
.chain-date-warning-section{border:1px solid #fed7aa;background:#fffaf5;border-radius:9px;padding:12px}
.chain-date-warning-section+.chain-date-warning-section{margin-top:14px}
.chain-date-warning-section-title{font-size:13px;font-weight:850;color:#9a3412;margin:0 0 10px}
.chain-date-warning-message{font-size:13px;font-weight:750;color:#334155;margin:0 0 9px}
.chain-date-warning-subsection+.chain-date-warning-subsection{margin-top:12px}
.chain-date-warning-changes{border:1px solid #cbd5e1;background:#f8fafc;border-radius:9px;padding:12px;margin-bottom:14px}
.chain-date-warning-changes-title{font-size:12px;font-weight:850;color:#334155;margin:0 0 8px}
.chain-date-warning-resolved{padding:12px;border:1px solid #bbf7d0;background:#f0fdf4;color:#166534;border-radius:8px;font-size:12px;font-weight:750}
.chain-date-warning-empty{padding:12px;border:1px solid #e2e8f0;background:#f8fafc;color:#64748b;border-radius:8px;font-size:12px}
.chain-date-warning-table{width:100%;border-collapse:collapse;font-size:12px}
.chain-date-warning-table th,.chain-date-warning-table td{padding:8px 9px;border:1px solid #e2e8f0;text-align:left;vertical-align:middle}
.chain-date-warning-table th{background:#f8fafc;color:#475569;font-size:11px}
.chain-date-warning-table td:first-child{font-weight:800;white-space:nowrap;color:#3730a3}
.chain-date-warning-key{color:#3730a3;text-decoration:none;font-weight:850}
.chain-date-warning-key:hover{text-decoration:underline}
.chain-date-warning-date{width:145px;max-width:100%;padding:6px 7px;border:1px solid #cbd5e1;border-radius:6px;background:#fff;color:#172033;font:inherit;font-size:12px}
.chain-date-warning-date:focus{outline:none;border-color:#f97316;box-shadow:0 0 0 3px rgba(249,115,22,.13)}
.chain-date-warning-current{white-space:nowrap;color:#64748b}
.chain-date-warning-revert{border:0;background:transparent;color:#4f46e5;font:inherit;font-size:11px;font-weight:750;cursor:pointer;padding:3px}
.chain-date-warning-revert:hover{text-decoration:underline}
.chain-date-warning-actions{display:flex;justify-content:flex-end;gap:8px;margin-top:18px}

/* ── Dashboard ──────────────────────────────────────────────────────────── */
#board.dashboard-board{width:100%;min-width:0;padding:18px 20px 40px}
#board.dashboard-board #lines{display:none!important}
.dashboard{max-width:1500px;margin:0 auto}
.dashboard-head{display:flex;align-items:flex-end;justify-content:space-between;gap:18px;margin-bottom:16px}
.dashboard-title{font-size:20px;font-weight:850;color:#172033}
.dashboard-subtitle{font-size:12px;color:#64748b;margin-top:3px}
.dashboard-updated{font-size:11px;color:#94a3b8}
.dashboard-stats{display:grid;grid-template-columns:repeat(6,minmax(0,1fr));gap:10px;margin-bottom:18px}
.dashboard-summary-link{cursor:pointer;transition:transform .15s,box-shadow .15s,border-color .15s}
.dashboard-summary-link:hover{transform:translateY(-1px);box-shadow:0 3px 10px rgba(15,23,42,.08);border-color:#cbd5e1}
.dashboard-summary-link:focus-visible{outline:2px solid #6366f1;outline-offset:2px}
.dashboard-stat{background:#fff;border:1px solid #e2e8f0;border-radius:10px;padding:13px 14px;min-width:0}
.dashboard-stat-value{font-size:23px;line-height:1;font-weight:850;color:#172033}
.dashboard-stat-label{font-size:10px;text-transform:uppercase;letter-spacing:.06em;font-weight:800;color:#64748b;margin-top:7px}
.dashboard-stat-help{font-size:10px;line-height:1.35;color:#94a3b8;margin-top:5px}
.dashboard-stat.risk{border-color:#fecaca;background:#fffafa}
.dashboard-stat.risk .dashboard-stat-value{color:#b91c1c}
 .dashboard-health-stat{min-width:0;grid-column:span 2}
.dashboard-stat.dashboard-attention-stat{grid-column:span 2}
.dashboard-attention-summary{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:5px;margin-top:7px}
.dashboard-attention-item{display:flex;align-items:center;justify-content:space-between;gap:8px;padding:5px 7px;border:1px solid #e2e8f0;background:#f8fafc;border-radius:6px;font-size:10px;color:#334155;cursor:pointer;text-align:left;width:100%}
.dashboard-attention-item:hover{background:#fff;border-color:#cbd5e1}
.dashboard-attention-item strong{font-size:10px;color:#172033}
.dashboard-upcoming-stack{display:flex;flex-direction:column;gap:10px;min-width:0}
.dashboard-upcoming-stack .dashboard-stat{width:100%}
.dashboard-upcoming-tabs{display:flex;gap:5px;margin:0 0 9px}
.dashboard-upcoming-tab{border:1px solid #cbd5e1;background:#f8fafc;color:#475569;border-radius:7px;padding:6px 12px;font:inherit;font-size:11px;font-weight:800;cursor:pointer}
.dashboard-upcoming-tab:hover{background:#fff}
.dashboard-upcoming-tab.active{background:#172033;color:#fff;border-color:#172033}
.dashboard-upcoming-panel[hidden]{display:none!important}
.dashboard-top-workload{display:flex;flex-direction:column;gap:4px;margin-top:7px}
.dashboard-top-workload-row{display:flex;align-items:center;justify-content:space-between;gap:8px;font-size:10px}
.dashboard-top-workload-row strong{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.dashboard-top-workload-count{font-weight:850;color:#6366f1;white-space:nowrap}
.dashboard-health-stat.green{border-color:#bbf7d0;background:#f7fff9}
.dashboard-health-stat.amber{border-color:#fde68a;background:#fffdf5}
.dashboard-health-stat.red{border-color:#fecaca;background:#fff8f8}
.dashboard-health-score-line{display:flex;align-items:center;justify-content:space-between;gap:8px}
.dashboard-health-status{font-size:9px;font-weight:850;text-transform:uppercase;letter-spacing:.06em;border-radius:999px;padding:4px 7px}
.dashboard-health-stat.green .dashboard-health-status{background:#dcfce7;color:#166534}
.dashboard-health-stat.amber .dashboard-health-status{background:#fef3c7;color:#92400e}
.dashboard-health-stat.red .dashboard-health-status{background:#fee2e2;color:#b91c1c}
.dashboard-health-breakdown{margin-top:9px;border-top:1px solid #e2e8f0;padding-top:7px}
.dashboard-health-row{display:flex;align-items:center;gap:8px;padding:3px 0;font-size:10px}
.dashboard-health-row-label{font-weight:750;color:#334155;white-space:nowrap}
.dashboard-health-row-detail{color:#94a3b8;flex:1;min-width:0}
.dashboard-health-row strong{font-size:10px;white-space:nowrap;color:#64748b}
.dashboard-health-stat.red .dashboard-health-row strong{color:#b91c1c}
.dashboard-health-stat.amber .dashboard-health-row strong{color:#92400e}
.dashboard-nav{position:sticky;top:0;z-index:20;display:flex;gap:6px;flex-wrap:wrap;padding:8px 0 10px;background:var(--bg);border-bottom:1px solid #e2e8f0;margin-bottom:12px}
.dashboard-nav button{border:1px solid #cbd5e1;background:#fff;color:#475569;border-radius:999px;padding:6px 11px;font:inherit;font-size:11px;font-weight:800;cursor:pointer}
.dashboard-nav button:hover,.dashboard-nav button.active{background:#172033;color:#fff;border-color:#172033}
.dashboard-section-group{scroll-margin-top:48px;margin-bottom:18px}
.dashboard-group-head{display:flex;align-items:baseline;justify-content:space-between;gap:12px;margin:18px 2px 9px}
.dashboard-group-head h2{font-size:15px;line-height:1.2;color:#172033;margin:0}
.dashboard-group-head span{font-size:11px;color:#64748b}
.dashboard-section{scroll-margin-top:52px;background:#fff;border:1px solid #e2e8f0;border-radius:10px;padding:14px;margin-bottom:10px}
.dashboard-section-heading{display:flex;align-items:baseline;gap:9px;min-width:0}
.dashboard-section-note{font-size:10px;color:#94a3b8;font-weight:500;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.dashboard-summary-section{padding-bottom:12px}
.dashboard-compact-list{display:flex;flex-direction:column;gap:5px}
.dashboard-compact-row{width:100%;display:flex;align-items:center;justify-content:space-between;gap:12px;text-align:left;border:1px solid #e2e8f0;background:#f8fafc;border-radius:7px;padding:8px 10px;color:#334155;cursor:pointer;font:inherit}
.dashboard-compact-row:hover{background:#fff;border-color:#cbd5e1;box-shadow:0 2px 7px rgba(15,23,42,.06)}
.dashboard-compact-main{display:flex;align-items:center;gap:8px;min-width:0}
.dashboard-compact-main>span:last-child{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.dashboard-compact-main strong{font-size:11px;flex:0 0 auto}
.dashboard-compact-badges{display:flex;gap:5px;align-items:center;flex:0 0 auto}
.dashboard-impact{font-size:11px;font-weight:800;color:#6366f1;white-space:nowrap}
.dashboard-workload-list{display:flex;flex-direction:column;gap:4px}
.dashboard-workload-row{display:grid;grid-template-columns:minmax(150px,210px) 1fr 42px;align-items:center;gap:10px;width:100%;border:0;background:transparent;padding:6px 4px;text-align:left;cursor:pointer;color:#334155;border-radius:6px}
.dashboard-workload-row:hover{background:#f8fafc}
.dashboard-workload-name{display:flex;align-items:center;gap:8px;min-width:0}
.dashboard-workload-name strong{overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:12px}
.dashboard-workload-name span{font-size:10px;color:#b91c1c;white-space:nowrap}
.dashboard-workload-bar{height:7px;background:#e2e8f0;border-radius:999px;overflow:hidden}
.dashboard-workload-bar span{display:block;height:100%;background:#6366f1;border-radius:999px}
.dashboard-workload-count{text-align:right;font-size:12px}
.dashboard-inline-stat{display:flex;align-items:baseline;gap:8px;padding:6px 2px;color:#64748b}
.dashboard-inline-stat strong{font-size:24px;color:#172033}
.dashboard-inline-stat span{font-size:12px}
.dashboard-section-head{display:flex;align-items:center;justify-content:space-between;gap:10px;margin-bottom:11px}
.dashboard-section-title{font-size:12px;font-weight:850;color:#172033}
.dashboard-section-count{font-size:10px;color:#64748b}
.dashboard-two-column{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr);gap:12px;align-items:start}
.dashboard-two-column .dashboard-section-group{min-width:0}
.dashboard-top-cards .dashboard-section-group,.dashboard-bottom-cards .dashboard-section-group{margin-bottom:18px}
.dashboard-ticket-wrap[hidden]{display:none}
.dashboard-pagination{display:flex;justify-content:center;gap:7px;margin-top:10px}
.dashboard-pagination button{border:1px solid #cbd5e1;background:#fff;color:#475569;border-radius:7px;padding:6px 10px;font:inherit;font-size:10px;font-weight:800;cursor:pointer}
.dashboard-pagination button:hover{background:#f8fafc;border-color:#94a3b8}
.dashboard-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(330px,1fr));gap:9px}
.dashboard-ticket{border:1px solid #e2e8f0;border-radius:8px;padding:9px 10px;background:#f8fafc;cursor:pointer}
.dashboard-ticket:hover{background:#fff;border-color:#cbd5e1;box-shadow:0 2px 7px rgba(15,23,42,.07)}
.dashboard-ticket.overdue{border-color:#fecaca;background:#fff7f7}
.dashboard-ticket-top{display:flex;align-items:center;justify-content:space-between;gap:8px}
.dashboard-ticket-key{font-size:11px;font-weight:850;color:#4f46e5;text-decoration:none}.dashboard-ticket-key:hover{text-decoration:underline}
.dashboard-ticket-summary{font-size:12px;font-weight:650;color:#334155;margin-top:3px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.dashboard-risks{display:flex;gap:4px;flex-wrap:wrap;margin-top:7px}
.dashboard-risk{font-size:9px;font-weight:800;border-radius:999px;padding:3px 6px;background:#eef2ff;color:#4338ca}
.dashboard-risk.overdue{background:#fee2e2;color:#b91c1c}
.dashboard-risk.unassigned{background:#dbeafe;color:#1d4ed8}
.dashboard-risk.dependencies{background:#fef3c7;color:#92400e}
.dashboard-risk.blocked{background:#ffedd5;color:#c2410c}
.dashboard-empty{font-size:12px;color:#64748b;padding:10px 2px}
@media(max-width:1000px){.dashboard-stats{grid-template-columns:repeat(2,minmax(0,1fr))}.dashboard-health-stat{grid-column:1 / -1}}
@media(max-width:1000px){.dashboard-two-column{grid-template-columns:1fr}}
@media(max-width:700px){.dashboard-stats{grid-template-columns:repeat(2,minmax(0,1fr))}.dashboard-grid{grid-template-columns:1fr}}

/* ── Settings ───────────────────────────────────────────────────────────── */
#settings-modal{display:none;position:fixed;inset:0;background:rgba(15,23,42,.52);backdrop-filter:blur(2px);z-index:10040;align-items:center;justify-content:center;padding:16px}
#settings-modal.open{display:flex}
.settings-card{width:min(480px,calc(100vw - 32px));max-height:calc(100vh - 32px);box-sizing:border-box;overflow-y:auto;background:#fff;border-radius:14px;box-shadow:0 24px 70px rgba(15,23,42,.28);padding:22px}
.settings-head{display:flex;align-items:center;justify-content:space-between;margin-bottom:16px}
.settings-head h2{font-size:18px;line-height:1.2;margin:0;color:#172033}
.settings-section{border:1px solid #e2e8f0;border-radius:9px;padding:12px;margin-bottom:10px}
.settings-section-title{font-size:11px;text-transform:uppercase;letter-spacing:.05em;font-weight:800;color:#64748b;margin-bottom:8px}
.settings-credential-row{display:flex;align-items:center;justify-content:space-between;gap:12px}
.settings-credential-info{font-size:12px;color:#334155}
.settings-credential-email{font-weight:700;color:#172033}
.settings-version-row{display:flex;align-items:center;justify-content:space-between;gap:12px}
.settings-version-info{font-size:12px;color:#334155;line-height:1.5}
.settings-version-value{font-weight:700;color:#172033}
.settings-version-status{font-size:11px;color:#64748b;margin-top:2px}
.settings-version-link{color:#4f46e5;text-decoration:none;font-weight:700;white-space:nowrap}
.settings-version-link:hover{text-decoration:underline}
.settings-help{font-size:11px;line-height:1.45;color:#64748b;margin-top:9px}
.settings-help a{color:#4f46e5;text-decoration:none;font-weight:700}
.settings-help a:hover{text-decoration:underline}
.settings-startup-row{display:flex;align-items:center;justify-content:space-between;gap:12px}
.settings-startup-info{font-size:12px;line-height:1.45;color:#334155}
.settings-messages-card{max-height:min(520px,70vh);overflow:auto}
.settings-message-item{border:1px solid #e2e8f0;border-radius:9px;padding:11px 12px;margin-bottom:9px}
.settings-message-item:last-child{margin-bottom:0}
.settings-message-title{font-size:12px;font-weight:800;color:#172033;margin-bottom:5px}
.settings-message-body{font-size:11px;line-height:1.5;color:#475569}
.settings-message-body p{margin:0 0 7px}
.settings-message-body p:last-child{margin-bottom:0}
.settings-message-empty{font-size:12px;line-height:1.5;color:#64748b}
.settings-back{display:inline-flex;align-items:center;border:0;background:transparent;color:#475569;padding:0;margin:0 0 14px;cursor:pointer;font-size:12px;font-weight:700}
.settings-back:hover{color:#172033}
.settings-feedback-row{display:flex;align-items:center;justify-content:space-between;gap:12px}
.settings-feedback-info{font-size:12px;line-height:1.45;color:#334155}
.settings-toggle-row{display:flex;align-items:center;justify-content:space-between;gap:14px}
.settings-toggle-info{font-size:12px;line-height:1.45;color:#334155}
.settings-toggle-title{font-weight:700;color:#172033}
.settings-toggle-help{font-size:10px;color:#64748b;margin-top:2px}
.settings-toggle{display:inline-flex;align-items:center;gap:7px;flex:0 0 auto;border:0;background:transparent;color:#475569;padding:0;cursor:pointer;font:inherit}
.settings-toggle-track{display:inline-block;position:relative;width:34px;height:20px;border-radius:10px;background:#cbd5e1;transition:background .18s}
.settings-toggle-track::after{content:"";position:absolute;width:16px;height:16px;border-radius:50%;background:#fff;top:2px;left:2px;box-shadow:0 1px 2px rgba(15,23,42,.18);transition:transform .18s}
.settings-toggle.active .settings-toggle-track{background:#6366f1}
.settings-toggle.active .settings-toggle-track::after{transform:translateX(14px)}
.settings-toggle-state{font-size:11px;font-weight:700;min-width:22px;text-align:right}
.settings-button{
  display:inline-flex;align-items:center;justify-content:center;flex:0 0 auto;
  min-width:132px;height:36px;padding:0 14px;
  border:1px solid #cbd5e1;background:#fff;color:#334155;border-radius:7px;
  font:inherit;font-size:12px;font-weight:700;line-height:1.2;
  cursor:pointer;text-decoration:none;white-space:nowrap;
}
.settings-button:hover{background:#f8fafc;border-color:#94a3b8}
.settings-button.primary{background:#6366f1;border-color:#6366f1;color:#fff;font-weight:800}
.settings-button.primary:hover{background:#4f46e5;border-color:#4f46e5}
.settings-actions{display:flex;justify-content:flex-end;gap:8px;margin-top:16px}
/* ── Advanced JQL settings ─────────────────────────────────────────────── */
.settings-advanced-row{display:flex;align-items:center;justify-content:space-between;gap:12px;margin-top:12px}
.settings-advanced-info{font-size:11px;line-height:1.45;color:#64748b}
.settings-advanced-link{border:0;background:transparent;color:#475569;font:inherit;font-size:12px;font-weight:750;cursor:pointer;padding:4px 0;text-align:left}
.settings-advanced-link:hover{color:#6366f1;text-decoration:underline}
.settings-jql-view{display:none}
.settings-jql-view.open{display:block}
.settings-jql-back{border:0;background:transparent;color:#64748b;font:inherit;font-size:12px;font-weight:750;cursor:pointer;padding:0;margin-bottom:14px}
.settings-jql-back:hover{color:#334155}
.settings-jql-label{display:block;font-size:10px;text-transform:uppercase;letter-spacing:.05em;font-weight:800;color:#64748b;margin-bottom:6px}
.settings-jql-default{width:100%;background:#f8fafc;border:1px solid #e2e8f0;border-radius:7px;padding:10px;font:11px/1.5 ui-monospace,SFMono-Regular,Consolas,"Liberation Mono",monospace;color:#334155;white-space:pre-wrap;overflow-wrap:anywhere;margin-bottom:14px}
.settings-jql-help{font-size:11px;line-height:1.5;color:#64748b;margin-bottom:8px}
.settings-jql-help a{color:#0057b8;text-decoration:underline}
.settings-jql-input{width:100%;min-height:125px;resize:vertical;padding:10px 11px;border:1px solid #cbd5e1;border-radius:7px;background:#fff;color:#172033;font:11px/1.5 ui-monospace,SFMono-Regular,Consolas,"Liberation Mono",monospace;outline:none}
.settings-jql-input:focus{border-color:#818cf8;box-shadow:0 0 0 3px rgba(99,102,241,.12)}
.settings-jql-status{min-height:17px;font-size:11px;line-height:1.4;margin-top:8px;color:#64748b}
.settings-jql-status.error{color:#b91c1c}
.settings-jql-status.success{color:#166534}
.settings-jql-actions{display:flex;justify-content:flex-end;gap:8px;margin-top:12px}
.custom-jql-indicator{display:none;min-width:36px;height:32px;padding:0 9px;box-sizing:border-box;align-items:center;justify-content:center;color:#172033;background:#f59e0b;border:1px solid #fbbf24;border-radius:7px;box-shadow:0 0 0 2px rgba(245,158,11,.25);text-decoration:none;cursor:pointer}
.custom-jql-indicator.active{display:inline-flex}
/* ── Credential setup / management ───────────────────────────────────────── */
#credential-modal{
  display:none;position:fixed;inset:0;background:rgba(15,23,42,.68);
  backdrop-filter:blur(4px);z-index:10050;align-items:center;justify-content:center;padding:20px;
}
#credential-modal.open{display:flex}
.credential-card{
  width:min(460px,calc(100vw - 32px));max-height:calc(100vh - 40px);box-sizing:border-box;overflow-y:auto;background:#fff;border-radius:14px;
  box-shadow:0 24px 80px rgba(15,23,42,.35);padding:25px;
}
.credential-card h2{font-size:20px;line-height:1.2;color:#172033;margin-bottom:8px}
.credential-card p{font-size:12px;line-height:1.55;color:#64748b;margin-bottom:18px}
.credential-field{margin-bottom:13px}
.credential-field label{display:block;font-size:10px;text-transform:uppercase;letter-spacing:.05em;font-weight:800;color:#64748b;margin-bottom:5px}
.credential-field input{
  width:100%;padding:10px 11px;border:1px solid #cbd5e1;border-radius:7px;
  background:#fff;font:inherit;font-size:13px;outline:none;
}
.credential-field input:focus{border-color:#818cf8;box-shadow:0 0 0 3px rgba(99,102,241,.12)}
.credential-note{
  background:#f8fafc;border:1px solid #e2e8f0;border-radius:7px;
  padding:9px 10px;font-size:10px;line-height:1.45;color:#64748b;margin:10px 0 15px;
}
.credential-actions{display:flex;justify-content:flex-end;gap:8px;margin-top:17px}
.credential-actions #credential-remove{margin-right:auto}
.credential-button{
  display:inline-flex;align-items:center;justify-content:center;
  border:1px solid #cbd5e1;background:#fff;color:#334155;border-radius:7px;
  padding:9px 14px;font-weight:700;cursor:pointer;text-decoration:none;
  font:inherit;line-height:1.2;
}
.credential-button:hover{background:#f8fafc;border-color:#94a3b8}
.credential-button.primary{background:#6366f1;border-color:#6366f1;color:#fff;font-weight:800}
.credential-button.primary:hover{background:#4f46e5;border-color:#4f46e5}
.credential-button:disabled{opacity:.55;cursor:not-allowed}
.credential-error{display:none;background:#fef2f2;border:1px solid #fecaca;color:#991b1b;border-radius:7px;padding:9px 10px;font-size:11px;line-height:1.4;margin-bottom:12px}
.credential-error.visible{display:block}
.credential-help{font-size:11px;color:#64748b;margin:-2px 0 10px;line-height:1.4}
.credential-help a{color:#0057b8;text-decoration:underline}
.credential-status{font-size:10px;color:#64748b;margin-top:8px;min-height:14px}


/* ── Required application update ───────────────────────────────────────── */
#required-update-modal{
  position:fixed;inset:0;z-index:50000;display:none;align-items:center;justify-content:center;
  padding:24px;background:rgba(15,23,42,.74);backdrop-filter:blur(4px);
}
#required-update-modal.open{display:flex}
.required-update-card{
  width:min(440px,100%);background:#fff;border:1px solid #cbd5e1;border-radius:14px;
  box-shadow:0 24px 70px rgba(15,23,42,.42);padding:26px;text-align:center;
}
.required-update-icon{
  width:52px;height:52px;margin:0 auto 15px;border-radius:50%;display:flex;
  align-items:center;justify-content:center;background:#eef2ff;color:#4f46e5;
  font-size:27px;font-weight:900;
}
.required-update-title{font-size:22px;line-height:1.2;color:#172033;margin-bottom:9px}
.required-update-message{color:#64748b;line-height:1.55;margin-bottom:19px}
.required-update-button{
  width:100%;border:0;border-radius:8px;background:#4f46e5;color:#fff;
  padding:11px 16px;font:inherit;font-weight:800;cursor:pointer;
}
.required-update-button:hover{background:#4338ca}
.required-update-button:focus-visible{outline:3px solid rgba(99,102,241,.3);outline-offset:3px}
.required-update-button:disabled{opacity:.65;cursor:wait}
.required-update-status{min-height:18px;margin-top:12px;color:#64748b;font-size:12px;line-height:1.45}
.required-update-status.error{color:#b91c1c}

@media (max-width:1100px){.dashboard-stats{grid-template-columns:repeat(3,minmax(0,1fr))}.dashboard-health-stat{grid-column:span 2}}
@media (max-width:700px){.dashboard-stats{grid-template-columns:1fr}.dashboard-health-stat{grid-column:span 1}.dashboard-two-column{grid-template-columns:1fr}}
</style>
</head>
<body>

<div id="required-update-modal" role="alertdialog" aria-modal="true" aria-labelledby="required-update-title">
  <div class="required-update-card">
    <div class="required-update-icon" aria-hidden="true">↻</div>
    <h2 class="required-update-title" id="required-update-title">New version available!</h2>
    <p class="required-update-message" id="required-update-message">A new version is ready to install.</p>
    <button class="required-update-button" id="required-update-button" type="button">Update now</button>
    <div class="required-update-status" id="required-update-status" role="status" aria-live="polite"></div>
  </div>
</div>


<div id="due-date-modal" role="dialog" aria-modal="true" aria-labelledby="due-date-title">
  <div class="due-date-card">
    <div class="due-date-head">
      <div><div class="due-date-title" id="due-date-title">Set due date</div><div class="due-date-key" id="due-date-key"></div></div>
      <button type="button" class="modal-close" id="due-date-close" aria-label="Close">×</button>
    </div>
    <input class="due-date-input" id="due-date-input" type="date">
    <div class="due-date-actions">
      <button type="button" class="due-date-button danger" id="due-date-clear">Clear date</button>
      <div class="due-date-actions-right"><button type="button" class="due-date-button" id="due-date-cancel">Cancel</button><button type="button" class="due-date-button primary" id="due-date-save">Save date</button></div>
    </div>
  </div>
</div>

<div id="chain-date-warning-modal" role="alertdialog" aria-modal="true" aria-labelledby="chain-date-warning-title">
  <div class="chain-date-warning-card">
    <h2 class="chain-date-warning-title" id="chain-date-warning-title">Chain date risk</h2>
    <div id="chain-date-warning-content"></div>
    <div class="chain-date-warning-actions">
      <button type="button" class="due-date-button" id="chain-date-warning-cancel">Cancel</button>
      <button type="button" class="due-date-button primary" id="chain-date-warning-confirm">Confirm change</button>
    </div>
  </div>
</div>

<div id="settings-modal" role="dialog" aria-modal="true" aria-labelledby="settings-title">
  <div class="settings-card">
    <div class="settings-head">
      <h2 id="settings-title">Settings</h2>
      <button class="modal-close" id="settings-close" type="button" aria-label="Close">×</button>
    </div>
    <div id="settings-main-view">
    <div class="settings-section">
      <div class="settings-section-title">Jira account</div>
      <div class="settings-credential-row">
        <div class="settings-credential-info">Stored credential<br><span class="settings-credential-email" id="settings-email">Not configured</span></div>
        <button class="settings-button" id="settings-manage-credential" type="button">Manage credential</button>
      </div>
      <div class="settings-help">
        Need an API token?
        <a href="https://id.atlassian.com/manage-profile/security/api-tokens" target="_blank" rel="noopener noreferrer">Create one in Atlassian</a>
      </div>
      <div class="settings-advanced-row settings-advanced-row-inline">
        <div class="settings-advanced-info">Change the Jira query used to build the dependency map.</div>
        <button class="settings-advanced-link" id="settings-advanced" type="button">Advanced</button>
      </div>
    </div>
    <div class="settings-section">
      <div class="settings-section-title">Board settings</div>
      <div class="settings-toggle-row">
        <div class="settings-toggle-info">
          <div class="settings-toggle-title">Use Jira modal</div>
          <div class="settings-toggle-help">Open Jira tickets inside the app instead of a new browser tab.</div>
        </div>
        <button class="settings-toggle" id="settings-use-jira-modal" type="button" role="switch" aria-checked="false">
          <span class="settings-toggle-track" aria-hidden="true"></span>
          <span class="settings-toggle-state">Off</span>
        </button>
      </div>
      <div class="settings-toggle-row" style="margin-top:12px">
        <div class="settings-toggle-info">
          <div class="settings-toggle-title">Starting board view</div>
          <div class="settings-toggle-help">Choose which view opens when the application starts.</div>
        </div>
        <select id="settings-starting-view" class="filter-user-select" style="width:145px">
          <option value="default">Default board</option>
          <option value="dashboard">Dashboard</option>
          <option value="milestone">Milestone view</option>
        </select>
      </div>
      <div class="settings-toggle-row" style="margin-top:12px">
        <div class="settings-toggle-info">
          <div class="settings-toggle-title">Show board minimap</div>
          <div class="settings-toggle-help">Show the mini overview when viewing a dependency chain.</div>
        </div>
        <button class="settings-toggle" id="settings-show-minimap" type="button" role="switch" aria-checked="true">
          <span class="settings-toggle-track" aria-hidden="true"></span>
          <span class="settings-toggle-state">On</span>
        </button>
      </div>
    </div>
    <div class="settings-section">
      <div class="settings-section-title">Startup messages</div>
      <div class="settings-startup-row">
        <div class="settings-startup-info">View the messages shown while the app is loading.</div>
        <button class="settings-button" id="settings-see-startup-messages" type="button">See all messages</button>
      </div>
    </div>
    <div class="settings-section">
      <div class="settings-section-title">Feedback and Features</div>
      <div class="settings-feedback-row">
        <div class="settings-feedback-info">Request a feature or improvement:</div>
        <a class="settings-button" href="https://warwick.ac.uk/services/marketing/teams/cds/opd/" target="_blank" rel="noopener noreferrer">Suggest a change</a>
      </div>      
    </div>
    <div class="settings-section">
      <div class="settings-section-title">Application</div>
      <div class="settings-version-row">
        <div class="settings-version-info">Current version <span class="settings-version-value" id="settings-current-version">Checking…</span><div class="settings-version-status" id="settings-latest-version">Checking latest release…</div></div>
        <a class="settings-button" id="settings-release-link" href="https://github.com/EdyerWarwick/jira-dependencies-map/releases/latest" target="_blank" rel="noopener">View latest release</a>
      </div>
    </div>
    </div>
    <div id="settings-jql-view" class="settings-jql-view">
      <button class="settings-jql-back" id="settings-jql-back" type="button">← Back to Settings</button>
      <div class="settings-section">
        <div class="settings-section-title">Custom JQL</div>
        <label class="settings-jql-label" for="settings-jql-input">Default JQL</label>
        <div class="settings-jql-default" id="settings-jql-default"></div>
        <div class="settings-jql-help">
          Add your own JQL. Please validate your JQL query here
          <a href="https://uow-idg.atlassian.net/issues/" target="_blank" rel="noopener noreferrer">https://uow-idg.atlassian.net/issues/</a>
          before adding.
        </div>
        <textarea class="settings-jql-input" id="settings-jql-input" spellcheck="false" placeholder="Enter your JQL query…"></textarea>
        <div class="settings-jql-status" id="settings-jql-status"></div>
        <div class="settings-jql-actions">
          <button class="settings-button" id="settings-jql-reset" type="button">Reset to default</button>
          <button class="settings-button primary" id="settings-jql-save" type="button">Save JQL</button>
        </div>
      </div>
    </div>
    <div id="settings-messages-view" style="display:none">
      <button class="settings-back" id="settings-back" type="button">← Back to Settings</button>
      <div class="settings-messages-card" id="settings-messages-list"></div>
    </div>
    <div class="settings-actions">
      <button class="settings-button" id="settings-close-bottom" type="button">Close</button>
    </div>
  </div>
</div>

<div id="credential-modal" role="dialog" aria-modal="true" aria-labelledby="credential-title">
  <div class="credential-card">
    <h2 id="credential-title">Jira credentials required</h2>
    <p id="credential-description">Enter your Jira email address and API key. The credential is stored in your Windows Credential Manager and is not stored in this application.</p>
    <div class="credential-error" id="credential-error"></div>
    <div class="credential-field">
      <label for="credential-email">Jira email</label>
      <input id="credential-email" type="email" autocomplete="username" spellcheck="false" placeholder="name@example.com">
    </div>
    <div class="credential-field">
      <label for="credential-api-key">Jira API key</label>
      <input id="credential-api-key" type="password" autocomplete="current-password" spellcheck="false" placeholder="Paste your API key">
    </div>
    <div class="credential-help">
      Need an API token?
      <a href="https://id.atlassian.com/manage-profile/security/api-tokens" target="_blank" rel="noopener noreferrer">Create one in Atlassian</a>
    </div>
    <div class="credential-note">The API key is converted to Jira's base64 Basic Authentication value only in memory when a Jira request is made. It is never written into the Python source or sent to the browser.</div>
    <div class="credential-status" id="credential-status"></div>
    <div class="credential-actions">
      <button class="credential-button" id="credential-remove" type="button" style="display:none">Remove credential &amp; restart</button>
      <button class="credential-button" id="credential-cancel" type="button" style="display:none">Cancel</button>
      <button class="credential-button primary" id="credential-save" type="button">Save &amp; connect</button>
    </div>
  </div>
</div>

<div id="dependency-status" aria-label="Dependency status key">
  <span class="status-pill blocked"><span class="status-arrow">←</span>Blocked by</span>
  <span class="status-pill blocks"><span class="status-arrow">→</span>Blocks</span>
  <span id="external-status" class="status-pill external"><span class="status-dot"></span>External blocker</span>
  <span id="cycle-status" class="status-pill cycle"><span class="status-dot"></span>Circular</span>
  <span id="locked-status" class="status-pill locked"><span class="status-dot"></span>Selected</span>
</div>


<header id="app-header">
  <div class="brand" data-action="escape" role="button" tabindex="0" title="Home" aria-label="Home">
    <span class="brand-icon"><img src="https://warwick.ac.uk/services/marketing/teams/cds/opd/1486504840-cog-cogwheel-gear-repr-options-setting_81360.png" alt="" aria-hidden="true"></span>
    <div>Jira Dependency Map<small id="brand-subtitle">Web Evolution dependencies</small></div>
  </div>

  <div class="header-center">
    <a class="custom-jql-indicator" id="custom-jql-indicator" href="#custom-jql" title="Custom JQL settings" aria-label="Open Custom JQL settings">
      <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M4 5h16M7 12h10M10 19h4"/></svg>
    </a>
    <!-- Search is shown only when nothing is locked -->
    <div class="search-wrap" id="search-wrap">
      <svg width="14" height="14" viewBox="0 0 24 24" fill="none"
           stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round">
        <circle cx="11" cy="11" r="8"/><path d="m21 21-4.35-4.35"/>
      </svg>
      <input id="search" type="text"
             placeholder="Search key, summary or epic&hellip;" autocomplete="off" spellcheck="false">
      <button id="search-clear" type="button" aria-label="Clear text search" title="Clear text search">&times;</button>
    </div>
    <div class="filter-controls" id="filter-controls">
      <button class="btn" id="filters-btn" type="button" aria-haspopup="true" aria-expanded="false">Filters</button>
      <div class="filter-menu" id="filter-menu">
        <div class="filter-menu-title">Filters</div>
        <label class="filter-option" style="display:block">
          <span class="filter-option-label" style="display:block;margin-bottom:6px">User</span>
          <select class="filter-user-select" id="filter-user" aria-label="Filter by user"></select>
        </label>
        <label class="filter-option" style="display:block">
          <span class="filter-option-label" style="display:block;margin-bottom:6px">Due date</span>
          <select class="filter-user-select" id="filter-due" aria-label="Filter by due date">
            <option value="all">Show all</option>
            <option value="next7">Due in the next 7 days</option>
            <option value="nextMonth">Due in the next month</option>
            <option value="overdue">Overdue</option>
            <option value="noDueDate">No due date set</option>
          </select>
        </label>
        <label class="filter-option">
          <span class="filter-option-label">Include With Remarkable</span>
          <input class="filter-checkbox" id="filter-remarkable" type="checkbox" checked>
        </label>
      </div>
      <button class="btn filter-clear" id="clear-filters" type="button" title="Clear search and filters" disabled>Clear filters</button>
    </div>
  </div>

  <div class="header-actions">
    <span id="status-text">Loading&hellip;</span>
    <button class="btn" id="deselect">&#x2190; Back</button>
    <button class="btn btn-save" id="save" hidden title="Save 0 issues" aria-label="Save 0 issues">
      <svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">
        <path d="M5 4h11l3 3v13H5z"/><path d="M8 4v6h8V4"/><path d="M8 20v-6h8v6"/>
      </svg><span id="save-count">0</span>
    </button>
    <button class="btn btn-discard" id="discard" hidden title="Discard all changes" aria-label="Discard all changes">
      <svg width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">
        <path d="M4 7h16"/><path d="M10 11v6"/><path d="M14 11v6"/><path d="M6 7l1 13h10l1-13"/><path d="M9 7V4h6v3"/>
      </svg>
    </button>
    <span class="header-divider" aria-hidden="true"></span>
    <button class="btn btn-toggle-completed" id="toggle-completed" title="Toggle visibility of Done / Completed tickets">
      <span class="toggle-track"></span>Completed
    </button>
    <div class="view-switcher" id="view-switcher" role="group" aria-label="Board view">
      <button class="view-switch active" data-view="default" type="button">Full board</button>
      <button class="view-switch" data-view="dashboard" type="button">Dashboard</button>
      <button class="view-switch" data-view="milestone" type="button">Milestones</button>
    </div>
    <button class="btn btn-settings" id="settings" title="Settings" aria-label="Settings">&#9881;</button>
    <button class="btn btn-refresh" id="refresh" title="Refresh from Jira">&#x21BB;</button>
  </div>
</header>

<button class="milestone-back" id="milestone-back" type="button"></button>
<div id="error"></div>
<div id="dependency-modal" role="dialog" aria-modal="true" aria-labelledby="dependency-modal-title">
  <div class="modal-card">
    <div class="modal-head"><h2 id="dependency-modal-title">Edit dependencies</h2><button class="modal-close" id="dependency-modal-close" type="button" aria-label="Close">×</button></div>
    <div class="modal-field"><label for="dep-issue-a">Issue A</label><select id="dep-issue-a" disabled></select></div>
    <div class="modal-field"><label for="dep-issue-b-search">Issue B</label>
      <div class="issue-combobox">
        <input class="issue-search" id="dep-issue-b-search" type="text"
               placeholder="Search issue key or summary…" autocomplete="off"
               spellcheck="false" role="combobox" aria-expanded="false"
               aria-controls="dep-issue-b-list" aria-autocomplete="list">
        <div class="issue-options" id="dep-issue-b-list" role="listbox"></div>
      </div>
    </div>
    <div class="modal-direction">
      <span id="dep-direction">Issue A blocks Issue B</span>
      <label class="direction-switch" title="Switch which issue blocks the other">
        <span class="direction-switch-label">Swap A / B</span>
        <input id="dep-swap" type="checkbox" aria-label="Swap Issue A and Issue B">
        <span class="switch-track" aria-hidden="true"></span>
      </label>
    </div>
    <div class="modal-actions">
      <button class="modal-secondary" id="dependency-modal-add" type="button">Add here</button>
      <button class="modal-secondary" id="dependency-modal-cancel" type="button">Close</button>
    </div>
    <div class="modal-existing">
      <h3>Current dependencies</h3>
      <div id="dependency-list"></div>
    </div>
  </div>
</div>
<div id="loading"><div class="loading-favicon-wrap"><img class="loading-favicon" src="https://warwick.ac.uk/services/marketing/teams/cds/opd/1486504840-cog-cogwheel-gear-repr-options-setting_81360.png" alt=""></div><div id="loading-label">Connecting to Jira&hellip;</div><div class="loading-progress"><div id="loading-progress-bar"></div></div><div id="loading-status">Working on it…</div><div id="startup-message" class="startup-message" style="display:none"></div></div>
<div id="app"><main id="board"><svg id="lines" aria-hidden="true"></svg></main></div>
<div id="board-minimap" aria-label="Board overview">
  <div id="board-minimap-stage">
    <div id="board-minimap-content" class="minimap-board"></div>
    <div id="board-minimap-viewport" aria-label="Current view"></div>
    <div id="board-minimap-hint">Drag to move</div>
  </div>
</div>
<div class="save-progress" id="save-progress" role="status" aria-live="polite">
  <div class="save-progress-text"><span id="save-progress-label">Saving 0 of 0&hellip;</span><span id="save-progress-percent">0%</span></div>
  <div class="save-progress-bar"><div class="save-progress-fill" id="save-progress-fill"></div></div>
</div>


<script>
// ── State ────────────────────────────────────────────────────────────────
const CFG = {jiraBaseUrl: 'https://uow-idg.atlassian.net'};

const state = {
  issues:[], edges:[], levels:0,
  lockedKey:null,
  selectionHistory:[],
  showBlocked:false,
  filterUser:"",
  filterDue:"all",
  includeWithRemarkable:true,
  // Each entry: { source, target, action:'add'|'delete' }
  pendingChanges:[],
  cleanSnapshot:null,
  history:[],
  redoHistory:[],
  historyApplying:false,
  showCompleted:false,          // toggle: OFF by default (done/completed hidden)
  completedDownloadStatus:'not-started',
  // Incremented for every Jira load. Older responses/background jobs are ignored.
  loadGeneration:0,
  showMilestones:false,         // toggle: OFF by default; milestone overview
  showDashboard:false,
  startingView:'default',
  showMiniMap:true, customJql:'', useJiraModal:false,
  displayIssues:[], displayEdges:[], displayLevels:0,
  hoverKey:null, hoverLockKey:null,
  returnMilestoneKey:null,
  dashboardReturnSection:null,
  // Preserve each view's independent scroll position across board rebuilds.
  scrollPositions:{
    main:{appLeft:0,appTop:0,columns:{}},
    locked:{appLeft:0,appTop:0,columns:{}},
    milestone:{appLeft:0,appTop:0,columns:{}}
  }
};

// ── Shareable selected-card URL ───────────────────────────────────────────
// URLs use the compact form ?opd-523 and optionally ?opd-523&showblocked.
function readSharedViewUrl(){
  const parts=window.location.search.replace(/^\?/,'').split('&').map(part=>decodeURIComponent(part).trim()).filter(Boolean);
  const keyPart=parts.find(part=>/^[A-Za-z][A-Za-z0-9_]*-\d+$/.test(part));
  return {
    key:keyPart ? keyPart.toUpperCase() : null,
    showBlocked:parts.some(part=>part.toLowerCase()==='showblocked')
  };
}
let pendingSharedView=readSharedViewUrl();

function syncSharedViewUrl(){
  const selectedKey=(!state.showDashboard && !state.showMilestones && state.lockedKey)
    ? String(state.lockedKey).toLowerCase()
    : '';
  const query=selectedKey
    ? '?' + encodeURIComponent(selectedKey) + (state.showBlocked ? '&showblocked' : '')
    : '';
  const nextUrl=window.location.pathname + query + window.location.hash;
  if(nextUrl !== window.location.pathname + window.location.search + window.location.hash){
    window.history.replaceState(null,'',nextUrl);
  }
}

// ── Filter preferences ────────────────────────────────────────────────────
let preferencesReady=false;
let startupViewPending=true;

async function loadPreferences(){
  // Preferences are optional. Never let a preferences-file/API problem stop
  // the main application from starting.
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), 2000);
  try{
    const r=await fetch('/api/preferences?ts='+Date.now(),{cache:'no-store',signal:controller.signal});
    const saved=await r.json().catch(()=>({}));
    if(!r.ok) throw new Error(saved.error || 'Unable to load preferences.');
    state.showCompleted=saved.showCompleted===true;
    state.filterUser=typeof saved.filterUser==='string' ? saved.filterUser : '';
    state.filterDue=['all','next7','nextMonth','overdue','noDueDate'].includes(saved.filterDue) ? saved.filterDue : 'all';
    state.includeWithRemarkable=saved.includeWithRemarkable!==false;
    state.customJql=typeof saved.customJql==='string' ? saved.customJql.trim() : '';
    state.useJiraModal=saved.useJiraModal===true;
    state.showMiniMap=saved.showMiniMap!==false;
    state.startingView=['default','dashboard','milestone'].includes(saved.startingView) ? saved.startingView : 'default';
  }catch(e){
    console.warn('Could not load persistent preferences; using defaults.',e);
  }finally{
    clearTimeout(timeout);
    preferencesReady=true;
  }
}

async function savePreferences(updates){
  Object.assign(state,updates||{});
  if(!preferencesReady) return;
  try{
    await fetch('/api/preferences',{
      method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({
        showCompleted:!!state.showCompleted, filterUser:state.filterUser||'', filterDue:state.filterDue||'all',
        includeWithRemarkable:state.includeWithRemarkable!==false,
        customJql:state.customJql||'', useJiraModal:!!state.useJiraModal,
        showMiniMap:state.showMiniMap!==false, startingView:state.startingView || 'default'
      }),cache:'no-store'
    });
  }catch(e){ console.warn('Could not save persistent preferences.',e); }
}
function saveFilterPreferences(){
  savePreferences({showCompleted:!!state.showCompleted,filterUser:state.filterUser||'',filterDue:state.filterDue||'all',
    includeWithRemarkable:state.includeWithRemarkable!==false});
}
function filterSnapshot(){
  return {searchTerm:state.searchTerm||'',showCompleted:!!state.showCompleted,filterUser:state.filterUser||'',filterDue:state.filterDue||'all',includeWithRemarkable:state.includeWithRemarkable!==false};
}
function restoreFilterSnapshot(snap){
  const s = snap || {};
  state.searchTerm = s.searchTerm || '';
  state.showCompleted = !!s.showCompleted;
  state.filterUser = s.filterUser || '';
  state.filterDue = ['all','next7','nextMonth','overdue','noDueDate'].includes(s.filterDue) ? s.filterDue : 'all';
  state.includeWithRemarkable = s.includeWithRemarkable !== false;
  if(searchEl) searchEl.value = state.searchTerm;
  saveFilterPreferences();
}
function clearAllFilters(){
  state.searchTerm = '';
  state.showCompleted = false;
  state.filterUser = '';
  state.filterDue = 'all';
  state.includeWithRemarkable = true;
  if(searchEl) searchEl.value = '';
  saveFilterPreferences();
  updateFilterControls();
  render();
}
function activeFilterCount(){
  return (state.searchTerm ? 1 : 0) + (state.showCompleted ? 1 : 0) + (state.filterUser ? 1 : 0) + (state.filterDue !== 'all' ? 1 : 0) + (!state.includeWithRemarkable ? 1 : 0);
}
function updateFilterControls(){
  const toggleCompletedBtn = document.getElementById('toggle-completed');
  if(toggleCompletedBtn) toggleCompletedBtn.classList.toggle('active', !!state.showCompleted);
  if(filterRemarkable) filterRemarkable.checked = state.includeWithRemarkable !== false;
  if(filterDue) filterDue.value = state.filterDue || 'all';
  const count = activeFilterCount();
  if(clearFiltersBtn){
    clearFiltersBtn.textContent = count ? 'Clear filters (' + count + ')' : 'Clear filters';
    clearFiltersBtn.disabled = count === 0;
  }
  if(filtersBtn) filtersBtn.setAttribute('aria-expanded', filterMenu?.classList.contains('open') ? 'true' : 'false');
}
function populateFilterUsers(){
  if(!filterUser) return;
  const users = new Map();
  // Build the user list from the tickets currently eligible for display.
  // This means users who only have completed tickets disappear when
  // Show completed is off, and reappear when it is enabled.
  const eligibleIssues = state.displayIssues || [];
  eligibleIssues.forEach(i => {
    const id = i.assigneeAccountId || '';
    const name = (i.assignee || '').trim() || 'Unassigned';
    if(id && !users.has(id)) users.set(id, name);
  });
  const current = state.filterUser || '';

  // Keep the currently selected user in the list even if they no longer have
  // an active ticket. This lets the UI explain that the selection is now empty
  // instead of silently changing the filter back to All users.
  if(current && current !== '__UNASSIGNED__' && !users.has(current)){
    const currentIssue = (state.issues || []).find(i => (i.assigneeAccountId || '') === current);
    if(currentIssue){
      users.set(current, (currentIssue.assignee || '').trim() || current);
    }
  }

  filterUser.innerHTML = '<option value="">All users</option>' +
    [...users.entries()].sort((a,b) => a[1].localeCompare(b[1])).map(([id,name]) => '<option value="' + esc(id) + '">' + esc(name) + '</option>').join('');
  // Unassigned must always be the first user option after All users.
  const unassigned = document.createElement('option');
  unassigned.value = '__UNASSIGNED__'; unassigned.textContent = 'Unassigned';
  filterUser.insertBefore(unassigned, filterUser.options[1] || null);
  filterUser.value = current;
  if(filterUser.value !== current) filterUser.value = '';
}

// ── DOM refs ─────────────────────────────────────────────────────────────
const board              = document.getElementById('board');
const lines              = document.getElementById('lines');
const boardMinimap       = document.getElementById('board-minimap');
const boardMinimapStage  = document.getElementById('board-minimap-stage');
const boardMinimapContent= document.getElementById('board-minimap-content');
const boardMinimapViewport = document.getElementById('board-minimap-viewport');
const loading            = document.getElementById('loading');
const dependencyStatus    = document.getElementById('dependency-status');
const statusText         = document.getElementById('status-text');
const errorEl            = document.getElementById('error');
const searchWrap         = document.getElementById('search-wrap');
const searchEl           = document.getElementById('search');
const searchClearBtn     = document.getElementById('search-clear');
const filtersBtn        = document.getElementById('filters-btn');
const filterMenu        = document.getElementById('filter-menu');
const toggleCompletedBtn = document.getElementById('toggle-completed');
const filterUser        = document.getElementById('filter-user');
const filterDue         = document.getElementById('filter-due');
const filterRemarkable  = document.getElementById('filter-remarkable');
const clearFiltersBtn   = document.getElementById('clear-filters');
const deselectBtn        = document.getElementById('deselect');
const milestoneBackBtn  = document.getElementById('milestone-back');
const loadingStage = document.getElementById('loading-stage');
const loadingProgressBar = document.getElementById('loading-progress-bar');
const credentialModal = document.getElementById('credential-modal');
const credentialEmail = document.getElementById('credential-email');
const credentialApiKey = document.getElementById('credential-api-key');
const credentialError = document.getElementById('credential-error');
const credentialStatus = document.getElementById('credential-status');
const credentialSave = document.getElementById('credential-save');
const credentialRemove = document.getElementById('credential-remove');
const credentialCancel = document.getElementById('credential-cancel');
const settingsBtn = document.getElementById('settings');
const settingsModal = document.getElementById('settings-modal');
const settingsEmail = document.getElementById('settings-email');
const settingsCurrentVersion = document.getElementById('settings-current-version');
const settingsLatestVersion = document.getElementById('settings-latest-version');
const settingsReleaseLink = document.getElementById('settings-release-link');
const settingsManageCredential = document.getElementById('settings-manage-credential');
const settingsAdvanced = document.getElementById('settings-advanced');
const settingsJqlView = document.getElementById('settings-jql-view');
const settingsJqlBack = document.getElementById('settings-jql-back');
const settingsJqlDefault = document.getElementById('settings-jql-default');
const settingsJqlInput = document.getElementById('settings-jql-input');
const settingsJqlStatus = document.getElementById('settings-jql-status');
const settingsJqlSave = document.getElementById('settings-jql-save');
const settingsJqlReset = document.getElementById('settings-jql-reset');
const customJqlIndicator = document.getElementById('custom-jql-indicator');
const brandSubtitle = document.getElementById('brand-subtitle');

const settingsUseJiraModal = document.getElementById('settings-use-jira-modal');
const settingsShowMiniMap = document.getElementById('settings-show-minimap');
const settingsStartingView = document.getElementById('settings-starting-view');
const settingsClose = document.getElementById('settings-close');
const settingsCloseBottom = document.getElementById('settings-close-bottom');
const settingsMainView = document.getElementById('settings-main-view');
const settingsMessagesView = document.getElementById('settings-messages-view');
const settingsSeeStartupMessages = document.getElementById('settings-see-startup-messages');
const settingsBack = document.getElementById('settings-back');
const settingsMessagesList = document.getElementById('settings-messages-list');
const startupMessage = document.getElementById('startup-message');
const dueDateModal = document.getElementById('due-date-modal');
const dueDateInput = document.getElementById('due-date-input');
const dueDateKey = document.getElementById('due-date-key');
const chainDateWarningModal = document.getElementById('chain-date-warning-modal');
const chainDateWarningContent = document.getElementById('chain-date-warning-content');
let pendingDueDateChange = null;

let loadingTimer = null;
let loadingProgressTimer = null;

function updateLoadingProgress(data){
  if(!data) return;
  const label=document.getElementById('loading-label');
  const status=document.getElementById('loading-status');
  if(data.phase) label.textContent=data.phase;
  if(data.detail) status.textContent=data.detail;
}
function startLoadingProgressPolling(){
  if(loadingProgressTimer) clearInterval(loadingProgressTimer);
  const poll=async()=>{
    try{
      const r=await fetch('/api/loading-status?ts='+Date.now(),{cache:'no-store'});
      if(r.ok) updateLoadingProgress(await r.json());
    }catch(e){}
  };
  poll();
  loadingProgressTimer=setInterval(poll,350);
}
function stopLoadingProgressPolling(){
  if(loadingProgressTimer) clearInterval(loadingProgressTimer);
  loadingProgressTimer=null;
}

// ── Settings ───────────────────────────────────────────────────────────────
let DEFAULT_JQL = "";

function getCustomJql(){ return String(state.customJql || '').trim(); }
function setCustomJql(value){
  state.customJql=String(value || '').trim();
  savePreferences({customJql:state.customJql});
  updateCustomJqlIndicator();
}
function getActiveJql(){ return getCustomJql() || DEFAULT_JQL; }
function updateCustomJqlIndicator(){
  const active = !!getCustomJql();
  if(customJqlIndicator) customJqlIndicator.classList.toggle('active', active);
  if(brandSubtitle) brandSubtitle.textContent = active ? 'Custom dependencies' : 'Web Evolution dependencies';
}
function setJqlStatus(message, type=''){
  if(!settingsJqlStatus) return;
  settingsJqlStatus.textContent = message || '';
  settingsJqlStatus.className = 'settings-jql-status' + (type ? ' ' + type : '');
}
function showSettingsJql(){
  settingsMainView.style.display = 'none';
  settingsMessagesView.style.display = 'none';
  settingsJqlView.classList.add('open');
  settingsJqlDefault.textContent = DEFAULT_JQL || "Loading default JQL…";
  settingsJqlInput.value = getCustomJql();
  setJqlStatus(getCustomJql() ? 'Custom JQL is currently active.' : 'Using the default JQL.');
  settingsJqlInput.focus();
}
function showSettingsMain(){
  settingsMainView.style.display = '';
  settingsMessagesView.style.display = 'none';
  settingsJqlView.classList.remove('open');
}
function saveCustomJql(){
  const value = settingsJqlInput.value.trim();
  if(!value){
    setJqlStatus('Enter a JQL query, or use Reset to default.', 'error');
    return;
  }
  setCustomJql(value);
  setJqlStatus('Custom JQL saved. Refreshing the dependency map…', 'success');
  closeSettings();
  load(true);
}
function resetCustomJql(){
  setCustomJql('');
  settingsJqlInput.value = '';
  setJqlStatus('Reset to the default JQL. Refreshing the dependency map…', 'success');
  closeSettings();
  load(true);
}
function getUseJiraModal(){ return state.useJiraModal === true; }
function setUseJiraModal(enabled){
  state.useJiraModal=!!enabled;
  savePreferences({useJiraModal:state.useJiraModal});
  updateJiraModalSetting();
  updateMiniMapSetting();
}
function updateJiraModalSetting(){
  if(!settingsUseJiraModal) return;
  const enabled = getUseJiraModal();
  settingsUseJiraModal.classList.toggle('active', enabled);
  settingsUseJiraModal.setAttribute('aria-checked', enabled ? 'true' : 'false');
  const stateLabel = settingsUseJiraModal.querySelector('.settings-toggle-state');
  if(stateLabel) stateLabel.textContent = enabled ? 'On' : 'Off';
}
function updateStartingViewSetting(){
  if(settingsStartingView) settingsStartingView.value = ['default','dashboard','milestone'].includes(state.startingView) ? state.startingView : 'default';
}
function setStartingView(value){
  state.startingView = ['default','dashboard','milestone'].includes(value) ? value : 'default';
  savePreferences({startingView:state.startingView});
  updateStartingViewSetting();
}
function updateMiniMapSetting(){
  if(!settingsShowMiniMap) return;
  const enabled = state.showMiniMap !== false;
  settingsShowMiniMap.classList.toggle('active', enabled);
  settingsShowMiniMap.setAttribute('aria-checked', enabled ? 'true' : 'false');
  const stateLabel = settingsShowMiniMap.querySelector('.settings-toggle-state');
  if(stateLabel) stateLabel.textContent = enabled ? 'On' : 'Off';
}
function setMiniMapSetting(enabled){
  state.showMiniMap = !!enabled;
  savePreferences({showMiniMap:state.showMiniMap});
  updateMiniMapSetting();
  scheduleMiniMapUpdate();
}
function renderStartupMessages(items){
  settingsMessagesList.innerHTML = '';
  if(!items.length){
    settingsMessagesList.innerHTML = '<div class="settings-message-empty">No startup messages are currently available.</div>';
    return;
  }
  items.forEach(item => {
    const el = document.createElement('div');
    el.className = 'settings-message-item';
    const title = document.createElement('div');
    title.className = 'settings-message-title';
    title.textContent = item.title || '';
    const body = document.createElement('div');
    body.className = 'settings-message-body';
    body.innerHTML = item.parsedContentBody || '';
    el.appendChild(title);
    el.appendChild(body);
    settingsMessagesList.appendChild(el);
  });
}
async function fetchStartupMessages(){
  const url = '/api/startup-messages?ts=' + Date.now();
  console.log('[Startup Messages] Fetching:', url);
  try{
    const r = await fetch(url,{cache:'no-store'});
    console.log('[Startup Messages] Browser response:', r.status, r.statusText);
    const data = await r.json().catch(async () => {
      console.error('[Startup Messages] Response was not valid JSON');
      return {};
    });
    console.log('[Startup Messages] Browser received:', data);
    if(!r.ok || !Array.isArray(data.items)){
      throw new Error(data.error || 'Unable to load startup messages');
    }
    console.log('[Startup Messages] Received', data.items.length, 'message(s)');
    return data.items;
  }catch(e){
    console.error('[Startup Messages] Fetch failed:', e);
    throw e;
  }
}
async function showAllStartupMessages(){
  console.log('[Startup Messages] Opening "See all messages"');
  settingsMainView.style.display = 'none';
  settingsMessagesView.style.display = '';
  settingsMessagesList.innerHTML = '<div class="settings-message-empty">Loading messages…</div>';
  try{
    const items = await fetchStartupMessages();
    console.log('[Startup Messages] Rendering', items.length, 'message(s) in Sitebuilder order');
    renderStartupMessages(items);
  }catch(e){
    console.error('[Startup Messages] Settings load failed:', e);
    settingsMessagesList.innerHTML = '<div class="settings-message-empty">Startup messages could not be loaded.</div>';
  }
}
function closeSettings(){ settingsModal.classList.remove('open'); showSettingsMain(); }
async function openSettings(openJql = false){
  updateJiraModalSetting();
  updateMiniMapSetting();
  updateStartingViewSetting();
  updateCustomJqlIndicator();
  settingsModal.classList.add('open');
  settingsEmail.textContent = 'Checking…';
  settingsCurrentVersion.textContent = 'Checking…';
  settingsLatestVersion.textContent = 'Checking latest release…';
  try{
    const r = await fetch('/api/credential-status',{cache:'no-store'});
    const data = await r.json().catch(()=>({}));
    settingsEmail.textContent = data.configured ? (data.email || 'Configured') : 'Not configured';
  }catch(e){ settingsEmail.textContent = 'Unable to check'; }
  try{
    const r = await fetch('/api/config',{cache:'no-store'});
    const data = await r.json().catch(()=>({}));
    if(r.ok && data.jql) DEFAULT_JQL = data.jql;
    if(openJql) showSettingsJql();
  }catch(e){ if(openJql) showSettingsJql(); }
  try{
    const r = await fetch('/api/app-version?ts=' + Date.now(),{cache:'no-store'});
    const data = await r.json().catch(()=>({}));
    if(!r.ok) throw new Error('version check failed');
    settingsCurrentVersion.textContent = data.current ? 'v' + data.current : 'Unknown';
    settingsLatestVersion.textContent = data.updateAvailable ? 'Latest release: v' + data.latest + ' available' : 'Latest release: v' + (data.latest || data.current || 'Unknown');
    if(data.releaseUrl) settingsReleaseLink.href = data.releaseUrl;
  }catch(e){
    settingsCurrentVersion.textContent = 'Unable to check';
    settingsLatestVersion.textContent = 'Latest release could not be checked';
  }
}

// ── Windows credential setup ───────────────────────────────────────────────
function showCredentialError(msg){
  credentialError.textContent = msg || '';
  credentialError.classList.toggle('visible', !!msg);
}
function openCredentialModal(manage=false, email=''){
  credentialModal.classList.add('open');
  credentialEmail.value = email || '';
  credentialApiKey.value = '';
  credentialError.classList.remove('visible');
  credentialStatus.textContent = manage ? 'Stored credential: ' + (email || 'configured') : '';
  credentialRemove.style.display = manage ? 'inline-block' : 'none';
  credentialCancel.style.display = manage ? 'inline-block' : 'none';
  credentialSave.textContent = manage ? 'Replace & connect' : 'Save & connect';
  credentialEmail.focus();
}
function closeCredentialModal(){
  credentialModal.classList.remove('open');
  showCredentialError('');
}
async function saveCredential(){
  const email = credentialEmail.value.trim();
  const apiKey = credentialApiKey.value.trim();
  showCredentialError('');
  if(!email || !apiKey){
    showCredentialError('Enter both your Jira email address and API key.');
    return;
  }
  credentialSave.disabled = true;
  credentialStatus.textContent = 'Saving and checking Jira authentication…';
  try{
    const r = await fetch('/api/credentials',{
      method:'POST',
      headers:{'Content-Type':'application/json'},
      body:JSON.stringify({email,apiKey})
    });
    const data = await r.json().catch(()=>({}));
    if(!r.ok || !data.ok) throw new Error(data.error || 'Could not save the credential.');
    closeCredentialModal();
    credentialStatus.textContent = '';
    hideError();
    load(true);
  }catch(e){
    showCredentialError(e.message || 'Could not save the credential.');
    credentialStatus.textContent = '';
  }finally{
    credentialSave.disabled = false;
  }
}
async function removeCredential(){
  if(!confirm('Remove the stored Jira credential and restart the application? You will need to enter a new API key after restart.')) return;
  credentialRemove.disabled = true;
  credentialSave.disabled = true;
  credentialCancel.disabled = true;
  credentialStatus.textContent = 'Removing credential and restarting…';
  showCredentialError('');
  try{
    const r = await fetch('/api/credentials/remove',{method:'POST'});
    const data = await r.json().catch(()=>({}));
    if(!r.ok || !data.ok) throw new Error(data.error || 'Could not remove the credential.');
    document.getElementById('credential-title').textContent = 'Restarting…';
    document.getElementById('credential-description').textContent = 'The stored Jira credential has been removed. The application is restarting so a new credential can be entered.';
    document.querySelectorAll('.credential-field,.credential-note,.credential-actions').forEach(el=>el.style.display='none');
    // The server is restarting, so retry until the new instance is listening.
    // A single location.reload() can race the startup and show
    // "localhost refused to connect".
    const reconnect = () => {
      fetch('/api/credential-status',{cache:'no-store'})
        .then(r => { if(r.ok) location.reload(); else throw new Error('not ready'); })
        .catch(() => setTimeout(reconnect,500));
    };
    setTimeout(reconnect,1500);
  }catch(e){
    showCredentialError(e.message || 'Could not remove the credential.');
    credentialRemove.disabled = false;
    credentialSave.disabled = false;
    credentialCancel.disabled = false;
    credentialStatus.textContent = '';
  }
}
updateCustomJqlIndicator();

// ── Required application update ───────────────────────────────────────────
let updateRestarting = false;
let requiredUpdateVersion = '';

function updateVersionTuple(value){
  return String(value || '').replace(/^[vV]/,'').split('.').map(part => {
    const match = String(part).match(/^\d+/);
    return match ? Number(match[0]) : 0;
  });
}

function updateVersionAtLeast(actual, expected){
  const a = updateVersionTuple(actual);
  const b = updateVersionTuple(expected);
  const length = Math.max(a.length,b.length);
  for(let i=0;i<length;i++){
    const left = a[i] || 0;
    const right = b[i] || 0;
    if(left !== right) return left > right;
  }
  return true;
}

function setRequiredUpdateStatus(message, isError=false){
  const status = document.getElementById('required-update-status');
  status.textContent = message || '';
  status.classList.toggle('error', !!isError);
}

async function waitForUpdatedApplication(previousPid, expectedVersion){
  const deadline = Date.now() + 180000;
  while(Date.now() < deadline){
    await new Promise(resolve => setTimeout(resolve,1000));
    try{
      const controller = new AbortController();
      const timer = setTimeout(() => controller.abort(),2500);
      const response = await fetch('/api/update-health?ts=' + Date.now(),{
        cache:'no-store',
        signal:controller.signal
      });
      clearTimeout(timer);
      const data = await response.json().catch(()=>({}));
      if(
        response.ok &&
        data.ok === true &&
        Number(data.pid) !== Number(previousPid) &&
        updateVersionAtLeast(data.version,expectedVersion)
      ){
        setRequiredUpdateStatus('Update installed. Reloading…');
        window.location.reload();
        return;
      }
    }catch(e){
      // The old server disappearing is expected while the launcher updates it.
    }
  }
  const button = document.getElementById('required-update-button');
  button.disabled = false;
  button.textContent = 'Try update again';
  updateRestarting = false;
  setRequiredUpdateStatus('The update is taking longer than expected. Try again or restart the app from the Start menu.',true);
}

async function installRequiredUpdate(){
  if(updateRestarting) return;
  updateRestarting = true;
  const button = document.getElementById('required-update-button');
  button.disabled = true;
  button.textContent = 'Restarting…';
  setRequiredUpdateStatus('Closing the app and downloading the new version…');

  try{
    const response = await fetch('/api/install-update',{
      method:'POST',
      cache:'no-store',
      headers:{'Content-Type':'application/json'},
      body:'{}'
    });
    const data = await response.json().catch(()=>({}));
    if(!response.ok || !data.ok) throw new Error(data.error || 'The updater could not be started.');
    waitForUpdatedApplication(data.pid,requiredUpdateVersion);
  }catch(e){
    updateRestarting = false;
    button.disabled = false;
    button.textContent = 'Try update again';
    setRequiredUpdateStatus(e.message || 'The updater could not be started.',true);
  }
}

async function checkForRequiredUpdate(){
  try{
    const response = await fetch('/api/app-version?ts=' + Date.now(),{cache:'no-store'});
    const data = await response.json().catch(()=>({}));
    if(!response.ok) return false;
    if(data.updateAvailable && data.canInstall){
      requiredUpdateVersion = String(data.latest || '');
      const current = data.current ? 'v' + data.current : 'this version';
      const latest = data.latest ? 'v' + data.latest : 'a newer version';
      document.getElementById('required-update-message').textContent =
        'Jira Dependency Map ' + latest + ' is available. You are using ' + current + '.';
      const modal = document.getElementById('required-update-modal');
      modal.classList.add('open');
      document.getElementById('required-update-button').focus();
      return true;
    }
  }catch(e){
    console.warn('Automatic update check failed:',e);
  }
  return false;
}

document.getElementById('required-update-button').addEventListener('click',installRequiredUpdate);

async function initialiseApp(){
  try{
    const r = await fetch('/api/credential-status',{cache:'no-store'});
    const data = await r.json().catch(()=>({}));
    if(!r.ok || data.error){
      showCredentialError(data.error || 'Unable to access the Windows Credential Manager.');
      openCredentialModal(false);
      return;
    }
    if(!data.configured){
      openCredentialModal(false);
      return;
    }
    const configResponse = await fetch('/api/config?ts=' + Date.now(),{cache:'no-store'});
    const config = await configResponse.json().catch(()=>({}));
    if(!configResponse.ok || !config.jql){
      throw new Error(config.error || 'Unable to load the default Jira JQL.');
    }
    DEFAULT_JQL = String(config.jql).trim();

    // Load optional per-user preferences after the server and Jira
    // configuration are confirmed. A preferences problem must never prevent
    // the normal application startup.
    await loadPreferences();
    updateJiraModalSetting();
    updateMiniMapSetting();
    updateStartingViewSetting();
    updateCustomJqlIndicator();
    updateFilterControls();

    load(true);
  }catch(e){
    openCredentialModal(false);
    showCredentialError(e.message || 'Unable to check the stored Jira credential.');
  }
}

// ── Utilities ─────────────────────────────────────────────────────────────
function esc(v){ return String(v == null ? '' : v).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;'); }
function showError(msg){ errorEl.textContent = msg; errorEl.style.display = 'block'; }
function hideError(){ errorEl.style.display = 'none'; }
let startupMessagePromise = null;

function setLoading(on, msg){
  loading.classList.toggle('show', on);
  dependencyStatus.classList.toggle('loading-hidden', on);
  if(on){
    document.getElementById('loading-label').textContent = msg || 'Connecting to Jira…';
    document.getElementById('loading-status').textContent = 'Connecting to Jira…';
    startLoadingProgressPolling();
    startupMessage.style.display = 'none';
    startupMessage.innerHTML = '';
    startupMessagePromise = fetchStartupMessages()
      .then(items => {
        if(!items.length){ startupMessage.style.display='none'; return items; }
        const item=items[Math.floor(Math.random()*items.length)];
        startupMessage.innerHTML='<div class="startup-message-title">'+esc(item.title || '')+'</div><div class="startup-message-body">'+(item.parsedContentBody || '')+'</div>';
        startupMessage.style.display='block';
        return items;
      })
      .catch(e => {
        console.error('[Startup Messages] Startup message fetch failed:',e);
        startupMessage.style.display='none'; startupMessage.innerHTML=''; return [];
      });
  }else{
    stopLoadingProgressPolling();
    startupMessagePromise=null;
  }
}
function startLoadingStages(msg){
  setLoading(true, msg || 'Connecting to Jira…');
}
function finishLoadingStages(){
  updateLoadingProgress({phase:'Ready',detail:'Your dependency map is ready'});
}
function normaliseSearch(value){
  return String(value || '')
    .toLocaleLowerCase('en-GB')
    .normalize('NFD')
    .replace(/[\u0300-\u036f]/g,'')
    .replace(/\s+/g,' ')
    .trim();
}
function getSearch(){ return state.searchTerm || ''; }
function buildSearchIndex(i){
  return normaliseSearch([
    i.key,
    i.summary,
    i.assignee,
    i.epic && i.epic.key,
    i.epic && i.epic.summary
  ].filter(Boolean).join(' '));
}
function searchWords(term){
  return normaliseSearch(term).split(' ').filter(Boolean);
}
function issueMatchesSearch(i, term){
  const words = searchWords(term);
  if(!words.length) return true;
  const haystack = buildSearchIndex(i);
  return words.every(word => haystack.includes(word));
}

// Search is applied directly to the rendered cards. Rebuilding the whole board
// on every keystroke caused intermittent cases where the input showed the latest
// text but the rendered results were still based on an earlier value.
function applySearchFilter(){
  if(state.lockedKey) return;

  const words = searchWords(state.searchTerm);
  const cards = [...board.querySelectorAll('.card')];
  const userFilter = state.filterUser || '';
  const dueFilter = state.filterDue || 'all';
  let visibleTotal = 0;

  cards.forEach(card => {
    const haystack = normaliseSearch(card.dataset.searchIndex || '');
    const textMatch = !words.length || words.every(word => haystack.includes(word));

    const assigneeId = card.dataset.assigneeAccountId || '';
    const userMatch = !userFilter ||
      (userFilter === '__UNASSIGNED__'
        ? !assigneeId
        : assigneeId === userFilter);

    const dueMatch = issueMatchesDueFilter({
      dueDate:card.dataset.dueDate || '',
      status:card.dataset.completed === '1' ? 'Done' : ''
    }, dueFilter);

    const match = textMatch && userMatch && dueMatch;
    card.hidden = !match;
    if(match) visibleTotal++;

    const summary = card.querySelector('.summary');
    if(summary){
      const rawSummary = card.dataset.summary || '';
      summary.innerHTML = words.length ? highlight(rawSummary, state.searchTerm) : esc(rawSummary);
    }
  });

  board.querySelectorAll('.column').forEach(col => {
    const count = col.querySelectorAll('.card:not([hidden])').length;
    const countEl = col.querySelector('.column-count');
    if(countEl) countEl.textContent = count;

    // When searching or filtering by user, hide levels containing no
    // matching cards, but never recalculate or renumber the levels themselves.
    col.style.display = (words.length || userFilter || dueFilter !== 'all') && count === 0 ? 'none' : '';
  });

  // If a selected user has become inactive because Completed was switched
  // off, keep that selection visible and explain the empty result in the board.
  const existingNoActiveUser = board.querySelector('.no-active-user');
  if(existingNoActiveUser) existingNoActiveUser.remove();
  const existingNoResults = board.querySelector('.no-results');
  if(existingNoResults) existingNoResults.remove();

  if(userFilter && visibleTotal === 0 && !words.length){
    const selectedName = userFilter === '__UNASSIGNED__'
      ? 'Unassigned'
      : ((state.issues || []).find(i => (i.assigneeAccountId || '') === userFilter)?.assignee || 'User');

    const activeUsers = new Map();
    (state.displayIssues || []).forEach(i => {
      const id = i.assigneeAccountId || '';
      if(id && !activeUsers.has(id)) activeUsers.set(id, (i.assignee || '').trim() || id);
    });

    const options = [...activeUsers.entries()]
      .sort((a,b) => a[1].localeCompare(b[1]))
      .map(([id,name]) => '<option value="' + esc(id) + '">' + esc(name) + '</option>').join('');

    const notice = document.createElement('div');
    notice.className = 'no-active-user';
    notice.innerHTML = '<div class="no-active-user-title">User has no active tickets</div>' +
      '<div class="no-active-user-label">' + esc(selectedName) + '</div>' +
      '<label class="no-active-user-select-label">Please select another user:<select class="no-active-user-select">' +
        '<option value="">Please select another user:</option>' +
        '<option value="__UNASSIGNED__">Unassigned</option>' +
        options +
      '</select></label>';
    board.appendChild(notice);

    const replacementSelect = notice.querySelector('.no-active-user-select');
    replacementSelect.addEventListener('change', () => {
      if(!replacementSelect.value) return;
      state.filterUser = replacementSelect.value;
      saveFilterPreferences();
      render();
    });
  } else if((words.length || userFilter || dueFilter !== 'all') && visibleTotal === 0){
    const notice = document.createElement('div');
    notice.className = 'no-results';
    notice.innerHTML = '<div class="no-results-title">No results to show.</div>' +
      '<div class="no-results-message">Please adjust your search or filters.</div>';
    board.appendChild(notice);
  }

  updateFilterControls();
  if(words.length || userFilter || dueFilter !== 'all'){
    statusText.textContent = visibleTotal.toLocaleString('en-GB') + ' of ' +
      state.displayIssues.length.toLocaleString('en-GB') + ' tickets match';
  }else{
    statusText.textContent = state.displayIssues.length.toLocaleString('en-GB') +
      ' tickets · ' + state.displayEdges.length.toLocaleString('en-GB') + ' dependencies';
  }
}

// Highlight matched text — properly regex-escapes the term BEFORE matching
function highlight(text, term){
  if(!term) return esc(text || '');
  // Escape HTML first, then find matches in the escaped string
  const escaped = esc(text || '');
  const safe = term.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'); // regex-escape the raw term
  const escapedTerm = esc(term).replace(/[.*+?^${}()|[\]\\]/g, '\\$&'); // regex-escape the HTML-escaped term
  return escaped.replace(new RegExp('(' + escapedTerm + ')', 'gi'), '<mark>$1</mark>');
}

// ── Compute display-filtered issues & edges ───────────────────────────────
// Called at the top of render(). Respects the showCompleted toggle and
// recalculates dependency levels for the visible subset.
// ── Scroll position preservation ─────────────────────────────────────────
// The board is rebuilt for selection changes, dependency edits, saves, etc.
// Capture the old DOM's scroll state before replacing it, then restore the
// corresponding view after the new columns have been created.
function getRenderedViewMode(){
  const app = document.getElementById('app');
  if(board.classList.contains('milestone-board') || app.classList.contains('milestone-mode')) return 'milestone';
  if(board.classList.contains('dashboard-board') || app.classList.contains('dashboard-mode')) return 'dashboard';
  if(app.classList.contains('locked')) return 'locked';
  return 'main';
}

function captureBoardScroll(){
  const app = document.getElementById('app');
  if(!app) return;
  const mode = getRenderedViewMode();
  const saved = state.scrollPositions[mode] || (state.scrollPositions[mode] = {appLeft:0,appTop:0,columns:{}});
  saved.appLeft = app.scrollLeft;
  saved.appTop = app.scrollTop;

  const columns = {};
  board.querySelectorAll('.column').forEach((column, index) => {
    const cards = column.querySelector('.cards');
    if(!cards) return;
    const level = column.dataset.level != null ? column.dataset.level : String(index);
    columns[level] = cards.scrollTop;
  });
  saved.columns = columns;
}

function restoreBoardScroll(){
  const app = document.getElementById('app');
  if(!app) return;
  const mode = getRenderedViewMode();
  const saved = state.scrollPositions[mode];
  if(!saved) return;

  app.scrollLeft = saved.appLeft || 0;
  app.scrollTop = saved.appTop || 0;

  board.querySelectorAll('.column').forEach((column, index) => {
    const cards = column.querySelector('.cards');
    if(!cards) return;
    const level = column.dataset.level != null ? column.dataset.level : String(index);
    if(Object.prototype.hasOwnProperty.call(saved.columns || {}, level)){
      cards.scrollTop = saved.columns[level] || 0;
    }
  });
}

function preserveBoardScrollDuringRender(){
  requestAnimationFrame(() => {
    // A newly selected card is a new chain view. Do not restore the previous
    // board position first, otherwise a card on the far right can briefly
    // jump back to the old left-hand position before being scrolled right.
    if(!state.revealSelectedKey){
      restoreBoardScroll();
    }

    // A second frame catches layout changes from route spacing and card
    // rendering before the browser paints the final scroll position.
    requestAnimationFrame(() => {
      if(!state.revealSelectedKey){
        restoreBoardScroll();
      }

      if(state.revealSelectedKey){
        requestAnimationFrame(() => {
          // Start the new chain from its natural top-left position and make
          // one direct, non-animated move to the selected card. This avoids
          // the visible left-then-right scroll when selecting far-right cards.
          const app = document.getElementById('app');
          if(app){
            app.scrollLeft = 0;
            app.scrollTop = 0;
          }
          board.querySelectorAll('.cards').forEach(cards => {
            cards.scrollTop = 0;
            cards.scrollLeft = 0;
          });

          revealSelectedCard(state.revealSelectedKey);
          state.revealSelectedKey = null;
        });
      }
    });
  });
}

function revealSelectedCard(key){
  if(!key || !state.lockedKey || key !== state.lockedKey) return;
  const card = board.querySelector('.card[data-key="' + CSS.escape(key) + '"]');
  if(!card) return;

  // Move directly to the selected card without an animation. The new chain
  // starts at the top-left, so this produces a single clean reposition rather
  // than scrolling back to the old position and then scrolling right again.
  card.scrollIntoView({
    behavior:'auto',
    block:'center',
    inline:'center'
  });

  card.classList.remove('dependency-flash');
  void card.offsetWidth;
  card.classList.add('dependency-flash');
  setTimeout(() => card.classList.remove('dependency-flash'), 950);
}

function computeDisplayData(){
  const DONE = new Set(['done','completed']);
  // Dependency structure must be calculated from the full active/completed
  // ticket set before the With Remarkable display filter is applied. A hidden
  // With Remarkable ticket is still a real blocker, so hiding it must never
  // promote the ticket it blocks into an earlier level.
  // Dependency chains still ignore search, user and With Remarkable filters,
  // but continue to honour the Show completed toggle.
  const structuralIssues = state.showCompleted
    ? state.issues
    : state.issues.filter(i => !DONE.has((i.status || '').toLowerCase().trim()));

  const structuralKeys = new Set(structuralIssues.map(i => i.key));
  const structuralEdges = state.edges.filter(e => structuralKeys.has(e.from) && structuralKeys.has(e.to));

  // Calculate levels from the structural graph, before any display-only
  // filtering. This preserves dependency depth when With Remarkable is hidden.
  const level = new Map(structuralIssues.map(i => [i.key, (i.externalBlockers && i.externalBlockers.length) ? 1 : 0]));
  for(let pass = 0; pass < structuralIssues.length; pass++){
    let changed = false;
    for(const e of structuralEdges){
      if(!level.has(e.from) || !level.has(e.to)) continue;
      const v = level.get(e.from) + 1;
      if(v > level.get(e.to)){ level.set(e.to, v); changed = true; }
    }
    if(!changed) break;
  }

  let issues = structuralIssues;
  if(!state.lockedKey && !state.showMilestones && !state.includeWithRemarkable){
    issues = issues.filter(i => (i.status || '').trim() !== 'With Remarkable');
  }

  const issueKeys = new Set(issues.map(i => i.key));
  // Only draw relationships whose endpoints are actually displayed.
  const edges = structuralEdges.filter(e => issueKeys.has(e.from) && issueKeys.has(e.to));

  // Keep the structural level on each displayed card even when its blocker is
  // hidden by the With Remarkable filter.
  state.displayIssues = issues.map(i => ({...i, level: level.get(i.key) ?? 0}));
  state.displayEdges  = edges;
  state.displayLevels = state.displayIssues.length ? Math.max(...state.displayIssues.map(i => i.level)) : 0;
}

// ── Dependency-chain traversal (ancestors of key) ─────────────────────────
function blockedChain(key){
  const keep = new Set([key]), q = [key];
  while(q.length){
    const k = q.shift();
    for(const e of state.displayEdges){
      if(e.from === k && !keep.has(e.to)){ keep.add(e.to); q.push(e.to); }
    }
  }
  return keep;
}

function chain(key){
  const keep = new Set([key]), q = [key];
  while(q.length){
    const k = q.shift();
    for(const e of state.displayEdges){
      if(e.to === k && !keep.has(e.from)){ keep.add(e.from); q.push(e.from); }
    }
  }
  return keep;
}

// The selected view normally shows the selected card and everything blocking it.
// When "See blocked cards" is enabled, expand that same view downstream so it
// behaves like the highest-level dependency in the revealed chain has been selected.
function activeSelectionChain(key){
  const keep = chain(key);
  if(state.showBlocked){
    blockedChain(key).forEach(k => keep.add(k));
  }
  return keep;
}

// ── Hover chain: ancestors + descendants of a key ─────────────────────────
function computeHoverChain(key){
  const keep = new Set([key]);
  // ancestors (blockers that lead to this key)
  const qa = [key];
  while(qa.length){
    const k = qa.shift();
    for(const e of state.displayEdges){
      if(e.to === k && !keep.has(e.from)){ keep.add(e.from); qa.push(e.from); }
    }
  }
  // descendants (things this key blocks, transitively)
  const qd = [key];
  while(qd.length){
    const k = qd.shift();
    for(const e of state.displayEdges){
      if(e.from === k && !keep.has(e.to)){ keep.add(e.to); qd.push(e.to); }
    }
  }
  return keep;
}

function renderHoverHighlight(key){
  if(!key || !state.lockedKey) return;
  state.hoverKey = key;
  const hc = state.showBlocked
    ? new Set([...computeHoverChain(key), ...activeSelectionChain(state.lockedKey)])
    : computeHoverChain(key);
  board.querySelectorAll('.card').forEach(c => {
    c.classList.toggle('hover-dimmed', !hc.has(c.dataset.key));
  });
  lines.querySelectorAll('path[data-from][data-to]').forEach(p => {
    const inChain = hc.has(p.dataset.from) && hc.has(p.dataset.to);
    p.classList.toggle('hover-dimmed', !inChain);
  });
  scheduleMiniMapUpdate();
}

function applyHoverHighlight(key){
  if(!state.lockedKey) return;
  renderHoverHighlight(key);
}

function clearHoverHighlight(){
  if(state.hoverLockKey){
    renderHoverHighlight(state.hoverLockKey);
    return;
  }
  state.hoverKey = null;
  board.querySelectorAll('.card.hover-dimmed').forEach(c => c.classList.remove('hover-dimmed'));
  lines.querySelectorAll('.hover-dimmed').forEach(el => el.classList.remove('hover-dimmed'));
  scheduleMiniMapUpdate();
}

function lockHoverHighlight(key){
  if(!key || !state.lockedKey) return;
  state.hoverLockKey = key;
  renderHoverHighlight(key);
  updateHoverLockButtons();
}

function clearHoverLock(){
  state.hoverLockKey = null;
  state.hoverKey = null;
  board.querySelectorAll('.card.hover-dimmed').forEach(c => c.classList.remove('hover-dimmed'));
  lines.querySelectorAll('.hover-dimmed').forEach(el => el.classList.remove('hover-dimmed'));
  updateHoverLockButtons();
  scheduleMiniMapUpdate();
}

function updateHoverLockButtons(){
  board.querySelectorAll('.hover-lock-btn').forEach(btn => {
    const key = btn.dataset.key;
    const selected = !!state.lockedKey && key === state.lockedKey;
    const active = !!state.hoverLockKey && key === state.hoverLockKey;
    const card = btn.closest('.card');

    // Every rendered card belongs to the selected dependency chain, so expose
    // a lock control on each one while chain view is active.
    btn.hidden = !state.lockedKey;
    if(card){
      card.classList.toggle('selection-highlight', selected);
      card.classList.toggle('highlight-locked', active);
    }

    btn.classList.toggle('active', active);
    btn.textContent = active ? '🔒' : '🔓';
    btn.title = active ? 'Unlock highlight' : 'Lock highlight to this chain';
    btn.setAttribute('aria-label', btn.title);
  });
  scheduleMiniMapUpdate();
}

// ── Save button ───────────────────────────────────────────────────────────
function updateSaveButton(){
  const b = document.getElementById('save');
  const d = document.getElementById('discard');
  const count = document.getElementById('save-count');
  if(!b || !d) return;
  const n = state.pendingChanges.length;
  if(count) count.textContent = String(n);
  b.hidden = n === 0;
  d.hidden = n === 0;
  b.disabled = n === 0;
  b.title = 'Save ' + n + ' issue' + (n === 1 ? '' : 's');
  b.setAttribute('aria-label', b.title);
  b.classList.toggle('unsaved', n > 0);
}

function updateSaveProgress(done, total, label){
  const popup = document.getElementById('save-progress');
  const text = document.getElementById('save-progress-label');
  const percent = document.getElementById('save-progress-percent');
  const fill = document.getElementById('save-progress-fill');
  if(!popup || !text || !percent || !fill) return;
  const pct = total ? Math.round((done / total) * 100) : 0;
  text.textContent = label || ('Saving ' + done + ' of ' + total + '\u2026');
  percent.textContent = pct + '%';
  fill.style.width = pct + '%';
  popup.classList.add('show');
}

function hideSaveProgress(){
  const popup = document.getElementById('save-progress');
  if(popup) popup.classList.remove('show');
}

function cloneCleanSnapshot(){
  return JSON.parse(JSON.stringify({issues:state.issues, edges:state.edges}));
}

function discardChanges(){
  if(!state.pendingChanges.length || !state.cleanSnapshot) return;
  const n = state.pendingChanges.length;
  if(!confirm('Discard all ' + n + ' unsaved change' + (n === 1 ? '' : 's') + '?')) return;
  state.issues = JSON.parse(JSON.stringify(state.cleanSnapshot.issues || []));
  state.edges = JSON.parse(JSON.stringify(state.cleanSnapshot.edges || []));
  state.pendingChanges = [];
  state.history = [];
  state.redoHistory = [];
  recalcLocalLevels();
  render();
  updateSaveButton();
}

function cloneLocalSnapshot(){
  return JSON.parse(JSON.stringify({
    issues: state.issues,
    edges: state.edges,
    pendingChanges: state.pendingChanges
  }));
}
function restoreLocalSnapshot(snap){
  state.issues = JSON.parse(JSON.stringify(snap.issues || []));
  state.edges = JSON.parse(JSON.stringify(snap.edges || []));
  state.pendingChanges = JSON.parse(JSON.stringify(snap.pendingChanges || []));
  recalcLocalLevels();
}
function pushHistory(){
  if(state.historyApplying) return;
  state.history.push(cloneLocalSnapshot());
  if(state.history.length > 100) state.history.shift();
  state.redoHistory = [];
}
function undoLocal(){
  if(!state.history.length) return;
  state.redoHistory.push(cloneLocalSnapshot());
  restoreLocalSnapshot(state.history.pop());
  render(); updateSaveButton();
}
function redoLocal(){
  if(!state.redoHistory.length) return;
  state.history.push(cloneLocalSnapshot());
  restoreLocalSnapshot(state.redoHistory.pop());
  render(); updateSaveButton();
}

// ── Local level recalc after drag-add ─────────────────────────────────────
function recalcLocalLevels(){
  const level = new Map(state.issues.map(i => [i.key, i.externalBlockers && i.externalBlockers.length ? 1 : 0]));
  const n = state.issues.length;
  for(let pass = 0; pass < n; pass++){
    let changed = false;
    for(const e of state.edges){
      if(!level.has(e.from) || !level.has(e.to)) continue;
      const v = level.get(e.from) + 1;
      if(v > level.get(e.to)){ level.set(e.to, v); changed = true; }
    }
    if(!changed) break;
  }
  state.issues.forEach(i => { i.level = level.get(i.key) || 0; });
  state.levels = Math.max(0, ...state.issues.map(i => i.level || 0));
}

function addLocalDependency(source, target){
  if(state.edges.some(e => e.from === source && e.to === target)) return false;
  pushHistory();
  // Cycle check
  const seen = new Set([target]), q = [target];
  while(q.length){
    const k = q.shift();
    for(const e of state.edges){
      if(e.from === k && !seen.has(e.to)){
        if(e.to === source) throw new Error('That dependency would create a circular dependency.');
        seen.add(e.to); q.push(e.to);
      }
    }
  }
  state.edges.push({from:source, to:target});
  const a = state.issues.find(i => i.key === source);
  const b = state.issues.find(i => i.key === target);
  if(a && !a.blocked.includes(target)) a.blocked.push(target);
  if(b && !b.blockers.includes(source)) b.blockers.push(source);
  recalcLocalLevels();
  state.pendingChanges.push({source, target, action:'add'});
  updateSaveButton();
  return true;
}


function deleteLocalDependency(source, target){
  // source = blocker, target = blocked  (matches addLocalDependency convention)
  if(!state.edges.some(e => e.from === source && e.to === target)) return;
  pushHistory();
  state.edges = state.edges.filter(e => !(e.from === source && e.to === target));
  const a = state.issues.find(i => i.key === source);
  const b = state.issues.find(i => i.key === target);
  if(a) a.blocked  = (a.blocked  || []).filter(k => k !== target);
  if(b) b.blockers = (b.blockers || []).filter(k => k !== source);
  // If this edge was only a pending add (not yet in Jira), cancel it outright.
  const addIdx = state.pendingChanges.findIndex(
    c => c.action === 'add' && c.source === source && c.target === target);
  if(addIdx >= 0){
    state.pendingChanges.splice(addIdx, 1);
  } else {
    // Already saved in Jira — stage a delete; SAVE button will send it.
    state.pendingChanges.push({source, target, action:'delete'});
  }
  recalcLocalLevels();
  updateSaveButton();
}

function stageIssueChange(key, field, value){
  const issue = state.issues.find(i => i.key === key);
  if(!issue) return;
  const oldValue = field === 'assignee' ? (issue.assigneeAccountId || null) : field === 'priority' ? issue.priority : (issue.dueDate || null);
  if(oldValue === (value || null)) return;
  pushHistory();
  const display = state.displayIssues.find(i => i.key === key);
  if(field === 'assignee'){
    const opt = [...document.querySelectorAll('.assignee-select')].find(s => s.closest('.card, .dashboard-ticket')?.dataset.key === key);
    const name = opt && opt.selectedOptions[0] ? opt.selectedOptions[0].textContent : 'Unassigned';
    issue.assigneeAccountId = value || null;
    issue.assignee = name;
    if(display){ display.assigneeAccountId = value || null; display.assignee = name; }
  }else if(field === 'priority'){
    issue.priority = value;
    if(display) display.priority = value;
  }else if(field === 'dueDate'){
    issue.dueDate = value || null;
    if(display) display.dueDate = value || null;
  }
  const existing = state.pendingChanges.find(c => c.action === 'update' && c.key === key);
  const payload = field === 'assignee' ? {assigneeAccountId:value || null} : field === 'priority' ? {priority:value} : {dueDate:value || null};
  if(existing) Object.assign(existing,payload);
  else state.pendingChanges.push(Object.assign({action:'update',key}, payload));
  updateSaveButton();
}

function stageDueDateChanges(changes){
  const applicable=(changes||[]).filter(change=>{
    const issue=state.issues.find(i=>i.key===change.key);
    return issue && (issue.dueDate||null)!==(change.value||null);
  });
  if(!applicable.length) return false;
  pushHistory();
  applicable.forEach(change=>{
    const issue=state.issues.find(i=>i.key===change.key);
    const display=state.displayIssues.find(i=>i.key===change.key);
    issue.dueDate=change.value||null;
    if(display) display.dueDate=change.value||null;
    const existing=state.pendingChanges.find(c=>c.action==='update' && c.key===change.key);
    if(existing) existing.dueDate=change.value||null;
    else state.pendingChanges.push({action:'update',key:change.key,dueDate:change.value||null});
  });
  updateSaveButton();
  return true;
}

async function saveChanges(){
  if(!state.pendingChanges.length) return;
  const changes = [...state.pendingChanges];
  const total = changes.length;
  let done = 0;
  hideError();
  updateSaveProgress(0, total);
  const saveBtn = document.getElementById('save');
  const discardBtn = document.getElementById('discard');
  if(saveBtn) saveBtn.disabled = true;
  if(discardBtn) discardBtn.disabled = true;
  try{
    for(const change of changes){
      let r;
      if(change.action === 'update'){
        r = await fetch('/api/issues', {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify({changes:[change]})});
      }else if(change.action === 'add'){
        r = await fetch('/api/links', {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify({links:[change]})});
      }else if(change.action === 'delete'){
        r = await fetch('/api/unlink', {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify({source:change.source, target:change.target})});
      }else{
        throw new Error('Unknown change type: ' + change.action);
      }
      const d = await r.json().catch(() => ({}));
      if(!r.ok) throw new Error(d.error || 'HTTP ' + r.status);
      done++;
      updateSaveProgress(done, total);
    }
    state.pendingChanges = [];
    state.history = [];
    state.redoHistory = [];
    state.cleanSnapshot = cloneCleanSnapshot();
    updateSaveProgress(total, total, 'Done!');
    updateSaveButton();
    render();
    await new Promise(resolve => setTimeout(resolve, 650));
  }catch(e){
    // Keep only the changes which were not successfully sent.
    state.pendingChanges = changes.slice(done);
    updateSaveProgress(done, total, 'Saving stopped at ' + done + ' of ' + total);
    showError(e.message || String(e));
    updateSaveButton();
  }finally{
    if(saveBtn) saveBtn.disabled = false;
    if(discardBtn) discardBtn.disabled = false;
    if(done < total) setTimeout(hideSaveProgress, 2200);
    else hideSaveProgress();
  }
}

// ── Status badge colour ───────────────────────────────────────────────────
function isCompletedStatus(status){
  const value = String(status || '').toLowerCase().trim();
  return value === 'completed' || value === 'done';
}

function statusStyle(s){
  const l = (s || '').toLowerCase();
  if(l.includes('done') || l.includes('complete'))
    return 'background:#dcfce7;color:#166534;border:1px solid #bbf7d0';
  if(l.includes('progress') || l.includes('doing') || l.includes('active'))
    return 'background:#dbeafe;color:#1e40af;border:1px solid #bfdbfe';
  if(l.includes('review'))
    return 'background:#f3e8ff;color:#6b21a8;border:1px solid #e9d5ff';
  if(l.includes('block'))
    return 'background:#fee2e2;color:#991b1b;border:1px solid #fecaca';
  return 'background:#f8fafc;color:#475569;border:1px solid #e2e8f0';
}

// ── Priority helpers ───────────────────────────────────────────────────────
const PRIORITY_ORDER=['Blocker','Critical','Major','Minor','Trivial','Highest','High','Medium','Low','Lowest'];
function priorityRank(p){const i=PRIORITY_ORDER.indexOf(p);return i===-1?PRIORITY_ORDER.length:i}
function priorityIconHtml(pri){
  if(!pri||!CFG.jiraBaseUrl)return`<span style="font-size:.75em;color:#cbd5e1;flex-shrink:0">·</span>`;
  return`<img class="priority-icon" src="${CFG.jiraBaseUrl}/images/icons/priorities/${pri.toLowerCase()}.svg" alt="${esc(pri)}" title="${esc(pri)}" width="14" height="14" loading="lazy" data-pri-trigger="">`;
}

// ── Relations HTML ────────────────────────────────────────────────────────
function relationHtml(i){
  const visible = state.lockedKey ? activeSelectionChain(state.lockedKey) : null;
  const blockedBy = (i.blockers || []).filter(k => {
    if(!visible || visible.has(k)) return true;
    const dependency = state.issues.find(x => x.key === k);
    return dependency && isCompletedStatus(dependency.status);
  }).sort();
  const external = (i.externalBlockers || []).filter(x => !visible || i.key === state.lockedKey).sort((a,b) => a.key.localeCompare(b.key));
  const blocks = (i.blocked || []).slice().sort();

  function keyItem(k, direction, extraCls){
    const x = state.issues.find(v => v.key === k);
    const cls = (extraCls || 'relation-key') + (x && isCompletedStatus(x.status) ? ' completed' : '');
    const issueUrl = x ? x.url : (CFG.jiraBaseUrl + '/browse/' + encodeURIComponent(k));
    const tooltip = x ? ((x.summary || x.key) + ' - ' + (x.assignee || 'Unassigned') + ' (' + (x.priority || 'No priority') + ')') : k;
    const anchor = '<a class="' + cls + '" href="' + esc(issueUrl) +
      '" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="' +
      esc(k) + '" title="' + esc(tooltip) + '">' + esc(k) + '</a>';
    return '<span class="relation-box ' + direction + '">' +
      (direction === 'up'
        ? '<span class="relation-arrow">←</span>' + anchor
        : anchor + '<span class="relation-arrow">→</span>') +
      '</span>';
  }

  const up = blockedBy.map(k => keyItem(k, 'up'));
  const ext = external.map(x => keyItem(x.key, 'up', 'relation-key external-key'));
  const down = blocks.map(k => keyItem(k, 'down'));
  const relationBoxes = up.concat(ext, down).join('');

  const downstream = state.lockedKey === i.key ? blockedChain(i.key) : new Set();
  downstream.delete(i.key);
  const seeBlockedHtml = state.lockedKey === i.key && downstream.size
    ? '<button class="see-blocked-btn" type="button" data-stop-propagation="1">' +
      (state.showBlocked ? 'Hide blocked cards' : 'See blocked cards') + '</button>'
    : '';

  const editHtml = '<button class="edit-dependency-btn" type="button" data-edit-dependency="' +
    esc(i.key) + '" data-stop-propagation="1">Edit dependencies</button>';

  return (relationBoxes ? '<div class="relations">' + relationBoxes + '</div>' : '') +
    seeBlockedHtml + editHtml;
}

function formatDueDate(value){
  if(!value) return '';
  const parts=String(value).split('-').map(Number);
  if(parts.length!==3 || parts.some(Number.isNaN)) return String(value);
  const d=new Date(Date.UTC(parts[0],parts[1]-1,parts[2]));
  return new Intl.DateTimeFormat('en-GB',{day:'numeric',month:'short',year:'numeric',timeZone:'UTC'}).format(d);
}
function localDateKey(value){
  const d=value instanceof Date ? value : new Date(value);
  if(Number.isNaN(d.getTime())) return '';
  return d.getFullYear()+'-'+String(d.getMonth()+1).padStart(2,'0')+'-'+String(d.getDate()).padStart(2,'0');
}
function isDueDateOverdue(value){
  if(!value) return false;
  return String(value) < localDateKey(new Date());
}
function issueMatchesDueFilter(issue, filterValue){
  const filter=filterValue || 'all';
  if(filter==='all') return true;
  const due=String(issue.dueDate || '');
  if(filter==='noDueDate') return !due;
  if(!due) return false;
  const today=new Date();
  const todayKey=localDateKey(today);
  if(filter==='overdue') return !isCompletedStatus(issue.status) && due < todayKey;
  if(due < todayKey) return false;
  let end=new Date(today.getFullYear(),today.getMonth(),today.getDate());
  if(filter==='next7'){
    end.setDate(end.getDate()+7);
  }else if(filter==='nextMonth'){
    const targetMonth=today.getMonth()+1;
    const lastDay=new Date(today.getFullYear(),targetMonth+1,0).getDate();
    end=new Date(today.getFullYear(),targetMonth,Math.min(today.getDate(),lastDay));
  }else{
    return true;
  }
  return due <= localDateKey(end);
}
function dueDateHtml(i){
  const overdue=!isCompletedStatus(i.status) && isDueDateOverdue(i.dueDate);
  const label=i.dueDate ? formatDueDate(i.dueDate) : 'Set due date';
  return '<button type="button" class="due-date' + (overdue ? ' overdue' : (!i.dueDate ? ' due-date-empty' : '')) + '" data-due-date-key="' + esc(i.key) + '" data-stop-propagation="1" title="' + esc(i.dueDate ? 'Change due date' : 'Add due date') + '"><span class="due-date-icon">▣</span> ' + esc(i.dueDate ? 'Due ' + label : label) + '</button>';
}

function isValidDueDateValue(value){
  return /^\d{4}-\d{2}-\d{2}$/.test(String(value || ''));
}

function chainDateRiskPairs(keys=null, dateOverrides=null){
  const allowed=keys ? new Set(keys) : null;
  const byKey=new Map(state.issues.map(i=>[i.key,i]));
  const outgoing=new Map();
  state.issues.forEach(i=>outgoing.set(i.key,[]));
  (state.edges||[]).forEach(edge=>{
    if(!outgoing.has(edge.from)) outgoing.set(edge.from,[]);
    outgoing.get(edge.from).push(edge.to);
  });
  const effectiveDate=key=>{
    if(dateOverrides && Object.prototype.hasOwnProperty.call(dateOverrides,key)) return dateOverrides[key] || '';
    return byKey.get(key)?.dueDate || '';
  };
  const pairs=[];
  const seenPairs=new Set();
  for(const source of state.issues){
    if(allowed && !allowed.has(source.key)) continue;
    if(isCompletedStatus(source.status)) continue;
    const sourceDate=effectiveDate(source.key);
    if(!isValidDueDateValue(sourceDate)) continue;
    const queue=[source.key], seen=new Set([source.key]);
    while(queue.length){
      const current=queue.shift();
      for(const targetKey of (outgoing.get(current)||[])){
        if(seen.has(targetKey)) continue;
        seen.add(targetKey);
        queue.push(targetKey);
        if(allowed && !allowed.has(targetKey)) continue;
        const target=byKey.get(targetKey);
        if(!target || isCompletedStatus(target.status)) continue;
        const targetDate=effectiveDate(targetKey);
        if(!isValidDueDateValue(targetDate) || targetDate>=sourceDate) continue;
        const pairId=source.key+'>'+targetKey;
        if(seenPairs.has(pairId)) continue;
        seenPairs.add(pairId);
        pairs.push({source:source.key,target:targetKey,sourceDate,targetDate});
      }
    }
  }
  return pairs;
}

function highlightSelectedChainDateRisks(){
  board.querySelectorAll('.due-date.chain-date-risk').forEach(el=>el.classList.remove('chain-date-risk'));
  board.querySelectorAll('.card.chain-date-risk-card').forEach(el=>el.classList.remove('chain-date-risk-card'));
  if(!state.lockedKey) return;
  const visibleKeys=activeSelectionChain(state.lockedKey);
  const pairs=chainDateRiskPairs(visibleKeys);
  if(!pairs.length) return;
  const details=new Map();
  pairs.forEach(pair=>{
    if(!details.has(pair.source)) details.set(pair.source,[]);
    if(!details.has(pair.target)) details.set(pair.target,[]);
    details.get(pair.source).push(pair.target+' is due '+formatDueDate(pair.targetDate)+' before this '+formatDueDate(pair.sourceDate)+' date');
    details.get(pair.target).push('Due '+formatDueDate(pair.targetDate)+' before '+pair.source+' ('+formatDueDate(pair.sourceDate)+')');
  });
  details.forEach((messages,key)=>{
    const card=board.querySelector('.card[data-key="'+CSS.escape(key)+'"]');
    const due=card?.querySelector('.due-date');
    if(!card || !due) return;
    card.classList.add('chain-date-risk-card');
    due.classList.add('chain-date-risk');
    const unique=[...new Set(messages)];
    due.title='Chain date risk: '+unique.join('; ')+'. Click to change due date.';
    due.setAttribute('aria-label',(due.textContent||'Due date').trim()+'. Chain date risk. '+unique.join('; '));
  });
}

// ── Card HTML ─────────────────────────────────────────────────────────────
function cardHtml(i, searchTerm){
  const isExternal = i.externalBlockers && i.externalBlockers.length;
  const isMilestone = (i.labels || []).some(label => String(label).toLowerCase() === 'milestone');
  const assignees = [...new Map(state.issues.filter(x => x.assigneeAccountId).map(x => [x.assigneeAccountId || '', {name:x.assignee || 'Unassigned', accountId:x.assigneeAccountId || ''}])).values()]
    .sort((a,b) => a.name.localeCompare(b.name));
  const priorities = PRIORITY_ORDER.filter((p,idx,arr) => arr.indexOf(p)===idx);
  let epicHtml = '';
  if(i.epic){
    const rawLabel = i.epic.summary ? i.epic.key + ' · ' + (i.epic.summary.length > 32 ? i.epic.summary.substring(0, 32) + '…' : i.epic.summary) : i.epic.key;
    epicHtml = '<a class="epic-badge" href="' + esc(i.epic.url) + '" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="' + esc(i.epic.key) + '" title="' + esc(i.epic.summary || i.epic.key) + '"><span class="epic-dot">◆</span>' + esc(rawLabel) + '</a>';
  }
  const summaryHtml = esc(i.summary);
  const priorityOptions = priorities.map(p =>
    '<button type="button" class="priority-option' + (p === i.priority ? ' selected' : '') + '" data-priority="' + esc(p) + '" data-stop-propagation="1">'
    + priorityIconHtml(p) + '<span>' + esc(p) + '</span></button>'
  ).join('');
  const assigneeOptions = assignees.map(a => '<option value="' + esc(a.accountId) + '"' + (a.accountId === (i.assigneeAccountId || '') ? ' selected' : '') + '>' + esc(a.name) + '</option>').join('');
  const assigneeSelect = '<select class="assignee-select' + (!i.assigneeAccountId ? ' unassigned' : '') + '" data-field="assignee" data-stop-propagation="1" title="Change assignee"><option value="">Unassigned</option>' + assigneeOptions + '</select>';
  const prioritySelect = '<span class="priority-picker" data-stop-propagation="1" title="Change priority">'
    + '<button type="button" class="priority-trigger" data-stop-propagation="1" aria-label="Change priority" aria-haspopup="true" aria-expanded="false">' + priorityIconHtml(i.priority) + '</button>'
    + '<span class="priority-menu" role="menu">' + priorityOptions + '</span>'
    + '</span>';

  const searchIndex = buildSearchIndex(i);
  const isCompleted = isCompletedStatus(i.status);
  const isOverdue = !isCompleted && isDueDateOverdue(i.dueDate);
  return '<article class="card' + (i.cycle ? ' cycle' : '') + (isExternal ? ' external' : '') + (isCompleted ? ' completed' : '') + (isOverdue ? ' overdue-card' : '') + '" data-key="' + esc(i.key) + '" data-assignee-account-id="' + esc(i.assigneeAccountId || '') + '" data-due-date="' + esc(i.dueDate || '') + '" data-completed="' + (isCompleted ? '1' : '0') + '" data-search-index="' + esc(searchIndex) + '" data-summary="' + esc(i.summary || '') + '">'
    + (isMilestone ? '<div class="milestone-banner">MILESTONE</div>' : '')
    + '<div class="card-top">'
    +   '<div class="card-top-left">'
    +     '<button type="button" class="hover-lock-btn" data-key="' + esc(i.key) + '" data-stop-propagation="1" title="Lock highlight to this chain" aria-label="Lock highlight to this chain">🔓</button>'
    +     prioritySelect
    +     '<a class="key" href="' + esc(i.url) + '" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="' + esc(i.key) + '">' + esc(i.key) + '</a>'
    +   '</div>'
    +   (i.status ? '<span class="status-badge" style="' + statusStyle(i.status) + '">' + esc(i.status) + '</span>' : '')
    + '</div>'
    + epicHtml
    + '<div class="summary">' + summaryHtml + '</div>'
    + '<div class="card-meta">' + assigneeSelect + dueDateHtml(i) + '</div>'
    + relationHtml(i)
   
    + '</article>';
}

// ── Dashboard ─────────────────────────────────────────────────────────────
function dashboardRiskInfo(issues){
  const active=issues.filter(i => !isCompletedStatus(i.status));
  const overdue=active.filter(i=>isDueDateOverdue(i.dueDate));
  const unassigned=active.filter(i=>!i.assigneeAccountId);
  const noDueDate=active.filter(i=>!i.dueDate);

  // Flag a ticket when a downstream ticket is due before an upstream ticket.
  // Compare every reachable upstream/downstream pair, not just direct links.
  const byKey=new Map(active.map(i=>[i.key,i]));
  const downstream=new Map();
  active.forEach(i=>downstream.set(i.key,(i.blocked||[]).filter(k=>byKey.has(k))));
  const chainDateRiskKeys=new Set();
  const chainDateRiskDetails=new Map();
  active.forEach(source=>{
    const sourceDate=source.dueDate ? new Date(source.dueDate+'T00:00:00') : null;
    if(!sourceDate || Number.isNaN(sourceDate.getTime())) return;
    const queue=[source.key], seen=new Set([source.key]);
    while(queue.length){
      const key=queue.shift();
      for(const next of (downstream.get(key)||[])){
        if(seen.has(next)) continue;
        seen.add(next); queue.push(next);
        const target=byKey.get(next);
        const targetDate=target?.dueDate ? new Date(target.dueDate+'T00:00:00') : null;
        if(targetDate && !Number.isNaN(targetDate.getTime()) && targetDate < sourceDate){
          chainDateRiskKeys.add(target.key);
          if(!chainDateRiskDetails.has(target.key)) chainDateRiskDetails.set(target.key,[]);
          chainDateRiskDetails.get(target.key).push({earlier:source.key,date:source.dueDate});
        }
      }
    }
  });
  const chainDateRisks=active.filter(i=>chainDateRiskKeys.has(i.key));

  // Detect circular dependency chains using DFS. A ticket is counted once even
  // if it participates in more than one cycle. The health score uses the
  // proportion of active tickets affected by each problem area.
  const circularKeys=new Set();
  const visitState=new Map();
  const stack=[];
  function visit(key){
    const stateValue=visitState.get(key)||0;
    if(stateValue===1){
      const idx=stack.indexOf(key);
      if(idx>=0) stack.slice(idx).forEach(k=>circularKeys.add(k));
      circularKeys.add(key);
      return;
    }
    if(stateValue===2) return;
    visitState.set(key,1);
    stack.push(key);
    for(const next of (downstream.get(key)||[])) visit(next);
    stack.pop();
    visitState.set(key,2);
  }
  active.forEach(i=>visit(i.key));
  const circularDependencies=active.filter(i=>circularKeys.has(i.key));

  const totalActive=active.length;
  // Front-load urgent delivery risks so the first occurrence has an immediate,
  // visible impact, then increase the deduction on a square-root curve as more
  // tickets are affected. Other hygiene deductions remain proportional.
  function frontLoadedDeduction(count,total,maxPoints,firstHitPoints){
    if(!count || !total) return 0;
    if(total<=1 || count>=total) return maxPoints;
    const additionalShare=Math.sqrt((count-1)/(total-1));
    return Math.min(maxPoints,firstHitPoints+(maxPoints-firstHitPoints)*additionalShare);
  }
  const overdueDeduction=frontLoadedDeduction(overdue.length,totalActive,55,8);
  const unassignedDeduction=totalActive ? (unassigned.length/totalActive)*20 : 0;
  const noDueDateDeduction=totalActive ? (noDueDate.length/totalActive)*15 : 0;
  const circularDeduction=totalActive ? (circularDependencies.length/totalActive)*7 : 0;
  const chainDateDeduction=frontLoadedDeduction(chainDateRisks.length,totalActive,10,5);
  const boardHealthScore=totalActive ? Math.max(0,Math.min(100,100-overdueDeduction-unassignedDeduction-noDueDateDeduction-circularDeduction-chainDateDeduction)) : 100;
  const boardHealthStatus=boardHealthScore>=90 ? 'green' : boardHealthScore>=70 ? 'amber' : 'red';

  return {
    active,overdue,unassigned,noDueDate,chainDateRisks,chainDateRiskKeys,chainDateRiskDetails,
    circularDependencies,circularKeys,
    boardHealthScore,boardHealthStatus,
    boardHealthBreakdown:{
      overdue:{weight:55,count:overdue.length,deduction:overdueDeduction},
      unassigned:{weight:20,count:unassigned.length,deduction:unassignedDeduction},
      noDueDate:{weight:15,count:noDueDate.length,deduction:noDueDateDeduction},
      circular:{weight:7,count:circularDependencies.length,deduction:circularDeduction},
      chainDates:{weight:10,count:chainDateRisks.length,deduction:chainDateDeduction}
    }
  };
}
function dashboardAssigneeOptions(i){
  const assignees=[...new Map(state.issues.filter(x=>x.assigneeAccountId).map(x=>[x.assigneeAccountId,{name:x.assignee||'Unassigned',accountId:x.assigneeAccountId}])).values()]
    .sort((a,b)=>a.name.localeCompare(b.name));
  return '<select class="assignee-select dashboard-assignee-select' + (!i.assigneeAccountId?' unassigned':'') + '" data-field="assignee" data-stop-propagation="1" title="Change assignee"><option value="">Unassigned</option>'+
    assignees.map(a=>'<option value="'+esc(a.accountId)+'"'+(a.accountId===(i.assigneeAccountId||'')?' selected':'')+'>'+esc(a.name)+'</option>').join('')+
    '</select>';
}
function dashboardPriorityHtml(i){
  const options=PRIORITY_ORDER.filter((p,idx,arr)=>arr.indexOf(p)===idx).map(p=>
    '<button type="button" class="priority-option'+(p===i.priority?' selected':'')+'" data-priority="'+esc(p)+'" data-stop-propagation="1">'+priorityIconHtml(p)+'<span>'+esc(p)+'</span></button>'
  ).join('');
  return '<span class="priority-picker" data-stop-propagation="1" title="Change priority">'+
    '<button type="button" class="priority-trigger" data-stop-propagation="1" aria-label="Change priority" aria-haspopup="true" aria-expanded="false">'+priorityIconHtml(i.priority)+'</button>'+
    '<span class="priority-menu" role="menu">'+options+'</span></span>';
}
function dashboardTicketHtml(i, risks){
  const overdue=isDueDateOverdue(i.dueDate);
  const chainRisk=risks.chainDateRiskKeys?.has(i.key);
  const riskDetails=risks.chainDateRiskDetails?.get(i.key)||[];
  const chainTitle=chainRisk ? 'Due before an earlier ticket in its dependency chain: '+riskDetails.map(x=>x.earlier+' ('+formatDueDate(x.date)+')').join(', ') : '';
  const riskHtml='<div class="dashboard-risks">'+(overdue?'<span class="dashboard-risk overdue">Overdue</span>':'')+(chainRisk?'<span class="dashboard-risk chain-date-risk" title="'+esc(chainTitle)+'">Due-date chain risk</span>':'')+(!i.assigneeAccountId?'<span class="dashboard-risk unassigned">Unassigned</span>':'')+'</div>';
  return '<article class="dashboard-ticket'+(overdue?' overdue':'')+(chainRisk?' chain-date-risk':'')+'" data-dashboard-key="'+esc(i.key)+'" data-key="'+esc(i.key)+'">'+
    riskHtml+
    '<div class="dashboard-ticket-top"><div class="dashboard-ticket-key-wrap">'+dashboardPriorityHtml(i)+'<a class="dashboard-ticket-key" href="'+esc(i.url)+'" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="'+esc(i.key)+'">'+esc(i.key)+'</a></div></div>'+ 
    '<div class="dashboard-ticket-summary">'+esc(i.summary||'')+'</div>'+ 
    '<div class="dashboard-ticket-controls">'+dashboardAssigneeOptions(i)+dueDateHtml(i)+'</div>'+ 
  '</article>';
}
function dashboardSortItems(items){
  return [...items].sort((a,b)=>{
    const ap=PRIORITY_ORDER.indexOf(String(a.priority||''));
    const bp=PRIORITY_ORDER.indexOf(String(b.priority||''));
    const priorityA=ap<0?PRIORITY_ORDER.length:ap;
    const priorityB=bp<0?PRIORITY_ORDER.length:bp;
    if(priorityA!==priorityB) return priorityA-priorityB;
    const ad=a.dueDate?String(a.dueDate):'9999-12-31';
    const bd=b.dueDate?String(b.dueDate):'9999-12-31';
    if(ad!==bd) return ad.localeCompare(bd);
    return String(a.key||'').localeCompare(String(b.key||''));
  });
}
function dashboardSection(title,items,risks,options={}){
  const id=options.id?' id="'+esc(options.id)+'"':'';
  const note=options.note?'<span class="dashboard-section-note">'+esc(options.note)+'</span>':'';
  const sorted=dashboardSortItems(items);
  const visibleCount=Math.min(10,sorted.length);
  const returnSection=options.returnSection||options.id||'';
  const cards=sorted.map((i,index)=>'<div class="dashboard-ticket-wrap" data-dashboard-ticket-index="'+index+'" data-dashboard-return-section="'+esc(returnSection)+'"'+(index>=visibleCount?' hidden':'')+'>'+dashboardTicketHtml(i,risks)+'</div>').join('');
  const remaining=Math.max(0,sorted.length-visibleCount);
  const controls=remaining>0
    ? '<div class="dashboard-pagination"><button type="button" class="dashboard-show-more" data-dashboard-show-more>Show more (+'+Math.min(10,remaining)+')</button><button type="button" class="dashboard-show-all" data-dashboard-show-all>Show all ('+sorted.length+')</button></div>'
    : '';
  return '<section class="dashboard-section"'+id+'><div class="dashboard-section-head"><div class="dashboard-section-heading"><span class="dashboard-section-title">'+esc(title)+'</span>'+note+'</div><span class="dashboard-section-count">'+items.length+'</span></div>'+
    (items.length?'<div class="dashboard-grid">'+cards+'</div>'+controls:'<div class="dashboard-empty">None currently.</div>')+'</section>';
}
function dashboardSummarySection(title,html,id,note){
  return '<section class="dashboard-section dashboard-summary-section"'+(id?' id="'+esc(id)+'"':'')+'><div class="dashboard-section-head"><div class="dashboard-section-heading"><span class="dashboard-section-title">'+esc(title)+'</span>'+(note?'<span class="dashboard-section-note">'+esc(note)+'</span>':'')+'</div></div>'+html+'</section>';
}
function dashboardRiskBadge(label,cls,title){
  return '<span class="dashboard-risk '+(cls||'')+'"'+(title?' title="'+esc(title)+'"':'')+'>'+esc(label)+'</span>';
}
function dashboardDueSoon(issues,days=7){
  const today=new Date(); today.setHours(0,0,0,0);
  const end=new Date(today); end.setDate(end.getDate()+days);
  return issues.filter(i=>{
    if(isCompletedStatus(i.status)||!i.dueDate) return false;
    const d=new Date(i.dueDate+'T00:00:00');
    return !Number.isNaN(d.getTime()) && d>=today && d<=end;
  }).sort((a,b)=>String(a.dueDate).localeCompare(String(b.dueDate)));
}
function dashboardHighPriorityRisk(issues,risks){
  const high=new Set(['Highest','Critical']);
  return issues.filter(i=>{
    if(isCompletedStatus(i.status)||!high.has(String(i.priority||''))) return false;
    const dueSoon=dashboardDueSoon([i]).length>0;
    return risks.overdue.includes(i)||risks.chainDateRiskKeys.has(i.key)||dueSoon;
  });
}
function dashboardDependencyBottlenecks(issues){
  const active=issues.filter(i=>!isCompletedStatus(i.status));
  const byKey=new Map(active.map(i=>[i.key,i]));
  const downstream=new Map(active.map(i=>[i.key,(i.blocked||[]).filter(k=>byKey.has(k))]));
  const impact=new Map();
  active.forEach(i=>{
    const seen=new Set([i.key]); const queue=[i.key];
    while(queue.length){
      const key=queue.shift();
      for(const next of (downstream.get(key)||[])){
        if(seen.has(next)) continue;
        seen.add(next); queue.push(next);
      }
    }
    impact.set(i.key,Math.max(0,seen.size-1));
  });
  return active.filter(i=>(impact.get(i.key)||0)>0).sort((a,b)=>(impact.get(b.key)||0)-(impact.get(a.key)||0)).slice(0,10).map(i=>({issue:i,impact:impact.get(i.key)||0}));
}
function dashboardUnblocking(issues){
  return dashboardDependencyBottlenecks(issues).filter(x=>x.issue.assigneeAccountId || x.issue.dueDate || x.issue.priority);
}
function dashboardWorkload(issues){
  const active=issues.filter(i=>!isCompletedStatus(i.status));
  const groups=new Map();
  active.forEach(i=>{
    const key=i.assigneeAccountId||'__unassigned__';
    if(!groups.has(key)) groups.set(key,{name:i.assignee||'Unassigned',accountId:i.assigneeAccountId||'',count:0,overdue:0,highRisk:0});
    const g=groups.get(key); g.count++;
    if(isDueDateOverdue(i.dueDate)) g.overdue++;
    if(['Highest','Critical'].includes(String(i.priority||'')) && (isDueDateOverdue(i.dueDate)||!i.dueDate)) g.highRisk++;
  });
  return [...groups.values()].sort((a,b)=>b.count-a.count || a.name.localeCompare(b.name));
}
function dashboardMilestones(issues){
  const active=issues.filter(i=>!isCompletedStatus(i.status));
  const milestones=active.filter(i=>(i.labels||[]).some(l=>String(l).toLowerCase()==='milestone'));
  return milestones.map(m=>{
    const due=m.dueDate?new Date(m.dueDate+'T00:00:00'):null;
    const blocked=(m.blocked||[]).map(k=>issues.find(i=>i.key===k)).filter(Boolean).filter(i=>!isCompletedStatus(i.status)).length;
    const overdue=isDueDateOverdue(m.dueDate);
    return {issue:m,blocked,overdue,due:due&&!Number.isNaN(due.getTime())?due:null};
  }).sort((a,b)=>Number(b.overdue)-Number(a.overdue) || (a.due?.getTime()||Infinity)-(b.due?.getTime()||Infinity));
}
function dashboardPriorityDistribution(issues){
  const active=issues.filter(i=>!isCompletedStatus(i.status));
  const groups=new Map();
  active.forEach(i=>{const p=String(i.priority||'Unspecified'); groups.set(p,(groups.get(p)||0)+1);});
  return [...groups.entries()].sort((a,b)=>b[1]-a[1]);
}
function dashboardCompletedHtml(items){
  if(!items.length) return '<div class="dashboard-empty">No completed tickets are available in the current dataset.</div>';
  return '<div class="dashboard-compact-list">'+items.map(i=>'<a class="dashboard-compact-row" href="'+esc(i.url)+'" target="_blank" rel="noopener noreferrer"><span class="dashboard-compact-main"><strong>'+esc(i.key)+'</strong><span>'+esc(i.summary||'')+'</span></span><span class="dashboard-impact">Completed</span></a>').join('')+'</div>';
}
function dashboardPriorityRiskHtml(items){
  if(!items.length) return '<div class="dashboard-empty">None currently.</div>';
  return '<div class="dashboard-compact-list">'+items.map(i=>'<button type="button" class="dashboard-compact-row" data-dashboard-key="'+esc(i.key)+'"><span class="dashboard-compact-main">'+priorityIconHtml(i.priority)+'<strong>'+esc(i.key)+'</strong><span>'+esc(i.summary||'')+'</span></span><span class="dashboard-compact-badges">'+(isDueDateOverdue(i.dueDate)?dashboardRiskBadge('Overdue','overdue'):'')+(dashboardDueSoon([i]).length?dashboardRiskBadge('Due soon','soon'):'')+(dashboardRiskBadge('High priority','high'))+'</span></button>').join('')+'</div>';
}
function dashboardBottleneckHtml(items){
  if(!items.length) return '<div class="dashboard-empty">No active ticket is currently blocking other active work.</div>';
  return '<div class="dashboard-compact-list">'+items.map(x=>'<button type="button" class="dashboard-compact-row" data-dashboard-unblocking="'+esc(x.issue.key)+'"><span class="dashboard-compact-main"><strong>'+esc(x.issue.key)+'</strong><span>'+esc(x.issue.summary||'')+'</span></span><span class="dashboard-impact">'+x.impact+' downstream '+(x.impact===1?'ticket':'tickets')+'</span></button>').join('')+'</div>';
}
function dashboardWorkloadHtml(items){
  if(!items.length) return '<div class="dashboard-empty">No active tickets.</div>';
  const max=Math.max(1,...items.map(x=>x.count));
  return '<div class="dashboard-workload-list">'+items.map(x=>'<button type="button" class="dashboard-workload-row" data-dashboard-assignee="'+esc(x.accountId)+'"><span class="dashboard-workload-name"><strong>'+esc(x.name)+'</strong>'+(x.overdue?'<span>'+x.overdue+' overdue</span>':'')+'</span><span class="dashboard-workload-bar"><span style="width:'+Math.max(4,Math.round(x.count/max*100))+'%"></span></span><strong class="dashboard-workload-count">'+x.count+'</strong></button>').join('')+'</div>';
}
function dashboardMilestoneHtml(items){
  if(!items.length) return '<div class="dashboard-empty">No active milestones found.</div>';
  return '<div class="dashboard-compact-list">'+items.map(x=>'<button type="button" class="dashboard-compact-row" data-dashboard-milestone="'+esc(x.issue.key)+'"><span class="dashboard-compact-main"><strong>'+esc(x.issue.key)+'</strong><span>'+esc(x.issue.summary||'')+'</span></span><span class="dashboard-compact-badges">'+(x.overdue?dashboardRiskBadge('Overdue','overdue'):'')+(x.blocked?dashboardRiskBadge(x.blocked+' blocked','high'):'')+(x.issue.dueDate?dashboardRiskBadge(formatDueDate(x.issue.dueDate),'soon'):'')+'</span></button>').join('')+'</div>';
}
function dashboardOverviewHtml(){
  const risks=dashboardRiskInfo(state.displayIssues||[]);
  const h=risks.boardHealthBreakdown;
  const score=Math.round(risks.boardHealthScore);
  const statusLabel=risks.boardHealthStatus==='green'?'Healthy':risks.boardHealthStatus==='amber'?'Needs attention':'At risk';
  const dueSoon=dashboardDueSoon(risks.active,7);
  const dueMonth=dashboardDueSoon(risks.active,31);
  const highPriorityRisk=dashboardHighPriorityRisk(risks.active,risks);
  const bottlenecks=dashboardDependencyBottlenecks(risks.active);
  const workload=dashboardWorkload(risks.active);
  const topWorkload=workload.filter(x=>x.accountId).slice(0,6);
  const milestones=dashboardMilestones(risks.active);
  const blockedTickets=risks.active.filter(i=>(i.blockers||[]).length);
  const priorityDistribution=dashboardPriorityDistribution(risks.active);
  const completed=(state.issues||[]).filter(i=>isCompletedStatus(i.status)).sort((a,b)=>String(b.updated||'').localeCompare(String(a.updated||''))).slice(0,8);
  const attentionItems=[
    ['high-priority-risk','High-priority risk',highPriorityRisk.length],
    ['overdue','Overdue tickets',risks.overdue.length],
    ['chain-risks','Dependency chain date risks',risks.chainDateRisks.length],
    ['unassigned','Unassigned tickets',risks.unassigned.length],
    ['missing-due','Missing due dates',risks.noDueDate.length],
    ['circular','Circular dependencies',risks.circularDependencies.length],
    ['blocked-tickets','Blocked tickets',blockedTickets.length]
  ];
  const attentionTotal=attentionItems.reduce((sum,x)=>sum+x[2],0);
  const attentionHtml=attentionItems.map(x=>'<button type="button" class="dashboard-attention-item" data-dashboard-nav="'+x[0]+'"><span>'+esc(x[1])+'</span><strong>'+x[2]+'</strong></button>').join('');
  const topWorkloadHtml=topWorkload.length
    ? topWorkload.map((x,idx)=>'<div class="dashboard-top-workload-row"><strong>'+((idx+1)+'. ') + esc(x.name)+'</strong><span class="dashboard-top-workload-count">'+x.count+'</span></div>').join('')
    : '<div class="dashboard-empty">No assigned active tickets.</div>';
  const hRows=[
    {label:'Overdue tickets',detail:risks.overdue.length+' affected · max '+h.overdue.weight+' pts',deduction:h.overdue.deduction},
    {label:'Unassigned tickets',detail:risks.unassigned.length+' affected · max '+h.unassigned.weight+' pts',deduction:h.unassigned.deduction},
    {label:'Missing due dates',detail:risks.noDueDate.length+' affected · max '+h.noDueDate.weight+' pts',deduction:h.noDueDate.deduction},
    {label:'Circular dependencies',detail:risks.circularDependencies.length+' affected · max '+h.circular.weight+' pts',deduction:h.circular.deduction},
    {label:'Chain date risks',detail:risks.chainDateRisks.length+' affected · max '+h.chainDates.weight+' pts',deduction:h.chainDates.deduction}
  ];
  const healthDetail=hRows.map(row=>'<div class="dashboard-health-row"><span class="dashboard-health-row-label">'+esc(row.label)+'</span><span class="dashboard-health-row-detail">'+esc(row.detail)+'</span><strong>'+(row.deduction>0?'−'+row.deduction.toFixed(1)+' pts':'0 pts')+'</strong></div>').join('');
  const nav=[['overview','Overview'],['milestones','Milestones'],['unblocking','Unblocking opportunities'],['upcoming','Upcoming'],['workload','Workload'],['priority-distribution','Priority distribution'],['attention','Needs attention']];
  return '<div class="dashboard"><div class="dashboard-head"><div><div class="dashboard-title">Dependency dashboard</div><div class="dashboard-subtitle">What is at risk, what is causing it, and what should be acted on first.</div></div><div class="dashboard-updated">'+risks.active.length.toLocaleString('en-GB')+' active tickets</div></div>'+ 
    '<nav class="dashboard-nav" aria-label="Dashboard sections">'+nav.map(x=>'<button type="button" data-dashboard-nav="'+x[0]+'">'+x[1]+'</button>').join('')+'</nav>'+ 
    '<section class="dashboard-section dashboard-overview" id="overview"><div class="dashboard-section-head"><div class="dashboard-section-heading"><span class="dashboard-section-title">Overview</span><span class="dashboard-section-note">Board health and immediate signals</span></div></div>'+ 
      '<div class="dashboard-stats">'+
        '<div class="dashboard-stat dashboard-summary-link dashboard-health-stat '+risks.boardHealthStatus+'" data-dashboard-nav="attention" role="button" tabindex="0"><div class="dashboard-health-score-line"><div class="dashboard-stat-value">'+score+'%</div><span class="dashboard-health-status">'+statusLabel+'</span></div><div class="dashboard-stat-label">Board health</div><div class="dashboard-stat-help">Health combines overdue, unassigned, missing due dates, circular dependencies and chain-date risks.</div><div class="dashboard-health-breakdown">'+healthDetail+'</div></div>'+ 
        '<div class="dashboard-stat dashboard-summary-link dashboard-attention-stat risk"><div class="dashboard-stat-value">'+attentionTotal+'</div><div class="dashboard-stat-label">Needs attention</div><div class="dashboard-stat-help">Each risk area links directly to its section below.</div><div class="dashboard-attention-summary">'+attentionHtml+'</div></div>'+ 
        '<div class="dashboard-upcoming-stack">'+
          '<div class="dashboard-stat dashboard-summary-link" data-dashboard-nav="upcoming" data-dashboard-upcoming-tab="7"><div class="dashboard-stat-value">'+dueSoon.length+'</div><div class="dashboard-stat-label">Due next 7 days</div><div class="dashboard-stat-help">Upcoming active work that needs attention soon.</div></div>'+ 
          '<div class="dashboard-stat dashboard-summary-link" data-dashboard-nav="upcoming" data-dashboard-upcoming-tab="month"><div class="dashboard-stat-value">'+dueMonth.length+'</div><div class="dashboard-stat-label">Due next month</div><div class="dashboard-stat-help">Active work due within the next 31 days.</div></div>'+ 
        '</div>'+ 
        '<div class="dashboard-stat dashboard-summary-link" data-dashboard-nav="workload"><div class="dashboard-stat-value">'+topWorkload.length+' assignees</div><div class="dashboard-stat-label">Top workload</div><div class="dashboard-stat-help">Highest workload assignees by active ticket count.</div><div class="dashboard-top-workload">'+topWorkloadHtml+'</div></div>'+ 
      '</div></section>'+ 
    '<div class="dashboard-two-column dashboard-top-cards">'+
      '<div class="dashboard-section-group" id="milestones"><div class="dashboard-group-head"><h2>Milestones</h2><span>Milestone health and delivery pressure</span></div>'+ 
        dashboardSummarySection('Milestone risk',dashboardMilestoneHtml(milestones),'milestone-risk','Active milestones with due dates, overdue status or blocked work')+
        dashboardSummarySection('Recently completed',dashboardCompletedHtml(completed),'recently-completed','Most recently updated completed tickets in the current dataset')+
      '</div>'+ 
      '<div class="dashboard-section-group" id="unblocking"><div class="dashboard-group-head"><h2>Unblocking opportunities</h2><span>Focus on work with the greatest downstream impact</span></div>'+ 
        dashboardSummarySection('Biggest dependency bottlenecks',dashboardBottleneckHtml(bottlenecks),'bottlenecks','Top active tickets by number of downstream active tickets affected')+
      '</div>'+ 
    '</div>'+ 
    '<div class="dashboard-section-group" id="upcoming"><div class="dashboard-group-head"><h2>Upcoming</h2><span>What needs attention next</span></div>'+ 
      '<div class="dashboard-upcoming-tabs" role="tablist" aria-label="Upcoming timeframe">'+
        '<button type="button" class="dashboard-upcoming-tab active" data-dashboard-upcoming-tab-button="7" role="tab" aria-selected="true">7 days</button>'+ 
        '<button type="button" class="dashboard-upcoming-tab" data-dashboard-upcoming-tab-button="month" role="tab" aria-selected="false">Month</button>'+ 
      '</div>'+ 
      '<div class="dashboard-upcoming-panel" data-upcoming-panel="7">'+dashboardSection('Due in the next 7 days',dueSoon,risks,{id:'due-soon',note:'Includes today through the next seven days'})+'</div>'+ 
      '<div class="dashboard-upcoming-panel" data-upcoming-panel="month" hidden>'+dashboardSection('Due in the next 31 days',dueMonth,risks,{id:'due-month',note:'Includes today through the next 31 days'})+'</div>'+ 
    '</div>'+ 
    '<div class="dashboard-two-column dashboard-bottom-cards">'+
      '<div class="dashboard-section-group" id="workload"><div class="dashboard-group-head"><h2>Workload</h2><span>Active tickets by assignee</span></div>'+ 
        dashboardSummarySection('Workload by assignee',dashboardWorkloadHtml(workload),'workload-by-assignee','Select a person to filter the main board')+
      '</div>'+ 
      '<div class="dashboard-section-group" id="priority-distribution"><div class="dashboard-group-head"><h2>Priority distribution</h2><span>Active tickets by Jira priority</span></div>'+ 
        dashboardSummarySection('Priority distribution','<div class="dashboard-compact-list">'+priorityDistribution.map(x=>'<div class="dashboard-compact-row" style="cursor:default"><span class="dashboard-compact-main"><strong>'+esc(x[0])+'</strong></span><span class="dashboard-impact">'+x[1]+'</span></div>').join('')+'</div>','priority-distribution-content','Active tickets by Jira priority')+
      '</div>'+ 
    '</div>'+ 
    '<div class="dashboard-section-group" id="attention"><div class="dashboard-group-head"><h2>Needs attention</h2><span>Risks that should be reviewed first</span></div>'+ 
      dashboardSection('High-priority risk',highPriorityRisk,risks,{id:'high-priority-risk',returnSection:'high-priority-risk',note:'Highest and Critical work that is overdue, due soon or has a chain-date risk'})+
      dashboardSection('Overdue tickets',risks.overdue,risks,{id:'overdue',returnSection:'overdue',note:'Past their due date'})+
      dashboardSection('Dependency chain date risks',risks.chainDateRisks,risks,{id:'chain-risks',returnSection:'chain-risks',note:'A downstream ticket is due before an earlier ticket in its chain'})+
      dashboardSection('Unassigned tickets',risks.unassigned,risks,{id:'unassigned',returnSection:'unassigned',note:'Active work with no assignee'})+
      dashboardSection('Missing due dates',risks.noDueDate,risks,{id:'missing-due',returnSection:'missing-due',note:'Active work without a due date'})+
      dashboardSection('Circular dependencies',risks.circularDependencies,risks,{id:'circular',returnSection:'circular',note:'Dependency loops that need resolving'})+
      dashboardSection('Blocked tickets',blockedTickets,risks,{id:'blocked-tickets',returnSection:'blocked-tickets',note:'Active tickets waiting on one or more blockers'})+
    '</div>'+ 
  '</div>';
}
function renderDashboard(){
  board.insertAdjacentHTML('beforeend', dashboardOverviewHtml());
  attachTicketKeyModalHandlers(board);
  attachEvents();

  function setUpcomingTab(tab){
    const value=tab==='month'?'month':'7';
    board.querySelectorAll('[data-dashboard-upcoming-tab-button]').forEach(btn=>{
      const active=btn.dataset.dashboardUpcomingTabButton===value;
      btn.classList.toggle('active',active);
      btn.setAttribute('aria-selected',active?'true':'false');
    });
    board.querySelectorAll('[data-upcoming-panel]').forEach(panel=>{
      panel.hidden=panel.dataset.upcomingPanel!==value;
    });
  }
  board.querySelectorAll('[data-dashboard-upcoming-tab-button]').forEach(btn=>{
    btn.addEventListener('click',()=>setUpcomingTab(btn.dataset.dashboardUpcomingTabButton));
  });
  board.querySelectorAll('[data-dashboard-nav]').forEach(btn=>{
    btn.addEventListener('click',()=>{
      if(btn.dataset.dashboardUpcomingTab) setUpcomingTab(btn.dataset.dashboardUpcomingTab);
      const target=document.getElementById(btn.dataset.dashboardNav);
      if(target) target.scrollIntoView({behavior:'smooth',block:'start'});
    });
  });
  board.querySelectorAll('[data-dashboard-show-more]').forEach(btn=>{
    btn.addEventListener('click',()=>{
      const section=btn.closest('.dashboard-section');
      if(!section) return;
      const hidden=[...section.querySelectorAll('[data-dashboard-ticket-index][hidden]')].slice(0,10);
      hidden.forEach(el=>el.hidden=false);
      updateDashboardPagination(section);
    });
  });
  board.querySelectorAll('[data-dashboard-show-all]').forEach(btn=>{
    btn.addEventListener('click',()=>{
      const section=btn.closest('.dashboard-section');
      if(!section) return;
      section.querySelectorAll('[data-dashboard-ticket-index][hidden]').forEach(el=>el.hidden=false);
      updateDashboardPagination(section);
    });
  });
  board.querySelectorAll('[data-dashboard-assignee]').forEach(btn=>{
    btn.addEventListener('click',e=>{
      e.stopPropagation();
      const accountId=btn.dataset.dashboardAssignee||'';
      state.filterUser=accountId;
      persistPreference('filterUser',state.filterUser);
      state.showDashboard=false;
      render();
    });
  });
  board.querySelectorAll('[data-dashboard-milestone]').forEach(el=>{
    el.addEventListener('click',e=>{
      if(e.target.closest('[data-stop-propagation]')) return;
      const key=el.dataset.dashboardMilestone;
      if(!key) return;
      state.showDashboard=false;
      state.showMilestones=true;
      state.lockedKey=null;
      state.selectionHistory=[];
      state.showBlocked=false;
      state.returnMilestoneKey=null;
      state.dashboardReturnSection=null;
      state.milestoneFlashKey=key;
      render();
    });
  });
  board.querySelectorAll('[data-dashboard-unblocking]').forEach(el=>{
    el.addEventListener('click',e=>{
      if(e.target.closest('[data-stop-propagation]')) return;
      const key=el.dataset.dashboardUnblocking;
      if(!key) return;
      state.showDashboard=false;
      state.showMilestones=false;
      state.lockedKey=key;
      state.selectionHistory=[];
      state.showBlocked=false;
      state.returnMilestoneKey=null;
      state.dashboardReturnSection='unblocking';
      render();
    });
  });
  board.querySelectorAll('[data-dashboard-key]').forEach(el=>{
    el.addEventListener('click',e=>{
      if(e.target.closest('[data-stop-propagation]')) return;
      const key=el.dataset.dashboardKey;
      if(!key) return;
      const wrap=el.closest('[data-dashboard-return-section]');
      state.showDashboard=false; state.showMilestones=false; state.lockedKey=key; state.selectionHistory=[]; state.showBlocked=false; state.dashboardReturnSection=wrap?.dataset.dashboardReturnSection||null; state.revealSelectedKey=key; render();
    });
  });
}
function updateDashboardPagination(section){
  if(!section) return;
  const items=section.querySelectorAll('[data-dashboard-ticket-index]');
  const hidden=section.querySelectorAll('[data-dashboard-ticket-index][hidden]');
  const more=section.querySelector('[data-dashboard-show-more]');
  const all=section.querySelector('[data-dashboard-show-all]');
  const remaining=hidden.length;
  if(more){ more.textContent='Show more (+'+Math.min(10,remaining)+')'; more.hidden=remaining===0; }
  if(all){ all.textContent='Show all ('+items.length+')'; all.hidden=remaining===0; }
}

// ── Milestone overview ───────────────────────────────────────────────────
function milestoneChainItems(milestoneKey){
  const byKey = new Map(state.displayIssues.map(i => [i.key, i]));
  const keep = new Set([milestoneKey]);
  const queue = [milestoneKey];

  // Walk backwards through every dependency so the overview includes the
  // complete chain, not just the milestone's direct blockers.
  while(queue.length){
    const key = queue.shift();
    for(const e of state.displayEdges){
      if(e.to === key && !keep.has(e.from)){
        keep.add(e.from);
        queue.push(e.from);
      }
    }
  }

  keep.delete(milestoneKey);
  const items = [...keep].map(k => byKey.get(k)).filter(Boolean);
  const chainKeys = new Set(items.map(i => i.key));

  // Recalculate levels relative to this milestone's dependency chain:
  // unblocked roots are level 0, their dependants are level 1, etc.
  const level = new Map();
  const incoming = new Map(items.map(i => [i.key, 0]));
  for(const e of state.displayEdges){
    if(chainKeys.has(e.from) && chainKeys.has(e.to)) incoming.set(e.to, (incoming.get(e.to) || 0) + 1);
  }
  const q = items.filter(i => (incoming.get(i.key) || 0) === 0).map(i => i.key);
  q.forEach(k => level.set(k, 0));
  while(q.length){
    const key = q.shift();
    for(const e of state.displayEdges){
      if(e.from !== key || !chainKeys.has(e.to)) continue;
      const nextLevel = (level.get(key) || 0) + 1;
      level.set(e.to, Math.max(level.get(e.to) ?? 0, nextLevel));
      incoming.set(e.to, incoming.get(e.to) - 1);
      if(incoming.get(e.to) === 0) q.push(e.to);
    }
  }

  // Cycles are unusual, but keep any remaining nodes visible rather than
  // dropping them. Give them the next sensible level after their neighbours.
  items.forEach(i => {
    if(!level.has(i.key)) level.set(i.key, i.level || 0);
  });

  return items.map(i => ({...i, chainLevel:level.get(i.key) || 0}))
    .sort((a,b) => (a.chainLevel - b.chainLevel) || a.key.localeCompare(b.key));
}

function closeTicketPreviewModal(){
  const backdrop = document.getElementById('ticket-preview-backdrop');
  if(backdrop) backdrop.remove();
  const modal = document.getElementById('ticket-preview-modal');
  if(modal) modal.remove();
}

function refreshJiraData(){
  load(false);
}

function refreshTicketPreview(){
  const iframe = document.querySelector('#ticket-preview-modal iframe');
  if(!iframe) return;
  const current = iframe.src;
  iframe.src = 'about:blank';
  requestAnimationFrame(() => { iframe.src = current; });
}

function openTicketPreviewModal(key, url, summary){
  closeTicketPreviewModal();

  const backdrop=document.createElement('div');
  backdrop.id='ticket-preview-backdrop';
  backdrop.className='ticket-preview-backdrop';
  backdrop.addEventListener('click', closeTicketPreviewModal);

  const modal=document.createElement('div');
  modal.id='ticket-preview-modal';
  modal.className='ticket-preview-modal';
  modal.setAttribute('role','dialog');
  modal.setAttribute('aria-modal','true');
  modal.setAttribute('aria-label',key+' Jira preview');
  modal.addEventListener('click', e => e.stopPropagation());

  const header=document.createElement('div');
  header.className='ticket-preview-header';

  const title=document.createElement('div');
  title.className='ticket-preview-title';
  title.textContent=key+(summary ? ' · '+summary : '');

  const actions=document.createElement('div');
  actions.className='ticket-preview-actions';

  const refresh=document.createElement('button');
  refresh.type='button';
  refresh.className='ticket-preview-open';
  refresh.textContent='Close & refresh';
  refresh.title='Close this preview and refresh Jira data';
  refresh.addEventListener('click', () => {
    closeTicketPreviewModal();
    refreshJiraData();
  });

  const open=document.createElement('a');
  open.className='ticket-preview-open';
  open.href=url;
  open.target='_blank';
  open.rel='noopener noreferrer';
  open.textContent='Open in Jira';

  const close=document.createElement('button');
  close.type='button';
  close.className='ticket-preview-close';
  close.setAttribute('aria-label','Close');
  close.textContent='Close';
  close.addEventListener('click',closeTicketPreviewModal);

  actions.appendChild(refresh);
  actions.appendChild(open);
  actions.appendChild(close);
  header.appendChild(title);
  header.appendChild(actions);

  const iframe=document.createElement('iframe');
  iframe.src=url;
  iframe.title=key+' Jira issue';

  modal.appendChild(header);
  modal.appendChild(iframe);
  document.body.appendChild(backdrop);
  document.body.appendChild(modal);
  close.focus();
}

function milestoneCardHtml(i){
  const isExternal = i.externalBlockers && i.externalBlockers.length;
  const isMilestone = (i.labels || []).some(label => String(label).toLowerCase() === 'milestone');
  let epicHtml = '';
  if(i.epic){
    const rawLabel = i.epic.summary ? i.epic.key + ' · ' + (i.epic.summary.length > 32 ? i.epic.summary.substring(0, 32) + '…' : i.epic.summary) : i.epic.key;
    epicHtml = '<a class="epic-badge" href="' + esc(i.epic.url) + '" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="' + esc(i.epic.key) + '" title="' + esc(i.epic.summary || i.epic.key) + '"><span class="epic-dot">◆</span>' + esc(rawLabel) + '</a>';
  }
  const isCompleted = isCompletedStatus(i.status);
      return '<article class="card' + (i.cycle ? ' cycle' : '') + (isExternal ? ' external' : '') + (isCompleted ? ' completed' : '') + '" data-key="' + esc(i.key) + '">' +
    (isMilestone ? '<div class="milestone-banner">MILESTONE</div>' : '') +
    '<div class="card-top">' +
      '<div class="card-top-left">' +
        '<span class="priority-picker" title="Priority">' + priorityIconHtml(i.priority) + '</span>' +
        '<a class="key" href="' + esc(i.url) + '" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="' + esc(i.key) + '">' + esc(i.key) + '</a>' +
      '</div>' +
      (i.status ? '<span class="status-badge" style="' + statusStyle(i.status) + '">' + esc(i.status) + '</span>' : '') +
    '</div>' + epicHtml +
    '<div class="summary">' + esc(i.summary) + '</div>' +
    '<div class="card-meta">' + dueDateHtml(i) + '</div>' +
  '</article>';
}

function milestoneOverviewHtml(milestones){
  function assigneeInitials(name){
    const clean = String(name || '').trim();
    if(!clean || clean.toLowerCase() === 'unassigned') return '';
    const parts = clean.split(/\s+/).filter(Boolean);
    if(parts.length === 1) return parts[0].slice(0,2).toUpperCase();
    return (parts[0][0] + parts[parts.length - 1][0]).toUpperCase();
  }

  function blockerItems(i){
    const blockers = milestoneChainItems(i.key);
    const count = blockers.length;
    const groups = new Map();
    blockers.forEach(b => {
      if(!groups.has(b.chainLevel)) groups.set(b.chainLevel, []);
      groups.get(b.chainLevel).push(b);
    });
    const levels = [...groups.keys()].sort((a,b) => a-b);
    const list = count
      ? levels.map(level => {
          const label = level === 0 ? 'Unblocked' : 'Level ' + level;
          return '<div class="milestone-blocked-group">' +
            '<div class="milestone-blocked-level">' + label + '</div>' +
            groups.get(level).sort((a,b) => {
              const pa = priorityRank(a.priority);
              const pb = priorityRank(b.priority);
              return pa === pb ? a.key.localeCompare(b.key) : pa - pb;
            }).map(b =>
              '<div class="milestone-blocked-item' + (isCompletedStatus(b.status) ? ' completed' : '') +
                '" data-milestone-chain="' + esc(b.key) + '" title="' + esc(b.key + ' - ' + (b.summary || '')) + '">' +
                '<span class="milestone-blocked-content">' +
                  '<span class="milestone-blocked-priority">' + priorityIconHtml(b.priority) + '</span>' +
                  '<a class="milestone-blocked-key" href="' + esc(b.url || (CFG.jiraBaseUrl + '/browse/' + b.key)) +
                  '" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="' +
                  esc(b.key) + '">' + esc(b.key) + '</a>' +
                  ' - ' + esc(b.summary || '') +
                '</span>' +
                (assigneeInitials(b.assignee) ? '<span class="milestone-blocked-assignee" title="Assigned to ' + esc(b.assignee) + '">' + esc(assigneeInitials(b.assignee)) + '</span>' : '<span class="milestone-blocked-assignee unassigned" title="Unassigned">U</span>') +
              '</div>'
            ).join('') +
          '</div>';
        }).join('')
      : '<div class="milestone-blocked-empty">No blockers</div>';
    return '<div class="milestone-blocked">' +
      '<div class="milestone-blocked-head">' +
        '<span class="milestone-blocked-title">Blocked by</span>' +
        '<span class="milestone-blocked-count">' + count + '</span>' +
      '</div>' +
      '<div class="milestone-blocked-list">' + list + '</div>' +
    '</div>';
  }

  return '<div class="milestone-overview">' +
    '<div class="milestone-overview-header">' +
      '<span class="milestone-overview-title">Milestones</span>' +
      '<span class="milestone-overview-count">' + milestones.length + '</span>' +
    '</div>' +
    '<div class="milestone-row">' +
      (milestones.length
        ? milestones.map(i => '<div class="milestone-item">' +
            '<div class="milestone-overview-card" data-milestone-card="' + esc(i.key) + '" data-milestone-chain="' + esc(i.key) + '">' + milestoneCardHtml(i) + '</div>' +
            blockerItems(i) +
          '</div>').join('')
        : '<div class="empty">No milestone tickets</div>') +
    '</div>' +
  '</div>';
}

function renderMilestoneOverview(flashKey){
  const milestones = state.displayIssues
    .filter(i => (i.labels || []).some(label => String(label).toLowerCase() === 'milestone'))
    .sort((a,b) => a.key.localeCompare(b.key));

  const existing = board.querySelector('.milestone-overview');
  if(existing) existing.remove();
  const wrapper = document.createElement('div');
  wrapper.innerHTML = milestoneOverviewHtml(milestones);
  board.appendChild(wrapper.firstElementChild);

  // Milestone elements are rendered separately from the normal board event
  // wiring, so attach the controls they contain here as well.
  attachTicketKeyModalHandlers(board);

  // The milestone overview has its own renderer, so the normal attachEvents()
  // due-date handler does not run for these buttons. Wire them explicitly.
  board.querySelectorAll('[data-due-date-key]').forEach(btn => {
    btn.addEventListener('click', e => {
      e.preventDefault();
      e.stopPropagation();
      openDueDateModal(btn.dataset.dueDateKey);
    });
  });

  board.querySelectorAll('[data-milestone-chain]').forEach(el => {
    el.addEventListener('click', e => {
      if(e.target.closest('[data-stop-propagation]')) return;
      e.preventDefault();
      e.stopPropagation();
      const key = el.dataset.milestoneChain;
      if(!key) return;
      const isBlockerItem = !!el.closest('.milestone-blocked-item');
      const parentMilestone = el.closest('.milestone-item');
      const parentMilestoneKey = parentMilestone ? (parentMilestone.querySelector('[data-milestone-card]')?.dataset.milestoneCard || null) : null;
      // Clicking either a milestone card/banner or one of its chain items
      // opens the normal dependency map with that issue at the end of the chain.
      state.returnMilestoneKey = isBlockerItem ? parentMilestoneKey : null;
      state.selectionHistory = [{key:null, filters:filterSnapshot()}];
      state.searchTerm = '';
      state.filterUser = '';
      state.includeWithRemarkable = true;
      searchEl.value = '';
      updateSearchClearButton();
      saveFilterPreferences();
      state.showMilestones = false;
      state.lockedKey = key;
      state.showBlocked = false;
      state.milestoneFlashKey = null;
      render();
      requestAnimationFrame(() => {
        requestAnimationFrame(() => {
          const card = board.querySelector('.card[data-key="' + CSS.escape(key) + '"]');
          if(!card) return;
          card.scrollIntoView({behavior:'smooth',block:'center',inline:'center'});
          card.classList.remove('dependency-flash');
          void card.offsetWidth;
          card.classList.add('dependency-flash');
          setTimeout(() => card.classList.remove('dependency-flash'), 950);
        });
      });
    });
  });

  statusText.textContent = milestones.length.toLocaleString('en-GB') + ' milestone' + (milestones.length === 1 ? '' : 's');
  const app = document.getElementById('app');
  requestAnimationFrame(() => {
    const savedMilestoneScroll = state.scrollPositions.milestone || {};
    app.scrollLeft = savedMilestoneScroll.appLeft || 0;
    app.scrollTop = savedMilestoneScroll.appTop || 0;
    if(flashKey){
      const target = board.querySelector('.milestone-overview-card[data-milestone-card="' + CSS.escape(flashKey) + '"]');
      if(target){
        target.scrollIntoView({behavior:'smooth',block:'center',inline:'center'});
        target.classList.remove('milestone-flash');
        void target.offsetWidth;
        target.classList.add('milestone-flash');
        setTimeout(() => target.classList.remove('milestone-flash'), 950);
      }
    }
  });
}

// ── Render ────────────────────────────────────────────────────────────────
function render(){
  // Capture the scroll position belonging to the view currently on screen.
  // This must happen before state.showMilestones/lockedKey changes are applied
  // and before the existing columns are removed.
  captureBoardScroll();

  const externalStatus = document.getElementById('external-status');
  const cycleStatus = document.getElementById('cycle-status');
  const hasExternal = (state.issues || []).some(i => (i.externalBlockers || []).length);
  const hasCycle = (state.issues || []).some(i => i.cycle);
  if(externalStatus) externalStatus.style.display = hasExternal ? 'inline-flex' : 'none';
  if(cycleStatus) cycleStatus.style.display = hasCycle ? 'inline-flex' : 'none';
  const lockedStatus = document.getElementById('locked-status');
  if(lockedStatus) lockedStatus.style.display = state.lockedKey ? 'inline-flex' : 'none';
  // A rebuild replaces the cards and SVG paths, so any previous hover state is stale.
  state.hoverKey = null;

  // Keep the search field stable while the board is rebuilt. This is important
  // because search results are rendered on every input event.
  const searchValue = searchEl ? searchEl.value : state.searchTerm;
  const searchWasFocused = document.activeElement === searchEl;
  const searchSelectionStart = searchEl ? searchEl.selectionStart : null;
  const searchSelectionEnd = searchEl ? searchEl.selectionEnd : null;

  document.querySelectorAll('.priority-picker.open').forEach(closePriorityPicker);
  // Remove the previous SVG dimensions first: otherwise its old width can be
  // included in the next board measurement and preserve stale horizontal space.
  resetDependencyLineCanvas();
  [...board.querySelectorAll('.column, .milestone-overview, .dashboard, .no-active-user, .no-results')].forEach(x => x.remove());
  if(state.completedDownloadStatus === 'ready' || !state.showCompleted) hideCompletedDownloadNotice();
  board.classList.toggle('milestone-board', state.showMilestones);
  board.classList.toggle('dashboard-board', state.showDashboard);
  document.getElementById('app').classList.toggle('milestone-mode', state.showMilestones);
  document.getElementById('app').classList.toggle('dashboard-mode', state.showDashboard);
  dependencyStatus.classList.toggle('view-hidden', state.showDashboard || state.showMilestones);
  // Rebuild display data honoring the completed toggle
  computeDisplayData();
  console.debug('Dependency graph render', {issues:state.displayIssues.length, edges:state.displayEdges.length, selected:state.lockedKey});

  // Sync filter controls
  populateFilterUsers();
  updateFilterControls();
  document.querySelectorAll('.view-switch').forEach(btn => btn.classList.toggle('active', btn.dataset.view === (state.showDashboard ? 'dashboard' : state.showMilestones ? 'milestone' : 'default')));

  if(state.showDashboard){
    state.lockedKey = null;
    state.selectionHistory = [];
    state.showBlocked = false;
    syncSharedViewUrl();
    document.getElementById('app').classList.remove('locked');
    searchWrap.style.visibility = 'hidden';
    if(filterMenu) filterMenu.classList.remove('open');
    if(filtersBtn) filtersBtn.style.visibility = 'hidden';
    if(clearFiltersBtn) clearFiltersBtn.style.visibility = 'hidden';
    deselectBtn.classList.remove('visible');
    if(milestoneBackBtn){ milestoneBackBtn.classList.remove('visible'); milestoneBackBtn.innerHTML=''; }
    renderDashboard();
    statusText.textContent = 'Dashboard';
    return;
  }

  // Milestone overview is a separate horizontal board mode. It clears selection
  // and intentionally does not render the normal dependency columns.
  if(state.showMilestones){
    // Milestone view must never retain the minimap from the previous chain
    // view. Hide it immediately rather than waiting for a queued RAF update.
    hideMiniMap();
    state.lockedKey = null;
    state.selectionHistory = [];
    state.showBlocked = false;
    syncSharedViewUrl();
    document.getElementById('app').classList.remove('locked');
    searchWrap.style.visibility = 'hidden';
    if(filterMenu) filterMenu.classList.remove('open');
    if(filtersBtn) filtersBtn.style.visibility = 'hidden';
    if(clearFiltersBtn) clearFiltersBtn.style.visibility = 'hidden';
    deselectBtn.classList.remove('visible');
    if(milestoneBackBtn) milestoneBackBtn.classList.remove('visible');
    const flashKey = state.milestoneFlashKey || null;
    state.milestoneFlashKey = null;
    renderMilestoneOverview(flashKey);
    return;
  }

  // If the locked key is no longer visible (e.g. toggle just hid it), clear selection
  if(state.lockedKey && !state.displayIssues.find(i => i.key === state.lockedKey)){
    state.lockedKey = null;
    state.selectionHistory = [];
    state.showBlocked = false;
  }
  syncSharedViewUrl();

  const locked = !!state.lockedKey;
  document.getElementById('app').classList.toggle('locked', locked);
  const searchTerm = locked ? '' : getSearch();

  // Header controls
  searchWrap.style.visibility = locked ? 'hidden' : 'visible';
  if(filtersBtn) filtersBtn.style.visibility = locked ? 'hidden' : 'visible';
  if(clearFiltersBtn) clearFiltersBtn.style.visibility = locked ? 'hidden' : 'visible';
  deselectBtn.classList.toggle('visible', locked);
  if(milestoneBackBtn){
    const backMilestone = state.returnMilestoneKey ? state.displayIssues.find(i => i.key === state.returnMilestoneKey) : null;
    const dashboardBackLabels = {
      'unblocking':'Unblocking opportunities',
      'high-priority-risk':'High-priority risk',
      'overdue':'Overdue tickets',
      'chain-risks':'Dependency chain date risks',
      'unassigned':'Unassigned tickets',
      'missing-due':'Missing due dates',
      'circular':'Circular dependencies',
      'blocked-tickets':'Blocked tickets'
    };
    const dashboardBack = !!state.dashboardReturnSection && !!dashboardBackLabels[state.dashboardReturnSection];
    milestoneBackBtn.classList.toggle('visible', !!backMilestone || dashboardBack);
    milestoneBackBtn.innerHTML = dashboardBack
      ? '&#8592; Back to ' + esc(dashboardBackLabels[state.dashboardReturnSection])
      : (backMilestone ? '&#8592; Back to ' + esc(backMilestone.key + ' - ' + (backMilestone.summary || 'Milestone')) : '');
  }

  // Search is applied after the cards are rendered. In selected mode the
  // dependency chain is still structurally filtered as before.
  let visibleKeys = locked ? activeSelectionChain(state.lockedKey) : null;
  let visibleIssues = visibleKeys
    ? state.displayIssues.filter(i => visibleKeys.has(i.key))
    : state.displayIssues;

  // Column map
  const cols = new Map();
  visibleIssues.forEach(i => { if(!cols.has(i.level)) cols.set(i.level, []); cols.get(i.level).push(i); });
  const max = visibleIssues.length ? Math.max(...visibleIssues.map(i => i.level || 0)) : 0;
  const labels = ['Unblocked', ...Array.from({length:max}, (_,n) => 'Level ' + (n+1))];
  const orders = [];
  for(let lv = 0; lv <= max; lv++) orders[lv] = [...(cols.get(lv) || [])].sort((a,b) => a.key.localeCompare(b.key));

  // Barycenter sort passes (use display edges & display issues)
  function neighbours(item, lv){
    const keys = new Set();
    (item.blockers || []).forEach(k => keys.add(k));
    state.displayEdges.forEach(e => { if(e.to === item.key) keys.add(e.from); if(e.from === item.key) keys.add(e.to); });
    return [...keys].map(k => state.displayIssues.find(x => x.key === k)).filter(Boolean)
      .filter(x => Math.abs((x.level || 0) - lv) === 1 && (!visibleKeys || visibleKeys.has(x.key)));
  }
  for(let pass = 0; pass < 8; pass++){
    for(let lv = 0; lv <= max; lv++){
      const pos = new Map();
      for(let l = 0; l <= max; l++) orders[l].forEach((x,i) => pos.set(x.key, {level:l, index:i}));
      orders[lv].sort((a,b) => {
        function score(item){ const ns = neighbours(item, lv); if(!ns.length) return 999999; return ns.reduce((s,n) => s + pos.get(n.key).index, 0) / ns.length; }
        const sa = score(a), sb = score(b);
        return sa === sb ? a.key.localeCompare(b.key) : sa - sb;
      });
    }
  }
  if(!locked){
    // On the default board, each level follows the exact same priority order
    // exposed by the priority menu. Priority is the primary order, with the
    // Jira key used only as a stable tie-breaker for tickets with the same priority.
    for(let lv = 0; lv <= max; lv++){
      orders[lv].sort((a,b) => {
        const pa = priorityRank(a.priority);
        const pb = priorityRank(b.priority);
        return pa === pb ? a.key.localeCompare(b.key) : pa - pb;
      });
    }
  }

  if(locked){
    // Order the revealed chain around the selected card. Upstream blockers remain
    // on the blocking side; when downstream cards are revealed they continue away
    // from the selected card instead of being treated as unrelated tickets.
    const distance = new Map([[state.lockedKey, 0]]), q = [state.lockedKey];
    while(q.length){
      const k = q.shift();
      for(const e of state.displayEdges){
        if(e.to === k && !distance.has(e.from)){
          distance.set(e.from, (distance.get(k) || 0) + 1); q.push(e.from);
        }
      }
    }
    if(state.showBlocked){
      const dq = [state.lockedKey], dSeen = new Set([state.lockedKey]);
      while(dq.length){
        const k = dq.shift();
        for(const e of state.displayEdges){
          if(e.from === k && !dSeen.has(e.to)){
            dSeen.add(e.to);
            if(!distance.has(e.to)) distance.set(e.to, -(distance.get(k) || 0) - 1);
            dq.push(e.to);
          }
        }
      }
    }
    for(let lv = 0; lv <= max; lv++) orders[lv].sort((a,b) => {
      const da = distance.has(a.key) ? distance.get(a.key) : -999999;
      const db = distance.has(b.key) ? distance.get(b.key) : -999999;
      return da !== db ? db - da : a.key.localeCompare(b.key);
    });
  }

  // Build columns
  for(let lv = 0; lv <= max; lv++){
    const col = document.createElement('section');
    col.className = 'column' + (locked ? ' unlocked' : '');
    col.dataset.level = String(lv);
    const items = orders[lv];
    const cardsDiv = document.createElement('div');
    cardsDiv.className = 'cards' + (locked ? ' noscroll' : '');
    cardsDiv.innerHTML = items.length
      ? items.map(i => cardHtml(i, searchTerm)).join('')
      : '<div class="empty">No tickets at this level</div>';

    const header = document.createElement('div');
    header.className = 'column-header';
    header.innerHTML = '<span class="column-title">' + (labels[lv] || 'Level ' + lv) + '</span>'
                     + '<span class="column-count">' + items.length + '</span>';
    col.appendChild(header);
    col.appendChild(cardsDiv);
    board.appendChild(col);
  }

  // The dashboard changes the board display model and can leave the first
  // post-transition layout pass with stale card geometry. Redraw after the
  // layout has settled at several points so returning Dashboard -> Chain
  // cannot permanently leave the SVG paths missing.
  requestAnimationFrame(() => {
    spaceLongRoutes();
    requestAnimationFrame(() => {
      drawLines();
      attachEvents();
      requestAnimationFrame(() => {
        drawLines();
        requestAnimationFrame(drawLines);
      });
      setTimeout(drawLines, 60);
      setTimeout(drawLines, 180);
      scheduleMiniMapUpdate();
    });
  });

  // Restore search focus/caret after a genuine board rebuild (refresh, toggle,
  // selection change, etc.). Typing itself no longer rebuilds the board.
  if(searchEl && searchEl.value !== searchValue) searchEl.value = searchValue;
  updateSearchClearButton();
  if(searchWasFocused){
    searchEl.focus({preventScroll:true});
    if(searchSelectionStart != null && searchSelectionEnd != null){
      try{ searchEl.setSelectionRange(searchSelectionStart, searchSelectionEnd); }catch(_){}
    }
  }

  // Restore the saved position after the new columns exist.
  preserveBoardScrollDuringRender();

  if(locked){
    statusText.textContent = visibleIssues.length.toLocaleString('en-GB') + ' tickets in chain · Esc to deselect';
  } else {
    applySearchFilter();
  }

}

// ── Board mini-map ────────────────────────────────────────────────────────
let minimapFrame = 0;
let minimapScrollFrame = 0;
let minimapDrag = null;
let minimapMetrics = null;

function scheduleMiniMapUpdate(){
  if(minimapFrame) return;
  minimapFrame = requestAnimationFrame(() => {
    minimapFrame = 0;
    updateMiniMap();
  });
}

// Scrolling only changes the minimap viewport rectangle. Rebuilding every
// minimap card/column during a scroll frame is unnecessarily expensive.
function scheduleMiniMapScrollUpdate(){
  if(minimapScrollFrame) return;
  minimapScrollFrame = requestAnimationFrame(() => {
    minimapScrollFrame = 0;
    updateMiniMapViewport();
  });
}

function hideMiniMap(){
  minimapMetrics = null;
  if(boardMinimap) boardMinimap.classList.remove('visible');
}

function updateMiniMapViewport(){
  if(!boardMinimap || !boardMinimapViewport || !minimapMetrics) return;
  const app = document.getElementById('app');
  if(!app || !boardMinimap.classList.contains('visible')) return;

  const {boardWidth, boardHeight, scale, offsetX, offsetY} = minimapMetrics;
  const maxLeft = Math.max(0, boardWidth - app.clientWidth);
  const maxTop = Math.max(0, boardHeight - app.clientHeight);
  const viewW = Math.min(app.clientWidth, boardWidth);
  const viewH = Math.min(app.clientHeight, boardHeight);

  boardMinimapViewport.style.width = Math.max(viewW * scale, 8) + 'px';
  boardMinimapViewport.style.height = Math.max(viewH * scale, 8) + 'px';
  boardMinimapViewport.style.left =
    (offsetX + Math.min(app.scrollLeft, maxLeft) * scale) + 'px';
  boardMinimapViewport.style.top =
    (offsetY + Math.min(app.scrollTop, maxTop) * scale) + 'px';
}

function updateMiniMap(){
  if(!boardMinimap || !boardMinimapStage || !boardMinimapContent || !boardMinimapViewport) return;

  // The overview is a dependency-chain aid only. Never show it on the
  // normal home board or in milestone view.
  if(state.showMiniMap === false || !state.lockedKey || state.showMilestones ||
     board.classList.contains('milestone-board')){
    hideMiniMap();
    return;
  }

  const app = document.getElementById('app');
  if(!app) return;

  const boardWidth = Math.max(board.scrollWidth, board.clientWidth);
  const boardHeight = Math.max(board.scrollHeight, board.clientHeight);
  const canScroll = boardWidth > app.clientWidth + 2 || boardHeight > app.clientHeight + 2;

  if(!canScroll){
    hideMiniMap();
    return;
  }

  boardMinimap.classList.add('visible');

  const stageW = boardMinimapStage.clientWidth;
  const stageH = boardMinimapStage.clientHeight;
  if(!stageW || !stageH || !boardWidth || !boardHeight) return;

  const scale = Math.min(stageW / boardWidth, stageH / boardHeight);
  const mapW = boardWidth * scale;
  const mapH = boardHeight * scale;
  const offsetX = (stageW - mapW) / 2;
  const offsetY = (stageH - mapH) / 2;

  minimapMetrics = {boardWidth, boardHeight, scale, offsetX, offsetY};

  boardMinimapContent.style.width = boardWidth + 'px';
  boardMinimapContent.style.height = boardHeight + 'px';
  boardMinimapContent.style.transform =
    'translate(' + offsetX + 'px,' + offsetY + 'px) scale(' + scale + ')';

  boardMinimapContent.innerHTML = '';

  // Show columns as light blocks so the overall dependency-map structure is
  // visible even where individual cards are tightly packed.
  board.querySelectorAll('.column').forEach(column => {
    const el = document.createElement('div');
    el.className = 'minimap-column';

    const x = column.offsetLeft;
    const y = column.offsetTop;
    // Keep the column backdrop slightly inset so it never visually
    // overlaps the ticket rectangles on the minimap.
    const inset = 2;
    const colW = Math.max(column.offsetWidth, 1);
    const header = column.querySelector('.column-header');
    const colH = Math.max(header ? header.offsetHeight : 20, 1);
    el.style.left = (x + inset) + 'px';
    el.style.top = (y + inset) + 'px';
    el.style.width = Math.max(colW - inset * 2, 1) + 'px';
    el.style.height = Math.max(colH - inset * 2, 1) + 'px';
    el.style.zIndex = '0';
    boardMinimapContent.appendChild(el);
  });

  // Card offsetTop/offsetLeft describe their position in the full cards
  // content, even when the .cards element itself is vertically scrolled.
  board.querySelectorAll('.column .card').forEach(card => {
    const cards = card.closest('.cards');
    const column = card.closest('.column');
    if(!cards || !column) return;

    const el = document.createElement('div');
    el.className = 'minimap-card';
    const key = card.dataset.key;
    const issue = state.displayIssues.find(i => i.key === key) || state.issues.find(i => i.key === key);
    const isMilestone = !!issue && (issue.labels || []).some(label => String(label).toLowerCase() === 'milestone');
    const isOverdue = !!issue && isDueDateOverdue(issue.dueDate);
    if(isMilestone) el.classList.add('milestone');
    if(isOverdue) el.classList.add('overdue');
    if(state.lockedKey && key === state.lockedKey) el.classList.add('selected');
    if(state.hoverLockKey && key === state.hoverLockKey) el.classList.add('highlight-locked');
    if(card.classList.contains('hover-dimmed')) el.classList.add('dimmed');

    el.style.left = (column.offsetLeft + cards.offsetLeft + card.offsetLeft) + 'px';
    el.style.top = (column.offsetTop + cards.offsetTop + card.offsetTop) + 'px';
    el.style.width = Math.max(card.offsetWidth, 8) + 'px';
    el.style.height = Math.max(card.offsetHeight, 5) + 'px';
    el.style.zIndex = '1';
    boardMinimapContent.appendChild(el);
  });

  // The outline is the portion of the board currently visible through #app.
  // App scroll and nested .cards scroll are deliberately represented as the
  // outer board viewport only; the card map itself still shows the full
  // contents of each column.
  const maxLeft = Math.max(0, boardWidth - app.clientWidth);
  const maxTop = Math.max(0, boardHeight - app.clientHeight);
  const viewW = Math.min(app.clientWidth, boardWidth);
  const viewH = Math.min(app.clientHeight, boardHeight);

  boardMinimapViewport.style.width = Math.max(viewW * scale, 8) + 'px';
  boardMinimapViewport.style.height = Math.max(viewH * scale, 8) + 'px';
  boardMinimapViewport.style.left =
    (offsetX + Math.min(app.scrollLeft, maxLeft) * scale) + 'px';
  boardMinimapViewport.style.top =
    (offsetY + Math.min(app.scrollTop, maxTop) * scale) + 'px';
}

function miniMapScrollTo(clientX, clientY){
  const app = document.getElementById('app');
  if(!app || !boardMinimapStage) return;

  const stageRect = boardMinimapStage.getBoundingClientRect();
  const boardWidth = Math.max(board.scrollWidth, board.clientWidth);
  const boardHeight = Math.max(board.scrollHeight, board.clientHeight);
  const stageW = boardMinimapStage.clientWidth;
  const stageH = boardMinimapStage.clientHeight;
  const scale = Math.min(stageW / boardWidth, stageH / boardHeight);
  const offsetX = (stageW - boardWidth * scale) / 2;
  const offsetY = (stageH - boardHeight * scale) / 2;

  const boardX = (clientX - stageRect.left - offsetX) / scale;
  const boardY = (clientY - stageRect.top - offsetY) / scale;

  const maxLeft = Math.max(0, boardWidth - app.clientWidth);
  const maxTop = Math.max(0, boardHeight - app.clientHeight);

  app.scrollLeft = Math.max(0, Math.min(maxLeft, boardX - app.clientWidth / 2));
  app.scrollTop = Math.max(0, Math.min(maxTop, boardY - app.clientHeight / 2));
  scheduleMiniMapUpdate();
}

function miniMapPointerDown(e){
  if(!boardMinimap.classList.contains('visible')) return;
  e.preventDefault();

  const target = e.target;
  if(target === boardMinimapViewport || boardMinimapViewport.contains(target)){
    minimapDrag = {
      pointerId:e.pointerId,
      startX:e.clientX,
      startY:e.clientY,
      startLeft:document.getElementById('app').scrollLeft,
      startTop:document.getElementById('app').scrollTop
    };
    boardMinimapViewport.classList.add('dragging');
    boardMinimapViewport.setPointerCapture?.(e.pointerId);
  }else{
    miniMapScrollTo(e.clientX, e.clientY);
  }
}

function miniMapPointerMove(e){
  if(!minimapDrag || e.pointerId !== minimapDrag.pointerId) return;
  const app = document.getElementById('app');
  if(!app) return;

  const boardWidth = Math.max(board.scrollWidth, board.clientWidth);
  const boardHeight = Math.max(board.scrollHeight, board.clientHeight);
  const stageW = boardMinimapStage.clientWidth;
  const stageH = boardMinimapStage.clientHeight;
  const scale = Math.min(stageW / boardWidth, stageH / boardHeight);

  const maxLeft = Math.max(0, boardWidth - app.clientWidth);
  const maxTop = Math.max(0, boardHeight - app.clientHeight);

  app.scrollLeft = Math.max(0, Math.min(maxLeft,
    minimapDrag.startLeft + (e.clientX - minimapDrag.startX) / scale));
  app.scrollTop = Math.max(0, Math.min(maxTop,
    minimapDrag.startTop + (e.clientY - minimapDrag.startY) / scale));
  scheduleMiniMapUpdate();
}

function miniMapPointerUp(e){
  if(!minimapDrag || e.pointerId !== minimapDrag.pointerId) return;
  boardMinimapViewport.classList.remove('dragging');
  minimapDrag = null;
}

boardMinimap?.addEventListener('pointerdown', miniMapPointerDown);
boardMinimap?.addEventListener('pointermove', miniMapPointerMove);
boardMinimap?.addEventListener('pointerup', miniMapPointerUp);
boardMinimap?.addEventListener('pointercancel', miniMapPointerUp);
document.getElementById('app')?.addEventListener('scroll', scheduleMiniMapScrollUpdate, {passive:true});
board?.addEventListener('scroll', scheduleMiniMapScrollUpdate, true);
window.addEventListener('resize', scheduleMiniMapUpdate);

// ── Geometry ──────────────────────────────────────────────────────────────
function spaceLongRoutes(){
  if(!state.lockedKey) return;
  const visible = activeSelectionChain(state.lockedKey), colEls = [...document.querySelectorAll('.column')];
  const colOf = el => { const c = el.closest('.column'); return c ? colEls.indexOf(c) : -1; };
  const br = board.getBoundingClientRect(), headerFloor = 42 + 10 + 18;
  for(const e of state.displayEdges.filter(e => visible.has(e.from) && visible.has(e.to))){
    const a = document.querySelector('.card[data-key="' + CSS.escape(e.from) + '"]');
    const b = document.querySelector('.card[data-key="' + CSS.escape(e.to)   + '"]');
    if(!a || !b) continue;
    const ca = colOf(a), cb = colOf(b); if(cb - ca <= 1) continue;
    const ra = a.getBoundingClientRect(), rb = b.getBoundingClientRect();
    const y = Math.max(headerFloor, Math.min(ra.top + 30, rb.top + 30) - br.top);
    for(let ci = ca + 1; ci < cb; ci++){
      for(const card of colEls[ci].querySelectorAll('.card')){
        const r = card.getBoundingClientRect(), top = r.top - br.top, bot = r.bottom - br.top;
        if(top <= y && bot >= y){ card.style.marginTop = Math.ceil(y - top + 18) + 'px'; break; }
      }
    }
  }
}

function resetDependencyLineCanvas(){
  // An absolutely-positioned SVG can still contribute to the scrollable
  // overflow area. Reset it before measuring a newly selected chain so an old,
  // wider line canvas cannot leave blank space to the right.
  lines.replaceChildren();
  lines.removeAttribute('width');
  lines.removeAttribute('height');
  lines.removeAttribute('viewBox');
  lines.style.left = '0px';
  lines.style.top = '0px';
  lines.style.right = 'auto';
  lines.style.bottom = 'auto';
  lines.style.width = '0px';
  lines.style.height = '0px';
}

function dependencyCanvasSize(){
  const br = board.getBoundingClientRect();
  const boardStyle = getComputedStyle(board);
  const padRight = parseFloat(boardStyle.paddingRight) || 0;
  const padBottom = parseFloat(boardStyle.paddingBottom) || 0;
  const content = [...board.querySelectorAll(':scope > .column')];
  let right = br.left + board.clientWidth;
  let bottom = br.top + board.clientHeight;
  for(const element of content){
    const rect = element.getBoundingClientRect();
    right = Math.max(right, rect.right + padRight);
    bottom = Math.max(bottom, rect.bottom + padBottom);
  }
  return {
    width: Math.max(board.clientWidth, Math.ceil(right - br.left)),
    height: Math.max(board.clientHeight, Math.ceil(bottom - br.top)),
  };
}

function clampBoardScroll(){
  const app = document.getElementById('app');
  if(!app) return;
  const maxLeft = Math.max(0, app.scrollWidth - app.clientWidth);
  const maxTop = Math.max(0, app.scrollHeight - app.clientHeight);
  if(app.scrollLeft > maxLeft) app.scrollLeft = maxLeft;
  if(app.scrollTop > maxTop) app.scrollTop = maxTop;
}

function drawLines(){
  resetDependencyLineCanvas();
  if(!state.lockedKey) {
    clampBoardScroll();
    return;
  }

  // Measure only the rendered columns. Measuring board.scrollWidth while the
  // previous SVG is still sized can create a self-sustaining overflow width.
  const br = board.getBoundingClientRect();
  const canvas = dependencyCanvasSize();
  const W = canvas.width;
  const H = canvas.height;
  if(!W || !H) return;

  // Set an explicit pixel canvas. The SVG has inset:0 in CSS, and percentage
  // sizing can resolve against a transient layout size during view changes.
  lines.style.left = '0px';
  lines.style.top = '0px';
  lines.style.right = 'auto';
  lines.style.bottom = 'auto';
  lines.style.width = W + 'px';
  lines.style.height = H + 'px';
  lines.setAttribute('width', W);
  lines.setAttribute('height', H);
  lines.setAttribute('viewBox', '0 0 ' + W + ' ' + H);

  const ns = 'http://www.w3.org/2000/svg';
  const defs = document.createElementNS(ns, 'defs');
  defs.innerHTML = '<marker id="arrow" markerWidth="4" markerHeight="4" refX="3.5" refY="2" orient="auto">'
    + '<path d="M0,0 L4,2 L0,4 z" class="arrow"/></marker>';
  lines.appendChild(defs);

  const colEls = [...document.querySelectorAll('.column')];
  if(!colEls.length) return;
  const colOf = el => { const c = el.closest('.column'); return c ? colEls.indexOf(c) : -1; };

  const lockedChain = activeSelectionChain(state.lockedKey);
  let edges = (state.displayEdges || []).filter(e =>
    lockedChain.has(e.from) && lockedChain.has(e.to)
  );

  // displayEdges can briefly be empty during a refresh/rebuild. Fall back to
  // the blocker relationships already present on the rendered issues so the
  // selected dependency chain still gets its lines.
  if(!edges.length){
    const derived = [];
    for(const issue of state.displayIssues || []){
      if(!lockedChain.has(issue.key)) continue;
      for(const blocker of (issue.blockers || [])){
        if(lockedChain.has(blocker)) derived.push({from:blocker,to:issue.key});
      }
    }
    edges = derived;
  }
  if(!edges.length) return;

  const cards = new Map();
  document.querySelectorAll('.card').forEach(c => cards.set(c.dataset.key, c));

  const entry = el => {
    const r = el.getBoundingClientRect();
    return {x:r.left - br.left, y:r.top + 30 - br.top};
  };
  const exit_ = el => {
    const r = el.getBoundingClientRect();
    return {x:r.right - br.left, y:r.top + 30 - br.top};
  };

  // Route the vertical leg through the whitespace gap immediately after the
  // source column. This keeps the line out of cards in the columns.
  edges.forEach(e => {
    const source = cards.get(e.from);
    const target = cards.get(e.to);
    if(!source || !target) return;

    const fromCol = colOf(source);
    const toCol = colOf(target);
    if(fromCol < 0 || toCol < 0 || toCol <= fromCol) return;

    const s = exit_(source);
    const t = entry(target);
    const nextCol = colEls[fromCol + 1];
    if(!nextCol) return;

    const sr = source.getBoundingClientRect();
    const nr = nextCol.getBoundingClientRect();
    const routeX = ((sr.right + nr.left) / 2) - br.left;

    const d = 'M ' + s.x + ' ' + s.y
      + ' L ' + routeX + ' ' + s.y
      + ' L ' + routeX + ' ' + t.y
      + ' L ' + t.x + ' ' + t.y;

    const path = document.createElementNS(ns, 'path');
    path.setAttribute('d', d);
    path.setAttribute('class', 'line highlighted-line');
    path.dataset.from = e.from;
    path.dataset.to = e.to;
    path.setAttribute('marker-end', 'url(#arrow)');
    lines.appendChild(path);
  });
  clampBoardScroll();
}

const dependencyModal = document.getElementById('dependency-modal');
const depA = document.getElementById('dep-issue-a');
const depBSearch = document.getElementById('dep-issue-b-search');
const depBList = document.getElementById('dep-issue-b-list');
const depSwap = document.getElementById('dep-swap');
const depDirection = document.getElementById('dep-direction');
const depList = document.getElementById('dependency-list');
let dependencyEditorKey = null;
let dependencyBKey = '';
let dependencyBIndex = -1;

function issueLabel(key){
  const issue = state.issues.find(i => i.key === key);
  return issue ? key + ' · ' + (issue.summary || '') : key;
}

function populateDependencyOptions(preselect){
  const opts = state.issues.slice().sort((a,b)=>a.key.localeCompare(b.key));
  depA.innerHTML = opts.map(i =>
    '<option value="' + esc(i.key) + '">' + esc(issueLabel(i.key)) + '</option>'
  ).join('');

  depA.value = preselect && state.issues.some(i=>i.key===preselect)
    ? preselect
    : (depA.options[0]?.value || '');

  dependencyBKey = '';
  dependencyBIndex = -1;
  depBSearch.value = '';
  depBSearch.setAttribute('aria-expanded','false');
  renderDependencyOptions();
  updateDependencyDirection();
  renderDependencyList();
}

function matchingDependencyOptions(){
  const q = depBSearch.value.trim().toLowerCase();
  return state.issues.slice().sort((a,b)=>a.key.localeCompare(b.key))
    .filter(i => !q ||
      i.key.toLowerCase().includes(q) ||
      (i.summary || '').toLowerCase().includes(q)
    );
}

function renderDependencyOptions(){
  const opts = matchingDependencyOptions();
  if(!opts.length){
    depBList.innerHTML = '<div class="issue-option">No matching issues</div>';
    dependencyBIndex = -1;
    return;
  }

  if(dependencyBIndex >= opts.length) dependencyBIndex = opts.length - 1;

  depBList.innerHTML = opts.map((i, idx) =>
    '<div class="issue-option' + (i.key === dependencyBKey || idx === dependencyBIndex ? ' active' : '') +
    '" role="option" aria-selected="' + (i.key === dependencyBKey ? 'true' : 'false') +
    '" data-issue-option="' + esc(i.key) + '">' +
      '<span class="issue-option-key">' + esc(i.key) + '</span>' +
      (i.summary ? '<span class="issue-option-summary"> · ' + esc(i.summary) + '</span>' : '') +
    '</div>'
  ).join('');

  depBList.querySelectorAll('[data-issue-option]').forEach(option => {
    option.addEventListener('mousedown', e => {
      e.preventDefault();
      selectDependencyB(option.dataset.issueOption);
    });
  });
}

function openDependencyOptions(){
  renderDependencyOptions();
  depBList.classList.add('open');
  depBSearch.setAttribute('aria-expanded','true');
}

function closeDependencyOptions(){
  depBList.classList.remove('open');
  depBSearch.setAttribute('aria-expanded','false');
  dependencyBIndex = -1;
}

function selectDependencyB(key){
  const issue = state.issues.find(i => i.key === key);
  if(!issue) return;
  dependencyBKey = key;
  depBSearch.value = issueLabel(key);
  closeDependencyOptions();
}

function moveDependencyB(delta){
  const opts = matchingDependencyOptions();
  if(!opts.length) return;
  openDependencyOptions();
  dependencyBIndex = Math.max(0, Math.min(opts.length - 1, dependencyBIndex + delta));
  const key = opts[dependencyBIndex].key;
  depBList.querySelectorAll('[data-issue-option]').forEach((el, idx) => {
    el.classList.toggle('active', idx === dependencyBIndex);
  });
  const active = depBList.querySelectorAll('[data-issue-option]')[dependencyBIndex];
  if(active) active.scrollIntoView({block:'nearest'});
}

function updateDependencyDirection(){
  depDirection.textContent = depSwap.checked ? 'Issue A is blocked by Issue B' : 'Issue A blocks Issue B';
}

function currentDependencyPairs(){
  const a = depA.value;
  if(!a) return {blockedBy:[], blocks:[]};
  const issue = state.issues.find(i => i.key === a);
  return {
    blockedBy: (issue?.blockers || []).slice().sort(),
    blocks: (issue?.blocked || []).slice().sort()
  };
}

function renderDependencyList(){
  const {blockedBy, blocks} = currentDependencyPairs();

  function row(key, source, target){
    const issue = state.issues.find(i => i.key === key);
    const issueUrl = issue?.url || (CFG.jiraBaseUrl + '/browse/' + encodeURIComponent(key));
    return '<div class="dependency-row">' +
      '<div class="dependency-row-text"><a class="dependency-row-key" href="' + esc(issueUrl) +
      '" target="_blank" rel="noopener noreferrer" data-issue-key="' + esc(key) + '">' + esc(key) + '</a> · ' +
      esc(issue?.summary || '') + '</div>' +
      '<button type="button" class="dependency-remove" data-remove-source="' + esc(source) +
      '" data-remove-target="' + esc(target) + '">Remove</button>' +
      '</div>';
  }

  function section(title, keys, sourceIsKey){
    return '<div class="dependency-section ' + (sourceIsKey ? 'blocked-by' : 'blocks') + '">' +
      '<div class="dependency-section-title">' + title + '</div>' +
      (keys.length
        ? keys.map(key => sourceIsKey ? row(key, key, depA.value) : row(key, depA.value, key)).join('')
        : '<div class="dependency-empty">None</div>') +
      '</div>';
  }

  depList.innerHTML =
    section('Blocked by', blockedBy, true) +
    section('Blocks', blocks, false);

  attachTicketKeyModalHandlers(depList);

  depList.querySelectorAll('.dependency-remove').forEach(btn => {
    btn.addEventListener('click', e => {
      e.stopPropagation();
      try{
        deleteLocalDependency(btn.dataset.removeSource, btn.dataset.removeTarget);
        renderDependencyList();
        render();
      }catch(err){ showError(err.message || String(err)); }
    });
  });
}

function openDependencyModal(preselect){
  dependencyEditorKey = preselect || null;
  populateDependencyOptions(preselect);
  dependencyModal.classList.add('open');
  closeDependencyOptions();
}

function closeDependencyModal(){
  dependencyModal.classList.remove('open');
  closeDependencyOptions();
  dependencyEditorKey = null;
}

function addDependencyFromEditor(){
  const a = depA.value;
  const b = dependencyBKey;
  if(!a || !b || a === b){ showError('Choose two different issues.'); return; }

  const source = depSwap.checked ? b : a;
  const target = depSwap.checked ? a : b;

  try{
    if(addLocalDependency(source, target)){
      render();
      dependencyEditorKey = a;
      populateDependencyOptions(a);
      dependencyBKey = '';
      depBSearch.value = '';
      renderDependencyOptions();
      renderDependencyList();
      closeDependencyOptions();
    }else{
      showError('That dependency already exists.');
    }
  }catch(err){ showError(err.message || String(err)); }
}

document.getElementById('dependency-modal-close').addEventListener('click', closeDependencyModal);
document.getElementById('dependency-modal-cancel').addEventListener('click', closeDependencyModal);
dependencyModal.addEventListener('click', e => { if(e.target === dependencyModal) closeDependencyModal(); });

depBSearch.addEventListener('focus', openDependencyOptions);
depBSearch.addEventListener('input', () => {
  dependencyBKey = '';
  dependencyBIndex = -1;
  openDependencyOptions();
});
depBSearch.addEventListener('keydown', e => {
  if(e.key === 'ArrowDown'){
    e.preventDefault();
    moveDependencyB(1);
  }else if(e.key === 'ArrowUp'){
    e.preventDefault();
    moveDependencyB(-1);
  }else if(e.key === 'Enter'){
    e.preventDefault();
    const opts = matchingDependencyOptions();
    if(dependencyBIndex >= 0 && opts[dependencyBIndex]){
      selectDependencyB(opts[dependencyBIndex].key);
    }else if(opts.length === 1){
      selectDependencyB(opts[0].key);
    }else{
      openDependencyOptions();
    }
  }else if(e.key === 'Escape'){
    closeDependencyOptions();
  }
});
document.addEventListener('click', e => {
  if(!e.target.closest('.issue-combobox')) closeDependencyOptions();
});
depSwap.addEventListener('change', updateDependencyDirection);
depA.addEventListener('change', () => {
  dependencyEditorKey = depA.value;
  renderDependencyList();
});
document.getElementById('dependency-modal-add').addEventListener('click', addDependencyFromEditor);

function restorePriorityMenu(picker){
  if(!picker) return;
  const menu = document.querySelector('.priority-menu[data-portal="1"]');
  if(menu && menu.__priorityPicker === picker){
    menu.style.display = '';
    menu.style.left = '';
    menu.style.top = '';
    menu.style.position = '';
    menu.style.zIndex = '';
    menu.removeAttribute('data-portal');
    picker.appendChild(menu);
  }
}

function closePriorityPicker(picker){
  if(!picker) return;
  picker.classList.remove('open');
  const t = picker.querySelector('.priority-trigger');
  if(t) t.setAttribute('aria-expanded','false');
  const menu = document.querySelector('.priority-menu[data-portal="1"]');
  if(menu && menu.__priorityPicker === picker) restorePriorityMenu(picker);
  else {
    const m = picker.querySelector('.priority-menu');
    if(m){ m.style.display=''; m.style.left=''; m.style.top=''; }
  }
}

function closePriorityPickers(e){
  if(e && e.target && e.target.closest && (e.target.closest('.priority-picker') || e.target.closest('.priority-menu'))) return;
  document.querySelectorAll('.priority-picker.open').forEach(closePriorityPicker);
}

// ── Event wiring (delegated — called after each render) ───────────────────
function attachTicketKeyModalHandlers(root=document){
  root.querySelectorAll(
    'a[data-issue-key], a.key, a.relation-key, a.milestone-blocked-key, a.dependency-row-key, a.epic-badge'
  ).forEach(link => {
    if(link.dataset.ticketModalBound === '1') return;
    link.dataset.ticketModalBound = '1';
    link.addEventListener('click', e => {
      if(e.button !== 0 || e.ctrlKey || e.metaKey || e.shiftKey || e.altKey) return;

      // Default behaviour: let the existing target="_blank" link open Jira in a new tab.
      // Only intercept the click when the user has explicitly enabled the Jira modal.
      if(!getUseJiraModal()){
        e.stopPropagation();
        return;
      }

      e.preventDefault();
      e.stopPropagation();

      const href=link.href;
      const hrefKey=decodeURIComponent((new URL(href,window.location.href).pathname.split('/').filter(Boolean).pop() || ''));
      const key=(link.dataset.issueKey || hrefKey || link.textContent.trim()).toUpperCase();
      const issue=state.issues.find(i => i.key === key);
      const card=link.closest('.card, .dashboard-ticket');
      const summary=issue?.summary || (card ? (card.querySelector('.summary')?.textContent.trim() || '') : '') || link.title || '';
      openTicketPreviewModal(key,href,summary);
    });
  });
}

document.addEventListener('keydown', e => {
  if(e.key === 'Escape'){
    if(state.hoverLockKey) clearHoverLock();
    closeTicketPreviewModal();
  }
});

document.querySelectorAll('[data-action="escape"]').forEach(btn => {
  if(btn.getAttribute('role') === 'button'){
    btn.addEventListener('keydown', e => {
      if(e.key === 'Enter' || e.key === ' '){
        e.preventDefault();
        btn.click();
      }
    });
  }
  btn.addEventListener('click', () => {
    clearHoverLock();
    closeTicketPreviewModal();

    // Home always resets the board position to the top-left. Clear the
    // stored scroll positions as well so render() cannot restore an old
    // horizontal/vertical position from the previous view.
    Object.keys(state.scrollPositions).forEach(mode => {
      state.scrollPositions[mode] = {appLeft:0, appTop:0, columns:{}};
    });

    if(state.showMilestones || state.showDashboard || state.showBlocked || state.lockedKey){
      // Home returns to the normal board view, but it must not change filters.
      // If a card was selected, restore the filters that were active before the
      // selection temporarily hid them for the dependency-chain view.
      const homeFilterSnapshot = state.selectionHistory.length
        ? state.selectionHistory[0].filters
        : null;
      if(homeFilterSnapshot) restoreFilterSnapshot(homeFilterSnapshot);

      // Home always returns to the configured starting board view.
      state.showMilestones = state.startingView === 'milestone';
      state.showDashboard = state.startingView === 'dashboard';
      state.showBlocked = false;
      state.lockedKey = null;
      state.selectionHistory = [];
      state.returnMilestoneKey = null;
      state.dashboardReturnSection = null;
      state.milestoneFlashKey = null;
      state.revealSelectedKey = null;
      render();
    }else{
      // Already on the main view: reset the existing DOM immediately.
      const app = document.getElementById('app');
      if(app) {
        app.scrollLeft = 0;
        app.scrollTop = 0;
      }
      board.querySelectorAll('.cards').forEach(cards => {
        cards.scrollTop = 0;
        cards.scrollLeft = 0;
      });
    }

    // Apply once more after layout/render so no restored or newly-created
    // scroll container can retain the previous position.
    requestAnimationFrame(() => {
      const app = document.getElementById('app');
      if(app) {
        app.scrollLeft = 0;
        app.scrollTop = 0;
      }
      board.querySelectorAll('.cards').forEach(cards => {
        cards.scrollTop = 0;
        cards.scrollLeft = 0;
      });
    });
  });
});

function openDueDateModal(key){
  const issue=state.issues.find(i=>i.key===key);
  if(!issue || !dueDateModal) return;
  dueDateKey.textContent=key + (issue.summary ? ' · ' + issue.summary : '');
  dueDateInput.value=issue.dueDate || '';
  dueDateModal.dataset.key=key;
  dueDateModal.classList.add('open');
  requestAnimationFrame(()=>{ dueDateInput.focus(); try{ dueDateInput.showPicker?.(); }catch(_){} });
}
function closeDueDateModal(){ if(dueDateModal) dueDateModal.classList.remove('open'); }

function reachableChainIssues(startKey, direction){
  const byKey=new Map(state.issues.map(i=>[i.key,i]));
  const adjacent=new Map();
  state.issues.forEach(i=>adjacent.set(i.key,[]));
  for(const edge of state.edges){
    const from=direction==='downstream' ? edge.from : edge.to;
    const to=direction==='downstream' ? edge.to : edge.from;
    if(!adjacent.has(from)) adjacent.set(from,[]);
    adjacent.get(from).push(to);
  }
  const result=[], queue=[startKey], seen=new Set([startKey]);
  while(queue.length){
    const current=queue.shift();
    for(const next of (adjacent.get(current)||[])){
      if(seen.has(next)) continue;
      seen.add(next);
      queue.push(next);
      const issue=byKey.get(next);
      if(issue) result.push(issue);
    }
  }
  return result;
}

function dueDateChainRisks(key, proposedDate, overrides=null){
  if(!isValidDueDateValue(proposedDate)) return {downstream:[],upstream:[]};
  const effectiveDate=issue=>{
    if(overrides && Object.prototype.hasOwnProperty.call(overrides,issue.key)) return overrides[issue.key] || '';
    return issue.dueDate || '';
  };
  const dated=items=>items.map(i=>Object.assign({},i,{riskDueDate:effectiveDate(i)})).filter(i=>isValidDueDateValue(i.riskDueDate));
  const sortRisks=items=>items.sort((a,b)=>(a.riskDueDate||'').localeCompare(b.riskDueDate||'') || a.key.localeCompare(b.key));
  return {
    downstream:sortRisks(dated(reachableChainIssues(key,'downstream')).filter(i=>i.riskDueDate < proposedDate)),
    upstream:sortRisks(dated(reachableChainIssues(key,'upstream')).filter(i=>i.riskDueDate > proposedDate))
  };
}

function chainDateIssueLink(issue){
  const url=issue?.url || (CFG.jiraBaseUrl ? CFG.jiraBaseUrl+'/browse/'+encodeURIComponent(issue.key) : '#');
  return '<a class="chain-date-warning-key" href="'+esc(url)+'" target="_blank" rel="noopener noreferrer" data-issue-key="'+esc(issue.key)+'">'+esc(issue.key)+'</a>';
}

function chainDateDateInput(key, value){
  return '<input class="chain-date-warning-date" type="date" value="'+esc(value||'')+'" data-chain-risk-date-key="'+esc(key)+'" aria-label="Due date for '+esc(key)+'">';
}

function chainDateRiskTable(items){
  return '<table class="chain-date-warning-table"><thead><tr><th>Key</th><th>Summary</th><th>Due date</th></tr></thead><tbody>'+
    items.map(i=>'<tr><td>'+chainDateIssueLink(i)+'</td><td>'+esc(i.summary||'')+'</td><td>'+chainDateDateInput(i.key,i.riskDueDate||i.dueDate||'')+'</td></tr>').join('')+
    '</tbody></table>';
}

function renderChainDateWarning(){
  if(!pendingDueDateChange || !chainDateWarningContent) return;
  const drafts=pendingDueDateChange.drafts || {};
  const changed=Object.keys(drafts).map(key=>{
    const issue=state.issues.find(i=>i.key===key);
    return issue ? {issue,value:drafts[key]||''} : null;
  }).filter(Boolean).filter(item=>(item.issue.dueDate||'')!==item.value);

  const changesHtml=changed.length
    ? '<section class="chain-date-warning-changes"><h3 class="chain-date-warning-changes-title">Proposed date changes</h3><table class="chain-date-warning-table"><thead><tr><th>Key</th><th>Current</th><th>Proposed</th><th></th></tr></thead><tbody>'+
      changed.map(item=>'<tr><td>'+chainDateIssueLink(item.issue)+'</td><td class="chain-date-warning-current">'+esc(item.issue.dueDate?formatDueDate(item.issue.dueDate):'No date')+'</td><td>'+chainDateDateInput(item.issue.key,item.value)+'</td><td><button type="button" class="chain-date-warning-revert" data-chain-risk-revert="'+esc(item.issue.key)+'">Revert</button></td></tr>').join('')+
      '</tbody></table></section>'
    : '<div class="chain-date-warning-empty">No date changes are currently proposed.</div>';

  const sections=[];
  changed.forEach(item=>{
    if(!isValidDueDateValue(item.value)) return;
    const risks=dueDateChainRisks(item.issue.key,item.value,drafts);
    if(!risks.downstream.length && !risks.upstream.length) return;
    const groups=[];
    if(risks.downstream.length){
      groups.push('<div class="chain-date-warning-subsection"><p class="chain-date-warning-message">This date is later than a due date later in the chain.</p>'+chainDateRiskTable(risks.downstream)+'</div>');
    }
    if(risks.upstream.length){
      groups.push('<div class="chain-date-warning-subsection"><p class="chain-date-warning-message">This date is earlier than a date earlier in the chain.</p>'+chainDateRiskTable(risks.upstream)+'</div>');
    }
    sections.push('<section class="chain-date-warning-section"><h3 class="chain-date-warning-section-title">('+esc(item.issue.key)+') - Chain date risk</h3>'+groups.join('')+'</section>');
  });

  const risksHtml=sections.length
    ? sections.join('')
    : (changed.length ? '<div class="chain-date-warning-resolved">These proposed dates no longer create a chain date risk.</div>' : '');
  chainDateWarningContent.innerHTML=changesHtml+risksHtml;
  const confirm=document.getElementById('chain-date-warning-confirm');
  if(confirm) confirm.disabled=!changed.length;

  chainDateWarningContent.querySelectorAll('[data-chain-risk-date-key]').forEach(input=>{
    input.addEventListener('change',()=>{
      const key=input.dataset.chainRiskDateKey;
      const issue=state.issues.find(i=>i.key===key);
      if(!issue) return;
      const value=input.value||'';
      if((issue.dueDate||'')===value) delete pendingDueDateChange.drafts[key];
      else pendingDueDateChange.drafts[key]=value;
      renderChainDateWarning();
    });
  });
  chainDateWarningContent.querySelectorAll('[data-chain-risk-revert]').forEach(button=>{
    button.addEventListener('click',()=>{
      delete pendingDueDateChange.drafts[button.dataset.chainRiskRevert];
      renderChainDateWarning();
    });
  });
  attachTicketKeyModalHandlers(chainDateWarningContent);
}

function openChainDateWarning(key, value, risks){
  if(!chainDateWarningModal || !chainDateWarningContent) return false;
  if(!risks || (!risks.downstream.length && !risks.upstream.length)) return false;
  pendingDueDateChange={primaryKey:key,drafts:{[key]:value||''}};
  renderChainDateWarning();
  chainDateWarningModal.classList.add('open');
  requestAnimationFrame(()=>document.getElementById('chain-date-warning-confirm')?.focus());
  return true;
}

function closeChainDateWarning(){
  pendingDueDateChange=null;
  chainDateWarningModal?.classList.remove('open');
}

function confirmChainDateChange(){
  const change=pendingDueDateChange;
  if(!change) return;
  const changes=Object.entries(change.drafts||{}).map(([key,value])=>({key,value:value||null}));
  pendingDueDateChange=null;
  chainDateWarningModal?.classList.remove('open');
  if(stageDueDateChanges(changes)) render();
}

function saveDueDateModal(clear=false){
  const key=dueDateModal?.dataset.key;
  if(!key) return;
  const value=clear ? null : (dueDateInput.value || null);
  const issue=state.issues.find(i=>i.key===key);
  if(!issue || (issue.dueDate||null)===(value||null)){
    closeDueDateModal();
    return;
  }
  if(value){
    const risks=dueDateChainRisks(key,value);
    if(risks.downstream.length || risks.upstream.length){
      closeDueDateModal();
      openChainDateWarning(key,value,risks);
      return;
    }
  }
  stageIssueChange(key,'dueDate',value);
  closeDueDateModal();
  render();
}

function attachEvents(){
  // ── Card click (select / deselect) ──
  board.querySelectorAll('.card').forEach(card => {
    card.addEventListener('click', e => {
      // Ignore clicks on links and controls inside the card.
      if(e.target.closest('[data-stop-propagation]')) return;
      const key = card.dataset.key;
      const issue = state.displayIssues.find(i => i.key === key);
      const isMilestone = issue && (issue.labels || []).some(label => String(label).toLowerCase() === 'milestone');
      // A milestone card behaves like every other card when selected.
      // Only the dedicated MILESTONE banner opens the milestone overview.
      if(state.lockedKey === key){
        // Clicking the selected card again keeps the current level in place.
        return;
      }
      state.selectionHistory.push({key: state.lockedKey, filters: filterSnapshot()});
      // Dependency chains always reveal every ticket, regardless of search or filters.
      state.searchTerm = '';
      state.filterUser = '';
      state.includeWithRemarkable = true;
      searchEl.value = '';
      saveFilterPreferences();
      clearHoverLock();
      state.lockedKey = key;
      state.showBlocked = false;
      // The selected card is the focus of the newly revealed chain. Ask render()
      // to reveal it after the rebuilt layout and scroll restoration have settled.
      state.revealSelectedKey = key;
      render();
    });
  });

  // ── Persistent hover highlight lock ─────────────────────────────────────
  board.querySelectorAll('.hover-lock-btn').forEach(btn => {
    btn.addEventListener('click', e => {
      e.preventDefault();
      e.stopPropagation();
      const key = btn.dataset.key;
      if(!key || !state.lockedKey) return;
      if(state.hoverLockKey === key) clearHoverLock();
      else lockHoverHighlight(key);
    });
  });

  // ── Milestone banner ─────────────────────────────────────────────────────
  // The card itself selects the normal dependency chain. The dedicated banner
  // is the separate navigation target for opening the milestone overview.
  board.querySelectorAll('.milestone-banner').forEach(banner => {
    banner.addEventListener('click', e => {
      e.preventDefault();
      e.stopPropagation();

      const card = banner.closest('.card');
      const key = card ? card.dataset.key : null;
      if(!key) return;

      state.showMilestones = true;
      state.showDashboard = false;
      clearHoverLock();
      state.lockedKey = null;
      state.selectionHistory = [];
      state.showBlocked = false;
      state.milestoneFlashKey = key;
      state.returnMilestoneKey = null;
      render();
    });
  });

  // ── Links/badges inside cards stop propagation via data attribute ──
  board.querySelectorAll('[data-stop-propagation]').forEach(el => {
    el.addEventListener('click', e => e.stopPropagation());
  });

  // ── Editable Jira fields ──
  board.querySelectorAll('select[data-field]').forEach(select => {
    select.addEventListener('change', e => {
      e.stopPropagation();
      const card = select.closest('.card, .dashboard-ticket');
      if(!card) return;
      if(select.dataset.field === 'assignee') select.classList.toggle('unassigned', !select.value);
      stageIssueChange(card.dataset.key, select.dataset.field, select.value);
    });
    select.addEventListener('click', e => e.stopPropagation());
  });

  // ── Due date picker ──
  board.querySelectorAll('[data-due-date-key]').forEach(btn => {
    btn.addEventListener('click', e => {
      e.preventDefault(); e.stopPropagation();
      openDueDateModal(btn.dataset.dueDateKey);
    });
  });

  // ── Custom priority picker with Jira icons ──
  board.querySelectorAll('.priority-picker').forEach(picker => {
    const trigger = picker.querySelector('.priority-trigger');
    trigger.addEventListener('click', e => {
      e.stopPropagation();
      const wasOpen = picker.classList.contains('open');
      document.querySelectorAll('.priority-picker.open').forEach(p => {
        if(p !== picker) closePriorityPicker(p);
      });
      picker.classList.toggle('open', !wasOpen);
      trigger.setAttribute('aria-expanded', String(!wasOpen));
      if(!wasOpen){
        const menu = picker.querySelector('.priority-menu');
        if(menu){
          // Move the menu to <body> so column/card overflow and stacking
          // contexts cannot clip or cover it.
          menu.__priorityPicker = picker;
          menu.setAttribute('data-portal','1');
          document.body.appendChild(menu);
          menu.style.display = 'block';
          menu.style.position = 'fixed';
          menu.style.zIndex = '100000';
          const r = trigger.getBoundingClientRect();
          menu.style.left = Math.max(6, r.left - 6) + 'px';
          menu.style.top = (r.bottom + 5) + 'px';
          const mr = menu.getBoundingClientRect();
          if(mr.bottom > window.innerHeight - 6){
            menu.style.top = Math.max(6, r.top - mr.height - 5) + 'px';
          }
          if(mr.right > window.innerWidth - 6){
            menu.style.left = Math.max(6, window.innerWidth - mr.width - 6) + 'px';
          }
        }
      }
    });
    picker.querySelectorAll('.priority-option').forEach(option => {
      option.addEventListener('click', e => {
        e.stopPropagation();
        const card = picker.closest('.card, .dashboard-ticket');
        if(!card) return;
        const value = option.dataset.priority;
        stageIssueChange(card.dataset.key, 'priority', value);
        const img = picker.querySelector('.priority-icon');
        if(img && CFG.jiraBaseUrl){
          img.src = CFG.jiraBaseUrl + '/images/icons/priorities/' + value.toLowerCase() + '.svg';
          img.alt = value; img.title = value;
        }
        const menu = option.closest('.priority-menu');
        if(menu) menu.querySelectorAll('.priority-option').forEach(x => x.classList.toggle('selected', x === option));
        closePriorityPicker(picker);
      });
    });
  });


  // ── Reveal downstream / higher-level blocked cards ──
  board.querySelectorAll('.see-blocked-btn').forEach(btn => {
    btn.addEventListener('click', e => {
      e.stopPropagation();
      state.showBlocked = !state.showBlocked;
      render();
    });
  });
  // ── Edit dependency buttons ──
  board.querySelectorAll('.edit-dependency-btn').forEach(btn => {
    btn.addEventListener('click', e => {
      e.stopPropagation();
      openDependencyModal(btn.dataset.editDependency);
    });
  });

  // ── Hover → highlight chain (only while an item is selected) ──
  board.querySelectorAll('.card').forEach(card => {
    card.addEventListener('mouseenter', () => {
      if(state.lockedKey) applyHoverHighlight(card.dataset.key);
    });
    card.addEventListener('mouseleave', () => {
      if(state.lockedKey) clearHoverHighlight();
    });
  });

  // Dependency lines are positioned relative to the board. In the locked view
  // the columns themselves do not scroll, so scrolling the app moves the cards
  // and SVG together. Do not rebuild the SVG on scroll: replacing all paths
  // during scrolling causes visible flicker and briefly resets hover styling.

  highlightSelectedChainDateRisks();
  updateSaveButton();
  attachTicketKeyModalHandlers();
  updateHoverLockButtons();
}

// ── Load data ─────────────────────────────────────────────────────────────
async function fetchGraph(mode, loadGeneration){
  const r = await fetch('/api/dependencies?mode=' + encodeURIComponent(mode) + '&jql=' + encodeURIComponent(getActiveJql()) + '&generation=' + encodeURIComponent(String(loadGeneration || '')), {cache:'no-store'});
  const d = await r.json();
  if(!r.ok) throw new Error(d.error || 'HTTP ' + r.status);
  console.log('Jira graph loaded', {issues:(d.issues || []).length, edges:(d.edges || []).length, withDueDates:(d.issues || []).filter(i => i.dueDate).length});
  return d;
}

let completedDownloadPollTimer = null;
async function pollCompletedDownload(loadGeneration = state.loadGeneration){
  if(completedDownloadPollTimer) clearInterval(completedDownloadPollTimer);
  // Always poll the background job belonging to the currently displayed Jira
  // load. This also makes calls from the Show completed toggle safe.
  loadGeneration = Number(loadGeneration);
  const generation=String(loadGeneration);
  const poll=async()=>{
    // A newer Jira load owns the UI now. Do not let this poll touch its state.
    if(loadGeneration !== state.loadGeneration){
      if(completedDownloadPollTimer) clearInterval(completedDownloadPollTimer);
      completedDownloadPollTimer=null;
      return;
    }
    try{
      const r=await fetch('/api/completed-status?jql=' + encodeURIComponent(getActiveJql()) + '&generation=' + encodeURIComponent(generation) + '&ts=' + Date.now(),{cache:'no-store'});
      if(!r.ok) return;
      const d=await r.json();
      if(loadGeneration !== state.loadGeneration) return;
      state.completedDownloadStatus=d.status || 'not-started';
      if(state.showCompleted && state.completedDownloadStatus !== 'ready') {
        showCompletedDownloadNotice(d.detail || 'Still downloading completed tickets…');
      }
      if(d.status === 'ready'){
        // Check again after the async status request. A refresh may have started
        // while this request was in flight.
        if(loadGeneration !== state.loadGeneration) return;
        const dataResponse=await fetch('/api/completed-data?jql=' + encodeURIComponent(getActiveJql()) + '&generation=' + encodeURIComponent(generation) + '&ts=' + Date.now(),{cache:'no-store'});
        if(!dataResponse.ok) return;
        const data=await dataResponse.json();
        // Never apply a completed graph belonging to an older refresh.
        if(loadGeneration !== state.loadGeneration) return;
        state.issues=data.issues || [];
        state.edges=data.edges || [];
        state.levels=data.levels || 0;
        state.cleanSnapshot=cloneCleanSnapshot();
        state.completedDownloadStatus='ready';
        // Replace the active-only board immediately with the completed graph.
        // render() also recalculates filters/levels and displays completed cards
        // when Show completed is enabled.
        hideCompletedDownloadNotice();
        render();
        if(completedDownloadPollTimer) clearInterval(completedDownloadPollTimer);
        completedDownloadPollTimer=null;
      }else if(d.status === 'error'){
        if(state.showCompleted) showCompletedDownloadNotice(d.error || 'Completed tickets could not be downloaded.');
        if(completedDownloadPollTimer) clearInterval(completedDownloadPollTimer);
        completedDownloadPollTimer=null;
      }
    }catch(e){}
  };
  await poll();
  if(state.completedDownloadStatus !== 'ready' && state.completedDownloadStatus !== 'error') completedDownloadPollTimer=setInterval(poll,700);
}
function showCompletedDownloadNotice(message){
  const existing=board.querySelector('.completed-download-notice');
  if(existing){ existing.querySelector('.completed-download-message').textContent=message; return; }
  const notice=document.createElement('div');
  notice.className='completed-download-notice';
  notice.innerHTML='<div class="completed-download-title">Still downloading completed tickets</div><div class="completed-download-message">'+esc(message || 'Please wait while completed tickets are downloaded.')+'</div>';
  board.appendChild(notice);
}
function hideCompletedDownloadNotice(){
  board.querySelector('.completed-download-notice')?.remove();
}

async function load(resetSelection){
  const loadGeneration=++state.loadGeneration;
  startLoadingStages('Connecting to Jira…'); hideError();
  try{
    const wantCompleted=!!state.showCompleted;
    const d=await fetchGraph(wantCompleted ? 'all' : 'active', loadGeneration);
    // A newer refresh may have started while Jira was loading. Its response
    // is authoritative, so discard this older response completely.
    if(loadGeneration !== state.loadGeneration) return;
    state.issues=d.issues || []; state.edges=d.edges || []; state.levels=d.levels || 0;
    state.completedDownloadStatus=wantCompleted ? 'ready' : 'downloading';
    state.cleanSnapshot=cloneCleanSnapshot();
    state.pendingChanges=[]; state.history=[]; state.redoHistory=[];
    if(resetSelection){
      state.lockedKey=null; state.selectionHistory=[]; state.showBlocked=false;
      if(pendingSharedView && pendingSharedView.key){
        const sharedIssue=state.issues.find(i => String(i.key).toUpperCase() === pendingSharedView.key);
        if(sharedIssue){
          state.showDashboard=false;
          state.showMilestones=false;
          state.lockedKey=sharedIssue.key;
          state.showBlocked=!!pendingSharedView.showBlocked;
          state.revealSelectedKey=sharedIssue.key;
          startupViewPending=false;
        }
        pendingSharedView=null;
      }
      if(startupViewPending){
        state.showDashboard = state.startingView === 'dashboard';
        state.showMilestones = state.startingView === 'milestone';
        startupViewPending=false;
      }
    }
    render(); updateSaveButton();
    if(startupMessagePromise) await startupMessagePromise;
    finishLoadingStages();
    if(!wantCompleted) pollCompletedDownload(loadGeneration);
    await new Promise(resolve => setTimeout(resolve,180));
  }catch(e){
    if(loadGeneration === state.loadGeneration){
      showError(e.message || String(e));
      statusText.textContent='Load failed';
    }
  }finally{
    if(loadGeneration === state.loadGeneration) setLoading(false);
  }
}

// ── Global event wiring ───────────────────────────────────────────────────
document.addEventListener('click', closePriorityPickers);
document.getElementById('save').addEventListener('click', saveChanges);
document.getElementById('refresh').addEventListener('click', () => {
  if(state.pendingChanges.length && !confirm('Discard ' + state.pendingChanges.length + ' unsaved change' + (state.pendingChanges.length === 1 ? '' : 's') + ' and refresh from Jira?')) return;
  load(true);
});
function goBackFromSelection(){
  if(state.selectionHistory.length){
    const previous = state.selectionHistory.pop();
    state.lockedKey = previous.key || null;
    restoreFilterSnapshot(previous.filters);
    state.showBlocked = false;
    // Treat the previous ticket as a newly focused chain. Reusing the old
    // locked-view scroll offset can otherwise strand the viewport in overflow
    // created by a wider chain.
    state.revealSelectedKey = state.lockedKey;
    state.scrollPositions.locked.appLeft = 0;
  }else{
    state.lockedKey = null;
    state.showBlocked = false;
    state.revealSelectedKey = null;
    state.scrollPositions.locked.appLeft = 0;
  }
  render();
}
deselectBtn.addEventListener('click', goBackFromSelection);

filtersBtn.addEventListener('click', e => {
  e.stopPropagation();
  filterMenu.classList.toggle('open');
  updateFilterControls();
});
filterMenu.addEventListener('click', e => e.stopPropagation());
toggleCompletedBtn.addEventListener('click', () => {
  state.showCompleted = !state.showCompleted;
  saveFilterPreferences();
  if(state.showCompleted && state.completedDownloadStatus !== 'ready'){
    showCompletedDownloadNotice('Completed tickets are still downloading. The active tickets remain available while this finishes.');
    render();
    pollCompletedDownload(state.loadGeneration);
    return;
  }
  hideCompletedDownloadNotice();
  render();
});
filterUser.addEventListener('change', () => {
  state.filterUser = filterUser.value;
  saveFilterPreferences();
  render();
});
filterDue.addEventListener('change', () => {
  state.filterDue = filterDue.value;
  saveFilterPreferences();
  render();
});
filterRemarkable.addEventListener('change', () => {
  state.includeWithRemarkable = filterRemarkable.checked;
  saveFilterPreferences();
  render();
});
clearFiltersBtn.addEventListener('click', clearAllFilters);
document.addEventListener('click', () => {
  if(filterMenu.classList.contains('open')){
    filterMenu.classList.remove('open');
    updateFilterControls();
  }
});

milestoneBackBtn.addEventListener('click', () => {
  if(state.dashboardReturnSection){
    const sectionId=state.dashboardReturnSection;
    state.dashboardReturnSection=null;
    state.returnMilestoneKey=null;
    state.showMilestones=false;
    state.showDashboard=true;
    state.lockedKey=null;
    state.selectionHistory=[];
    state.showBlocked=false;
    state.milestoneFlashKey=null;
    render();
    requestAnimationFrame(()=>{
      const target=document.getElementById(sectionId);
      if(target) target.scrollIntoView({behavior:'smooth',block:'start'});
    });
    return;
  }
  const key = state.returnMilestoneKey;
  if(!key) return;
  const previous = state.selectionHistory.length ? state.selectionHistory[0] : null;
  if(previous && previous.filters) restoreFilterSnapshot(previous.filters);
  state.showMilestones = true;
  state.lockedKey = null;
  state.selectionHistory = [];
  state.showBlocked = false;
  state.milestoneFlashKey = key;
  state.returnMilestoneKey = null;
  render();
});

document.querySelectorAll('.view-switch').forEach(btn => {
  btn.addEventListener('click', () => {
    const view=btn.dataset.view;
    state.showDashboard=view==='dashboard';
    state.showMilestones=view==='milestone';
    state.lockedKey=null;
    state.selectionHistory=[];
    state.showBlocked=false;
    state.returnMilestoneKey=null;
    state.dashboardReturnSection=null;
    render();
  });
});

searchEl.addEventListener('keydown', e => {
  // The main search is live as you type. Enter must not activate/select a card
  // or trigger any browser/default keyboard action.
  if(e.key === 'Enter'){
    e.preventDefault();
    e.stopPropagation();
  }
});
function updateSearchClearButton(){
  if(!searchClearBtn) return;
  const hasText = !!searchEl.value;
  searchClearBtn.classList.toggle('visible', hasText);
  searchClearBtn.disabled = !hasText;
}

searchEl.addEventListener('input', () => {
  // Never rebuild the board while typing. Filter the existing cards directly so
  // the input value and the search state cannot get out of sync.
  state.searchTerm = searchEl.value;
  updateSearchClearButton();
  applySearchFilter();
});
searchClearBtn.addEventListener('click', () => {
  // Clear only the text query. User, due-date and Remarkable filters remain.
  searchEl.value = '';
  state.searchTerm = '';
  updateSearchClearButton();
  applySearchFilter();
  searchEl.focus({preventScroll:true});
});
document.addEventListener('keydown', e => {
  const mod = e.ctrlKey || e.metaKey;
  const key = e.key.toLowerCase();

  if(mod && key === 's'){
    e.preventDefault();
    if(state.pendingChanges.length) saveChanges();
    return;
  }
  if(mod && key === 'k'){
    e.preventDefault();
    if(!state.lockedKey){ searchEl.focus(); searchEl.select(); }
    return;
  }
  if(mod && !e.shiftKey && key === 'z'){
    e.preventDefault(); undoLocal(); return;
  }
  if(mod && (key === 'y' || (e.shiftKey && key === 'z'))){
    e.preventDefault(); redoLocal(); return;
  }
  if(e.key === 'Escape'){
    if(dependencyModal.classList.contains('open')){ closeDependencyModal(); return; }
    if(state.lockedKey || state.selectionHistory.length){
      goBackFromSelection();
    }else if(activeFilterCount()){
      clearAllFilters();
    }
  }
});


credentialSave.addEventListener('click', saveCredential);
credentialRemove.addEventListener('click', removeCredential);
credentialCancel.addEventListener('click', closeCredentialModal);
settingsBtn.addEventListener('click', () => openSettings());
document.getElementById('due-date-close')?.addEventListener('click', closeDueDateModal);
document.getElementById('due-date-cancel')?.addEventListener('click', closeDueDateModal);
document.getElementById('due-date-clear')?.addEventListener('click', () => saveDueDateModal(true));
document.getElementById('due-date-save')?.addEventListener('click', () => saveDueDateModal(false));
dueDateModal?.addEventListener('click', e => { if(e.target === dueDateModal) closeDueDateModal(); });
dueDateInput?.addEventListener('keydown', e => { if(e.key === 'Enter'){ e.preventDefault(); saveDueDateModal(false); } if(e.key === 'Escape') closeDueDateModal(); });
document.getElementById('chain-date-warning-cancel')?.addEventListener('click', closeChainDateWarning);
document.getElementById('chain-date-warning-confirm')?.addEventListener('click', confirmChainDateChange);
chainDateWarningModal?.addEventListener('click', e => { if(e.target === chainDateWarningModal) closeChainDateWarning(); });
chainDateWarningModal?.addEventListener('keydown', e => { if(e.key === 'Escape'){ e.preventDefault(); closeChainDateWarning(); } });
customJqlIndicator?.addEventListener('click', e => {
  e.preventDefault();
  if(!getCustomJql()) return;
  openSettings(true);
});
customJqlIndicator?.addEventListener('keydown', e => {
  if(e.key === 'Enter' || e.key === ' '){ e.preventDefault(); if(getCustomJql()) openSettings(true); }
});
settingsAdvanced?.addEventListener('click', showSettingsJql);
settingsJqlBack?.addEventListener('click', showSettingsMain);
settingsJqlSave?.addEventListener('click', saveCustomJql);
settingsJqlReset?.addEventListener('click', resetCustomJql);

document.getElementById('discard').addEventListener('click', discardChanges);
settingsUseJiraModal.addEventListener('click', () => {
  setUseJiraModal(!getUseJiraModal());
});
settingsStartingView?.addEventListener('change', () => setStartingView(settingsStartingView.value));
settingsShowMiniMap?.addEventListener('click', () => {
  setMiniMapSetting(!(state.showMiniMap !== false));
});
settingsSeeStartupMessages.addEventListener('click', showAllStartupMessages);
settingsBack.addEventListener('click', showSettingsMain);
settingsClose.addEventListener('click', closeSettings);
settingsCloseBottom.addEventListener('click', closeSettings);
settingsModal.addEventListener('click', e => { if(e.target === settingsModal) closeSettings(); });
settingsManageCredential.addEventListener('click', async () => {
  closeSettings();
  try{
    const r = await fetch('/api/credential-status',{cache:'no-store'});
    const data = await r.json().catch(()=>({}));
    if(!r.ok || !data.configured){
      openCredentialModal(false);
      return;
    }
    openCredentialModal(true, data.email || '');
  }catch(e){
    showCredentialError(e.message || 'Unable to check the stored credential.');
    openCredentialModal(true);
  }
});
credentialApiKey.addEventListener('keydown', e => {
  if(e.key === 'Enter') saveCredential();
});
credentialEmail.addEventListener('keydown', e => {
  if(e.key === 'Enter') credentialApiKey.focus();
});

window.addEventListener('beforeunload', e => {
  if(state.pendingChanges.length && !updateRestarting){
    e.preventDefault();
    e.returnValue = '';
  }
});

window.addEventListener('resize', () => { requestAnimationFrame(drawLines); scheduleMiniMapUpdate(); });
// Do not redraw dependency SVG paths while the app scrolls. In the selected
// view the board, cards and SVG move together, so rebuilding the paths on
// every scroll frame only causes flicker.

updateJiraModalSetting();
checkForRequiredUpdate().then(updateRequired => {
  if(!updateRequired) initialiseApp();
});
</script>
</body>
</html>"""

# ---------------------------------------------------------------------------
# Server startup
# ---------------------------------------------------------------------------

def clear_port_windows(port):
    command=f"""
$deadline = (Get-Date).AddSeconds(5)
do {{
    $owners = @(Get-NetTCPConnection -LocalPort {port} -State Listen -ErrorAction SilentlyContinue |
        Select-Object -ExpandProperty OwningProcess -Unique)
    foreach ($owner in $owners) {{
        Stop-Process -Id $owner -Force -ErrorAction SilentlyContinue
    }}
    if (-not @(Get-NetTCPConnection -LocalPort {port} -State Listen -ErrorAction SilentlyContinue)) {{
        exit 0
    }}
    Start-Sleep -Milliseconds 100
}} while ((Get-Date) -lt $deadline)
Write-Error "Port {port} is still in use."
exit 1
"""
    result=subprocess.run(
        ["powershell.exe","-NoProfile","-NonInteractive","-Command",command],
        capture_output=True,text=True
    )
    if result.returncode:
        detail=(result.stderr or result.stdout).strip()
        raise RuntimeError(f"Could not clear port {port}: {detail}")


def make_tray_icon():
    from PIL import Image
    path = resource_path(os.path.join("assets", "tray-icon.png"))
    return Image.open(path).convert("RGBA").resize(
        (64, 64), Image.Resampling.LANCZOS
    )

def run_flask():
    app.run(host="127.0.0.1", port=PORT, debug=False, use_reloader=False)

if __name__ == "__main__":
    # Packaged EXE behaviour is unchanged:
    # - reclaim the fixed port
    # - run the tray application
    #
    # Local .py behaviour:
    # - reclaim the fixed port before starting Flask
    # - do not require pystray/Pillow or the packaged tray asset
    # - start Flask and open the browser directly
    if getattr(sys, "frozen", False):
        clear_port_windows(PORT)

        flask_thread = threading.Thread(target=run_flask, daemon=True)
        flask_thread.start()

        try:
            import pystray
            from PIL import Image as _Img

            def on_open(icon, item):
                webbrowser.open(f'http://localhost:{PORT}')

            def on_quit(icon, item):
                icon.stop()
                sys.exit(0)

            menu = pystray.Menu(
                pystray.MenuItem('Open Dependency Map', on_open, default=True),
                pystray.Menu.SEPARATOR,
                pystray.MenuItem('Quit', on_quit),
            )

            tray = pystray.Icon(
                'jira-dependency-map',
                make_tray_icon(),
                'Jira Dependency Map',
                menu
            )

            if os.environ.get('JIRA_DEP_MAP_RESTART') != '1':
                threading.Timer(
                    0.8,
                    lambda: webbrowser.open(f'http://localhost:{PORT}')
                ).start()

            print(f'Jira Dependency Map -> http://localhost:{PORT}')
            tray.run()

        except ImportError:
            print('  pystray / Pillow not found - running in terminal mode.')
            print(f'  Starting -> http://localhost:{PORT}')
            if os.environ.get('JIRA_DEP_MAP_RESTART') != '1':
                webbrowser.open(f'http://localhost:{PORT}')
            try:
                flask_thread.join()
            except KeyboardInterrupt:
                print('\n  Stopped.')
                sys.exit(0)

    else:
        # Local Python development mode.
        # Reclaim the fixed port just like the packaged application so an
        # existing local instance cannot prevent this copy from starting.
        # Keep the tray application behaviour completely separate.
        clear_port_windows(PORT)

        flask_thread = threading.Thread(target=run_flask, daemon=True)
        flask_thread.start()

        print(f'Jira Dependency Map -> http://localhost:{PORT}')

        if os.environ.get('JIRA_DEP_MAP_RESTART') != '1':
            threading.Timer(
                0.8,
                lambda: webbrowser.open(f'http://localhost:{PORT}')
            ).start()

        try:
            flask_thread.join()
        except KeyboardInterrupt:
            print('\n  Stopped.')
            sys.exit(0)
