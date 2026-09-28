#!/usr/bin/env python3
"""Jira Dependency Map — standalone Flask application."""
import subprocess,sys,time,threading,webbrowser,os,base64,json,ctypes
from collections import defaultdict,deque
import requests as req
from flask import Flask,Response,jsonify,request

JIRA_BASE_URL="https://uow-idg.atlassian.net"
JQL_QUERY="project IN (OPD, WT) AND status NOT IN (Epics, Component) AND issuetype != Epic AND issuetype NOT IN subTaskIssueTypes()"
PORT=5001

# GitHub Actions patches APP_VERSION during the build. Updates are installed
# by jira_dependency_map_launcher.py, never by the running application.
APP_VERSION="1.0.0"
GITHUB_REPO=os.environ.get("JIRA_DEP_MAP_GITHUB_REPO","EdyerWarwick/jira-dependencies-map")

# Credentials are stored in the current Windows user's Credential Manager.
# Nothing sensitive is embedded in this source file or sent to the browser.
CREDENTIAL_TARGET="Jira Dependency Map"
CRED_TYPE_GENERIC=1
CRED_PERSIST_LOCAL_MACHINE=2

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

def jira_fetch_all_issues():
    url=f"{JIRA_BASE_URL}/rest/api/3/search/jql"
    # parent = next-gen epic; customfield_10014 = classic epic link (optional — ignored if absent)
    fields=["summary","status","priority","assignee","issuelinks","parent","customfield_10014","labels"]
    all_issues=[]; token=None; page=0
    while True:
        page+=1; body={"jql":JQL_QUERY,"maxResults":100,"fields":fields}
        if token: body["nextPageToken"]=token
        print(f"  -> Jira page {page} (have {len(all_issues):,} so far)")
        started=time.time(); resp=req.post(url,headers=get_jira_headers(),json=body,timeout=60)
        print(f"  <- HTTP {resp.status_code} ({len(resp.content):,} bytes, {time.time()-started:.2f}s)")
        if not resp.ok: raise RuntimeError(f"Jira API {resp.status_code}: {jira_error(resp)}")
        data=resp.json(); batch=data.get("issues",[]); all_issues.extend(batch); token=data.get("nextPageToken")
        if not token or not batch: break
    print(f"  OK fetched {len(all_issues):,} issues")
    return all_issues

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

def serialize_graph(raw):
    issues,edges=parse_dependency_graph(raw); levels,cycles=calculate_levels(issues,edges); out=[]
    for k,v in issues.items():
        out.append({
            "key":k,"summary":v["summary"],"status":v["status"],"priority":v["priority"],"assignee":v.get("assignee") or "Unassigned","assigneeAccountId":v.get("assigneeAccountId"),
            "labels":v.get("labels") or [],
            "epic":v.get("epic"),"url":v["url"],
            "blockers":sorted(v["blockers"]),"blocked":sorted(v["blocked"]),
            "externalBlockers":sorted(v["externalBlockers"],key=lambda x:x["key"]),
            "level":levels.get(k,0),"cycle":k in cycles
        })
    out.sort(key=lambda x:(x["level"],x["key"]))
    return {"issues":out,"edges":[{"from":a,"to":b} for a,b in sorted(edges)],
            "levels":max((i["level"] for i in out),default=0),
            "cycleKeys":sorted(cycles),"total":len(out),"jql":JQL_QUERY}

# ---------------------------------------------------------------------------
# Flask routes
# ---------------------------------------------------------------------------

@app.route("/api/dependencies")
def api_dependencies():
    try: return jsonify(serialize_graph(jira_fetch_all_issues()))
    except RuntimeError as e: return jsonify({"error":str(e)}),502
    except Exception as e: return jsonify({"error":f"Unexpected error: {e}"}),500

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

@app.route("/api/app-version")
def api_app_version():
    result={
        "current":APP_VERSION,
        "latest":APP_VERSION,
        "updateAvailable":False,
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

@app.route("/api/update-health")
def api_update_health():
    return jsonify({"ok":True,"version":APP_VERSION,"pid":os.getpid()})


@app.route("/api/config")
def api_config(): return jsonify({"jiraBaseUrl":JIRA_BASE_URL,"port":PORT,"jql":JQL_QUERY})

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
.brand{display:flex;align-items:center;gap:9px;font-weight:700;flex-shrink:0}
.brand-icon{font-size:20px}
.brand small{display:block;font-size:11px;color:#94a3b8;font-weight:400;margin-top:1px}
.header-center{flex:1;display:flex;justify-content:center}
.search-wrap{width:100%;max-width:360px;position:relative}
.search-wrap svg{position:absolute;left:10px;top:50%;transform:translateY(-50%);pointer-events:none;opacity:.45}
#search{
  width:100%;background:rgba(255,255,255,.1);border:1px solid rgba(255,255,255,.2);
  color:#fff;border-radius:7px;padding:7px 30px 7px 32px;font-size:13px;
  outline:none;transition:background .15s,border-color .15s;
}
#search:focus{background:rgba(255,255,255,.16);border-color:rgba(255,255,255,.45)}
#search::placeholder{color:rgba(255,255,255,.38)}
#search-clear{
  position:absolute;right:9px;top:50%;transform:translateY(-50%);
  background:none;border:none;color:rgba(255,255,255,.5);cursor:pointer;
  font-size:15px;line-height:1;padding:2px;display:none;
}
#search-clear.visible{display:block}
.header-actions{display:flex;align-items:center;gap:8px;flex-shrink:0}
.btn{
  border:1px solid rgba(255,255,255,.15);background:rgba(255,255,255,.08);
  color:#e2e8f0;border-radius:7px;padding:7px 11px;cursor:pointer;font-size:13px;
  transition:background .12s;display:inline-flex;align-items:center;gap:5px;
}
.btn:hover{background:rgba(255,255,255,.17)}
.btn-save{font-weight:800;min-width:96px}
.btn-save.unsaved{background:#f59e0b;color:#172033;border-color:#fbbf24;box-shadow:0 0 0 2px rgba(245,158,11,.25);opacity:1}
.btn-save:disabled{opacity:.45;cursor:default}
#save-state{font-size:10px;color:#94a3b8;white-space:nowrap;min-width:92px}
#save-state.unsaved{color:#fbbf24;font-weight:800}
#save-state:not(.unsaved){color:#94a3b8}
.header-divider{width:1px;height:22px;background:#334155;opacity:.45;margin:0 2px}
.btn-refresh{min-width:32px;padding-left:8px;padding-right:8px;font-size:16px}
.btn-settings{min-width:32px;width:32px;height:32px;padding:0;justify-content:center;font-size:18px;color:#cbd5e1}
.btn-settings:hover{color:#fff}
#save-state.unsaved{color:#fbbf24;font-weight:800}
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
#board.milestone-board{display:block;width:max-content;min-width:100%;}
#board.milestone-board #lines{display:none!important}
.milestone-overview{width:max-content;min-width:100%;padding:0 0 70px;display:flex;flex-direction:column;gap:18px}
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
.milestone-blocked-list{display:flex;flex-direction:column;gap:4px}
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
.milestone-blocked-item{display:block;width:100%;border:1px solid #e2e8f0;border-radius:5px;background:#f8fafc;padding:5px 7px;text-align:left;cursor:pointer;font-size:10px;line-height:1.3;color:#475569;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
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
#status-text{font-size:12px;color:#94a3b8;white-space:nowrap}

/* ── Jira ticket preview modal ─────────────────────────────────────────── */
.ticket-preview-backdrop{
  position:fixed;inset:0;z-index:10009;
  background:rgba(15,23,42,.22);
}
.ticket-preview-modal{
  position:fixed;left:50%;top:50%;transform:translate(-50%,-50%);
  width:min(1600px,calc(100vw - 48px));height:min(760px,calc(100vh - 48px));
  z-index:10010;display:flex;flex-direction:column;overflow:hidden;resize:none;
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

/* ── App shell ───────────────────────────────────────────────────────────── */
#app{height:calc(100vh - 58px);overflow-x:auto;overflow-y:hidden;position:relative}
#app.locked{overflow-y:auto}
#app.milestone-mode{overflow-x:auto;overflow-y:auto}
#board{
  min-width:max-content;position:relative;
  padding:26px 28px 80px;display:flex;gap:42px;align-items:flex-start;
}
#lines{position:absolute;inset:0;pointer-events:none;z-index:1;overflow:visible}

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
  position:fixed;inset:58px 0 0;background:rgba(241,245,249,.9);
  backdrop-filter:blur(4px);display:flex;flex-direction:column;
  align-items:center;justify-content:center;gap:12px;
  z-index:100;opacity:0;pointer-events:none;transition:opacity .15s;
}
#loading.show{opacity:1;pointer-events:auto}
.spinner{
  width:34px;height:34px;border:3px solid #cbd5e1;
  border-top-color:var(--accent);border-radius:50%;
  animation:spin .7s linear infinite;
}
@keyframes spin{to{transform:rotate(360deg)}}
#loading-label{font-size:13px;color:#475569}
#loading-stage{font-size:11px;color:#94a3b8;min-width:48px;text-align:center}
.loading-progress{width:220px;height:4px;background:#e2e8f0;border-radius:999px;overflow:hidden}
#loading-progress-bar{height:100%;width:10%;background:var(--accent);border-radius:999px;transition:width .2s ease}

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


/* ── Settings ───────────────────────────────────────────────────────────── */
#settings-modal{display:none;position:fixed;inset:0;background:rgba(15,23,42,.52);backdrop-filter:blur(2px);z-index:10040;align-items:center;justify-content:center;padding:16px}
#settings-modal.open{display:flex}
.settings-card{width:min(480px,calc(100vw - 32px));background:#fff;border-radius:14px;box-shadow:0 24px 70px rgba(15,23,42,.28);padding:22px}
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
.settings-actions{display:flex;justify-content:flex-end;gap:8px;margin-top:16px}
/* ── Credential setup / management ───────────────────────────────────────── */
#credential-modal{
  display:none;position:fixed;inset:0;background:rgba(15,23,42,.68);
  backdrop-filter:blur(4px);z-index:10050;align-items:center;justify-content:center;padding:20px;
}
#credential-modal.open{display:flex}
.credential-card{
  width:min(460px,calc(100vw - 32px));background:#fff;border-radius:14px;
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
.credential-primary{
  border:0;background:#6366f1;color:#fff;border-radius:7px;padding:9px 14px;
  font-weight:800;cursor:pointer;
}
.credential-primary:hover{background:#4f46e5}
.credential-danger{
  border:1px solid #fecaca;background:#fff;color:#b91c1c;border-radius:7px;
  padding:9px 14px;font-weight:700;cursor:pointer;margin-right:auto;
}
.credential-danger:hover{background:#fef2f2}
.credential-secondary{
  border:1px solid #cbd5e1;background:#fff;color:#334155;border-radius:7px;
  padding:9px 14px;cursor:pointer;
}
.credential-error{display:none;background:#fef2f2;border:1px solid #fecaca;color:#991b1b;border-radius:7px;padding:9px 10px;font-size:11px;line-height:1.4;margin-bottom:12px}
.credential-error.visible{display:block}
.credential-status{font-size:10px;color:#64748b;margin-top:8px;min-height:14px}
</style>
</head>
<body>

<div id="settings-modal" role="dialog" aria-modal="true" aria-labelledby="settings-title">
  <div class="settings-card">
    <div class="settings-head">
      <h2 id="settings-title">Settings</h2>
      <button class="modal-close" id="settings-close" type="button" aria-label="Close">×</button>
    </div>
    <div class="settings-section">
      <div class="settings-section-title">Jira account login</div>
      <div class="settings-credential-row">
        <div class="settings-credential-info">Stored credential<br><span class="settings-credential-email" id="settings-email">Not configured</span></div>
        <button class="modal-secondary" id="settings-manage-credential" type="button">Manage credential</button>
      </div>
    </div>
    <div class="settings-section">
      <div class="settings-section-title">Application</div>
      <div class="settings-version-row">
        <div class="settings-version-info">Current version <span class="settings-version-value" id="settings-current-version">Checking…</span><div class="settings-version-status" id="settings-latest-version">Checking latest release…</div></div>
        <a class="settings-version-link" id="settings-release-link" href="https://github.com/EdyerWarwick/jira-dependencies-map/releases/latest" target="_blank" rel="noopener">View release</a>
      </div>
    </div>
    <div class="settings-actions">
      <button class="modal-secondary" id="settings-close-bottom" type="button">Close</button>
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
    <div class="credential-note">The API key is converted to Jira's base64 Basic Authentication value only in memory when a Jira request is made. It is never written into the Python source or sent to the browser.</div>
    <div class="credential-status" id="credential-status"></div>
    <div class="credential-actions">
      <button class="credential-danger" id="credential-remove" type="button" style="display:none">Remove credential &amp; restart</button>
      <button class="credential-secondary" id="credential-cancel" type="button" style="display:none">Cancel</button>
      <button class="credential-primary" id="credential-save" type="button">Save &amp; connect</button>
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
  <div class="brand">
    <span class="brand-icon">&#x2197;</span>
    <div>Jira Dependency Map<small>Web Evolution dependencies</small></div>
  </div>

  <div class="header-center">
    <!-- Search is shown only when nothing is locked -->
    <div class="search-wrap" id="search-wrap">
      <svg width="14" height="14" viewBox="0 0 24 24" fill="none"
           stroke="currentColor" stroke-width="2.5" stroke-linecap="round" stroke-linejoin="round">
        <circle cx="11" cy="11" r="8"/><path d="m21 21-4.35-4.35"/>
      </svg>
      <input id="search" type="search"
             placeholder="Search key, summary or epic&hellip;" autocomplete="off" spellcheck="false">
      <button id="search-clear" title="Clear (Esc)">&#x2715;</button>
    </div>
  </div>

  <div class="header-actions">
    <span id="status-text">Loading&hellip;</span>
    <button class="btn" id="deselect">&#x2190; Back</button>
<button type="button" class="btn" data-action="escape" title="Clear the current selection and highlight lock">Esc</button>
    <span id="save-state">&#10003; All changes saved</span>
    <button class="btn btn-save" id="save" disabled>SAVE (0)</button>
    <span class="header-divider" aria-hidden="true"></span>
    <button class="btn btn-toggle-completed" id="toggle-completed" title="Toggle visibility of Done / Completed tickets">
      <span class="toggle-track"></span>Completed
    </button>
    <button class="btn btn-toggle-milestones" id="toggle-milestones" title="View milestone overview">
      View Milestones
    </button>
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
<div id="loading"><div class="spinner"></div><div id="loading-stage">1 of 10</div><div class="loading-progress"><div id="loading-progress-bar"></div></div><div id="loading-label">Connecting to Jira&hellip;</div></div>
<div id="app"><main id="board"><svg id="lines" aria-hidden="true"></svg></main></div>


<script>
// ── State ────────────────────────────────────────────────────────────────
const CFG = {jiraBaseUrl: 'https://uow-idg.atlassian.net'};

const state = {
  issues:[], edges:[], levels:0,
  lockedKey:null,
  selectionHistory:[],
  showBlocked:false,
  // Each entry: { source, target, action:'add'|'delete' }
  pendingChanges:[],
  history:[],
  redoHistory:[],
  historyApplying:false,
  showCompleted:false,          // toggle: OFF by default (done/completed hidden)
  showMilestones:false,         // toggle: OFF by default; milestone overview
  displayIssues:[], displayEdges:[], displayLevels:0,
  hoverKey:null, hoverLockKey:null,
  returnMilestoneKey:null
};

// ── DOM refs ─────────────────────────────────────────────────────────────
const board              = document.getElementById('board');
const lines              = document.getElementById('lines');
const loading            = document.getElementById('loading');
const statusText         = document.getElementById('status-text');
const errorEl            = document.getElementById('error');
const searchWrap         = document.getElementById('search-wrap');
const searchEl           = document.getElementById('search');
const searchClear        = document.getElementById('search-clear');
const deselectBtn        = document.getElementById('deselect');
const toggleCompletedBtn = document.getElementById('toggle-completed');
const toggleMilestonesBtn = document.getElementById('toggle-milestones');
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
const settingsClose = document.getElementById('settings-close');
const settingsCloseBottom = document.getElementById('settings-close-bottom');

let loadingTimer = null;
let loadingStageNo = 1;
const loadingStages = [
  'Connecting to Jira…',
  'Authenticating…',
  'Requesting tickets…',
  'Fetching Jira data…',
  'Reading ticket details…',
  'Building dependencies…',
  'Calculating levels…',
  'Preparing the board…',
  'Rendering tickets…',
  'Ready'
];


// ── Settings ───────────────────────────────────────────────────────────────
function closeSettings(){ settingsModal.classList.remove('open'); }
async function openSettings(){
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
function setLoading(on, msg){
  loading.classList.toggle('show', on);
  if(on){
    if(loadingTimer) clearInterval(loadingTimer);
    loadingStageNo = 1;
    loadingStage.textContent = '1 of 10';
    loadingProgressBar.style.width = '10%';
    document.getElementById('loading-label').textContent = msg || loadingStages[0];
  }else{
    if(loadingTimer) clearInterval(loadingTimer);
    loadingTimer = null;
  }
}
function startLoadingStages(msg){
  setLoading(true, msg || loadingStages[0]);
  loadingTimer = setInterval(() => {
    if(loadingStageNo >= 9) return;
    loadingStageNo += 1;
    loadingStage.textContent = loadingStageNo + ' of 10';
    loadingProgressBar.style.width = (loadingStageNo * 10) + '%';
    document.getElementById('loading-label').textContent = loadingStages[loadingStageNo - 1];
  }, 350);
}
function finishLoadingStages(){
  if(loadingTimer) clearInterval(loadingTimer);
  loadingTimer = null;
  loadingStageNo = 10;
  loadingStage.textContent = '10 of 10';
  loadingProgressBar.style.width = '100%';
  document.getElementById('loading-label').textContent = loadingStages[9];
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
  let visibleTotal = 0;

  cards.forEach(card => {
    const haystack = normaliseSearch(card.dataset.searchIndex || '');
    const match = !words.length || words.every(word => haystack.includes(word));
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

    // While searching, hide entire dependency levels that contain no matches.
    // This keeps matching levels adjacent so users do not have to horizontally
    // scroll through empty columns (e.g. matches in Level 3 and Level 5 only).
    // When the search is cleared, restore all columns.
    col.style.display = words.length && count === 0 ? 'none' : '';
  });

  searchClear.classList.toggle('visible', !!words.length && !state.lockedKey);
  statusText.textContent = words.length
    ? visibleTotal.toLocaleString('en-GB') + ' of ' + state.displayIssues.length.toLocaleString('en-GB') + ' tickets match'
    : state.displayIssues.length.toLocaleString('en-GB') + ' tickets · ' + state.displayEdges.length.toLocaleString('en-GB') + ' dependencies';
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
function computeDisplayData(){
  const DONE = new Set(['done','completed']);
  const issues = state.showCompleted
    ? state.issues
    : state.issues.filter(i => !DONE.has((i.status || '').toLowerCase().trim()));

  const issueKeys = new Set(issues.map(i => i.key));

  // Keep only edges where both endpoints are visible
  const edges = state.edges.filter(e => issueKeys.has(e.from) && issueKeys.has(e.to));

  // Recalculate levels for this visible subset (BFS / relaxation)
  const level = new Map(issues.map(i => [i.key, (i.externalBlockers && i.externalBlockers.length) ? 1 : 0]));
  for(let pass = 0; pass < issues.length; pass++){
    let changed = false;
    for(const e of edges){
      if(!level.has(e.from) || !level.has(e.to)) continue;
      const v = level.get(e.from) + 1;
      if(v > level.get(e.to)){ level.set(e.to, v); changed = true; }
    }
    if(!changed) break;
  }

  // Build display copies with recalculated level
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
    if(card) card.classList.toggle('highlight-locked', active);

    btn.classList.toggle('active', active);
    btn.textContent = active ? '🔒' : '🔓';
    btn.title = active ? 'Unlock highlight' : 'Lock highlight to this chain';
    btn.setAttribute('aria-label', btn.title);
  });
}

// ── Save button ───────────────────────────────────────────────────────────
function updateSaveButton(){
  const b = document.getElementById('save'); if(!b) return;
  const n = state.pendingChanges.length;
  b.textContent = n ? 'SAVE (' + n + ')' : 'SAVE (0)';
  b.disabled = n === 0;
  b.classList.toggle('unsaved', n > 0);
  const indicator = document.getElementById('save-state');
  if(indicator){
    indicator.textContent = n ? '● ' + n + ' unsaved change' + (n === 1 ? '' : 's') : 'All changes saved';
    indicator.classList.toggle('unsaved', n > 0);
  }
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
  const oldValue = field === 'assignee' ? (issue.assigneeAccountId || null) : issue.priority;
  if(oldValue === (value || null)) return;
  pushHistory();
  const display = state.displayIssues.find(i => i.key === key);
  if(field === 'assignee'){
    const opt = [...document.querySelectorAll('.assignee-select')].find(s => s.closest('.card')?.dataset.key === key);
    const name = opt && opt.selectedOptions[0] ? opt.selectedOptions[0].textContent : 'Unassigned';
    issue.assigneeAccountId = value || null;
    issue.assignee = name;
    if(display){ display.assigneeAccountId = value || null; display.assignee = name; }
  }else if(field === 'priority'){
    issue.priority = value;
    if(display) display.priority = value;
  }
  const existing = state.pendingChanges.find(c => c.action === 'update' && c.key === key);
  if(existing) existing[field === 'assignee' ? 'assigneeAccountId' : 'priority'] = value || null;
  else state.pendingChanges.push(Object.assign({action:'update',key}, field === 'assignee' ? {assigneeAccountId:value || null} : {priority:value}));
  updateSaveButton();
}

async function saveChanges(){
  if(!state.pendingChanges.length) return;
  const changes = [...state.pendingChanges];
  const adds    = changes.filter(c => c.action === 'add');
  const deletes = changes.filter(c => c.action === 'delete');
  const updates = changes.filter(c => c.action === 'update');
  setLoading(true, 'Saving changes to Jira\u2026'); hideError();
  try{
    // ── Save issue field updates ──
    if(updates.length){
      const r = await fetch('/api/issues', {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify({changes:updates})});
      const d = await r.json().catch(() => ({}));
      if(!r.ok) throw new Error(d.error || 'HTTP ' + r.status);
    }
    // ── Save additions ──
    if(adds.length){
      const r = await fetch('/api/links', {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify({links:adds})});
      const d = await r.json().catch(() => ({}));
      if(!r.ok) throw new Error(d.error || 'HTTP ' + r.status);
    }
    // ── Save deletions (sequential so each error can be surfaced) ──
    for(const del of deletes){
      const r = await fetch('/api/unlink', {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify({source:del.source, target:del.target})});
      const d = await r.json().catch(() => ({}));
      if(!r.ok) throw new Error(d.error || 'HTTP ' + r.status);
    }
    state.pendingChanges = [];
    state.history = [];
    state.redoHistory = [];
    updateSaveButton();
    render();
  }catch(e){ showError(e.message || String(e)); }
  finally{ setLoading(false); }
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
  const blockedBy = (i.blockers || []).filter(k => !visible || visible.has(k)).sort();
  const external = (i.externalBlockers || []).filter(x => !visible || i.key === state.lockedKey).sort((a,b) => a.key.localeCompare(b.key));
  const blocks = (i.blocked || []).slice().sort();

  function keyItem(k, direction, extraCls){
    const x = state.issues.find(v => v.key === k);
    const cls = extraCls || 'relation-key';
    const issueUrl = x ? x.url : (CFG.jiraBaseUrl + '/browse/' + encodeURIComponent(k));
    const anchor = '<a class="' + cls + '" href="' + esc(issueUrl) +
      '" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="' +
      esc(k) + '">' + esc(k) + '</a>';
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
  const assigneeSelect = '<select class="assignee-select" data-field="assignee" data-stop-propagation="1" title="Change assignee"><option value="">Unassigned</option>' + assigneeOptions + '</select>';
  const prioritySelect = '<span class="priority-picker" data-stop-propagation="1" title="Change priority">'
    + '<button type="button" class="priority-trigger" data-stop-propagation="1" aria-label="Change priority" aria-haspopup="true" aria-expanded="false">' + priorityIconHtml(i.priority) + '</button>'
    + '<span class="priority-menu" role="menu">' + priorityOptions + '</span>'
    + '</span>';

  const searchIndex = buildSearchIndex(i);
  const isCompleted = isCompletedStatus(i.status);
  return '<article class="card' + (i.cycle ? ' cycle' : '') + (isExternal ? ' external' : '') + (isCompleted ? ' completed' : '') + '" data-key="' + esc(i.key) + '" data-search-index="' + esc(searchIndex) + '" data-summary="' + esc(i.summary || '') + '">'
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
    + assigneeSelect
    + relationHtml(i)
   
    + '</article>';
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
  '</article>';
}

function milestoneOverviewHtml(milestones){
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
            groups.get(level).sort((a,b) => a.key.localeCompare(b.key)).map(b =>
              '<div class="milestone-blocked-item' + (isCompletedStatus(b.status) ? ' completed' : '') +
                '" data-milestone-chain="' + esc(b.key) + '" title="' + esc(b.key + ' - ' + (b.summary || '')) + '">' +
                '<a class="milestone-blocked-key" href="' + esc(b.url || (CFG.jiraBaseUrl + '/browse/' + b.key)) +
                '" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="' +
                esc(b.key) + '">' + esc(b.key) + '</a>' +
                ' - ' + esc(b.summary || '') +
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

  // Milestone elements are rendered after the normal board event wiring.
  attachTicketKeyModalHandlers(board);

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
      state.showMilestones = false;
      state.selectionHistory = [];
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
    app.scrollLeft = 0;
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
  [...board.querySelectorAll('.column, .milestone-overview')].forEach(x => x.remove());
  board.classList.toggle('milestone-board', state.showMilestones);
  document.getElementById('app').classList.toggle('milestone-mode', state.showMilestones);
  lines.innerHTML = '';

  // Rebuild display data honoring the completed toggle
  computeDisplayData();

  // Sync toggle button appearance
  toggleCompletedBtn.classList.toggle('active', state.showCompleted);
  toggleMilestonesBtn.classList.toggle('active', state.showMilestones);

  // Milestone overview is a separate horizontal board mode. It clears selection
  // and intentionally does not render the normal dependency columns.
  if(state.showMilestones){
    state.lockedKey = null;
    state.selectionHistory = [];
    state.showBlocked = false;
    document.getElementById('app').classList.remove('locked');
    searchWrap.style.visibility = 'hidden';
    searchClear.classList.remove('visible');
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

  const locked = !!state.lockedKey;
  document.getElementById('app').classList.toggle('locked', locked);
  const searchTerm = locked ? '' : getSearch();

  // Header controls
  searchWrap.style.visibility = locked ? 'hidden' : 'visible';
  searchClear.classList.toggle('visible', !locked && !!searchTerm);
  deselectBtn.classList.toggle('visible', locked);
  if(milestoneBackBtn){
    const backMilestone = state.returnMilestoneKey ? state.displayIssues.find(i => i.key === state.returnMilestoneKey) : null;
    milestoneBackBtn.classList.toggle('visible', !!backMilestone);
    milestoneBackBtn.innerHTML = backMilestone
      ? '&#8592; Back to ' + esc(backMilestone.key + ' - ' + (backMilestone.summary || 'Milestone'))
      : '';
  }

  // Search is applied after the cards are rendered. In selected mode the
  // dependency chain is still structurally filtered as before.
  let visibleKeys = locked ? activeSelectionChain(state.lockedKey) : null;
  const visibleIssues = visibleKeys
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

  requestAnimationFrame(() => { spaceLongRoutes(); requestAnimationFrame(() => { drawLines(); attachEvents(); }); });

  // Restore search focus/caret after a genuine board rebuild (refresh, toggle,
  // selection change, etc.). Typing itself no longer rebuilds the board.
  if(searchEl && searchEl.value !== searchValue) searchEl.value = searchValue;
  if(searchWasFocused){
    searchEl.focus({preventScroll:true});
    if(searchSelectionStart != null && searchSelectionEnd != null){
      try{ searchEl.setSelectionRange(searchSelectionStart, searchSelectionEnd); }catch(_){}
    }
  }

  if(locked){
    statusText.textContent = visibleIssues.length.toLocaleString('en-GB') + ' tickets in chain · Esc to deselect';
  } else {
    applySearchFilter();
  }

}

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

function drawLines(){
  lines.innerHTML = '';

  // Dependency lines only exist while an item is selected.
  if(!state.lockedKey) return;

  const br = board.getBoundingClientRect();
  const W = Math.max(board.scrollWidth, br.width), H = Math.max(board.scrollHeight, br.height);
  if(!W || !H) return;
  lines.setAttribute('width', W); lines.setAttribute('height', H);
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
  const edges = state.displayEdges.filter(e =>
    lockedChain.has(e.from) && lockedChain.has(e.to)
  );
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

  // Each dependency is a complete individual path:
  // horizontal spoke → vertical leg → horizontal arrow.
  // No shared vertical bus is used.
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
    const routeX = nextCol
      ? ((source.getBoundingClientRect().right + nextCol.getBoundingClientRect().left) / 2) - br.left
      : s.x + 18;

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

}

// ── Dependency creation modal ─────────────────────────────────────────────
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
      e.preventDefault();
      e.stopPropagation();

      const href=link.href;
      const hrefKey=decodeURIComponent((new URL(href,window.location.href).pathname.split('/').filter(Boolean).pop() || ''));
      const key=(link.dataset.issueKey || hrefKey || link.textContent.trim()).toUpperCase();
      const issue=state.issues.find(i => i.key === key);
      const card=link.closest('.card');
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
  btn.addEventListener('click', () => {
    clearHoverLock();
    closeTicketPreviewModal();
    if(state.showBlocked || state.lockedKey){
      state.showBlocked = false;
      state.lockedKey = null;
      state.selectionHistory = [];
      state.returnMilestoneKey = null;
      render();
    }
  });
});

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
      if(state.lockedKey) state.selectionHistory.push(state.lockedKey);
      clearHoverLock();
      state.lockedKey = key;
      state.showBlocked = false;
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
      const card = select.closest('.card');
      if(!card) return;
      stageIssueChange(card.dataset.key, select.dataset.field, select.value);
    });
    select.addEventListener('click', e => e.stopPropagation());
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
        const card = picker.closest('.card');
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

  updateSaveButton();
  attachTicketKeyModalHandlers();
  updateHoverLockButtons();
}

// ── Load data ─────────────────────────────────────────────────────────────
async function load(resetSelection){
  startLoadingStages('Connecting to Jira\u2026'); hideError();
  try{
    const r = await fetch('/api/dependencies', {cache:'no-store'});
    const d = await r.json();
    if(!r.ok) throw new Error(d.error || 'HTTP ' + r.status);
    state.issues = d.issues || []; state.edges = d.edges || []; state.levels = d.levels || 0;
    // A load is a clean Jira reload. Never re-apply unsaved local changes.
    state.pendingChanges = [];
    state.history = [];
    state.redoHistory = [];
    if(resetSelection){
      state.lockedKey = null;
      state.selectionHistory = [];
      state.showBlocked = false;
    }
    render(); updateSaveButton();
    finishLoadingStages();
    await new Promise(resolve => setTimeout(resolve, 180));
  }catch(e){ showError(e.message || String(e)); statusText.textContent = 'Load failed'; }
  finally{ setLoading(false); }
}

// ── Global event wiring ───────────────────────────────────────────────────
document.addEventListener('click', closePriorityPickers);
document.getElementById('save').addEventListener('click', saveChanges);
document.getElementById('refresh').addEventListener('click', () => {
  if(state.pendingChanges.length && !confirm('Discard ' + state.pendingChanges.length + ' unsaved change' + (state.pendingChanges.length === 1 ? '' : 's') + ' and refresh from Jira?')) return;
  load(true);
});
deselectBtn.addEventListener('click', () => {
  if(state.selectionHistory.length){
    state.lockedKey = state.selectionHistory.pop();
    state.showBlocked = false;
  }else{
    state.lockedKey = null;
    state.showBlocked = false;
  }
  render();
});

toggleCompletedBtn.addEventListener('click', () => {
  state.showCompleted = !state.showCompleted;
  render();
});

milestoneBackBtn.addEventListener('click', () => {
  const key = state.returnMilestoneKey;
  if(!key) return;
  state.showMilestones = true;
  state.lockedKey = null;
  state.selectionHistory = [];
  state.showBlocked = false;
  state.milestoneFlashKey = key;
  state.returnMilestoneKey = null;
  render();
});

toggleMilestonesBtn.addEventListener('click', () => {
  state.showMilestones = !state.showMilestones;
  state.lockedKey = null;
  state.selectionHistory = [];
  state.showBlocked = false;
  state.returnMilestoneKey = null;
  if(state.showMilestones) document.getElementById('app').scrollLeft = 0;
  render();
});

searchEl.addEventListener('input', () => {
  // Never rebuild the board while typing. Filter the existing cards directly so
  // the input value and the search state cannot get out of sync.
  state.searchTerm = searchEl.value;
  applySearchFilter();
});
searchClear.addEventListener('click', () => {
  state.searchTerm = '';
  searchEl.value = '';
  applySearchFilter();
  searchEl.focus();
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
  if(e.key === 'Enter' && document.activeElement === searchEl){
    const first = [...board.querySelectorAll('.card')].find(c => !c.hidden);
    if(first){ e.preventDefault(); first.click(); }
    return;
  }
  if(e.key === 'Escape'){
    if(dependencyModal.classList.contains('open')){ closeDependencyModal(); return; }
    if(state.lockedKey){ state.lockedKey = null; state.selectionHistory = []; state.showBlocked = false; render(); }
    else if(state.searchTerm){ state.searchTerm = ''; searchEl.value = ''; applySearchFilter(); searchEl.focus(); }
  }
});


credentialSave.addEventListener('click', saveCredential);
credentialRemove.addEventListener('click', removeCredential);
credentialCancel.addEventListener('click', closeCredentialModal);
settingsBtn.addEventListener('click', openSettings);
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
  if(state.pendingChanges.length){
    e.preventDefault();
    e.returnValue = '';
  }
});

window.addEventListener('resize', () => requestAnimationFrame(drawLines));
// Do not redraw dependency SVG paths while the app scrolls. In the selected
// view the board, cards and SVG move together, so rebuilding the paths on
// every scroll frame only causes flicker.

initialiseApp();
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
    from PIL import Image, ImageDraw
    img = Image.new('RGBA', (64, 64), (0, 0, 0, 0))
    d   = ImageDraw.Draw(img)
    d.rounded_rectangle([2, 8, 62, 62], radius=8, fill='#16213e')
    d.rounded_rectangle([2, 8, 62, 26], radius=8, fill='#6366f1')
    d.rectangle([2, 17, 62, 26], fill='#6366f1')
    for rx in (15, 39):
        d.rounded_rectangle([rx, 2, rx + 9, 18], radius=3, fill='white')
    for row in range(3):
        for col in range(4):
            x, y = 10 + col * 14, 32 + row * 10
            d.ellipse([x, y, x + 5, y + 5], fill=(255, 255, 255, 180))
    return img

def run_flask():
    app.run(host="127.0.0.1", port=PORT, debug=False, use_reloader=False)

if __name__ == "__main__":
    clear_port_windows(PORT)
    flask_thread = threading.Thread(target=run_flask, daemon=True)
    flask_thread.start()
    try:
        import pystray
        from PIL import Image as _Img
        def on_open(icon, item): webbrowser.open(f'http://localhost:{PORT}')
        def on_quit(icon, item): icon.stop(); sys.exit(0)
        menu = pystray.Menu(
            pystray.MenuItem('Open Dependency Map', on_open, default=True),
            pystray.Menu.SEPARATOR,
            pystray.MenuItem('Quit', on_quit),
        )
        tray = pystray.Icon('jira-dependency-map', make_tray_icon(), 'Jira Dependency Map', menu)
        if os.environ.get('JIRA_DEP_MAP_RESTART') != '1':
            threading.Timer(0.8, lambda: webbrowser.open(f'http://localhost:{PORT}')).start()
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
