#!/usr/bin/env python3
"""Jira Dependency Map — standalone Flask application."""
import subprocess,sys,time,threading,webbrowser,os,base64,json,ctypes
from collections import defaultdict,deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from email.utils import parsedate_to_datetime
from datetime import datetime, timezone
import requests as req
from flask import Flask,Response,jsonify,request

JIRA_BATCH_SIZE=1000
# The enhanced search endpoint gives only a nextPageToken for complete issue
# records (often a 100-result limit). Ask for IDs alone, then retrieve the
# selected fields through parallel bulk requests, as recommended by Atlassian.
JIRA_ID_BATCH_SIZE=5000
JIRA_DETAIL_BATCH_SIZE=100  # links/labels require the normal bulk-fetch limit
JIRA_DETAIL_WORKERS=4
JIRA_MAX_CONCURRENT_REQUESTS=5
_jira_request_slots=threading.BoundedSemaphore(JIRA_MAX_CONCURRENT_REQUESTS)
_loading_progress={"phase":"Idle","batch":0,"fetched":0,"total":None,"detail":""}
_loading_progress_lock=threading.Lock()

def _set_loading_progress(**values):
    with _loading_progress_lock:
        _loading_progress.update(values)

def _get_loading_progress():
    with _loading_progress_lock:
        return dict(_loading_progress)

_jira_session_local=threading.local()

def _jira_session():
    """Keep-alive connections within each worker, without sharing Session state."""
    if not hasattr(_jira_session_local,"session"):
        _jira_session_local.session=req.Session()
    return _jira_session_local.session

def _jira_retry_wait(response, attempt):
    """Respect Jira's Retry-After header, with a bounded exponential fallback."""
    retry_after=response.headers.get("Retry-After", "").strip()
    if retry_after:
        try:
            return min(30.0,max(0.0,float(retry_after)))
        except ValueError:
            try:
                date=parsedate_to_datetime(retry_after)
                return min(30.0,max(0.0,(date-datetime.now(timezone.utc)).total_seconds()))
            except (TypeError,ValueError,OverflowError):
                pass
    return min(12.0, 1.5*(2**attempt))


# Background cache for the slower full/completed-ticket load. The initial board
# can render from active tickets while this cache is populated.
_completed_loads={}
_completed_loads_lock=threading.Lock()

JIRA_BASE_URL="https://uow-idg.atlassian.net"
JQL_QUERY="project IN (OPD, WT) AND status NOT IN (Epics, Component) AND issuetype != Epic AND issuetype NOT IN subTaskIssueTypes() AND parent != OPD-457"
PORT=5001
STARTUP_MESSAGES_URL="https://sitebuilder.warwick.ac.uk/sitebuilder2/api/dataentry/entries.json?page=/services/marketing/teams/cds/opd/startup/"
FAQS_URL="https://sitebuilder.warwick.ac.uk/sitebuilder2/api/dataentry/entries.json?page=/services/marketing/teams/cds/opd/jdm-faqs/"

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
    "customJql":"","useJiraModal":False,"showMiniMap":True,"startingView":"default","personalUserAccountId":"","personalUserName":"","myViewSorts":{},"dashboardTabSorts":{},
    "ganttScale":12,"ganttShowDependencies":True,"ganttNarrow":False,
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
    out["ganttScale"]=out["ganttScale"] if out["ganttScale"] in (6,12,20) and type(out["ganttScale"]) is int else 12
    out["ganttShowDependencies"]=out["ganttShowDependencies"] is not False
    out["ganttNarrow"]=out["ganttNarrow"] is True
    out["startingView"]=out["startingView"] if out["startingView"] in {"default","my-view","dashboard","milestone"} else "default"
    out["personalUserAccountId"]=str(out["personalUserAccountId"] or "")
    out["personalUserName"]=str(out["personalUserName"] or "").strip()
    valid_sort_fields={"priority","dueDate","key","summary","epic","status","blockers","blocked"}
    sort_values=out.get("myViewSorts")
    cleaned={}
    if isinstance(sort_values,dict):
        for user_id,sorting in list(sort_values.items())[:500]:
            if isinstance(user_id,str) and user_id and len(user_id)<256 and isinstance(sorting,dict):
                field=sorting.get("field")
                direction=sorting.get("direction")
                if field in valid_sort_fields and direction in {"asc","desc"}:
                    cleaned[user_id]={"field":field,"direction":direction}
    out["myViewSorts"]=cleaned
    dashboard_fields={"priority","dueDate","key","summary","epic","status","blockers","blocked","assignee","riskScore"}
    dashboard_tabs={"needs-attention","upcoming-7","upcoming-31","overdue","missing-due","unassigned","biggest-unblockers","chain-risks","circular","in-development"}
    dashboard_sorts={}
    raw_dashboard_sorts=out.get("dashboardTabSorts")
    if isinstance(raw_dashboard_sorts,dict):
        for tab, sorting in raw_dashboard_sorts.items():
            if tab in dashboard_tabs and isinstance(sorting,dict):
                field=sorting.get("field")
                direction=sorting.get("direction")
                if field in dashboard_fields and direction in {"asc","desc"}:
                    dashboard_sorts[tab]={"field":field,"direction":direction}
    out["dashboardTabSorts"]=dashboard_sorts
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
        timeout=5,
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

# Organisation-wide usage reporting: the build may bundle a tiny Python module
# named usage_collector_config.py with WEBHOOK_URL and WEBHOOK_KEY. The module is
# generated by the release workflow from GitHub Actions secrets BEFORE
# PyInstaller runs. PyInstaller's static import discovery includes it in the EXE
# automatically. There is nothing to set up on each user's Windows account.
#
# Do not commit usage_collector_config.py or its real values to a public repo.
# This is lightweight app-usage reporting, not secure identity/audit evidence:
# a distributed EXE cannot keep its embedded shared key genuinely secret.
def _usage_collector_settings():
    try:
        from usage_collector_config import WEBHOOK_URL, WEBHOOK_KEY
        bundled_url=str(WEBHOOK_URL or "").strip()
        bundled_key=str(WEBHOOK_KEY or "").strip()
        if bundled_url.startswith("https://") and bundled_key:
            return bundled_url,bundled_key,"bundled"
    except ImportError:
        pass  # Normal developer build without an organisation collector.
    except Exception as exc:
        print(f"  Usage collector config could not be loaded: {exc}")
    # Legacy local override remains optional for testing older deployments;
    # no user is required to configure environment variables.
    url=os.environ.get("JIRA_DEP_MAP_USAGE_WEBHOOK_URL", "").strip()
    key=os.environ.get("JIRA_DEP_MAP_USAGE_WEBHOOK_KEY", "").strip()
    if url.startswith("https://") and key:
        return url,key,"environment"
    return "","","disabled"

USAGE_WEBHOOK_URL,USAGE_WEBHOOK_KEY,USAGE_CONFIG_SOURCE=_usage_collector_settings()
_usage_checkins={}
_usage_checkins_lock=threading.Lock()

def _queue_usage_checkin(jira_user, credential_email):
    """Report a verified Jira user's app access without blocking the UI.

    Deduplicate openings for the same identity within a five-minute window.
    Credentials are never transmitted; a missing collector keeps this disabled.
    The collector's shared key is suitable for lightweight metrics, not a
    tamper-proof audit trail: a distributed client cannot keep a secret.
    """
    if not (USAGE_WEBHOOK_URL.startswith("https://") and USAGE_WEBHOOK_KEY):
        return
    if not isinstance(jira_user, dict):
        return
    account_id=str(jira_user.get("accountId") or "").strip()
    email=str(jira_user.get("emailAddress") or credential_email or "").strip().lower()
    if not account_id or not email:
        return
    now=time.monotonic()
    with _usage_checkins_lock:
        if now - _usage_checkins.get(account_id,-600) < 300:
            return
        _usage_checkins[account_id]=now
    event={
        "sharedKey":USAGE_WEBHOOK_KEY,
        "eventType":"app_open",
        "accountId":account_id,
        "email":email,
        "displayName":str(jira_user.get("displayName") or "").strip(),
        "appVersion":APP_VERSION,
        "observedAtUTC":datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00","Z")
    }
    def send():
        try:
            # Apps Script doPost accepts text/plain and JSON.parse(postData.contents).
            result=req.post(USAGE_WEBHOOK_URL,data=json.dumps(event),
                            headers={"Content-Type":"text/plain;charset=utf-8"},timeout=12)
            result.raise_for_status()
            payload=result.json()
            if payload.get("ok") is not True:
                raise RuntimeError("Usage collector did not accept the check-in")
        except Exception as exc:
            # A usage report must never prevent Jira work; permit a retry.
            with _usage_checkins_lock:
                if _usage_checkins.get(account_id)==now:
                    _usage_checkins.pop(account_id,None)
            print(f"  Usage check-in failed (app continues normally): {exc}")
    threading.Thread(target=send,daemon=True,name="jira-usage-checkin").start()

app=Flask(__name__)

@app.after_request
def _disable_browser_caching(response):
    """Dependency-map API data is live Jira data; never cache API responses."""
    if request.path.startswith("/api/"):
        response.headers["Cache-Control"]="no-store, no-cache, max-age=0, must-revalidate"
        response.headers["Pragma"]="no-cache"
        response.headers["Expires"]="0"
    return response

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
    # Give every Jira search request a unique URL as well as no-cache headers.
    # This prevents an intermediary/proxy from reusing an older search response.
    url=f"{JIRA_BASE_URL}/rest/api/3/search/jql"
    all_issues=[]; token=None; page=0; batch_size=JIRA_BATCH_SIZE
    _set_loading_progress(phase=f"Downloading batch {page} work items…",batch=0,fetched=0,total=None,detail="Connecting to Jira…")
    while True:
        page+=1
        body={"jql":jql,"maxResults":batch_size,"fields":fields}
        if token: body["nextPageToken"]=token
        # Cache-bust each Jira page so a manual refresh always requests fresh data.
        request_url=f"{url}?_refresh={int(time.time()*1000)}_{page}"
        _set_loading_progress(phase=f"Downloading batch {page} work items…",batch=page,fetched=len(all_issues),detail=f"Requesting batch {page}…")
        print(f"  -> Jira {label} page {page} (have {len(all_issues):,} so far; batch size {batch_size:,})")
        started=time.time()
        resp=_jira_post(request_url,body,retry_label=f"{label} search")
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


class JiraBulkFetchUnavailable(RuntimeError):
    """Bulk fetch was unsuccessful; the caller can use normal JQL pagination."""


def _jira_post(url, body, *, retry_label="Jira", timeout=60):
    """Rate-limit-aware POST, with one shared concurrency cap across workers."""
    headers=get_jira_headers()
    headers.update({"Cache-Control":"no-store, no-cache, max-age=0",
                    "Pragma":"no-cache","Expires":"0"})
    for attempt in range(4):
        with _jira_request_slots:
            response=_jira_session().post(url, headers=headers, json=body, timeout=timeout)
        if response.status_code not in (429,500,502,503,504) or attempt==3:
            return response
        pause=_jira_retry_wait(response,attempt)
        print(f"  <- {retry_label}: HTTP {response.status_code}; retry {attempt+1}/3 in {pause:.1f}s")
        time.sleep(pause)
    return response


def _jira_search_ids(jql,label):
    """Fetch matching Jira issue IDs with the fast, high-capacity index search.

    With NO 'fields' entry in the request, Jira can return up to 5,000 IDs
    per cursor page; selecting 'fields' would impose the ~100-details limit.
    The cursor must still be followed sequentially for each ID page.
    """
    url=f"{JIRA_BASE_URL}/rest/api/3/search/jql"
    token=None
    page=0
    batch_size=JIRA_ID_BATCH_SIZE
    ids=[]
    seen=set()
    seen_tokens=set()
    while True:
        page+=1
        body={"jql":jql,"maxResults":batch_size}
        if token: body["nextPageToken"]=token
        request_url=f"{url}?_refresh={time.time_ns()}_{page}"
        _set_loading_progress(phase=f"Finding {label} ticket IDs…",batch=page,
                              fetched=len(ids),total=None,
                              detail=f"Finding ticket IDs (index page {page})…")
        started=time.perf_counter()
        resp=_jira_post(request_url,body,retry_label=f"{label} ID search")
        if resp.status_code==400 and batch_size!=100:
            # Some Jira sites cap even lightweight JQL searches. Never skip a
            # page just because the requested maximum was not accepted.
            batch_size=100
            page-=1
            continue
        if not resp.ok:
            raise RuntimeError(f"Jira ID search API {resp.status_code}: {jira_error(resp)}")
        data=resp.json()
        batch=data.get("issues")
        if not isinstance(batch,list):
            raise RuntimeError("Jira ID search did not return an issues list.")
        for issue in batch:
            issue_id=str((issue or {}).get("id") or "").strip()
            if not issue_id:
                raise RuntimeError("Jira ID search returned an issue without an ID.")
            if issue_id not in seen:
                seen.add(issue_id)
                ids.append(issue_id)
        print(f"  <- Jira {label} IDs page {page}: {len(batch):,} IDs "
              f"(total {len(ids):,}, {time.perf_counter()-started:.2f}s)")
        token=data.get("nextPageToken")
        if not token or data.get("isLast") is True:
            break
        if token in seen_tokens:
            raise RuntimeError("Jira returned a repeated ID-page cursor; stopping to prevent missing tickets.")
        seen_tokens.add(token)
    return ids


def _jira_bulk_issue_chunk(ids,fields,label):
    """Fetch precisely these issues (including dependency links) in one call."""
    url=f"{JIRA_BASE_URL}/rest/api/3/issue/bulkfetch"
    body={"issueIdsOrKeys":ids,"fields":fields}
    started=time.perf_counter()
    resp=_jira_post(url,body,retry_label=f"{label} bulk details")
    if not resp.ok:
        raise JiraBulkFetchUnavailable(
            f"HTTP {resp.status_code}: {jira_error(resp)}")
    data=resp.json()
    batch=data.get("issues")
    errors=data.get("issueErrors") or []
    if not isinstance(batch,list) or errors:
        raise JiraBulkFetchUnavailable(f"Invalid/partial Jira bulk result: {errors}")
    returned_ids={str(issue.get("id") or "") for issue in batch}
    if returned_ids != set(ids) or len(batch)!=len(ids):
        # Issues can disappear/change permissions between the ID snapshot and
        # bulk lookup. Re-run normal search instead of silently dropping any.
        raise JiraBulkFetchUnavailable(
            f"Requested {len(ids)} IDs but received {len(batch)} complete issues")
    print(f"  <- Jira {label} bulk: {len(batch):,} details "
          f"({time.perf_counter()-started:.2f}s)")
    return batch


def _jira_search_parallel(jql,fields,label):
    """Index scan + bounded concurrent bulk details, with safe fallback.

    Cursor pages are never requested concurrently. Once all the independent
    issue IDs are known, details are fetched in parallel. The output has the
    exact same Jira issue structure expected by dependency parsing.
    """
    started=time.perf_counter()
    try:
        ids=_jira_search_ids(jql,label)
    except Exception as exc:
        print(f"  Jira {label}: fast ID search failed ({exc}); using normal pagination")
        return _jira_search(jql,fields,label)

    if not ids:
        _set_loading_progress(phase=f"Downloaded {label} work items", batch=0,
                              fetched=0,total=0,detail="No matching tickets")
        return []

    id_seconds=time.perf_counter()-started
    chunks=[ids[i:i+JIRA_DETAIL_BATCH_SIZE]
            for i in range(0,len(ids),JIRA_DETAIL_BATCH_SIZE)]
    print(f"  Jira {label}: {len(ids):,} matching IDs found in {id_seconds:.2f}s; "
          f"fetching {len(chunks):,} independent detail batches with "
          f"{min(JIRA_DETAIL_WORKERS,len(chunks))} workers")
    _set_loading_progress(phase=f"Downloading {label} ticket details…",batch=0,
                          fetched=0,total=len(ids),
                          detail=f"0 of {len(ids):,} tickets; {len(chunks)} parallel batches")
    fetched=0
    completed_batches=0
    results=[None]*len(chunks)
    try:
        with ThreadPoolExecutor(max_workers=min(JIRA_DETAIL_WORKERS,len(chunks)),
                                thread_name_prefix="jira-bulk") as pool:
            future_map={pool.submit(_jira_bulk_issue_chunk,chunk,fields,label):n
                        for n,chunk in enumerate(chunks)}
            for future in as_completed(future_map):
                index=future_map[future]
                result=future.result()
                results[index]=result
                fetched+=len(result)
                completed_batches+=1
                _set_loading_progress(phase=f"Downloading {label} ticket details…",
                                      batch=completed_batches,fetched=fetched,
                                      total=len(ids),
                                      detail=f"{fetched:,} of {len(ids):,} tickets "
                                             f"({completed_batches}/{len(chunks)} batches)")
    except Exception as exc:
        print(f"  Jira {label}: parallel bulk fetch failed ({exc}); "
              "reloading from sequential JQL to preserve all tickets")
        return _jira_search(jql,fields,label)
    issues=[issue for group in results for issue in group]
    if len(issues)!=len(ids):
        print(f"  Jira {label}: count mismatch; retrying via normal pagination")
        return _jira_search(jql,fields,label)
    _set_loading_progress(phase=f"Downloaded {label} work items",
                          batch=len(chunks),fetched=len(issues),total=len(issues),
                          detail=f"{len(issues):,} work items downloaded")
    print(f"  OK {label}: {len(issues):,} issues in "
          f"{time.perf_counter()-started:.2f}s "
          f"(ID search {id_seconds:.2f}s, details "
          f"{time.perf_counter()-started-id_seconds:.2f}s)")
    return issues

# These statuses are intentionally excluded from the dependency map. A link
# to one must not be represented as an external, unresolved blocker.
EXCLUDED_ISSUE_STATUSES={"cancelled","canceled","archived"}


def _block_link(source, link):
    """Return (blocker, blocked, linked_blocker_status) for a Jira Blocks link.

    Jira supplies either outwardIssue or inwardIssue relative to `source`.
    The inward linked issue can include a status even if Jira's search endpoint
    does not return the full linked issue (e.g. out-of-scope/permission cases).
    """
    link=link or {}
    relation=link.get("type") or {}
    outward=link.get("outwardIssue") or {}
    inward=link.get("inwardIssue") or {}
    source=str(source or "").strip()
    if not source:
        return None
    if str(relation.get("outward") or "").strip().lower()=="blocks" and outward.get("key"):
        blocker,blocked=source,str(outward["key"]).strip()
        linked_status=None
    elif str(relation.get("inward") or "").strip().lower()=="is blocked by" and inward.get("key"):
        blocker,blocked=str(inward["key"]).strip(),source
        linked_status=(inward.get("fields") or {}).get("status")
    else:
        return None
    if not blocker or not blocked or blocker==blocked:
        return None
    return blocker,blocked,linked_status


def _nonblocking_external_status(status):
    """A known inactive/finished linked issue cannot be an *active external* blocker.

    Only applies to issues missing from the loaded raw data. Known issues retain
    their real historical links and completed visibility in the normal graph.
    """
    if not isinstance(status,dict):
        return False
    name=str(status.get("name") or "").strip().lower()
    category=status.get("statusCategory") or {}
    category_key=str(category.get("key") or "").strip().lower() if isinstance(category,dict) else ""
    return (name in EXCLUDED_ISSUE_STATUSES or name in {"done","completed","resolved","closed"}
            or category_key=="done")


def _external_blocker_keys(raw_issues):
    """Return linked blockers missing from the current fetch for a follow-up lookup."""
    in_scope={str(r.get("key") or "").strip() for r in raw_issues if r.get("key")}
    external=set()
    for r in raw_issues:
        source=str(r.get("key") or "").strip()
        if source not in in_scope: continue
        for link in (r.get("fields") or {}).get("issuelinks") or []:
            pair=_block_link(source,link)
            if not pair: continue
            blocker,blocked,_status=pair
            if blocker not in in_scope and blocked in in_scope:
                # Still fetch completed linked tickets so historical relations
                # can be shown when the user enables Show completed.
                external.add(blocker)
    return sorted(external)

def jira_fetch_external_issues(raw_issues, include_completed=True, known_issues=()):
    """Recursively fetch external blockers until no new blocker keys are found."""
    fields=_base_issue_fields()
    # Jira can impose a limit on the number of values in an IN clause. Keep the
    # normal case to one JQL request, and only split unusually large sets.
    chunk_size=250

    # Completed fetches may reference already downloaded active blockers. Do not
    # request those issues again; their own ancestors were explored in the first pass.
    known={str(r.get("key")).strip() for r in raw_issues if r.get("key")}
    known.update(str(r.get("key")).strip() for r in known_issues if r.get("key"))
    pending=set(_external_blocker_keys(raw_issues)) - known
    fetched=[]
    round_no=0

    while pending:
        round_no += 1
        current=sorted(pending)
        pending.clear()
        print(f"  External blockers: round {round_no}, {len(current):,} new ticket(s) to fetch")

        chunks=[current[start:start+chunk_size] for start in range(0,len(current),chunk_size)]
        def fetch_chunk(chunk):
            key_list=", ".join(chunk)
            jql=f"key in ({key_list})"
            if not include_completed:
                jql=f"({jql}) AND statusCategory != Done"
            print(f"  External blockers: requesting {len(chunk):,} ticket(s) in one JQL")
            return _jira_search(jql,fields,"external blocker")
        # Only independent key groups are parallel. Jira's nextPageToken pages
        # remain strictly sequential; cap concurrency to respect Cloud rate limits.
        if len(chunks)==1:
            results=[fetch_chunk(chunks[0])]
        else:
            with ThreadPoolExecutor(max_workers=min(3,len(chunks)),thread_name_prefix="jira-external") as executor:
                results=list(executor.map(fetch_chunk,chunks))
        round_fetched=[issue for result in results for issue in result]

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

_jira_schedule_fields_lock=threading.Lock()
_jira_schedule_fields_cache=None

def _jira_schedule_fields():
    """Find configured Jira Start date field IDs once per application session."""
    global _jira_schedule_fields_cache
    with _jira_schedule_fields_lock:
        if _jira_schedule_fields_cache is not None:
            return list(_jira_schedule_fields_cache)
        result=[]
        try:
            response=req.get(f"{JIRA_BASE_URL}/rest/api/3/field",headers=get_jira_headers(),timeout=15)
            response.raise_for_status()
            for item in response.json():
                if not isinstance(item,dict): continue
                name=str(item.get("name") or "").casefold().replace(" ","").replace("_","").replace("-","")
                fid=str(item.get("id") or "")
                if name=="startdate" and (fid=="startdate" or fid.startswith("customfield_")) and fid not in result:
                    result.append(fid)
            print(f"  Jira Gantt start date fields: {result or 'not configured'}")
            _jira_schedule_fields_cache=tuple(result)
        except Exception as exc:
            # A missing field should not stop the dependency map loading.
            # Retry next fetch if the lookup itself failed.
            print(f"  Jira Gantt start date field lookup failed: {exc}")
        return list(result)

def _base_issue_fields():
    return ["summary","description","status","priority","assignee","duedate","created","issuelinks","parent","customfield_10014","labels"] + _jira_schedule_fields()


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
    all_issues=_jira_search_parallel(active_jql,fields,"open")

    # First external-ticket pass: only after every open/main ticket has been
    # downloaded. This keeps the first board build focused on active work.
    _set_loading_progress(phase="Checking external blockers for open tickets…",batch=0,fetched=len(all_issues),total=len(all_issues),detail="Checking links from open tickets…")
    external_issues=jira_fetch_external_issues(all_issues, include_completed=True)
    _merge_issues(all_issues, external_issues)
    return all_issues

def jira_fetch_completed_issues(jql=None, known_issues=()):
    fields=_base_issue_fields()
    completed_jql=_completed_jql(jql)
    completed=_jira_search_parallel(completed_jql,fields,"completed")

    # Second external-ticket pass: only after every completed ticket has been
    # downloaded, so blockers referenced solely by completed work are included.
    _set_loading_progress(phase="Checking external blockers for completed tickets…",batch=0,fetched=len(completed),total=len(completed),detail="Checking links from completed tickets…")
    external_issues=jira_fetch_external_issues(completed, include_completed=True, known_issues=known_issues)
    _merge_issues(completed, external_issues)
    return completed

def jira_fetch_all_issues(jql=None):
    """Load open tickets, check their externals, then completed tickets, then their externals."""
    began=time.perf_counter()
    active=jira_fetch_active_issues(jql)
    active_seconds=time.perf_counter()-began
    completed=jira_fetch_completed_issues(jql, known_issues=active)
    print(f"  TIMING active+external={active_seconds:.2f}s completed+external={time.perf_counter()-began-active_seconds:.2f}s")
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
        completed=jira_fetch_completed_issues(jql, known_issues=active_raw)
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

def _prune_completed_loads(max_finished=8):
    """Keep recent completed snapshots without discarding active downloads.

    Caller holds _completed_loads_lock. Older finished generations are only
    retained briefly to support the browser's status/data polling endpoints.
    """
    finished=[key for key,entry in _completed_loads.items()
              if entry.get("status") in ("ready","error")]
    for key in finished[:-max_finished]:
        _completed_loads.pop(key,None)


def _start_background_full_load(jql, active_raw, generation=None):
    key=_completed_cache_key(jql,generation)
    with _completed_loads_lock:
        existing=_completed_loads.get(key)
        # A completed snapshot must never suppress a new Jira refresh.
        # Only coalesce an identical request while its worker is still running.
        if existing and existing.get("status") == "downloading":
            return
        _completed_loads[key]={"status":"queued","fetched":0,"detail":"Queued completed ticket download…","graph":None,"error":None}
        _prune_completed_loads()
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

def _jira_description_present(value):
    if value is None or value == "" or value == {} or value == []:
        return False
    if isinstance(value,str):
        return bool(value.strip())
    if isinstance(value,dict) and value.get("type")=="doc":
        # Empty rich-text paragraphs are visually blank in Jira too.
        def contains_content(node):
            if isinstance(node,list):
                return any(contains_content(item) for item in node)
            if not isinstance(node,dict):
                return False
            if str(node.get("text") or "").strip():
                return True
            if node.get("type") in ("media", "mediaSingle", "mediaGroup", "inlineCard", "blockCard", "mention", "emoji", "rule"):
                return True
            return contains_content(node.get("content") or [])
        return contains_content(value.get("content") or [])
    return bool(value)


def parse_dependency_graph(raw):
    # Keep Done/Completed for historical relationships. Exclude cancelled
    # statuses, and treat Jira-search-missing linked issues as unverified.
    # Jira's ARCHIVE action is not a status change: the archived issue may
    # still say Backlog, so searching status alone cannot identify it.
    raw_keys={str(r.get("key") or "").strip() for r in raw if r.get("key")}
    issues={}
    for r in raw:
        key=r.get("key"); f=r.get("fields") or {}; s=f.get("status") or {}; name=s.get("name") or ""
        if not key or name.strip().lower() in EXCLUDED_ISSUE_STATUSES: continue
        issues[key]={
            "key":key,"summary":f.get("summary") or "","status":name,
            "priority":(f.get("priority") or {}).get("name"),
            "assignee":((f.get("assignee") or {}).get("displayName") or (f.get("assignee") or {}).get("name") or "Unassigned"),
            "assigneeAccountId":(f.get("assignee") or {}).get("accountId"),
            "dueDate":f.get("duedate") or None,
            "startDate":next((str(f.get(field) or "")[:10] for field in _jira_schedule_fields_cache or () if f.get(field)),None),
            "created":str(f.get("created") or "")[:10] or None,
            "hasDescription":_jira_description_present(f.get("description")),
            "labels":f.get("labels") or [],
            "epic":_extract_epic(f),
            "url":f"{JIRA_BASE_URL}/browse/{key}",
            "blockers":set(),"blocked":set(),"externalBlockers":[],"unavailableBlockers":[]
        }
    edges=set(); unavailable=defaultdict(dict)
    for r in raw:
        source=r.get("key")
        if source not in issues: continue
        for link in (r.get("fields") or {}).get("issuelinks") or []:
            pair=_block_link(source,link)
            if not pair: continue
            blocker,blocked,linked_status=pair
            if blocker in issues and blocked in issues:
                # Fetched issues remain normal blockers, including completed
                # issues that can be displayed using Show completed.
                edges.add((blocker,blocked))
            elif blocked in issues and blocker not in issues:
                if blocker in raw_keys:
                    # Jira DID return the linked issue, but its status made us
                    # deliberately exclude it (Cancelled/Archived). Not external.
                    continue
                if _nonblocking_external_status(linked_status):
                    # Explicitly completed/closed/cancelled linked issues are
                    # historical and have no effect on the active graph.
                    continue
                # IMPORTANT: Jira Cloud's JQL search silently omits archived
                # issues, even when their workflow status is still Backlog or
                # In Progress. The link itself does not reveal archival state.
                # A missing issue could also be deleted or inaccessible.
                # Do not assert that it is an *active external blocker*.
                # Retain it for inspection/removal in Edit dependencies only.
                unavailable[blocked][blocker]={"key":blocker,"url":f"{JIRA_BASE_URL}/browse/{blocker}"}
    for a,b in edges: issues[a]["blocked"].add(b); issues[b]["blockers"].add(a)
    for k,v in unavailable.items(): issues[k]["unavailableBlockers"]=list(v.values())
    return issues,edges

def _dependency_components(keys, edges):
    """Find strongly-connected components iteratively in O(vertices + edges).

    Unlike DFS back-edge marking, this includes *every* member of a cycle,
    including overlapping cycles. No recursion limit issues on large boards.
    """
    keys=list(keys)
    outgoing={key:[] for key in keys}
    incoming={key:[] for key in keys}
    for source,target in edges:
        if source in outgoing and target in outgoing:
            outgoing[source].append(target)
            incoming[target].append(source)

    visited=set()
    finished=[]
    for start in keys:
        if start in visited:
            continue
        visited.add(start)
        stack=[(start,iter(outgoing[start]))]
        while stack:
            node, neighbours=stack[-1]
            try:
                nxt=next(neighbours)
                if nxt not in visited:
                    visited.add(nxt)
                    stack.append((nxt,iter(outgoing[nxt])))
            except StopIteration:
                finished.append(node)
                stack.pop()

    component_of={}
    components=[]
    for start in reversed(finished):
        if start in component_of:
            continue
        index=len(components)
        members=[]
        stack=[start]
        component_of[start]=index
        while stack:
            node=stack.pop()
            members.append(node)
            for nxt in incoming[node]:
                if nxt not in component_of:
                    component_of[nxt]=index
                    stack.append(nxt)
        components.append(members)
    cycles={key for members in components if len(members)>1 for key in members}
    cycles.update(a for a,b in edges if a==b and a in outgoing)
    return components,component_of,cycles


def detect_cycles(keys,edges):
    """Return all tickets belonging to a circular dependency."""
    return _dependency_components(keys,edges)[2]


def calculate_levels(issues,edges):
    """Lay out cycles as a single level, then advance downstream components."""
    components,component_of,cycles=_dependency_components(issues.keys(),edges)
    count=len(components)
    successors=[set() for _ in range(count)]
    indegree=[0]*count
    level=[1 if any(issues[key]["externalBlockers"] for key in group) else 0
           for group in components]

    for source,target in edges:
        if source not in component_of or target not in component_of:
            continue
        a,b=component_of[source],component_of[target]
        if a==b or b in successors[a]:
            continue
        successors[a].add(b)
        indegree[b]+=1

    queue=deque(i for i in range(count) if indegree[i]==0)
    while queue:
        a=queue.popleft()
        for b in successors[a]:
            level[b]=max(level[b],level[a]+1)
            indegree[b]-=1
            if indegree[b]==0:
                queue.append(b)
    return {key:level[component_of[key]] for key in issues},cycles


def serialize_graph(raw, jql=None):
    issues,edges=parse_dependency_graph(raw); levels,cycles=calculate_levels(issues,edges); out=[]
    for k,v in issues.items():
        out.append({
            "key":k,"summary":v["summary"],"status":v["status"],"priority":v["priority"],"assignee":v.get("assignee") or "Unassigned","assigneeAccountId":v.get("assigneeAccountId"),
            "labels":v.get("labels") or [],
            "dueDate":v.get("dueDate"),"startDate":v.get("startDate"),"created":v.get("created"),
            "hasDescription":v.get("hasDescription",False),
            "epic":v.get("epic"),"url":v["url"],
            "blockers":sorted(v["blockers"]),"blocked":sorted(v["blocked"]),
            "externalBlockers":sorted(v["externalBlockers"],key=lambda x:x["key"]),
            "unavailableBlockers":sorted(v["unavailableBlockers"],key=lambda x:x["key"]),
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
        started=time.perf_counter()
        if mode == "active":
            raw=jira_fetch_active_issues(active_jql)
            # Associate the slower completed-ticket load with the exact browser
            # refresh that requested it. An older refresh must never publish its
            # snapshot into a newer refresh.
            _start_background_full_load(active_jql, raw, generation)
            downloaded=time.perf_counter()
            graph=serialize_graph(raw,active_jql)
            print(f"  TIMING active fetch={downloaded-started:.2f}s serialize={time.perf_counter()-downloaded:.2f}s total={time.perf_counter()-started:.2f}s")
            return jsonify(graph)
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

@app.route("/api/usage-config-status")
def api_usage_config_status():
    """Diagnostic: shows whether usage reporting is enabled, never its secret."""
    return jsonify({"enabled":bool(USAGE_WEBHOOK_URL and USAGE_WEBHOOK_KEY),
                    "source":USAGE_CONFIG_SOURCE})

@app.route("/api/credential-status")
def api_credential_status():
    try:
        credential=_credential_read()
        jira_user={}
        if credential:
            try:
                me=req.get(f"{JIRA_BASE_URL}/rest/api/3/myself",headers=get_jira_headers(),timeout=10)
                if me.ok:
                    jira_user=me.json()
                    _queue_usage_checkin(jira_user,credential["email"])
            except Exception as exc:
                print(f"  Jira identity verification unavailable: {exc}")
        email=credential["email"] if credential else ""
        return jsonify({"configured":bool(credential),"email":email,
                        "accountId":str(jira_user.get("accountId") or ""),
                        "displayName":str(jira_user.get("displayName") or "")})
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

@app.route("/api/faqs")
def api_faqs():
    print(f"[FAQs] Fetching Sitebuilder feed: {FAQS_URL}", flush=True)
    try:
        response=req.get(FAQS_URL,timeout=15,headers={"Accept":"application/json","Cache-Control":"no-cache"})
        if not response.ok:
            return jsonify({"error":f"Sitebuilder returned HTTP {response.status_code}"}),502
        data=response.json()
        items=data.get("items",[]) if isinstance(data,dict) else []
        faqs=[]
        for item in items if isinstance(items,list) else []:
            if not isinstance(item,dict): continue
            title=str(item.get("title") or "").strip()
            body=str(item.get("parsedContentBody") or "").strip()
            categories=item.get("categories") or []
            if not isinstance(categories,list): categories=[]
            categories=[str(category).strip() for category in categories if isinstance(category,str) and category.strip()]
            if title or body: faqs.append({"title":title,"parsedContentBody":body,"categories":categories})
        return jsonify({"items":faqs})
    except Exception as e:
        print(f"[FAQs] ERROR: {type(e).__name__}: {e}",flush=True)
        return jsonify({"error":f"Could not load FAQs: {e}"}),502

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
        jira_user=test.json()
        _queue_usage_checkin(jira_user,email)
        return jsonify({"ok":True,"email":email,
                        "accountId":str(jira_user.get("accountId") or ""),
                        "displayName":str(jira_user.get("displayName") or "")})
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

# ---------------------------------------------------------------------------
# Milestone Gantt PDF export: vector PDF written using the standard library,
# so the packaged Windows app does not require any new runtime dependencies.
# ---------------------------------------------------------------------------
def _gantt_pdf_escape(value, limit=220):
    """Escape a string as a WinAnsi PDF string with no untrusted operators."""
    import unicodedata
    value=str(value or '')[:limit].replace('\r',' ').replace('\n',' ')
    value=value.replace('\u2011','-').replace('\u2192','->')
    value=''.join(ch if ch.encode('cp1252',errors='ignore') else (unicodedata.normalize('NFKD',ch).encode('ascii',errors='ignore').decode('ascii') or '?') for ch in value)
    return value.replace('\\','\\\\').replace('(','\\(').replace(')','\\)')


def _gantt_pdf_bytes(payload):
    """Return a complete landscape, multipage, dependency-aware vector PDF."""
    from datetime import date,timedelta
    import io,re
    if not isinstance(payload,dict): raise ValueError('Invalid Gantt PDF request.')
    milestone=payload.get('milestone') or {}
    # Match the current board controls. Validate incoming PDF settings because
    # this route also accepts requests from outside the normal browser UI.
    scale=payload.get('scale',12)
    if type(scale) is not int or scale not in (6,12,20):
        raise ValueError('Invalid Gantt PDF timeline scale.')
    narrow=payload.get('narrow') is True
    scale_name={6:'Compact',12:'Normal',20:'Expanded'}[scale]
    records=payload.get('rows') or []
    links=payload.get('edges') or []
    if not isinstance(records,list) or not isinstance(links,list) or len(records)>1800 or len(links)>10000:
        raise ValueError('Gantt is too large to export.')
    def date_value(v):
        if not v: return None
        try: return date.fromisoformat(str(v)[:10])
        except (TypeError,ValueError): return None
    rows=[];seen=set()
    for item in records:
        if not isinstance(item,dict): continue
        key=str(item.get('key') or '').strip()[:60]
        if not key or key in seen: continue
        seen.add(key)
        start=date_value(item.get('start')); end=date_value(item.get('end'))
        raw_color=str(item.get('color') or '')
        color=raw_color if re.fullmatch(r'#[0-9a-fA-F]{6}',raw_color) else '#64748b'
        rows.append({'key':key,'summary':str(item.get('summary') or '')[:300],
                     'status':str(item.get('status') or '')[:60],
                     'assignee':str(item.get('assignee') or 'Unassigned')[:140],
                     'start':start,'end':end,'color':color,
                     'source':str(item.get('source') or '')[:70],
                     'reason':str(item.get('reason') or '')[:140],
                     'milestone':bool(item.get('milestone'))})
    scheduled=[r for r in rows if r['start'] is not None and r['end'] is not None and r['end']>=r['start']]
    unscheduled=[r for r in rows if r['start'] is None or r['end'] is None or r['end']<r['start']]
    page_w,page_h=1190.55,841.89   # A3 landscape, points
    margin=40.; left_w=275. if narrow else 360.
    chart_left=margin+left_w
    # Match screen zoom proportions while respecting legibility on A3 paper.
    chart_w=page_w-margin-chart_left; day_w={6:3.,12:5.,20:10.}[scale]
    row_h=19. if narrow else 28.
    table_top=632.; table_bottom=88.
    per_page=max(1,int((table_top-table_bottom)/row_h))
    capacity=max(1,int(chart_w/day_w))
    dates=[d for r in scheduled for d in (r['start'],r['end'])]
    first=min(dates) if dates else date.today()
    last=max(dates) if dates else first
    days=(last-first).days+1
    slices=max(1,(days+capacity-1)//capacity) if scheduled else 0
    page_specs=[]
    for ix in range(slices):
        begin=first+timedelta(days=ix*capacity)
        finish=min(last,begin+timedelta(days=capacity-1))
        for offset in range(0,len(scheduled),per_page):
            page_specs.append(('timeline',ix+1,begin,finish,scheduled[offset:offset+per_page]))
    for offset in range(0,len(unscheduled),per_page):
        page_specs.append(('unscheduled',0,None,None,unscheduled[offset:offset+per_page]))
    if not page_specs:
        page_specs.append(('unscheduled',0,None,None,[]))
    def rgb(value):
        return tuple(int(value[i:i+2],16)/255 for i in (1,3,5))
    def poscolor(hex_value):
        r,g,b=rgb(hex_value);return f'{r:.3f} {g:.3f} {b:.3f}'
    def txt(x,y,label,size=10,bold=False,shade='#172033',max_chars=100):
        safe=_gantt_pdf_escape(str(label)[:max_chars])
        return f'BT /{"F2" if bold else "F1"} {size} Tf {poscolor(shade)} rg 1 0 0 1 {x:.2f} {y:.2f} Tm ({safe}) Tj ET\n'
    def fit_label(value,max_width,size=9,bold=False):
        # Helvetica has a proportional font. Conservative approximate glyph
        # widths keep text within the label column without clipping the chart.
        value=str(value or '').replace('\n',' ').replace('\r',' ')
        limit=max(1,int(max_width/(size*(.67 if bold else .61))))
        return value if len(value)<=limit else value[:max(1,limit-1)].rstrip()+'…'
    def rect(x,y,w,h,c,stroke=None):
        op=f'{poscolor(c)} rg {x:.2f} {y:.2f} {w:.2f} {h:.2f} re f\n'
        if stroke: op+=f'{poscolor(stroke)} RG 0.5 w {x:.2f} {y:.2f} {w:.2f} {h:.2f} re S\n'
        return op
    def line(x1,y1,x2,y2,c='#cbd5e1',width=.65):
        return f'{poscolor(c)} RG {width:.2f} w {x1:.2f} {y1:.2f} m {x2:.2f} {y2:.2f} l S\n'
    def diamond(cx,cy,r,c):
        return f'{poscolor(c)} rg {cx:.2f} {cy+r:.2f} m {cx+r:.2f} {cy:.2f} l {cx:.2f} {cy-r:.2f} l {cx-r:.2f} {cy:.2f} l h f\n'
    def assignee_badge(cx,cy,assignee):
        name=str(assignee or '').strip()
        unassigned=not name or name.casefold()=='unassigned'
        parts=name.split()
        initials='U' if unassigned else (parts[0][:1]+parts[-1][:1] if len(parts)>1 else parts[0][:1]).upper()
        fill='#2563eb' if unassigned else '#e2e8f0'
        foreground='#ffffff' if unassigned else '#334155'
        r=7.3
        # Four Bezier curves yield a circular badge, including in narrow mode.
        k=.55228475*r
        circle=(f'{poscolor(fill)} rg '
                f'{cx+r:.2f} {cy:.2f} m '
                f'{cx+r:.2f} {cy+k:.2f} {cx+k:.2f} {cy+r:.2f} {cx:.2f} {cy+r:.2f} c '
                f'{cx-k:.2f} {cy+r:.2f} {cx-r:.2f} {cy+k:.2f} {cx-r:.2f} {cy:.2f} c '
                f'{cx-r:.2f} {cy-k:.2f} {cx-k:.2f} {cy-r:.2f} {cx:.2f} {cy-r:.2f} c '
                f'{cx+k:.2f} {cy-r:.2f} {cx+r:.2f} {cy-k:.2f} {cx+r:.2f} {cy:.2f} c f\n')
        size=6.5
        # Approximate the glyph width to centre both one- and two-letter badges.
        return circle+txt(cx-len(initials)*size*.34,cy-size*.34,initials,size,True,foreground,2)
    content=[]
    total_pages=len(page_specs)
    all_edges={(str(e.get('from')),str(e.get('to'))) for e in links if isinstance(e,dict)}
    is_milestone=milestone.get('isMilestone') is not False
    is_overview=milestone.get('isOverview') is True
    title=str(milestone.get('summary') or milestone.get('key') or 'Milestone')[:110]
    key=str(milestone.get('key') or '')[:60]
    for page_no,(mode,part,begin,finish,page_rows) in enumerate(page_specs,1):
        cmds=[]
        cmds.append(rect(0,page_h-112,page_w,112,'#172033'))
        cmds.append(txt(margin,page_h-47,('PROJECT MILESTONES  /  ' if is_overview else 'MILESTONE GANTT  /  ' if is_milestone else 'SELECTED CHAIN GANTT  /  ')+key,12,True,'#bfdbfe'))
        cmds.append(txt(margin,page_h-78,title,20,True,'#ffffff',102))
        cmds.append(txt(page_w-270,page_h-49,'Page '+str(page_no)+' of '+str(total_pages),11,True,'#ffffff'))
        detail='Scheduled '+str(len(scheduled))+'  |  Unscheduled '+str(len(unscheduled))+'  |  '+scale_name+' timeline  |  '+('Narrow' if narrow else 'Standard')+' labels'
        cmds.append(txt(margin,page_h-137,detail,10,False,'#475569'))
        if mode=='timeline':
            cmds.append(txt(margin,page_h-162,'Timeline: '+begin.strftime('%d %b %Y')+' - '+finish.strftime('%d %b %Y')+f'  (date segment {part}/{slices})',10,True))
        else:
            cmds.append(txt(margin,page_h-162,('Milestones without valid start and due dates' if is_overview else 'Unscheduled tasks  |  Missing due date, usable start date or invalid date range'),10,True))
        cmds.append(rect(margin,table_top+15,left_w,32,'#f1f5f9'))
        cmds.append(txt(margin+8,table_top+26,'ISSUE / SUMMARY'+(' (NARROW)' if narrow else ''),10,True))
        if mode=='timeline':
            cmds.append(rect(chart_left,table_top+15,chart_w,32,'#e0f2fe'))
            cursor=begin
            last_month_label_end=chart_left-10
            while cursor<=finish:
                idx=(cursor-begin).days; x=chart_left+idx*day_w
                if cursor.day==1 or cursor==begin:
                    label=cursor.strftime('%b %Y')
                    # Short date ranges can begin near a month boundary; keep
                    # adjacent printed month labels from overlapping.
                    label_x=max(x+3,last_month_label_end+6)
                    if label_x+43<page_w-margin:
                        cmds.append(txt(label_x,table_top+26,label,9,True,'#0369a1'))
                        last_month_label_end=label_x+43
                # The printed date ticks mirror the three on-screen modes.
                if (scale==12 and cursor.day%5==0) or scale==20:
                    cmds.append(txt(x+1,table_top+18,str(cursor.day),8,False,'#475569'))
                if cursor.weekday()==0:
                    cmds.append(line(x,table_bottom,x,table_top+15,'#e2e8f0',.45))
                cursor+=timedelta(days=1)
        else:
            cmds.append(rect(chart_left,table_top+15,chart_w,32,'#f1f5f9'))
            cmds.append(txt(chart_left+10,table_top+26,'REASON / DATES AVAILABLE',10,True))
        row_centers={}
        for idx,r in enumerate(page_rows):
            y=table_top-idx*row_h-row_h; cy=y+row_h/2
            row_centers[r['key']]=cy
            if idx%2==1: cmds.append(rect(margin,y,page_w-2*margin,row_h,'#f8fafc'))
            cmds.append(line(margin,y,page_w-margin,y,'#e2e8f0',.45))
            cmds.append(assignee_badge(margin+left_w-16,cy,r['assignee']))
            key_label=r['key']+(('  [Milestone]' if is_milestone else '  [Selected]') if r['milestone'] and not is_overview else '')
            if narrow:
                one_line=key_label+'  |  '+r['summary']
                cmds.append(txt(margin+8,cy-3,fit_label(one_line,left_w-43,9,False),9,False,'#172033'))
            else:
                heading=(key_label+'  |  '+r['start'].strftime('%d %b %y')+' - '+r['end'].strftime('%d %b %y')) if is_overview and mode=='timeline' else key_label+'  |  '+r['status']
                cmds.append(txt(margin+8,y+17,fit_label(heading,left_w-43,9,True),9,True,'#172033'))
                cmds.append(txt(margin+8,y+5,fit_label(r['summary'],left_w-43,8),8,False,'#64748b'))
            if mode=='timeline':
                a=max(r['start'],begin); b=min(r['end'],finish)
                if b>=a:
                    x=chart_left+((a-begin).days)*day_w+1
                    length=max(3,((b-a).days+1)*day_w-2)
                    if r['milestone'] and not is_overview:
                        # A milestone is a dated diamond at its due date, not
                        # a bar that spans its start and end. Only render the
                        # marker in the PDF date slice containing its due date.
                        if begin<=r['end']<=finish:
                            mx=chart_left+((r['end']-begin).days+.5)*day_w
                            cmds.append(diamond(mx,cy,6.5,'#b45309'))
                    else:
                        cmds.append(rect(x,cy-5,length,10,r['color']))
                if r['start']<begin or r['end']>finish:
                    pass
            else:
                dates='Start: '+(r['start'].isoformat() if r['start'] else 'missing') + '   Due: '+(r['end'].isoformat() if r['end'] else 'missing')
                if narrow:
                    cmds.append(txt(chart_left+9,cy-3,fit_label(r['reason'] or 'Missing schedule data',chart_w-18,9,True),9,True,'#b45309'))
                else:
                    cmds.append(txt(chart_left+9,y+17,r['reason'] or 'Missing schedule data',9,True,'#b45309',110))
                    cmds.append(txt(chart_left+9,y+5,dates+'  |  '+r['status'],8,False,'#64748b',110))
        if mode=='timeline':
            visible={r['key']:r for r in page_rows}
            for parent,child in all_edges:
                if parent not in visible or child not in visible: continue
                a,b=visible[parent],visible[child]
                # A visible milestone diamond takes incoming arrows at its
                # left tip (its due date), rather than at the nominal task
                # start. All other targets use the start of their task bar.
                target_diamond=b['milestone'] and not is_overview
                target_date=b['end'] if target_diamond else b['start']
                # In multipage exports, only draw the link in a date segment
                # containing both *visible* endpoints.
                if not(begin<=a['end']<=finish and begin<=target_date<=finish):continue
                x1=chart_left+((a['end']-begin).days+1)*day_w-1
                if a['milestone'] and not is_overview:
                    x1=chart_left+((a['end']-begin).days+.5)*day_w+6.5
                x2=(chart_left+((target_date-begin).days+.5)*day_w-6.5 if target_diamond
                    else chart_left+((target_date-begin).days)*day_w+1)
                y1,y2=row_centers[parent],row_centers[child]
                if x2>x1+14:
                    mid=(x1+x2)/2
                    coords=[(x1,y1),(mid,y1),(mid,y2),(x2,y2)]
                else:
                    midy=(y1+y2)/2
                    coords=[(x1,y1),(x1+7,y1),(x1+7,midy),
                            (max(chart_left+1,x2-7),midy),
                            (max(chart_left+1,x2-7),y2),(x2,y2)]
                for (px,py),(qx,qy) in zip(coords,coords[1:]):
                    cmds.append(line(px,py,qx,qy,'#94a3b8',.8))
                cmds.append(f'{poscolor("#64748b")} rg {x2:.2f} {y2:.2f} m {x2-4.5:.2f} {y2+2.3:.2f} l {x2-4.5:.2f} {y2-2.3:.2f} l h f\n')
        cmds.append(line(margin,table_bottom,page_w-margin,table_bottom))
        if is_overview:
            cmds.append(txt(margin,55,'Bars span the milestone start and due dates; blocker tasks are not included.',9,False,'#64748b'))
            cmds.append(txt(margin,38,'Start: Jira start > first blocker after prior milestone > creation.',9,False,'#64748b'))
        else:
            cmds.append(txt(margin,55,'Start source: Jira start date > latest direct blocker due date + 1 day > Jira creation date.',9,False,'#64748b'))
            cmds.append(txt(margin,38,'PDF includes the upstream dependency chain; tasks without complete dates are listed separately.',9,False,'#64748b'))
        content.append(''.join(cmds).encode('cp1252',errors='replace'))
    # Minimal standards-compliant PDF writer (xref & page tree), no font files.
    objects=[b'']
    def add(b): objects.append(b);return len(objects)-1
    pages_obj=add(b'')
    font_regular=add(b'<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>')
    font_bold=add(b'<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica-Bold /Encoding /WinAnsiEncoding >>')
    page_ids=[]
    for stream in content:
        body=add(b'<< /Length '+str(len(stream)).encode()+b' >>\nstream\n'+stream+b'\nendstream')
        page_ids.append(add((f'<< /Type /Page /Parent {pages_obj} 0 R /MediaBox [0 0 {page_w:.2f} {page_h:.2f}] /Resources << /Font << /F1 {font_regular} 0 R /F2 {font_bold} 0 R >> >> /Contents {body} 0 R >>').encode('ascii')))
    objects[pages_obj]=b'<< /Type /Pages /Kids ['+b' '.join((str(i)+' 0 R').encode() for i in page_ids)+b'] /Count '+str(len(page_ids)).encode()+b' >>'
    root=add((f'<< /Type /Catalog /Pages {pages_obj} 0 R >>').encode())
    pdf=io.BytesIO();pdf.write(b'%PDF-1.4\n%\xe2\xe3\xcf\xd3\n');offsets=[0]
    for n,obj in enumerate(objects[1:],1):
        offsets.append(pdf.tell())
        pdf.write(f'{n} 0 obj\n'.encode()+obj+b'\nendobj\n')
    pointer=pdf.tell();pdf.write(f'xref\n0 {len(objects)}\n0000000000 65535 f \n'.encode())
    for off in offsets[1:]:pdf.write(f'{off:010d} 00000 n \n'.encode())
    pdf.write(f'trailer\n<< /Size {len(objects)} /Root {root} 0 R >>\nstartxref\n{pointer}\n%%EOF\n'.encode())
    return pdf.getvalue()

@app.route('/api/gantt-pdf',methods=['POST'])
def api_gantt_pdf():
    try:
        if request.content_length and request.content_length>2500000:
            return jsonify({'error':'Gantt export exceeds the size limit.'}),413
        body=request.get_json(force=True)
        pdf=_gantt_pdf_bytes(body)
        milestone=(body.get('milestone') or {}).get('key','milestone')
        import re
        filename=re.sub(r'[^A-Za-z0-9_-]','_',str(milestone))[:60] or 'milestone'
        return Response(pdf,mimetype='application/pdf',headers={
            'Content-Disposition':f'attachment; filename="{filename}_gantt.pdf"',
            'Cache-Control':'no-store'
        })
    except (ValueError,TypeError) as exc:
        return jsonify({'error':str(exc)}),400
    except Exception as exc:
        return jsonify({'error':'Could not generate Gantt PDF: '+str(exc)}),500


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
#toggle-completed.dashboard-hidden{display:none!important}
.btn-toggle-milestones{padding-left:11px;padding-right:11px}
.btn-toggle-milestones.active{background:rgba(56,189,248,.16);border-color:rgba(56,189,248,.45);color:#bae6fd}
/* Milestones fill the viewport without creating a second, full-page vertical
   scrollbar. Only each milestone's own blocker list scrolls vertically. */
#board.milestone-board{display:block;width:max-content;min-width:100%;height:100%;max-height:100%;min-height:0;padding:18px 28px 14px;}
#board.milestone-board #lines{display:none!important}
.milestone-overview{width:max-content;min-width:100%;height:100%;min-height:0;padding:0;display:flex;flex-direction:column;gap:12px}
/* The milestone cards form a very wide, horizontally scrolling board.
   Anchor the header to the scrollport (not the far-right card) so its actions
   remain on the visible right edge at every horizontal scroll position. */
#app.milestone-mode .milestone-overview-header{position:sticky;left:28px;z-index:20;width:calc(100vw - 56px);max-width:calc(100vw - 56px);box-sizing:border-box;flex:0 0 auto;background:var(--bg)}
.milestone-overview-header{display:flex;align-items:center;justify-content:space-between;padding:0 2px}
.milestone-overview-title{font-size:12px;text-transform:uppercase;letter-spacing:.08em;font-weight:800;color:var(--muted)}
.milestone-overview-tools{position:sticky;right:0;z-index:21;display:flex;align-items:center;gap:10px;flex:0 0 auto;margin-left:auto;background:var(--bg)}
.milestone-project-gantt{display:inline-flex;align-items:center;gap:6px;padding:7px 10px;border-radius:7px;border:1px solid #818cf8;background:#eef2ff;color:#3730a3;font-size:11px;font-weight:800;cursor:pointer}
.milestone-project-gantt:hover,.milestone-project-gantt:focus-visible{background:#e0e7ff}
.milestone-project-gantt:disabled{opacity:.5;cursor:default}
.milestone-overview-count{font-size:12px;background:#e0f2fe;border-radius:999px;padding:3px 9px;color:#0369a1;font-weight:800}
.milestone-row{display:flex;flex:1;min-height:0;gap:14px;overflow:visible;padding:2px 2px 0;align-items:stretch}
.milestone-item{width:600px;min-width:600px;height:100%;max-height:100%;min-height:0;overflow:hidden;display:flex;flex-direction:column;gap:7px}
.milestone-item .card{width:100%;}
.milestone-blocked{border:1px solid var(--border);border-radius:9px;background:#fff;padding:9px 10px;box-shadow:0 1px 2px rgba(15,23,42,.04);display:flex;flex-direction:column;flex:1;min-height:0;overflow:hidden}
.milestone-blocked-head{display:flex;align-items:center;justify-content:space-between;gap:8px;margin-bottom:7px;flex-shrink:0}
.milestone-blocked-title{font-size:10px;text-transform:uppercase;letter-spacing:.05em;font-weight:800;color:#9a6700}
.milestone-blocked-count{font-size:10px;background:#fff7ed;border:1px solid #fed7aa;border-radius:999px;padding:2px 6px;color:#9a6700;font-weight:800}
.milestone-blocked-list{display:flex;flex-direction:column;gap:4px;flex:1;min-height:0;max-height:none;overflow-y:auto;overscroll-behavior:contain;padding-right:2px}
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
.hover-gantt-btn{display:none;align-items:center;justify-content:center;width:24px;height:22px;margin:-1px 5px 0 0;padding:2px;border:1px solid #c7d2fe;border-radius:5px;background:#eef2ff;color:#4338ca;cursor:pointer}
.card.selection-highlight .hover-gantt-btn{display:inline-flex}
.hover-gantt-btn:hover,.hover-gantt-btn:focus-visible{background:#dbeafe;border-color:#818cf8}
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
body.gantt-open .ticket-preview-backdrop{z-index:25030}
body.gantt-open .ticket-preview-modal{z-index:25031}
#faqs-modal{display:none;position:fixed;inset:0;z-index:10079;background:rgba(15,23,42,.22);align-items:center;justify-content:center;padding:24px}
#faqs-modal.open{display:flex}
.faqs-dialog{width:min(760px,calc(100vw - 48px));height:min(760px,calc(100vh - 48px));display:flex;flex-direction:column;overflow:hidden;background:#fff;border:1px solid #cbd5e1;border-radius:10px;box-shadow:0 24px 70px rgba(15,23,42,.28)}
.faqs-header{display:flex;align-items:center;justify-content:space-between;gap:12px;padding:10px 14px;background:#f8fafc;border-bottom:1px solid #e2e8f0;flex:0 0 auto}
.faqs-header h2{font-size:14px;color:#0f172a}.faqs-search-wrap{padding:12px 14px;border-bottom:1px solid #e2e8f0;flex:0 0 auto}
#faqs-search{width:100%;padding:10px 12px;border:1px solid #cbd5e1;border-radius:7px;font:inherit;outline-color:#6366f1}
#faqs-list{flex:1 1 auto;overflow:auto;padding:12px 14px;min-height:0}
.faq-section{margin-bottom:20px}
.faq-section:last-child{margin-bottom:0}
.faq-section[hidden],.faq-item[hidden]{display:none}
.faq-section-title{font-size:13px;font-weight:800;color:#475569;padding:7px 2px 10px;margin:0;line-height:1.4;border-bottom:1px solid #e2e8f0;margin-bottom:10px}
.faq-item{border:1px solid #e2e8f0;border-radius:8px;margin-bottom:8px;overflow:hidden}
.faq-question{list-style:none;display:block;cursor:pointer;padding:13px 38px 13px 14px;font-weight:750;color:#172033;position:relative}
.faq-question::-webkit-details-marker{display:none}.faq-question:after{content:'+';position:absolute;right:14px;top:10px;font-size:20px;color:#64748b}.faq-item[open] .faq-question:after{content:'−'}
.faq-answer{padding:0 14px 14px;color:#334155;line-height:1.55}.faq-answer p{margin:0 0 9px}.faq-answer p:last-child{margin-bottom:0}.faq-answer ul,.faq-answer ol{padding-left:22px;margin:6px 0}.faq-answer a{color:#4338ca;text-decoration:underline}
.faqs-footer{flex:0 0 auto;display:flex;justify-content:flex-end;padding:10px 14px;border-top:1px solid #e2e8f0;background:#f8fafc}
.faqs-ask{border:0;background:#4338ca;color:#fff;border-radius:7px;padding:10px 15px;font-weight:750;cursor:pointer}.faqs-ask:hover{background:#3730a3}
.faqs-empty{padding:20px;color:#64748b;text-align:center}mark.faq-highlight{background:#fef08a;color:inherit;padding:0;border-radius:2px}
@media(max-width:700px){#faqs-modal{padding:8px}.faqs-dialog{width:calc(100vw - 16px);height:calc(100vh - 16px)}}

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
#app.milestone-mode{overflow-x:auto;overflow-y:hidden;overscroll-behavior-y:contain}
#app.milestone-mode #board-minimap{display:none!important}
/* The full-board dependency SVG should not participate in layout or painting
   on views which cannot display its connections. */
#app:not(.locked) #lines,#app.milestone-mode #lines,#app.dashboard-mode #lines,#app.my-view-mode #lines,body.gantt-open #lines{display:none!important}
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
  /* Do not chain a wheel fling into the parent page at the top/bottom.
     Native overflow anchoring can fight our explicit per-column restoration. */
  overscroll-behavior-y:contain;
  overflow-anchor:none;
  scrollbar-gutter:stable;
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
/* Cards have their real height from the first paint. Using content-visibility
   with an estimated height caused the scrollbar to jump when offscreen ticket
   cards were measured during scrolling. The edit controls remain lazy. */
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
.line.cycle-line{stroke:#d97706;stroke-dasharray:4 3;stroke-width:2}
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
.due-date-empty{color:#1d4ed8;background:#eff6ff;border-color:#bfdbfe;font-weight:750}
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
.dashboard-health-breakdown{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:4px 14px;margin-top:9px;border-top:1px solid #e2e8f0;padding-top:7px}
.dashboard-health-row{display:flex;align-items:baseline;justify-content:space-between;flex-wrap:wrap;gap:2px 7px;min-width:0;padding:3px 0;font-size:10px}
.dashboard-health-row-label{font-weight:750;color:#334155;min-width:0;overflow-wrap:break-word}
.dashboard-health-row-detail{color:#94a3b8;white-space:nowrap;flex:0 0 auto}
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
/* Priority distribution: same labels/icons as the priority picker, with each
   fill representing its share of all active tickets (not its rank). */
.dashboard-priority-row{display:grid;grid-template-columns:minmax(96px,122px) minmax(0,1fr) 76px;gap:12px;cursor:default}
.dashboard-priority-row:hover{background:#f8fafc;border-color:#e2e8f0;box-shadow:none}
.dashboard-priority-label{min-width:0;white-space:nowrap}
.dashboard-priority-bar{display:block;height:9px;min-width:0;overflow:hidden;background:#e2e8f0;border-radius:999px}
.dashboard-priority-bar-fill{display:block;height:100%;min-width:2px;background:#6366f1;border-radius:999px}
.dashboard-priority-count{display:flex;align-items:baseline;justify-content:flex-end;gap:6px;white-space:nowrap;color:#4338ca;font-size:11px}
.dashboard-priority-count small{font-size:10px;color:#64748b;font-weight:650}
@media(max-width:420px){.dashboard-priority-row{grid-template-columns:minmax(82px,106px) minmax(0,1fr) 65px;gap:7px}.dashboard-priority-count{gap:3px}}
.dashboard-milestone-risk-row{display:grid;grid-template-columns:minmax(0,1fr) minmax(270px,330px);gap:16px}
.dashboard-milestone-risk-main{min-width:0}
.dashboard-milestone-risk-metrics{display:grid;grid-template-columns:94px 88px minmax(82px,1fr);align-items:center;gap:10px;justify-items:start;font-size:11px;font-weight:800;white-space:nowrap}
.dashboard-milestone-risk-blocked{color:#9a6700}
.dashboard-milestone-risk-blocks{color:#4338ca}
.dashboard-milestone-risk-date{color:#475569;font-weight:700}
.dashboard-milestone-risk-date.due-date.overdue{color:#b91c1c;background:#fef2f2;border:1px solid #fecaca;border-radius:5px;padding:3px 6px;font-weight:800}
@media(max-width:700px){.dashboard-milestone-risk-row{grid-template-columns:minmax(0,1fr)}.dashboard-milestone-risk-metrics{grid-template-columns:94px 88px minmax(82px,1fr);padding-left:0}}
.dashboard-impact{font-size:11px;font-weight:800;color:#6366f1;white-space:nowrap}
.dashboard-workload-list{display:flex;flex-direction:column;gap:4px}
.dashboard-workload-row{display:grid;grid-template-columns:minmax(150px,210px) 1fr 42px;align-items:center;gap:10px;width:100%;border:0;background:transparent;padding:6px 4px;text-align:left;color:#334155;border-radius:6px}
.dashboard-workload-row:hover{background:#f8fafc}
.dashboard-workload-name{display:flex;align-items:center;gap:8px;min-width:0}
.dashboard-workload-name strong{overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:12px}
.dashboard-workload-name span{font-size:10px;color:#b91c1c;white-space:nowrap}
.dashboard-workload-bar{height:7px;background:#e2e8f0;border-radius:999px;overflow:hidden}
.dashboard-workload-bar span{display:block;height:100%;background:#6366f1;border-radius:999px}
.dashboard-workload-count{text-align:right;font-size:12px}
.dashboard-personal-view{margin:14px 0 22px;padding:14px;background:#fff;border:1px solid #dbe2ea;border-radius:10px}
.dashboard-personal-grid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:10px}
.dashboard-personal-metric{display:flex;align-items:center;justify-content:space-between;gap:12px;padding:12px;border:1px solid #e2e8f0;border-radius:8px;background:#f8fafc;min-width:0}
.dashboard-personal-metric>div:first-child{display:flex;flex-direction:column;gap:3px;min-width:0}
.dashboard-personal-label{font-size:12px;color:#475569;font-weight:700}
.dashboard-personal-metric strong{font-size:25px;color:#172033}
.dashboard-personal-help{font-size:10px;color:#64748b}
.dashboard-personal-actions{display:flex;flex-direction:column;align-items:flex-start;gap:6px;flex-shrink:0}
.dashboard-show-personal{border:1px solid #c7d2fe;background:#eef2ff;color:#3730a3;border-radius:6px;padding:6px 8px;font-size:11px;font-weight:750;cursor:pointer;white-space:nowrap}
.dashboard-show-personal:hover{background:#e0e7ff}
.personal-overwrite-note{font-weight:700;color:#64748b}.personal-user-change{display:flex;align-items:center;gap:8px;margin-left:auto}.personal-user-change label{font-size:12px;color:#475569;font-weight:700}.personal-user-mapping{max-width:240px;min-width:170px;padding:7px 9px;border:1px solid #cbd5e1;border-radius:7px;background:#fff;color:#172033;font-size:12px}.dashboard-personal-actions{justify-content:center}
@media(max-width:1100px){.dashboard-personal-grid{grid-template-columns:repeat(2,minmax(0,1fr))}}
@media(max-width:700px){.dashboard-personal-grid{grid-template-columns:1fr}.dashboard-personal-metric{align-items:flex-start}}
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


/* Dedicated personal view; table remains readable in a narrow window. */
#board.my-view-board{width:100%;min-width:0;display:block;padding:18px 20px 40px}
#board.my-view-board #lines{display:none!important}
#app.my-view-mode{overflow-x:hidden;overflow-y:auto}
.my-view{display:flex;flex-direction:column;gap:16px;max-width:1500px;margin:0 auto;min-width:0}
.my-view .dashboard-personal-view{margin:0}
.my-view-table-section{background:#fff;border:1px solid #dbe2ea;border-radius:10px;padding:15px;min-width:0}
.my-view-table-heading{display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap;margin-bottom:12px}
.my-view-table-heading h2{font-size:15px;color:#172033}
.my-view-table-heading p{font-size:11px;color:#64748b;margin-top:3px}
.my-view-sort-actions{display:flex;align-items:center;gap:10px;flex-wrap:wrap}
.my-view-sort-status{color:#64748b;font-size:11px}
.my-view-save-sort{border:1px solid #6366f1;border-radius:7px;padding:8px 12px;background:#4f46e5;color:#fff;cursor:pointer;font-weight:750;font-size:12px}
.my-view-save-sort:hover{background:#4338ca}
.my-view-save-sort:disabled{background:#e2e8f0;border-color:#cbd5e1;color:#64748b;cursor:default}
/* Keep the wide table inside the My view card, with its own horizontal scroll. */
.my-view-table-scroll{overflow-x:auto;overflow-y:hidden;max-width:100%;min-width:0;-webkit-overflow-scrolling:touch;overscroll-behavior-x:contain;scrollbar-width:thin;scrollbar-color:#94a3b8 #f1f5f9}
.my-view-table-scroll::-webkit-scrollbar{height:10px}
.my-view-table-scroll::-webkit-scrollbar-thumb{background:#94a3b8;border:2px solid #f1f5f9;border-radius:8px}
.my-view-table-scroll::-webkit-scrollbar-track{background:#f1f5f9}
.my-view-table-scroll:focus-visible{outline:2px solid #6366f1;outline-offset:2px}
.my-view-scroll-controls{display:flex;align-items:center;justify-content:flex-end;gap:8px;margin:0 0 9px}
.my-view-scroll-controls[hidden]{display:none!important}
.my-view-scroll-hint{font-size:11px;color:#64748b;margin-right:2px}
.my-view-scroll-button{width:32px;height:28px;display:inline-flex;align-items:center;justify-content:center;border:1px solid #cbd5e1;border-radius:6px;background:#fff;color:#475569;cursor:pointer;font-size:16px;font-weight:800}
.my-view-scroll-button:not(:disabled):hover{background:#eef2ff;color:#4338ca;border-color:#a5b4fc}
.my-view-scroll-button:focus-visible{outline:2px solid #6366f1;outline-offset:2px}
.my-view-scroll-button:disabled{opacity:.4;cursor:default}
.my-view-table{width:100%;min-width:1080px;border-collapse:separate;border-spacing:0;font-size:12px}
.my-view-table th{text-align:left;background:#f1f5f9;color:#475569;font-weight:750;border-block:1px solid #e2e8f0;padding:10px 8px;white-space:nowrap}
.my-view-table th:first-child{border-radius:6px 0 0 6px;padding-left:12px}
.my-view-table th:last-child{border-radius:0 6px 6px 0}
.my-view-table th button{display:inline-flex;align-items:center;gap:6px;border:0;background:transparent;color:inherit;font:inherit;font-weight:inherit;cursor:pointer;text-align:left;padding:0}
.my-view-table th button.active{color:#4338ca}
.my-view-table th button:focus-visible{outline:2px solid #6366f1;outline-offset:3px}
.my-view-row{cursor:pointer}
.my-view-row td{padding:10px 8px;border-bottom:1px solid #e2e8f0;background:#fff;vertical-align:middle;color:#334155}
.my-view-row td:first-child{padding-left:12px;white-space:nowrap}
.my-view-row:hover td{background:#f8fafc}
.my-view-row .my-view-summary{min-width:230px;max-width:480px;line-height:1.4}
.my-view-row .my-view-priority{display:flex;align-items:center;gap:8px;white-space:nowrap}
.my-view-row .my-view-parent a{color:#4338ca;text-decoration:none}
.my-view-row .my-view-parent a:hover{text-decoration:underline}
.my-view-row .dashboard-ticket-key{font-size:12px;font-weight:800}
.my-view-row .due-date{white-space:nowrap}
.my-view-row .status-badge{white-space:nowrap}
.my-view-count{display:inline-block;font-weight:800;font-size:12px;color:#475569;min-width:24px}
.my-view-count.upstream{color:#9a6700}.my-view-count.downstream{color:#4338ca}
.my-view-empty{text-align:center!important;padding:22px!important;color:#64748b!important}
/* Milestone blocker rows stay on one line. Only the summary is truncated. */
.milestone-blocked-item{flex-wrap:nowrap;overflow:hidden;white-space:nowrap;gap:8px;min-width:0}
.milestone-blocked-content{display:flex;align-items:center;flex:1 1 auto;min-width:0;overflow:hidden;white-space:nowrap;gap:4px}
.milestone-blocked-content .milestone-blocked-priority,
.milestone-blocked-content .milestone-blocked-key{flex-shrink:0;margin:0}
.milestone-blocked-summary{display:block;min-width:0;flex:1 1 auto;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.milestone-blocked-editor{display:flex;align-items:center;gap:7px;justify-content:flex-end;flex:0 0 auto;flex-wrap:nowrap;width:auto;padding:0;margin-left:auto}
.milestone-blocked-editor .assignee-select{width:125px;max-width:125px;min-width:125px;margin-top:0;font-size:11px;text-overflow:ellipsis}
.milestone-blocked-editor .due-date{font-size:11px;flex-shrink:0}
.milestone-blocked-item .due-date-empty{color:#1d4ed8}
.milestone-blocked-actions{display:flex;align-items:center;gap:7px}
.milestone-blocked-copy{width:25px;height:25px;padding:4px;display:inline-flex;align-items:center;justify-content:center;border:1px solid #cbd5e1;border-radius:6px;background:#fff;color:#475569;cursor:pointer}
.milestone-blocked-copy:hover{background:#eef2ff;border-color:#a5b4fc;color:#4338ca}
.milestone-blocked-copy:focus-visible{outline:2px solid #6366f1;outline-offset:2px}
.milestone-blocked-copy:disabled{opacity:.45;cursor:default}
.milestone-blocked-copy.copied{background:#d1fae5;color:#047857;border-color:#6ee7b7}
.my-view-remarkable-toggle{display:inline-flex;align-items:center;gap:8px;font-size:12px;font-weight:650;color:#334155;white-space:nowrap;cursor:pointer}
.my-view-remarkable-toggle input{width:16px;height:16px;accent-color:#6366f1;cursor:pointer}
.my-view-remarkable-count{font-size:10px;color:#64748b}
.my-view-row .my-view-parent{min-width:175px;max-width:275px}
.my-view-row .my-view-parent a{display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.milestone-overview-card .card-meta{display:flex;align-items:center;flex-wrap:wrap;gap:7px}
.milestone-overview-card .assignee-select{min-width:160px;max-width:230px}
.milestone-overview-card .card-meta{padding-right:35px}

@media (max-width:1100px){.dashboard-stats{grid-template-columns:repeat(3,minmax(0,1fr))}.dashboard-health-stat{grid-column:span 2}}
@media (max-width:700px){.dashboard-stats{grid-template-columns:1fr}.dashboard-health-stat{grid-column:span 1}.dashboard-two-column{grid-template-columns:1fr}}
/* ── Full-screen milestone Gantt viewer ───────────────────────────────── */
.milestone-overview-card{position:relative}
.milestone-gantt-launch{position:absolute;bottom:10px;right:9px;z-index:5;width:28px;height:28px;display:grid;place-items:center;border:1px solid #cbd5e1;border-radius:6px;background:#fff;color:#4338ca;box-shadow:0 1px 3px #0001;cursor:pointer}
.milestone-gantt-launch:hover,.milestone-gantt-launch:focus-visible{background:#eef2ff;border-color:#818cf8;outline-offset:2px}
body.gantt-open{overflow:hidden}
#gantt-overlay[hidden]{display:none!important}
#gantt-overlay{position:fixed;inset:0;z-index:25000;background:rgba(15,23,42,.6);display:flex;align-items:stretch;justify-content:stretch;padding:12px}
.gantt-modal{display:flex;flex-direction:column;width:100%;height:100%;min-width:0;min-height:0;background:#fff;border-radius:12px;box-shadow:0 16px 55px #0004;overflow:hidden}
.gantt-header{padding:14px 18px;background:#172033;color:#fff;display:flex;gap:12px;justify-content:space-between;align-items:center;flex-wrap:wrap}
.gantt-header-main{min-width:0;flex:1}
.gantt-eyebrow{font-size:10px;letter-spacing:.09em;text-transform:uppercase;color:#93c5fd;font-weight:750}
.gantt-header h2{font-size:18px;margin:3px 0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.gantt-counts{color:#cbd5e1;font-size:11px}
.gantt-actions{display:flex;align-items:center;gap:8px;flex-wrap:wrap}
.gantt-action{border:1px solid #64748b;border-radius:7px;padding:8px 12px;background:#334155;color:#fff;font-size:12px;font-weight:750;cursor:pointer}
.gantt-action:hover{background:#475569}
.gantt-export{background:#4f46e5;border-color:#818cf8}
.gantt-export:hover{background:#4338ca}
.gantt-action:disabled{opacity:.6;cursor:wait}
.gantt-toolbar{display:flex;gap:14px;align-items:center;padding:9px 18px;background:#f8fafc;border-bottom:1px solid #e2e8f0;flex-wrap:wrap}
.gantt-scale-buttons{display:flex;gap:3px}
.gantt-scale{border:1px solid #cbd5e1;background:#fff;color:#334155;padding:5px 10px;border-radius:6px;font-size:11px;cursor:pointer}
.gantt-scale.active{background:#e0e7ff;color:#3730a3;border-color:#818cf8;font-weight:750}
.gantt-dependency-toggle{display:inline-flex;align-items:center;gap:6px;white-space:nowrap;color:#334155;font-size:11px;font-weight:650;cursor:pointer}
.gantt-dependency-toggle input{accent-color:#4f46e5;width:14px;height:14px}
.gantt-legend{display:flex;gap:10px;align-items:center;flex-wrap:wrap;font-size:11px;color:#64748b}
.gantt-legend [hidden]{display:none!important}
.gantt-legend b{width:9px;height:9px;border-radius:2px;display:inline-block;margin-right:3px;background:#64748b}
.gantt-legend .gantt-legend-milestone{display:inline-block;width:11px;height:11px;background:#b45309;transform:rotate(45deg);margin:0 6px 0 4px}
.gantt-export-status{font-size:11px;color:#c7d2fe;min-height:16px}
.gantt-chart-wrap{min-height:140px;flex:1;overflow:auto;overscroll-behavior:contain;background:#fff}
.gantt-canvas{--gantt-left:420px;position:relative;min-width:100%;}
.gantt-timeline-heading{display:flex;position:sticky;top:0;z-index:12;background:#e2e8f0;border-bottom:1px solid #cbd5e1}
.gantt-heading-label{position:sticky;left:0;z-index:14;flex:0 0 var(--gantt-left);width:var(--gantt-left);display:flex;flex-direction:column;justify-content:center;padding:9px 12px;font-size:11px;font-weight:850;color:#334155;background:#e2e8f0;border-right:1px solid #cbd5e1}
.gantt-heading-label small{font-size:10px;font-weight:500;color:#64748b}
.gantt-heading-scale{position:relative;flex:0 0 auto;background:linear-gradient(#dbeafe,#eff6ff);overflow: hidden;}
.gantt-month-label{background-color: #e1edfe;position:absolute;top:7px;white-space:nowrap;font-size:11px;font-weight:800;color:#1e40af;border-left:1px solid #93c5fd;padding-left:5px}
.gantt-day-label{position:absolute;top:32px;transform:translateX(-50%);text-align:center;font-size:9px;line-height:14px;color:#475569;white-space:nowrap;pointer-events:none;user-select:none}
.gantt-task-area{position:relative}
.gantt-task-row{position:relative;display:flex;min-height:66px;border-bottom:1px solid #e2e8f0}
.gantt-task-row:nth-of-type(even){background:#f8fafc}
.gantt-task-label{position:sticky;left:0;z-index:11;box-sizing:border-box;width:var(--gantt-left);flex:0 0 var(--gantt-left);display:flex;align-items:center;gap:10px;background:inherit;border-right:1px solid #cbd5e1;padding:6px 12px;white-space:normal;overflow-wrap:anywhere;font-size:11px;line-height:15px}
.gantt-task-info{flex:1 1 auto;min-width:0}
.gantt-assignee{display:flex;align-items:center;justify-content:center;align-self:center;flex:0 0 26px;width:26px;height:26px;box-sizing:border-box;border-radius:50%;background:#e2e8f0;color:#334155;border:1px solid #cbd5e1;font-size:10px;font-weight:800;line-height:1;white-space:nowrap;letter-spacing:-.2px}
.gantt-assignee.unassigned{background:#2563eb;border-color:#1d4ed8;color:#fff}
.gantt-task-row:nth-of-type(even) .gantt-task-label{background:#f8fafc}
.gantt-task-row:nth-of-type(odd) .gantt-task-label{background:#fff}
.gantt-task-info>a{color:#4338ca;font-weight:800;text-decoration:none}
.gantt-task-info>a:hover{text-decoration:underline}
.gantt-task-summary{display:block;white-space:normal;overflow-wrap:anywhere;color:#475569;margin:2px 0}
 .gantt-task-dates{display:block;color:#64748b;font-size:9px;white-space:normal;overflow-wrap:anywhere}
/* Narrow: a single-line key and summary, with less horizontal label space. */
.gantt-canvas.gantt-narrow .gantt-task-row{min-height:34px}
.gantt-canvas.gantt-narrow .gantt-task-label{white-space:nowrap;overflow:hidden;min-width:0}
.gantt-canvas.gantt-narrow .gantt-task-info{display:flex;align-items:center;gap:6px;min-width:0;overflow:hidden}
.gantt-canvas.gantt-narrow .gantt-task-info>a,.gantt-canvas.gantt-narrow .gantt-milestone-tag{flex:0 0 auto}
.gantt-canvas.gantt-narrow .gantt-task-summary{min-width:0;flex:1;display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;margin:0;overflow-wrap:normal}
.gantt-canvas.gantt-narrow .gantt-task-dates,.gantt-canvas.gantt-narrow .gantt-heading-label small{display:none}
/* Pointer-events stay off: hovering the timeline must not stop ticket links or bar tooltips. */
.gantt-hover-guide{position:absolute;top:0;bottom:0;width:0;border-left:1px solid rgba(220,38,38,.48);box-shadow:0 0 2px rgba(220,38,38,.12);pointer-events:none;z-index:10}
.gantt-heading-scale .gantt-hover-guide{z-index:20}
.gantt-hover-guide[hidden],.gantt-hover-date[hidden]{display:none!important}
.gantt-hover-date{position:absolute;top:44px;z-index:21;transform:translateX(-50%);pointer-events:none;white-space:nowrap;border:1px solid #fecaca;border-radius:3px;background:#fff7f7;color:#991b1b;padding:1px 4px;font-size:10px;font-weight:700;line-height:14px;box-shadow:0 1px 2px #0001}
.gantt-milestone-tag{font-size:8px;color:#92400e;background:#fef3c7;border-radius:3px;padding:2px 4px;margin-left:5px;font-weight:800}
.gantt-task-track{position:relative;flex:0 0 auto}
.gantt-calendar-overlay{pointer-events:none;position:absolute;top:0;bottom:0;z-index:0}
.gantt-week-line{position:absolute;top:0;bottom:0;border-left:1px dashed #e2e8f0}
.gantt-today{position:absolute;top:0;bottom:0;border-left:2px solid #ef4444;z-index:10;pointer-events:none;box-shadow:0 0 0 1px rgba(255,255,255,.4)}
.gantt-links-svg{position:absolute;top:0;z-index:2;overflow:visible;pointer-events:none}
.gantt-bar{position:absolute;z-index:3;top:50%;transform:translateY(-50%);height:12px;min-width:4px;border-radius:4px;opacity:.95;box-shadow:0 1px 2px #0002}
.gantt-diamond{position:absolute;top:50%;z-index:4;width:13px;height:13px;transform:translateY(-50%) rotate(45deg);border:1px solid #fff;box-shadow:0 1px 2px #0003}
.gantt-unscheduled{border-top:1px solid #dbe2ea;background:#fff;flex:0 0 auto;max-height:25vh;overflow:auto;padding:10px 18px;color:#475569}
.gantt-unscheduled-heading{font-size:12px;font-weight:850;color:#334155;margin-bottom:7px}
.gantt-unscheduled-item{display:grid;grid-template-columns:85px minmax(0,1fr) 250px;gap:10px;padding:5px 0;border-bottom:1px solid #f1f5f9;font-size:11px;align-items:center}
.gantt-unscheduled-item a{color:#4338ca;font-weight:750;text-decoration:none}
.gantt-unscheduled-item span{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.gantt-unscheduled-item strong{color:#b45309}
.gantt-unscheduled-empty,.gantt-schedule-notes{font-size:11px;color:#64748b}
.gantt-schedule-notes{margin-top:9px}
@media(max-width:700px){#gantt-overlay{padding:0}.gantt-modal{border-radius:0}.gantt-header{padding:10px}.gantt-header h2{font-size:14px}.gantt-unscheduled-item{grid-template-columns:70px minmax(0,1fr)}.gantt-unscheduled-item strong{grid-column:2}}


/* Project overview: tab-specific sortable/paginated My View tables. */
.dashboard-table-tabs{top:0;flex-wrap:nowrap;overflow-x:auto;overscroll-behavior-x:contain;scrollbar-width:thin;padding:10px 1px;scroll-margin-top:15px}
.dashboard-table-tabs button{flex:0 0 auto;white-space:nowrap}
.dashboard-table-section{scroll-margin-top:60px}
/* Shared fixed column tracks keep every standard column at the same x-position
   across all tabs. Risk columns extend to the right only on Needs Attention. */
/* Fill the visible table region, while retaining the stable minimum column tracks
   and horizontal scrolling at narrower browser widths. */
.dashboard-table-section .my-view-table{table-layout:fixed;width:max(100%,1374px);min-width:100%}
.dashboard-table-section .my-view-table.has-risk-columns{width:max(100%,1739px);min-width:100%}
.dashboard-table-section .my-view-row td{min-width:0;max-width:none;box-sizing:border-box;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;height:44px}
.dashboard-table-section .my-view-row .my-view-summary{min-width:0;max-width:none;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.dashboard-table-section .my-view-row .my-view-parent a{display:inline-block;max-width:100%;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;vertical-align:middle}
.dashboard-table-section .my-view-row .status-badge{display:inline-block;max-width:100%;box-sizing:border-box;overflow:hidden;text-overflow:ellipsis;vertical-align:middle}
/* Populating the lazy native select must never resize its table column. */
.dashboard-table-section .dashboard-assignee-select{display:block;box-sizing:border-box;width:100%;min-width:0;max-width:100%;height:25px;margin:0;padding:2px 19px 2px 7px;overflow:hidden;white-space:nowrap;text-overflow:ellipsis}
.dashboard-table-section .dashboard-reason-cell{min-width:0;max-width:none}
.dashboard-reason-list{display:block;max-width:100%;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.dashboard-risk-score{font-weight:850;color:#b91c1c;font-variant-numeric:tabular-nums}
.dashboard-risk-reason{display:inline-flex;margin:2px 4px 2px 0;padding:3px 6px;border-radius:5px;background:#fff1f2;color:#9f1239;font-size:10px;white-space:nowrap}
.dashboard-clear-attention-filter{margin-top:7px;border:1px solid #fda4af;border-radius:20px;background:#fff1f2;color:#9f1239;padding:4px 10px;font-size:11px;cursor:pointer}
.dashboard-table-pagination{display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:10px;padding-top:12px;color:#64748b;font-size:11px}
/* The pagination bar remains at the bottom of the visible dashboard while
   its table is in view; it scrolls away at the end of the table section. */
.dashboard-table-section .dashboard-table-pagination.bottom{
  position:sticky;bottom:0;z-index:19;
  background:#fff;border-top:1px solid #dbe2ea;
  margin:12px -15px -15px;padding:10px 15px 12px;
  border-radius:0 0 10px 10px;
  box-shadow:0 -5px 14px rgba(15,23,42,.07);
}
.dashboard-table-pagination>div{display:flex;align-items:center;gap:6px;flex-wrap:wrap}
.dashboard-table-pagination .dashboard-page-number{margin:0 5px;white-space:nowrap}
.dashboard-table-pagination .dashboard-page-count{white-space:nowrap;font-variant-numeric:tabular-nums}
.dashboard-table-pagination button{padding:6px 10px;border:1px solid #cbd5e1;border-radius:6px;background:#fff;color:#334155;font:inherit;font-weight:750;cursor:pointer}
.dashboard-table-pagination button:hover:not(:disabled){background:#eef2ff;color:#4338ca}
.dashboard-table-pagination button:disabled{opacity:.45;cursor:default}
.dashboard-workload-panel .dashboard-section-group{min-width:0;margin:0}
.dashboard-attention-stat .dashboard-stat-value{font-size:clamp(18px,2vw,23px);font-variant-numeric:tabular-nums;white-space:nowrap}
.milestone-overview-card .card-top{align-items:center;flex-wrap:wrap}
.milestone-overview-card .milestone-card-top-right{display:flex;align-items:center;justify-content:flex-end;flex-wrap:nowrap;gap:5px;min-width:0;max-width:100%}
.milestone-overview-card .milestone-card-top-right .epic-badge{margin:0;max-width:230px;min-width:0;box-sizing:border-box;line-height:17px;height:25px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;flex:0 1 auto}
.milestone-overview-card .milestone-card-top-right .status-badge{display:inline-flex;align-items:center;box-sizing:border-box;height:25px;line-height:19px;margin:0;white-space:nowrap}
.milestone-overview-card .card-meta{padding-right:0}
.milestone-chain-meta{display:flex;align-items:center;gap:14px;margin-top:9px;padding-top:9px;border-top:1px solid #e2e8f0}
.milestone-chain-meta .my-view-count{font-size:11px}
.milestone-chain-meta .milestone-gantt-launch{position:static;flex:0 0 28px;margin-left:auto}
@media(max-width:900px){.dashboard-table-tabs{top:0}.dashboard-stats{grid-template-columns:repeat(2,minmax(0,1fr))}.dashboard-stat.dashboard-attention-stat{grid-column:span 2}}
@media(max-width:600px){.dashboard-stats{grid-template-columns:1fr}.dashboard-stat.dashboard-attention-stat,.dashboard-health-stat{grid-column:span 1}.dashboard-table-pagination{align-items:flex-start}.dashboard-table-pagination>div{gap:4px}}

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
          <option value="my-view">My view</option>
          <option value="dashboard">Project overview</option>
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
            <option value="nextMonth">Due in the next 31 days</option>
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
      <button class="view-switch" data-view="my-view" type="button">My view</button>
      <button class="view-switch" data-view="dashboard" type="button">Project overview</button>
      <button class="view-switch" data-view="milestone" type="button">Milestones</button>
    </div>
    <button class="btn btn-settings" id="settings" title="Settings" aria-label="Settings">&#9881;</button>
    <button class="btn btn-settings" id="faqs-open" title="FAQs" aria-label="FAQs" style="font-size:15px;font-weight:800">?</button>
    <button class="btn btn-refresh" id="refresh" title="Refresh from Jira">&#x21BB;</button>
  </div>
</header>

<button class="milestone-back" id="milestone-back" type="button"></button>
<div id="error"></div>
<div id="faqs-modal" role="dialog" aria-modal="true" aria-labelledby="faqs-title">
  <div class="faqs-dialog">
    <div class="faqs-header"><h2 id="faqs-title">Frequently asked questions</h2><button class="ticket-preview-close" id="faqs-close" type="button" aria-label="Close FAQs">Close ×</button></div>
    <div class="faqs-search-wrap"><label class="sr-only" for="faqs-search">Search FAQs</label><input id="faqs-search" type="search" placeholder="Search questions and answers…" autocomplete="off"></div>
    <div id="faqs-list" aria-live="polite"><div class="faqs-empty">Loading FAQs…</div></div>
    <div class="faqs-footer"><a class="faqs-ask" href="mailto:edward.dyer@warwick.ac.uk?subject=Jira%20Dependency%20Map%20Question">Ask a question</a></div>
  </div>
</div>
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
<div id="gantt-overlay" role="dialog" aria-modal="true" aria-labelledby="gantt-title" hidden>
  <section class="gantt-modal">
    <div class="gantt-header">
      <div class="gantt-header-main"><div class="gantt-eyebrow">Milestone timeline</div><h2 id="gantt-title"></h2><div id="gantt-counts" class="gantt-counts"></div></div>
      <div class="gantt-actions"><span id="gantt-export-status" class="gantt-export-status" role="status" aria-live="polite"></span><button type="button" class="gantt-action gantt-export" id="gantt-export">↓ Download PDF</button><button type="button" class="gantt-action" id="gantt-close">Close ×</button></div>
    </div>
    <div class="gantt-toolbar"><div class="gantt-scale-buttons" role="group" aria-label="Timeline zoom"><button type="button" class="gantt-scale" data-gantt-scale="6">Compact</button><button type="button" class="gantt-scale active" data-gantt-scale="12">Normal</button><button type="button" class="gantt-scale" data-gantt-scale="20">Expanded</button></div><label class="gantt-dependency-toggle"><input type="checkbox" id="gantt-show-dependencies" checked> Show dependencies</label><label class="gantt-dependency-toggle"><input type="checkbox" id="gantt-narrow"> Narrow</label><div class="gantt-legend"><span id="gantt-legend-active"><b style="background:#2563eb"></b>In progress</span><span id="gantt-legend-completed"><b style="background:#16a34a"></b>Completed</span><span id="gantt-legend-remarkable"><b style="background:#d97706"></b>With Remarkable</span><span id="gantt-legend-milestone"><i class="gantt-legend-milestone"></i>Milestone</span><span id="gantt-legend-dependencies">→ Dependencies</span><span style="color:#ef4444">│ Today</span></div></div>
    <div id="gantt-chart" class="gantt-chart-wrap" aria-label="Milestone Gantt timeline"></div>
    <div id="gantt-unscheduled" class="gantt-unscheduled"></div>
  </section>
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
  showMyView:false,
  myViewSavedSorts:{}, myViewSort:{field:'priority',direction:'asc'},
  dashboardSavedSorts:{},dashboardDraftSorts:{},dashboardTab:'needs-attention',dashboardPages:{},dashboardAttentionFilter:'',
  startingView:'default',
  showMiniMap:true, customJql:'', useJiraModal:false, ganttScale:12, ganttShowDependencies:true, ganttNarrow:false, currentUserName:'', currentUserAccountId:'', personalUserOverride:false, personalTicketFilter:'',
  displayIssues:[], displayEdges:[], displayLevels:0,
  hoverKey:null, hoverLockKey:null,
  returnMilestoneKey:null,
  dashboardReturnSection:null,
  // Preserve each view's independent scroll position across board rebuilds.
  scrollPositions:{
    main:{appLeft:0,appTop:0,columns:{}},
    locked:{appLeft:0,appTop:0,columns:{}},
    milestone:{appLeft:0,appTop:0,columns:{}},
    'my-view':{appLeft:0,appTop:0,columns:{}}
  }
};
// Initial credential data is obtained by initialiseApp once; do not trigger
// another Jira /myself call here before the first board loads.

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
let savedFullBoardView=null;

function syncSharedViewUrl(){
  const selectedKey=(!state.showDashboard && !state.showMilestones && !state.showMyView && state.lockedKey)
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
    state.ganttScale=[6,12,20].includes(saved.ganttScale) ? saved.ganttScale : 12;
    state.ganttShowDependencies=saved.ganttShowDependencies!==false;
    state.ganttNarrow=saved.ganttNarrow===true;
    state.startingView=['default','my-view','dashboard','milestone'].includes(saved.startingView) ? saved.startingView : 'default';
    state.myViewSavedSorts=(saved.myViewSorts && typeof saved.myViewSorts==='object' && !Array.isArray(saved.myViewSorts)) ? saved.myViewSorts : {};
    state.dashboardSavedSorts=(saved.dashboardTabSorts && typeof saved.dashboardTabSorts==='object' && !Array.isArray(saved.dashboardTabSorts)) ? saved.dashboardTabSorts : {};
    state.dashboardDraftSorts={...state.dashboardSavedSorts};
    if(saved.personalUserAccountId || saved.personalUserName){
      state.currentUserAccountId=saved.personalUserAccountId||'';
      state.currentUserName=saved.personalUserName||'';
      state.personalUserOverride=true;
    }
    resetMyViewSort();
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
    const response=await fetch('/api/preferences',{
      method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({
        showCompleted:!!state.showCompleted, filterUser:state.filterUser||'', filterDue:state.filterDue||'all',
        includeWithRemarkable:state.includeWithRemarkable!==false,
        customJql:state.customJql||'', useJiraModal:!!state.useJiraModal,
        showMiniMap:state.showMiniMap!==false, startingView:state.startingView || 'default',
        ganttScale:state.ganttScale, ganttShowDependencies:state.ganttShowDependencies!==false, ganttNarrow:state.ganttNarrow===true,
        personalUserAccountId:state.currentUserAccountId||'', personalUserName:state.currentUserName||'',
        myViewSorts:state.myViewSavedSorts||{}, dashboardTabSorts:state.dashboardSavedSorts||{}
      }),cache:'no-store'
    });
    if(!response.ok) throw new Error('Preferences API returned '+response.status);
    return true;
  }catch(e){ console.warn('Could not save persistent preferences.',e); return false; }
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
  state.personalTicketFilter='';
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
  if(settingsStartingView) settingsStartingView.value = ['default','my-view','dashboard','milestone'].includes(state.startingView) ? state.startingView : 'default';
}
function setStartingView(value){
  state.startingView = ['default','my-view','dashboard','milestone'].includes(value) ? value : 'default';
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
const faqsModal=document.getElementById('faqs-modal');
const faqsList=document.getElementById('faqs-list');
const faqsSearch=document.getElementById('faqs-search');
function highlightFaqText(root, query){
  // Restore the original text before applying the current query, then merge
  // adjacent text nodes. This avoids progressively fragmenting the DOM as the
  // user types and supports matches that span inline markup such as <strong>.
  root.querySelectorAll('mark.faq-highlight').forEach(mark=>mark.replaceWith(document.createTextNode(mark.textContent||'')));
  root.normalize();
  if(!query) return;
  const walker=document.createTreeWalker(root,NodeFilter.SHOW_TEXT,{acceptNode(node){return node.parentElement && !node.parentElement.closest('script,style,mark') ? NodeFilter.FILTER_ACCEPT : NodeFilter.FILTER_REJECT;}});
  const nodes=[];let fullText='';
  while(walker.nextNode()){const node=walker.currentNode;nodes.push({node,start:fullText.length,end:fullText.length+(node.nodeValue||'').length});fullText+=node.nodeValue||'';}
  if(!fullText) return;
  const escaped=query.replace(/[.*+?^${}()|[\]\\]/g,'\\$&');
  let regex;try{regex=new RegExp(escaped,'ig')}catch(_){return}
  const matches=[];let match;while((match=regex.exec(fullText))!==null){matches.push({start:match.index,end:match.index+match[0].length});if(!match[0].length)regex.lastIndex++;}
  if(!matches.length)return;
  nodes.forEach(({node,start,end})=>{
    const value=node.nodeValue||'';const overlaps=matches.filter(m=>m.start<end&&m.end>start);if(!overlaps.length)return;
    const frag=document.createDocumentFragment();let cursor=0;
    overlaps.forEach(m=>{const a=Math.max(0,m.start-start),b=Math.min(value.length,m.end-start);if(a>cursor)frag.append(document.createTextNode(value.slice(cursor,a)));if(b>a){const mark=document.createElement('mark');mark.className='faq-highlight';mark.textContent=value.slice(a,b);frag.append(mark);cursor=b;}});
    if(cursor<value.length)frag.append(document.createTextNode(value.slice(cursor)));
    node.replaceWith(frag);
  });
}
// Sitebuilder category tags (e.g. "3 Milestones and Gantt") control the
// heading order; FAQ titles (e.g. "13. How do I…?") control question order.
// Leading numbers are metadata, not part of the displayed text.
function parseFaqOrder(value, isCategory=false){
  const text=String(value||'').trim();
  const match=isCategory ? text.match(/^(\d+)\s+(.+)$/s) : text.match(/^(\d+)\s*[.)]\s*(.+)$/s);
  return match ? {order:Number(match[1]),label:match[2].trim()} : {order:Number.POSITIVE_INFINITY,label:text};
}
function filterFaqs(){
  const query=faqsSearch.value.trim();const needle=query.toLocaleLowerCase();let visible=0;
  faqsList.querySelectorAll('.faq-section').forEach(section=>{
    let shownInSection=0;
    section.querySelectorAll('.faq-item').forEach(item=>{
      const match=!needle||(item.dataset.searchText||'').includes(needle);
      item.hidden=!match;
      if(match){visible++;shownInSection++;}
      item.open=!!needle&&match;
      highlightFaqText(item.querySelector('.faq-question'),query);
      highlightFaqText(item.querySelector('.faq-answer'),query);
    });
    section.hidden=shownInSection===0;
    // Section headings are for organisation only, not search matches.
    highlightFaqText(section.querySelector('.faq-section-title'),'');
  });
  let empty=faqsList.querySelector('.faqs-no-results');
  if(!visible&&query){if(!empty){empty=document.createElement('div');empty.className='faqs-empty faqs-no-results';faqsList.appendChild(empty);}empty.textContent='No FAQs match your search.';}else if(empty)empty.remove();
}
function renderFaqs(items){
  faqsList.innerHTML='';
  if(!items.length){faqsList.innerHTML='<div class="faqs-empty">No FAQs are currently available.</div>';return;}
  const groups=new Map();
  items.forEach((item,index)=>{
    const title=parseFaqOrder(item.title);
    const categories=(Array.isArray(item.categories)?item.categories:[])
      .map(category=>parseFaqOrder(category,true))
      .filter(category=>category.label)
      .sort((a,b)=>a.order-b.order||a.label.localeCompare(b.label));
    // One primary section per question, even if Sitebuilder has multiple tags.
    const category=categories[0]||{order:Number.POSITIVE_INFINITY,label:'Other questions'};
    const id=category.order+'::'+category.label;
    if(!groups.has(id))groups.set(id,{...category,items:[]});
    groups.get(id).items.push({title,body:item.parsedContentBody||'',index});
  });
  const orderedGroups=[...groups.values()].sort((a,b)=>a.order-b.order||a.label.localeCompare(b.label));
  orderedGroups.forEach((group,groupIndex)=>{
    const section=document.createElement('section');section.className='faq-section';
    const heading=document.createElement('h3');heading.className='faq-section-title';
    heading.id='faq-section-heading-'+groupIndex;heading.textContent=group.label;
    section.setAttribute('aria-labelledby',heading.id);section.appendChild(heading);
    group.items.sort((a,b)=>a.title.order-b.title.order||a.title.label.localeCompare(b.title.label,undefined,{numeric:true})||a.index-b.index);
    group.items.forEach(item=>{
      const details=document.createElement('details');details.className='faq-item';
      const question=document.createElement('summary');question.className='faq-question';
      question.textContent=item.title.label||'Untitled question';
      const answer=document.createElement('div');answer.className='faq-answer';answer.innerHTML=item.body;
      // Match the FAQ's question and answer, not its category heading.
      details.dataset.searchText=(question.textContent+' '+answer.textContent).toLocaleLowerCase();
      details.append(question,answer);section.appendChild(details);
    });
    faqsList.appendChild(section);
  });
  filterFaqs();
}
async function openFaqs(){
  faqsModal.classList.add('open');faqsSearch.value='';
  faqsList.innerHTML='<div class="faqs-empty">Loading FAQs…</div>';faqsSearch.focus();
  try{
    // Always request the latest FAQ entries when reopening the modal.
    const r=await fetch('/api/faqs?ts='+Date.now(),{cache:'no-store'});
    const data=await r.json();
    if(!r.ok||!Array.isArray(data.items))throw new Error(data.error||'Unable to load FAQs');
    renderFaqs(data.items);
  }catch(e){faqsList.innerHTML='<div class="faqs-empty">FAQs could not be loaded. Please try again later.</div>';console.error('[FAQs] Load failed:',e);}
}
document.getElementById('faqs-open').addEventListener('click',openFaqs);
document.getElementById('faqs-close').addEventListener('click',()=>faqsModal.classList.remove('open'));
faqsModal.addEventListener('click',e=>{if(e.target===faqsModal)faqsModal.classList.remove('open');});
faqsSearch.addEventListener('input',filterFaqs);
document.addEventListener('keydown',e=>{if(e.key==='Escape')faqsModal.classList.remove('open');});

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
    if(!state.personalUserOverride){
      state.currentUserName=data.displayName||'';
      state.currentUserAccountId=data.accountId||'';
    }
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
    // Independent local endpoints can run together; neither depends on Jira
    // issue downloads, and no credential-status check is duplicated at startup.
    const [r,configResponse] = await Promise.all([
      fetch('/api/credential-status',{cache:'no-store'}),
      fetch('/api/config?ts='+Date.now(),{cache:'no-store'})
    ]);
    const [data,config] = await Promise.all([
      r.json().catch(()=>({})),configResponse.json().catch(()=>({}))
    ]);
    if(!r.ok || data.error){
      showCredentialError(data.error || 'Unable to access the Windows Credential Manager.');
      openCredentialModal(false);
      return;
    }
    if(!data.configured){openCredentialModal(false);return;}
    if(!configResponse.ok || !config.jql){
      throw new Error(config.error || 'Unable to load the default Jira JQL.');
    }
    DEFAULT_JQL=String(config.jql).trim();
    // Saved manual user mapping takes precedence over credential discovery.
    if(!state.personalUserOverride){
      state.currentUserName=data.displayName || (String(data.email||'').toLowerCase()==='edward.dyer@warwick.ac.uk'?'Edward Dyer':'');
      state.currentUserAccountId=data.accountId||'';
    }
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
  let visibleExternal = false;
  let visibleCycle = false;
  const byKey=state.displayByKey || new Map();

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
    let personalMatch = true;
    if(state.personalTicketFilter === 'unblocked' || state.personalTicketFilter === 'blocked-by-others'){
      const issue=byKey.get(card.dataset.key);
      const activeBlockers=((issue&&issue.blockers)||[]).map(k=>byKey.get(k)).filter(Boolean);
      if(state.personalTicketFilter === 'unblocked') personalMatch=activeBlockers.length===0;
      else personalMatch=activeBlockers.some(i=>i.assigneeAccountId!==state.currentUserAccountId);
    }

    const match = textMatch && userMatch && dueMatch && personalMatch;
    card.hidden = !match;
    if(match){
      visibleTotal++;
      if(card.classList.contains('external')) visibleExternal=true;
      if(card.classList.contains('cycle')) visibleCycle=true;
    }

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

  // The legend describes the tickets on screen, not unrelated hidden work.
  const externalStatus=document.getElementById('external-status');
  const cycleStatus=document.getElementById('cycle-status');
  if(externalStatus) externalStatus.style.display=visibleExternal?'inline-flex':'none';
  if(cycleStatus) cycleStatus.style.display=visibleCycle?'inline-flex':'none';
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
  if(board.classList.contains('my-view-board') || app.classList.contains('my-view-mode')) return 'my-view';
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
    const entry = {top:cards.scrollTop};
    // Remember the first actually visible ticket as a scroll anchor. If a
    // refresh changes card heights or sort order, keep that ticket at the
    // same position instead of letting the column jump or appear to bounce.
    const viewport=cards.getBoundingClientRect();
    for(const card of cards.querySelectorAll(':scope > .card:not([hidden])')){
      const rect=card.getBoundingClientRect();
      if(rect.bottom>viewport.top+1 && rect.top<viewport.bottom){
        entry.anchorKey=card.dataset.key;
        entry.anchorOffset=rect.top-viewport.top;
        break;
      }
    }
    columns[level]=entry;
  });
  saved.columns=columns;
  if(mode==='milestone'){
    const lists={};
    board.querySelectorAll('.milestone-item').forEach(item=>{
      const key=item.querySelector('[data-milestone-card]')?.dataset.milestoneCard;
      const list=item.querySelector('.milestone-blocked-list');
      if(key && list) lists[key]=list.scrollTop;
    });
    saved.milestoneLists=lists;
  }
}

function restoreBoardScroll(){
  const app=document.getElementById('app');
  if(!app) return;
  const saved=state.scrollPositions[getRenderedViewMode()];
  if(!saved) return;
  app.scrollLeft=saved.appLeft || 0;
  app.scrollTop=saved.appTop || 0;

  board.querySelectorAll('.column').forEach((column,index)=>{
    const cards=column.querySelector('.cards');
    if(!cards) return;
    const level=column.dataset.level!=null?column.dataset.level:String(index);
    const entry=(saved.columns || {})[level];
    if(entry===undefined) return;
    // Accept older saved snapshots that stored a simple numeric scrollTop.
    cards.scrollTop=typeof entry==='number'?entry:(entry.top || 0);
    if(!entry || typeof entry!=='object' || !entry.anchorKey) return;
    const anchor=cards.querySelector('.card[data-key="'+CSS.escape(entry.anchorKey)+'"]');
    if(!anchor || anchor.hidden) return;
    const actualOffset=anchor.getBoundingClientRect().top-cards.getBoundingClientRect().top;
    cards.scrollTop+=actualOffset-entry.anchorOffset;
  });
}

function preserveBoardScrollDuringRender(){
  // All cards now exist synchronously. Restore before the browser's first
  // paint, rather than across multiple animation frames while heights grow.
  if(state.revealSelectedKey){
    const app=document.getElementById('app');
    if(app){app.scrollLeft=0;app.scrollTop=0;}
    board.querySelectorAll('.cards').forEach(cards=>{
      cards.scrollTop=0;
      cards.scrollLeft=0;
    });
    revealSelectedCard(state.revealSelectedKey);
    state.revealSelectedKey=null;
  }else{
    restoreBoardScroll();
  }
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

// The graph is rebuilt only when issue data or dependencies change, or when the
// completed toggle changes. Switching board views does not rerun graph layout.
let graphRevision=0;
let structuralGraphCache=null;
function invalidateGraphCache(){
  graphRevision++;
  structuralGraphCache=null;
  assigneeCache=null;
}

function calculateGraphLayout(issues, edges){
  const keys=new Set(issues.map(i=>i.key));
  const outgoing=new Map(), incoming=new Map();
  keys.forEach(k=>{outgoing.set(k,[]);incoming.set(k,[]);});
  for(const e of edges){
    if(!keys.has(e.from) || !keys.has(e.to)) continue;
    outgoing.get(e.from).push(e.to);
    incoming.get(e.to).push(e.from);
  }

  // Iterative Kosaraju: every member of a cycle shares its component/column.
  const visited=new Set(), finished=[];
  for(const start of keys){
    if(visited.has(start)) continue;
    visited.add(start);
    const stack=[{key:start,index:0}];
    while(stack.length){
      const frame=stack[stack.length-1], neighbours=outgoing.get(frame.key);
      if(frame.index>=neighbours.length){ finished.push(frame.key);stack.pop();continue; }
      const next=neighbours[frame.index++];
      if(!visited.has(next)){ visited.add(next);stack.push({key:next,index:0}); }
    }
  }
  const componentOf=new Map(), components=[];
  for(let index=finished.length-1;index>=0;index--){
    const start=finished[index];
    if(componentOf.has(start)) continue;
    const id=components.length, members=[], stack=[start];
    componentOf.set(start,id);
    while(stack.length){
      const key=stack.pop();members.push(key);
      for(const next of incoming.get(key)){
        if(!componentOf.has(next)){componentOf.set(next,id);stack.push(next);}
      }
    }
    components.push(members);
  }
  const cycleKeys=new Set();
  components.forEach(members=>{if(members.length>1) members.forEach(k=>cycleKeys.add(k));});
  edges.forEach(e=>{if(e.from===e.to && keys.has(e.from)) cycleKeys.add(e.from);});

  const successors=components.map(()=>new Set()), indegree=components.map(()=>0);
  const byKey=new Map(issues.map(i=>[i.key,i]));
  const componentLevels=components.map(group=>group.some(k=>(byKey.get(k).externalBlockers||[]).length)?1:0);
  for(const e of edges){
    const from=componentOf.get(e.from),to=componentOf.get(e.to);
    if(from===undefined || to===undefined || from===to || successors[from].has(to)) continue;
    successors[from].add(to);indegree[to]++;
  }
  const queue=[];
  indegree.forEach((n,id)=>{if(n===0) queue.push(id);});
  for(let cursor=0;cursor<queue.length;cursor++){
    const from=queue[cursor];
    for(const to of successors[from]){
      componentLevels[to]=Math.max(componentLevels[to],componentLevels[from]+1);
      if(--indegree[to]===0) queue.push(to);
    }
  }
  const levels=new Map();
  keys.forEach(key=>levels.set(key,componentLevels[componentOf.get(key)]||0));
  return {levels,cycleKeys,outgoing,incoming};
}

function computeDisplayData(){
  const unchanged=structuralGraphCache &&
    structuralGraphCache.issues===state.issues &&
    structuralGraphCache.edges===state.edges &&
    structuralGraphCache.revision===graphRevision &&
    structuralGraphCache.showCompleted===state.showCompleted;
  if(!unchanged){
    const structuralIssues=state.showCompleted ? state.issues :
      state.issues.filter(i=>!isCompletedStatus(i.status));
    const keys=new Set(structuralIssues.map(i=>i.key));
    const structuralEdges=state.edges.filter(e=>keys.has(e.from)&&keys.has(e.to));
    const layout=calculateGraphLayout(structuralIssues,structuralEdges);
    structuralGraphCache={issues:state.issues,edges:state.edges,revision:graphRevision,
      showCompleted:state.showCompleted,structuralIssues,structuralEdges,...layout};
  }
  const graph=structuralGraphCache;
  // Hidden With Remarkable items still influence structural depth.
  const issues=(!state.lockedKey&&!state.showMilestones&&!state.includeWithRemarkable)
    ? graph.structuralIssues.filter(i=>(i.status||'').trim()!=='With Remarkable')
    : graph.structuralIssues;
  const keys=new Set(issues.map(i=>i.key));
  state.displayEdges=graph.structuralEdges.filter(e=>keys.has(e.from)&&keys.has(e.to));
  state.displayIssues=issues.map(i=>({...i,level:graph.levels.get(i.key)||0,cycle:graph.cycleKeys.has(i.key)}));
  state.displayByKey=new Map(state.displayIssues.map(i=>[i.key,i]));
  state.displayOutgoing=new Map(),state.displayIncoming=new Map();
  keys.forEach(k=>{state.displayOutgoing.set(k,[]);state.displayIncoming.set(k,[]);});
  state.displayEdges.forEach(e=>{state.displayOutgoing.get(e.from).push(e.to);state.displayIncoming.get(e.to).push(e.from);});
  state.displayLevels=state.displayIssues.length?Math.max(...state.displayIssues.map(i=>i.level)):0;
}

// ── Dependency-chain traversal (ancestors of key) ─────────────────────────
function traverseDisplayGraph(start, adjacent){
  const keep=new Set([start]),queue=[start];
  for(let cursor=0;cursor<queue.length;cursor++){
    for(const next of (adjacent.get(queue[cursor])||[])){
      if(!keep.has(next)){keep.add(next);queue.push(next);}
    }
  }
  return keep;
}
function blockedChain(key){return traverseDisplayGraph(key,state.displayOutgoing);}
function chain(key){return traverseDisplayGraph(key,state.displayIncoming);}

// The selected view normally shows the upstream chain; optional downstream
// cards are added without changing the blockers' layout depth.
function activeSelectionChain(key){
  const keep=chain(key);
  if(state.showBlocked) blockedChain(key).forEach(k=>keep.add(k));
  return keep;
}
function computeHoverChain(key){
  return new Set([...chain(key),...blockedChain(key)]);
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
  invalidateGraphCache();
  const layout=calculateGraphLayout(state.issues,state.edges);
  state.issues.forEach(i=>{
    i.level=layout.levels.get(i.key)||0;
    i.cycle=layout.cycleKeys.has(i.key);
  });
  state.levels=state.issues.length?Math.max(...state.issues.map(i=>i.level)):0;
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
  // source = blocker, target = blocked. Links to unavailable Jira issues
  // (often archived) are informational, not graph edges, but can be removed.
  const isInternal=state.edges.some(e => e.from === source && e.to === target);
  const b=state.issues.find(i=>i.key===target);
  const isExternal=!!b && (b.externalBlockers||[]).some(x=>x.key===source);
  const isUnavailable=!!b && (b.unavailableBlockers||[]).some(x=>x.key===source);
  if(!isInternal && !isExternal && !isUnavailable) return;
  pushHistory();
  if(isInternal) state.edges = state.edges.filter(e => !(e.from === source && e.to === target));
  const a = state.issues.find(i => i.key === source);
  if(a) a.blocked = (a.blocked || []).filter(k => k !== target);
  if(b){
    b.blockers = (b.blockers || []).filter(k => k !== source);
    b.externalBlockers = (b.externalBlockers || []).filter(x => x.key !== source);
    b.unavailableBlockers = (b.unavailableBlockers || []).filter(x => x.key !== source);
  }
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
    const focused=document.activeElement;
    const opt = (focused?.matches?.('.assignee-select') && focused.closest('.card, .dashboard-ticket')?.dataset.key===key) ? focused : [...document.querySelectorAll('.assignee-select')].find(s => s.closest('.card, .dashboard-ticket')?.dataset.key === key);
    const name = opt && opt.selectedOptions[0] ? opt.selectedOptions[0].textContent : 'Unassigned';
    issue.assigneeAccountId = value || null;
    issue.assignee = name;
    assigneeCache=null;
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
    const tooltip = x ? ((x.summary || x.key) + ' - ' + (x.assignee || 'Unassigned') + ' (' + (x.priority || 'No priority') + ')') : (extraCls && extraCls.includes('external-key') ? 'Linked blocker not returned by Jira: ' + k : k);
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
    end.setDate(end.getDate()+31);
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

// All due-date checks must use the same *active* links as the normal board
// (Show completed OFF). Completed tickets cannot be an intermediate hop in a
// risk path. Do not apply the With Remarkable visibility filter here: those
// tickets are still active blockers even when hidden from the board.
function activeDateRiskGraph(){
  const active=state.issues.filter(i=>!isCompletedStatus(i.status));
  const byKey=new Map(active.map(i=>[i.key,i]));
  const outgoing=new Map(),incoming=new Map();
  byKey.forEach((_,key)=>{outgoing.set(key,[]);incoming.set(key,[]);});
  for(const edge of (state.edges||[])){
    if(!byKey.has(edge.from) || !byKey.has(edge.to)) continue;
    outgoing.get(edge.from).push(edge.to);
    incoming.get(edge.to).push(edge.from);
  }
  return {active,byKey,outgoing,incoming};
}

function chainDateRiskPairs(keys=null, dateOverrides=null){
  const allowed=keys ? new Set(keys) : null;
  const {active,byKey,outgoing}=activeDateRiskGraph();
  const effectiveDate=key=>{
    if(dateOverrides && Object.prototype.hasOwnProperty.call(dateOverrides,key)) return dateOverrides[key] || '';
    return byKey.get(key)?.dueDate || '';
  };
  const pairs=[];
  for(const source of active){
    if(allowed && !allowed.has(source.key)) continue;
    const sourceDate=effectiveDate(source.key);
    if(!isValidDueDateValue(sourceDate)) continue;
    const queue=[source.key],seen=new Set([source.key]);
    for(let cursor=0;cursor<queue.length;cursor++){
      for(const targetKey of (outgoing.get(queue[cursor])||[])){
        if(seen.has(targetKey)) continue;
        seen.add(targetKey);
        queue.push(targetKey);
        if(allowed && !allowed.has(targetKey)) continue;
        const targetDate=effectiveDate(targetKey);
        if(!isValidDueDateValue(targetDate) || targetDate>=sourceDate) continue;
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
let assigneeCache=null;
function getSortedAssignees(){
  if(assigneeCache && assigneeCache.issues===state.issues && assigneeCache.revision===graphRevision)
    return assigneeCache.options;
  const unique=new Map();
  for(const issue of state.issues){
    if(issue.assigneeAccountId) unique.set(issue.assigneeAccountId,
      {name:issue.assignee||'Unassigned',accountId:issue.assigneeAccountId});
  }
  const options=[...unique.values()].sort((a,b)=>a.name.localeCompare(b.name));
  assigneeCache={issues:state.issues,revision:graphRevision,options};
  return options;
}

function cardHtml(i, searchTerm){
  const isExternal = i.externalBlockers && i.externalBlockers.length;
  const isMilestone = (i.labels || []).some(label => String(label).toLowerCase() === 'milestone');
  // Full option lists are inserted only when a control is used; large boards
  // no longer produce tens of thousands of unused option/menu DOM nodes.
  let epicHtml = '';
  if(i.epic){
    const rawLabel = i.epic.summary ? i.epic.key + ' · ' + (i.epic.summary.length > 32 ? i.epic.summary.substring(0, 32) + '…' : i.epic.summary) : i.epic.key;
    epicHtml = '<a class="epic-badge" href="' + esc(i.epic.url) + '" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="' + esc(i.epic.key) + '" title="' + esc(i.epic.summary || i.epic.key) + '"><span class="epic-dot">◆</span>' + esc(rawLabel) + '</a>';
  }
  const summaryHtml = esc(i.summary);
  const assigneeSelect = lazyAssigneeSelectHtml(i);
  const prioritySelect = lazyPriorityPickerHtml(i);

  const searchIndex = buildSearchIndex(i);
  const isCompleted = isCompletedStatus(i.status);
  const isOverdue = !isCompleted && isDueDateOverdue(i.dueDate);
  return '<article class="card' + (i.cycle ? ' cycle' : '') + (isExternal ? ' external' : '') + (isCompleted ? ' completed' : '') + (isOverdue ? ' overdue-card' : '') + '" data-key="' + esc(i.key) + '" data-assignee-account-id="' + esc(i.assigneeAccountId || '') + '" data-due-date="' + esc(i.dueDate || '') + '" data-completed="' + (isCompleted ? '1' : '0') + '" data-search-index="' + esc(searchIndex) + '" data-summary="' + esc(i.summary || '') + '">'
    + (isMilestone ? '<div class="milestone-banner">MILESTONE</div>' : '')
    + '<div class="card-top">'
    +   '<div class="card-top-left">'
    +     '<button type="button" class="hover-lock-btn" data-key="' + esc(i.key) + '" data-stop-propagation="1" title="Lock highlight to this chain" aria-label="Lock highlight to this chain">🔓</button>'
    +     '<button type="button" class="hover-gantt-btn" data-gantt-chain="' + esc(i.key) + '" data-stop-propagation="1" title="View Gantt for selected dependency chain" aria-label="View Gantt for selected dependency chain"><svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M3 4v16M3 7h18M3 12h18M3 17h18"/><path d="M7 5v4h5V5M14 10v4h6v-4M8 15v4h8v-4"/></svg></button>'
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
let dashboardTraversalCache=null;
function dashboardGraphTraversal(issues){
  const active=issues.filter(i=>!isCompletedStatus(i.status));
  const cacheKey=state.issues;
  const flags=String(graphRevision)+':'+String(state.showCompleted)+':'+String(state.includeWithRemarkable);
  if(dashboardTraversalCache && dashboardTraversalCache.key===cacheKey &&
     dashboardTraversalCache.flags===flags && dashboardTraversalCache.count===active.length &&
     dashboardTraversalCache.edges===state.edges){
    // Metadata such as due dates, priority and assignee is mutable. Reuse only
    // the graph shape, and always read the latest issue objects during metrics.
    dashboardTraversalCache.active=active;
    return dashboardTraversalCache;
  }
  const byKey=new Map(active.map((issue,index)=>[issue.key,index]));
  const count=active.length;
  const outgoing=active.map(i=>(i.blocked||[]).map(k=>byKey.get(k)).filter(k=>k!==undefined));
  const incoming=Array.from({length:count},()=>[]);
  outgoing.forEach((list,index)=>list.forEach(target=>incoming[target].push(index)));

  const seen=new Uint8Array(count), finished=[];
  for(let start=0;start<count;start++){
    if(seen[start]) continue;
    seen[start]=1;
    const stack=[[start,0]];
    while(stack.length){
      const frame=stack[stack.length-1], adj=outgoing[frame[0]];
      if(frame[1]>=adj.length){finished.push(frame[0]);stack.pop();continue;}
      const next=adj[frame[1]++];
      if(!seen[next]){seen[next]=1;stack.push([next,0]);}
    }
  }
  const compId=new Int32Array(count).fill(-1), members=[];
  for(let pos=finished.length-1;pos>=0;pos--){
    const start=finished[pos];
    if(compId[start]!==-1) continue;
    const id=members.length, list=[], stack=[start];compId[start]=id;
    while(stack.length){
      const cur=stack.pop();list.push(cur);
      for(const prev of incoming[cur]) if(compId[prev]===-1){compId[prev]=id;stack.push(prev);}
    }
    members.push(list);
  }
  const c=members.length, children=Array.from({length:c},()=>new Set());
  const parents=Array.from({length:c},()=>new Set()), indegree=new Int32Array(c);
  outgoing.forEach((targets,source)=>targets.forEach(target=>{
    const a=compId[source],b=compId[target];
    if(a!==b && !children[a].has(b)){
      children[a].add(b);parents[b].add(a);indegree[b]++;
    }
  }));
  const order=[],queue=[];
  for(let i=0;i<c;i++) if(!indegree[i]) queue.push(i);
  for(let cursor=0;cursor<queue.length;cursor++){
    const a=queue[cursor];order.push(a);
    for(const b of children[a]) if(!--indegree[b]) queue.push(b);
  }
  // One bit per SCC, not per ticket; this includes all members of cycles.
  // Limit quadratic memory on exceptionally huge boards.
  const useBits=c<=10000;
  const words=Math.ceil(c/32);
  const down=useBits?Array.from({length:c},()=>new Uint32Array(words)):null;
  const up=useBits?Array.from({length:c},()=>new Uint32Array(words)):null;
  if(useBits){
    for(let i=0;i<c;i++){
      down[i][i>>>5]|=(1<<(i&31));
      up[i][i>>>5]|=(1<<(i&31));
    }
    for(let pos=order.length-1;pos>=0;pos--){
      const a=order[pos],row=down[a];
      for(const b of children[a]){
        const other=down[b];
        for(let w=0;w<words;w++) row[w]|=other[w];
      }
    }
    for(const a of order){
      const row=up[a];
      for(const b of parents[a]){
        const other=up[b];
        for(let w=0;w<words;w++) row[w]|=other[w];
      }
    }
  }
  const descendantCounts=new Int32Array(c),ancestorCounts=new Int32Array(c);
  const weights=members.map(x=>x.length);
  function visitComponents(start,reverse,visit){
    if(!useBits){
      const seen=new Set([start]),todo=[start],adj=reverse?parents:children;
      for(let cursor=0;cursor<todo.length;cursor++){
        for(const next of adj[todo[cursor]]) if(!seen.has(next)){seen.add(next);todo.push(next);}
      }
      todo.forEach(visit);return;
    }
    const row=(reverse?up:down)[start];
    for(let w=0;w<row.length;w++){
      let bits=row[w];
      while(bits){
        const position=31-Math.clz32(bits&-bits), id=w*32+position;
        if(id<c) visit(id);
        bits&=bits-1;
      }
    }
  }
  for(let a=0;a<c;a++){
    visitComponents(a,false,b=>{descendantCounts[a]+=weights[b];});
    visitComponents(a,true,b=>{ancestorCounts[a]+=weights[b];});
  }
  function eachReachable(key,callback,reverse=false){
    const index=byKey.get(key);
    if(index===undefined) return;
    visitComponents(compId[index],reverse,id=>{
      for(const member of members[id]) if(member!==index) callback(result.active[member]);
    });
  }
  const result={key:cacheKey,flags,count,edges:state.edges,active,byKey,eachReachable,
    downstreamCount:key=>{const i=byKey.get(key);return i===undefined?0:descendantCounts[compId[i]]-1;},
    upstreamCount:key=>{const i=byKey.get(key);return i===undefined?0:ancestorCounts[compId[i]]-1;}};
  dashboardTraversalCache=result;
  return result;
}

function dashboardRiskInfo(issues){
  // Project overview always uses ALL active tickets, independently of filters,
  // including With Remarkable. A ticket is counted once in Needs attention.
  const active=issues.filter(i=>!isCompletedStatus(i.status));
  const overdue=active.filter(i=>isDueDateOverdue(i.dueDate));
  const unassigned=active.filter(i=>!i.assigneeAccountId);
  const noDueDate=active.filter(i=>!i.dueDate);
  const noDescription=active.filter(i=>i.hasDescription===false);
  const graph=dashboardGraphTraversal(issues);
  const chainDateRiskKeys=new Set();
  const chainDateRiskDetails=new Map();
  active.forEach(source=>{
    const sourceDate=source.dueDate ? new Date(source.dueDate+'T00:00:00') : null;
    if(!sourceDate || Number.isNaN(sourceDate.getTime())) return;
    graph.eachReachable(source.key,target=>{
      const targetDate=target.dueDate ? new Date(target.dueDate+'T00:00:00') : null;
      if(targetDate && !Number.isNaN(targetDate.getTime()) && targetDate<sourceDate){
        chainDateRiskKeys.add(target.key);
        if(!chainDateRiskDetails.has(target.key)) chainDateRiskDetails.set(target.key,[]);
        chainDateRiskDetails.get(target.key).push({earlier:source.key,date:source.dueDate});
      }
    });
  });
  const chainDateRisks=active.filter(i=>chainDateRiskKeys.has(i.key));
  const circularKeys=calculateGraphLayout(active,state.edges).cycleKeys;
  const circularDependencies=active.filter(i=>circularKeys.has(i.key));
  const today=new Date();today.setHours(0,0,0,0);
  const ticketRisks=new Map();
  const attention=[];
  active.forEach(issue=>{
    const reasons=[];
    let score=0;
    if(isDueDateOverdue(issue.dueDate)){
      const due=new Date(issue.dueDate+'T00:00:00');
      // Add 5 points for each completed calendar month since the due date.
      let months=(today.getFullYear()-due.getFullYear())*12+today.getMonth()-due.getMonth();
      if(today.getDate()<due.getDate()) months--;
      months=Math.max(0,months);
      const points=30+5*months;
      reasons.push({id:'overdue',label:'Overdue'+(months?' ('+months+' month'+(months===1?'':'s')+')':''),points});
      score+=points;
    }
    if(!issue.assigneeAccountId){reasons.push({id:'unassigned',label:'Unassigned',points:10});score+=10;}
    if(!issue.dueDate){reasons.push({id:'missing-due',label:'Missing due date',points:15});score+=15;}
    if(chainDateRiskKeys.has(issue.key)){reasons.push({id:'chain-risks',label:'Chain date risk',points:20});score+=20;}
    if(circularKeys.has(issue.key)){reasons.push({id:'circular',label:'Circular dependency',points:25});score+=25;}
    if(issue.hasDescription===false){reasons.push({id:'missing-description',label:'Missing description',points:5});score+=5;}
    ticketRisks.set(issue.key,{score,reasons});
    if(score>0) attention.push(issue);
  });
  // Healthy tickets are the baseline: widespread issues must affect Board Health
  // even when each issue has only a small risk score. Deduct additional points
  // for severity, without disproportionately penalising larger projects.
  const averageRisk=active.length ? active.reduce((sum,i)=>sum+Math.min(100,ticketRisks.get(i.key).score),0)/active.length : 0;
  const affectedRate=active.length ? attention.length/active.length : 0;
  const boardHealthScore=Math.max(0,Math.min(100,100*(1-affectedRate)-averageRisk*.25));
  const boardHealthStatus=boardHealthScore>=90?'green':boardHealthScore>=70?'amber':'red';
  return {active,overdue,unassigned,noDueDate,noDescription,chainDateRisks,chainDateRiskKeys,chainDateRiskDetails,
    circularDependencies,circularKeys,attention,ticketRisks,averageRisk,boardHealthScore,boardHealthStatus};
}
function lazyAssigneeSelectHtml(i, dashboard=false){
  // The current selection must be present immediately for value/keyboard
  // semantics; every other option is populated on first interaction.
  const currentId=i.assigneeAccountId||'';
  const currentName=i.assignee||'Unassigned';
  return '<select class="assignee-select'+(dashboard?' dashboard-assignee-select':'')+(!currentId?' unassigned':'')+'" data-field="assignee" data-stop-propagation="1" title="Change assignee" data-assignees-lazy="1">'+
    '<option value="'+esc(currentId)+'">'+esc(currentId?currentName:'Unassigned')+'</option></select>';
}
function populateAssigneeSelect(select){
  if(!select || select.dataset.assigneesLazy!=='1') return;
  const selected=select.value;
  const oldLabel=select.selectedOptions[0]?.textContent||'';
  const assignees=getSortedAssignees();
  // Use native option nodes so a selected label cannot be lost when an
  // assignee is no longer among the users on the current board.
  const fragment=document.createDocumentFragment();
  const unassigned=new Option('Unassigned','',false,!selected);
  fragment.appendChild(unassigned);
  let found=!selected;
  for(const a of assignees){
    fragment.appendChild(new Option(a.name,a.accountId,false,a.accountId===selected));
    if(a.accountId===selected) found=true;
  }
  if(selected && !found) fragment.appendChild(new Option(oldLabel,selected,false,true));
  select.replaceChildren(fragment);
  select.dataset.assigneesLazy='0';
}
function lazyPriorityPickerHtml(i){
  return '<span class="priority-picker" data-stop-propagation="1" title="Change priority">'+
    '<button type="button" class="priority-trigger" data-stop-propagation="1" aria-label="Change priority" aria-haspopup="true" aria-expanded="false">'+priorityIconHtml(i.priority)+'</button>'+
    '<span class="priority-menu" role="menu"></span></span>';
}
function populatePriorityMenu(picker){
  const menu=picker.querySelector('.priority-menu');
  if(!menu || menu.dataset.optionsReady==='1') return;
  const key=picker.closest('.card, .dashboard-ticket')?.dataset.key;
  const active=state.issues.find(i=>i.key===key);
  const selected=active?.priority||'';
  menu.innerHTML=PRIORITY_ORDER.filter((p,idx,arr)=>arr.indexOf(p)===idx).map(p=>
    '<button type="button" class="priority-option'+(p===selected?' selected':'')+'" data-priority="'+esc(p)+'" data-stop-propagation="1">'+priorityIconHtml(p)+'<span>'+esc(p)+'</span></button>'
  ).join('');
  menu.dataset.optionsReady='1';
}
function dashboardAssigneeOptions(i){return lazyAssigneeSelectHtml(i,true);}
function dashboardPriorityHtml(i){return lazyPriorityPickerHtml(i);}
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
  const visibleCount=options.showAll?sorted.length:Math.min(10,sorted.length);
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
  const graph=dashboardGraphTraversal(issues);
  return graph.active.map(issue=>({issue,impact:graph.downstreamCount(issue.key)}))
    .filter(x=>x.impact>0)
    .sort((a,b)=>b.impact-a.impact)
    .slice(0,10);
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
  const graph=dashboardGraphTraversal(issues);
  const milestones=graph.active.filter(i=>(i.labels||[]).some(l=>String(l).toLowerCase()==='milestone'));
  return milestones.map(m=>{
    const due=m.dueDate?new Date(m.dueDate+'T00:00:00'):null;
    const blockers=graph.upstreamCount(m.key);
    const blocked=graph.downstreamCount(m.key);
    const overdue=isDueDateOverdue(m.dueDate);
    return {issue:m,blockers,blocked,overdue,due:due&&!Number.isNaN(due.getTime())?due:null};
  }).sort((a,b)=>Number(b.overdue)-Number(a.overdue) || (a.due?.getTime()||Infinity)-(b.due?.getTime()||Infinity));
}
function dashboardPriorityDistribution(issues){
  const active=issues.filter(i=>!isCompletedStatus(i.status));
  const groups=new Map();
  active.forEach(i=>{const p=String(i.priority||'Unspecified'); groups.set(p,(groups.get(p)||0)+1);});
  // Follow the same order as the card's priority-menu, irrespective of counts.
  // Unrecognised Jira priorities (including Unspecified) come afterwards.
  return [...groups.entries()].sort((a,b)=>priorityRank(a[0])-priorityRank(b[0]) || a[0].localeCompare(b[0]));
}
function dashboardPriorityDistributionHtml(items){
  if(!items.length) return '<div class="dashboard-empty">No active tickets.</div>';
  const total=items.reduce((sum,x)=>sum+x[1],0);
  return '<div class="dashboard-compact-list">'+items.map(([priority,count])=>{
    const percent=total?count/total*100:0;
    const displayPercent=percent.toLocaleString('en-GB',{maximumFractionDigits:1});
    const icon=priority==='Unspecified'?priorityIconHtml(null):priorityIconHtml(priority);
    return '<div class="dashboard-compact-row dashboard-priority-row">'+
      '<span class="dashboard-compact-main dashboard-priority-label">'+icon+'<strong>'+esc(priority)+'</strong></span>'+
      '<span class="dashboard-priority-bar" role="progressbar" aria-label="'+esc(priority)+' share of active tickets" aria-valuemin="0" aria-valuemax="100" aria-valuenow="'+percent.toFixed(1)+'" aria-valuetext="'+esc(displayPercent)+'% of active tickets">'+
        '<span class="dashboard-priority-bar-fill" style="width:'+percent.toFixed(2)+'%"></span></span>'+
      '<span class="dashboard-priority-count"><strong>'+count+'</strong><small>'+displayPercent+'%</small></span>'+ 
    '</div>';
  }).join('')+'</div>';
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
  return '<div class="dashboard-workload-list">'+items.map(x=>'<div class="dashboard-workload-row"><span class="dashboard-workload-name"><strong>'+esc(x.name)+'</strong>'+(x.overdue?'<span>'+x.overdue+' overdue</span>':'')+'</span><span class="dashboard-workload-bar"><span style="width:'+Math.max(4,Math.round(x.count/max*100))+'%"></span></span><strong class="dashboard-workload-count">'+x.count+'</strong></div>').join('')+'</div>';
}
function dashboardMilestoneHtml(items){
  if(!items.length) return '<div class="dashboard-empty">No active milestones found.</div>';
  return '<div class="dashboard-compact-list dashboard-milestone-risk-list">'+items.map(x=>'<button type="button" class="dashboard-compact-row dashboard-milestone-risk-row" data-dashboard-milestone="'+esc(x.issue.key)+'"><span class="dashboard-compact-main dashboard-milestone-risk-main"><strong>'+esc(x.issue.key)+'</strong><span>'+esc(x.issue.summary||'')+'</span></span><span class="dashboard-milestone-risk-metrics"><span class="dashboard-milestone-risk-blocked">'+(x.blockers===0?'—':x.blockers+' blockers')+'</span><span class="dashboard-milestone-risk-blocks">'+(x.blocked===0?'—':x.blocked+' blocked')+'</span>'+(x.issue.dueDate?'<span class="dashboard-milestone-risk-date'+(x.overdue?' due-date overdue':'')+'">'+esc(formatDueDate(x.issue.dueDate))+'</span>':'<span class="dashboard-milestone-risk-date">No date</span>')+'</span></button>').join('')+'</div>';
}
function dashboardPersonalUserOptions(){
  const users=new Map();
  (state.issues||[]).forEach(i=>{if(i.assigneeAccountId && i.assignee) users.set(i.assigneeAccountId,String(i.assignee).trim());});
  const selectedId=state.currentUserAccountId||'';
  if(selectedId && !users.has(selectedId)) users.set(selectedId,state.currentUserName||selectedId);
  const options=[...users.entries()].sort((a,b)=>a[1].localeCompare(b[1])).map(([id,name])=>'<option value="'+esc(id)+'"'+(id===selectedId?' selected':'')+'>'+esc(name)+'</option>').join('');
  return '<select id="personal-user-mapping" class="personal-user-mapping" aria-label="Change user"><option value="">Choose a user…</option>'+options+'</select>';
}
function dashboardPersonalViewHtml(activeIssues){
  // Use all active Jira issues for personal counts so With Remarkable tickets
  // remain counted even when the board's display toggle hides them.
  const personalActive=(state.issues||[]).filter(i=>!isCompletedStatus(i.status));
  const sourceIssues=personalActive.length ? personalActive : activeIssues;
  const currentName=String(state.currentUserName||'Edward Dyer').trim().toLowerCase();
  const mine=sourceIssues.filter(i=>String(i.assignee||'').trim().toLowerCase()===currentName ||
    (state.currentUserAccountId && i.assigneeAccountId===state.currentUserAccountId));
  const byKey=new Map(sourceIssues.map(i=>[i.key,i]));
  const isRemarkable=i=>String(i.status||'').trim().toLowerCase()==='with remarkable';
  const hasActiveBlocker=i=>(i.blockers||[]).some(k=>byKey.has(k));
  const unblocked=mine.filter(i=>!hasActiveBlocker(i) && !isRemarkable(i));
  const withRemarkable=mine.filter(isRemarkable);
  const blockedByOthers=mine.filter(i=>isRemarkable(i)||(i.blockers||[]).some(k=>{
    const blocker=byKey.get(k); return blocker && blocker.assigneeAccountId!==state.currentUserAccountId;
  }));
  const overdue=mine.filter(i=>isDueDateOverdue(i.dueDate));
  const next7=dashboardDueSoon(mine,7);
  const nextMonth=dashboardDueSoon(mine,31);
  const selectedName=String(state.currentUserName||'the selected user').trim();
  const metric=(label,count,description,filter,extra='')=>'<div class="dashboard-personal-metric"><div><span class="dashboard-personal-label">'+esc(label)+'</span><strong>'+count+'</strong><span class="dashboard-personal-help">'+esc(description)+'</span>'+extra+'</div>'+(filter?'<div class="dashboard-personal-actions"><button type="button" class="dashboard-show-personal" data-personal-filter="'+filter+'">Show on board</button></div>':'')+'</div>';
  return '<div class="dashboard-personal-grid">'+
    metric('Tickets assigned to '+selectedName,mine.length,'Active tickets assigned to '+selectedName,'assigned')+
    metric('Unblocked tickets',unblocked.length,'Tickets with no active blockers, excluding With Remarkable tickets',null,withRemarkable.length?'<span class="dashboard-personal-help">Plus '+withRemarkable.length+' with Remarkable</span>':'')+
    metric('Tickets blocked by other assignees',blockedByOthers.length,'Includes tickets with active blockers assigned to someone else and With Remarkable tickets',null)+
    metric('Overdue',overdue.length,selectedName+'’s tickets past their due date','overdue')+
    metric('Due in the next 7 days',next7.length,selectedName+'’s tickets due today through the next seven days','next7')+
    metric('Due in the next 31 days',nextMonth.length,selectedName+'’s tickets due today through the next 31 days','nextMonth')+
    '</div>';
}
const DASHBOARD_TABS=[
  ['needs-attention','Needs attention'],['upcoming-7','Upcoming 7 days'],['upcoming-31','Upcoming 31 days'],
  ['overdue','Overdue'],['missing-due','Missing Due Date'],['unassigned','Unassigned tickets'],
  ['biggest-unblockers','Biggest unblockers'],['chain-risks','Dependency chain date risks'],
  ['circular','Circular Dependencies'],['in-development','In development'],
  ['workload-priorities','Workload and Priorities']
];
const DASHBOARD_TABLE_FIELDS=[['key','Key'],['summary','Summary'],['priority','Priority'],['dueDate','Due date'],
  ['epic','Parent (epic)'],['assignee','Assignee'],['status','Status'],['blockers','Blockers'],['blocked','Blocked']];
function dashboardDefaultSort(tab){
  if(tab==='needs-attention') return {field:'riskScore',direction:'desc'};
  if(tab==='biggest-unblockers') return {field:'blocked',direction:'desc'};
  if(tab==='missing-due') return {field:'priority',direction:'asc'};
  return {field:'dueDate',direction:'asc'};
}
function dashboardSortForTab(tab){return state.dashboardDraftSorts?.[tab]||state.dashboardSavedSorts?.[tab]||dashboardDefaultSort(tab);}
function dashboardSortChanged(tab){
  const saved=state.dashboardSavedSorts?.[tab]||dashboardDefaultSort(tab);
  const current=dashboardSortForTab(tab);
  return saved.field!==current.field||saved.direction!==current.direction;
}
function dashboardTableData(risks,tab){
  const active=risks.active;
  switch(tab){
    case 'needs-attention':return risks.attention.filter(i=>state.dashboardAttentionFilter!=='missing-description'||i.hasDescription===false);
    case 'upcoming-7':return dashboardDueSoon(active,7);
    case 'upcoming-31':return dashboardDueSoon(active,31);
    case 'overdue':return risks.overdue;
    case 'missing-due':return risks.noDueDate;
    case 'unassigned':return risks.unassigned;
    case 'biggest-unblockers':{
      const graph=dashboardGraphTraversal(active);
      // This preset is deliberately limited to the 20 largest downstream chains.
      return [...active].filter(i=>graph.downstreamCount(i.key)>0)
        .sort((a,b)=>graph.downstreamCount(b.key)-graph.downstreamCount(a.key)||a.key.localeCompare(b.key)).slice(0,20);
    }
    case 'chain-risks':return risks.chainDateRisks;
    case 'circular':return risks.circularDependencies;
    case 'in-development':return active.filter(isWithRemarkableStatus);
    default:return [];
  }
}
function dashboardCompareTable(a,b,tab,risks,graph){
  const sort=dashboardSortForTab(tab);
  function value(i,field){
    if(field==='priority') return priorityRank(i.priority);
    if(field==='dueDate') return i.dueDate||'';
    if(field==='epic') return (i.epic?.summary||i.epic?.key||'').toLowerCase();
    if(field==='assignee') return (i.assigneeAccountId?i.assignee:'').toLowerCase();
    if(field==='blockers') return graph.upstreamCount(i.key);
    if(field==='blocked') return graph.downstreamCount(i.key);
    if(field==='riskScore') return risks.ticketRisks.get(i.key)?.score||0;
    return String(i[field]||'').toLowerCase();
  }
  const compare=(field,direction)=>{
    const x=value(a,field),y=value(b,field);
    if(field==='dueDate' && (!x||!y) && x!==y) return !x?1:-1;
    const cmp=typeof x==='number'?x-y:String(x).localeCompare(String(y),undefined,{numeric:true});
    return (direction==='desc'?-1:1)*cmp;
  };
  return compare(sort.field,sort.direction) ||
    (sort.field==='dueDate'||sort.field==='riskScore'||(tab==='biggest-unblockers'&&sort.field==='blocked')?compare('dueDate','asc'):sort.field==='priority'?compare('dueDate','asc'):0) ||
    (sort.field==='riskScore'||tab==='biggest-unblockers'?compare('priority','asc'):0) ||
    a.key.localeCompare(b.key);
}
function dashboardTableHtml(risks,tab){
  const graph=dashboardGraphTraversal(risks.active);
  const data=dashboardTableData(risks,tab).sort((a,b)=>dashboardCompareTable(a,b,tab,risks,graph));
  const pageSize=30;
  const pageCount=Math.max(1,Math.ceil(data.length/pageSize));
  const page=Math.max(1,Math.min(pageCount,state.dashboardPages?.[tab]||1));
  state.dashboardPages[tab]=page;
  const start=(page-1)*pageSize;
  const rows=data.slice(start,start+pageSize);
  const activeSort=dashboardSortForTab(tab);
  const headers=tab==='needs-attention'?[...DASHBOARD_TABLE_FIELDS,['riskScore','Risk score'],['riskReasons','Risk reasons']]:DASHBOARD_TABLE_FIELDS;
  const headerHtml=headers.map(([field,label])=>{
    if(field==='riskReasons') return '<th scope="col">'+label+'</th>';
    const active=activeSort.field===field;
    return '<th scope="col" aria-sort="'+(active?(activeSort.direction==='asc'?'ascending':'descending'):'none')+'"><button type="button" data-dashboard-sort="'+field+'" class="'+(active?'active':'')+'">'+label+' <span aria-hidden="true">'+(active?(activeSort.direction==='asc'?'▲':'▼'):'↕')+'</span></button></th>';
  }).join('');
  const colWidths=[104,300,92,170,218,184,140,83,83];
  const colgroup='<colgroup>'+colWidths.map(w=>'<col style="width:'+w+'px">').join('')+
    (tab==='needs-attention'?'<col style="width:95px"><col style="width:270px">':'')+'</colgroup>';
  const rowHtml=rows.map(i=>{
    const epic=i.epic;
    const epicLabel=epic?(epic.summary?epic.summary+' ('+epic.key+')':epic.key):'';
    const epicHtml=epic?'<a href="'+esc(epic.url)+'" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="'+esc(epic.key)+'" title="'+esc(epicLabel)+'">'+esc(epicLabel)+'</a>':'—';
    const risk=risks.ticketRisks.get(i.key)||{score:0,reasons:[]};
    const riskColumns=tab==='needs-attention'?'<td><strong class="dashboard-risk-score">'+risk.score+'</strong></td><td class="dashboard-reason-cell"><span class="dashboard-reason-list" title="'+esc(risk.reasons.map(x=>x.label+' (+'+x.points+')').join(', '))+'">'+risk.reasons.map(x=>'<span class="dashboard-risk-reason" title="+'+x.points+' points">'+esc(x.label)+'</span>').join('')+'</span></td>':'';
    return '<tr class="my-view-row dashboard-ticket" data-key="'+esc(i.key)+'" data-dashboard-row-key="'+esc(i.key)+'" tabindex="0" title="Open dependency chain for '+esc(i.key)+'">'+
      '<td><a class="dashboard-ticket-key" href="'+esc(i.url)+'" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="'+esc(i.key)+'">'+esc(i.key)+'</a></td>'+
      '<td class="my-view-summary" title="'+esc(i.summary||'')+'">'+esc(i.summary||'')+'</td>'+
      '<td><div class="my-view-priority" title="'+esc(i.priority||'Unspecified')+'">'+dashboardPriorityHtml(i)+'</div></td>'+
      '<td>'+dueDateHtml(i)+'</td>'+
      '<td class="my-view-parent">'+epicHtml+'</td>'+
      '<td>'+dashboardAssigneeOptions(i)+'</td>'+
      '<td><span class="status-badge" style="'+statusStyle(i.status)+'">'+esc(i.status||'—')+'</span></td>'+
      '<td><span class="my-view-count upstream">'+graph.upstreamCount(i.key)+'</span></td>'+
      '<td><span class="my-view-count downstream">'+graph.downstreamCount(i.key)+'</span></td>'+
      riskColumns+'</tr>';
  }).join('');
  const title=DASHBOARD_TABS.find(x=>x[0]===tab)?.[1]||'Tickets';
  const filterNote=state.dashboardAttentionFilter==='missing-description'&&tab==='needs-attention'
    ? '<button class="dashboard-clear-attention-filter" type="button">Missing descriptions only ×</button>':'';
  const sortStatus=dashboardSortChanged(tab)?'Sorting not saved':state.dashboardSavedSorts?.[tab]?'Sorting saved':'Default sorting';
  const pagination=data.length>pageSize?'<nav class="dashboard-table-pagination bottom" aria-label="Table pagination" data-dashboard-page-count="'+pageCount+'"><span class="dashboard-page-count">Showing '+(start+1)+'–'+Math.min(start+pageSize,data.length)+' of '+data.length+'</span><div><button type="button" data-dashboard-page="first"'+(page===1?' disabled':'')+' aria-label="First page">« First</button><button type="button" data-dashboard-page="prev"'+(page===1?' disabled':'')+'>Previous</button><span class="dashboard-page-number">Page '+page+' of '+pageCount+'</span><button type="button" data-dashboard-page="next"'+(page===pageCount?' disabled':'')+'>Next</button><button type="button" data-dashboard-page="last"'+(page===pageCount?' disabled':'')+' aria-label="Last page">Last »</button></div></nav>':'';
  return '<section class="my-view-table-section dashboard-table-section" id="dashboard-table-panel"><div class="my-view-table-heading"><div><h2>'+esc(title)+' <span class="dashboard-section-count">('+data.length+')</span></h2><p>Active tickets · Select a row to open its dependency chain · Click a column heading to sort</p>'+filterNote+'</div><div class="my-view-sort-actions"><span class="my-view-sort-status">'+sortStatus+'</span><button type="button" class="my-view-save-sort" id="dashboard-save-sort"'+(!dashboardSortChanged(tab)?' disabled':'')+'>Save sort</button></div></div>'+
    '<div class="my-view-scroll-controls" hidden><span class="my-view-scroll-hint">Scroll to see more columns</span><button type="button" class="my-view-scroll-button" data-my-view-scroll="left" aria-label="Scroll table left">&#8592;</button><button type="button" class="my-view-scroll-button" data-my-view-scroll="right" aria-label="Scroll table right">&#8594;</button></div>'+
    '<div class="my-view-table-scroll" role="region" aria-label="'+esc(title)+' table, horizontally scrollable" tabindex="0"><table class="my-view-table'+(tab==='needs-attention'?' has-risk-columns':'')+'">'+colgroup+'<thead><tr>'+headerHtml+'</tr></thead><tbody>'+
    (rowHtml||'<tr><td class="my-view-empty" colspan="'+headers.length+'">No matching active tickets.</td></tr>')+'</tbody></table></div>'+pagination+'</section>';
}
function dashboardOverviewHtml(){
  const risks=dashboardRiskInfo(state.issues||[]);
  const tab=DASHBOARD_TABS.some(x=>x[0]===state.dashboardTab)?state.dashboardTab:'needs-attention';
  const dueSoon=dashboardDueSoon(risks.active,7);
  const dueMonth=dashboardDueSoon(risks.active,31);
  const workload=dashboardWorkload(risks.active);
  const priorityDistribution=dashboardPriorityDistribution(risks.active);
  const topWorkload=workload.filter(x=>x.accountId).slice(0,6);
  const assignedPeopleCount=new Set(risks.active.filter(i=>i.assigneeAccountId).map(i=>i.assigneeAccountId)).size;
  const count=risks.attention.length;
  const activeCount=risks.active.length;
  const attentionPercent=activeCount?Math.round(count/activeCount*100):0;
  const attentionItems=[
    ['overdue','Overdue tickets',risks.overdue.length],
    ['unassigned','Unassigned tickets',risks.unassigned.length],
    ['missing-due','Missing due dates',risks.noDueDate.length],
    ['chain-risks','Dependency chain date risks',risks.chainDateRisks.length],
    ['circular','Circular dependencies',risks.circularDependencies.length],
    ['missing-description','Missing descriptions',risks.noDescription.length]
  ];
  const healthScore=Math.round(risks.boardHealthScore);
  const healthLabel=risks.boardHealthStatus==='green'?'Healthy':risks.boardHealthStatus==='amber'?'Needs attention':'At risk';
  const topWorkloadHtml=topWorkload.length?topWorkload.map((x,index)=>'<div class="dashboard-top-workload-row"><strong>'+((index+1)+'. ')+esc(x.name)+'</strong><span class="dashboard-top-workload-count">'+x.count+'</span></div>').join(''):'<div class="dashboard-empty">No assigned active tickets.</div>';
  const riskTotals=attentionItems.map(([id,label,n])=>'<button type="button" class="dashboard-attention-item" data-dashboard-risk-link="'+id+'"><span>'+esc(label)+'</span><strong>'+n+'</strong></button>').join('');
  const healthDetails=attentionItems.map(([id,label,n])=>'<div class="dashboard-health-row"><span class="dashboard-health-row-label">'+esc(label)+'</span><span class="dashboard-health-row-detail">'+n+' affected</span></div>').join('');
  const tabs=DASHBOARD_TABS.map(([id,label])=>'<button type="button" role="tab" aria-selected="'+(tab===id?'true':'false')+'" data-dashboard-tab="'+id+'" class="'+(tab===id?'active':'')+'">'+esc(label)+'</button>').join('');
  const mainPanel=tab==='workload-priorities'
    ? '<div class="dashboard-two-column dashboard-workload-panel">'+
        '<div class="dashboard-section-group">'+dashboardSummarySection('Workload by assignee',dashboardWorkloadHtml(workload),'workload-by-assignee','Select a person to filter the main board')+'</div>'+
        '<div class="dashboard-section-group">'+dashboardSummarySection('Priority distribution',dashboardPriorityDistributionHtml(priorityDistribution),'priority-distribution-content','Active tickets by Jira priority')+'</div></div>'
    : dashboardTableHtml(risks,tab);
  return '<div class="dashboard"><div class="dashboard-head"><div><div class="dashboard-title">Project overview</div><div class="dashboard-subtitle">Delivery risks, deadlines and priorities across all active tickets.</div></div><div class="dashboard-updated">'+risks.active.length.toLocaleString('en-GB')+' active tickets</div></div>'+
    '<section class="dashboard-section dashboard-overview" id="overview"><div class="dashboard-stats">'+
      '<div class="dashboard-stat dashboard-summary-link dashboard-health-stat '+risks.boardHealthStatus+'" role="button" tabindex="0" data-dashboard-risk-link="needs-attention"><div class="dashboard-health-score-line"><div class="dashboard-stat-value">'+healthScore+'%</div><span class="dashboard-health-status">'+healthLabel+'</span></div><div class="dashboard-stat-label">Board health</div><div class="dashboard-stat-help">Percentage of active tickets without risks, minus 25% of the average risk points. Includes all six risk areas.</div><div class="dashboard-health-breakdown">'+healthDetails+'</div></div>'+
      '<div class="dashboard-stat dashboard-attention-stat risk"><div class="dashboard-stat-value">'+count.toLocaleString('en-GB')+' / '+activeCount.toLocaleString('en-GB')+' ('+attentionPercent+'%)</div><div class="dashboard-stat-label">Needs attention</div><div class="dashboard-stat-help">Unique active tickets with one or more risks. Select a category to see its tickets.</div><div class="dashboard-attention-summary">'+riskTotals+'</div></div>'+
      '<div class="dashboard-upcoming-stack">'+
        '<div class="dashboard-stat dashboard-summary-link" data-dashboard-risk-link="upcoming-7"><div class="dashboard-stat-value">'+dueSoon.length+'</div><div class="dashboard-stat-label">Due next 7 days</div></div>'+
        '<div class="dashboard-stat dashboard-summary-link" data-dashboard-risk-link="upcoming-31"><div class="dashboard-stat-value">'+dueMonth.length+'</div><div class="dashboard-stat-label">Due next 31 days</div></div></div>'+
      '<div class="dashboard-stat dashboard-summary-link" data-dashboard-risk-link="workload-priorities"><div class="dashboard-stat-value">'+assignedPeopleCount+' assignees</div><div class="dashboard-stat-label">Top workload</div><div class="dashboard-top-workload">'+topWorkloadHtml+'</div></div>'+
    '</div></section>'+
    '<nav class="dashboard-nav dashboard-table-tabs" role="tablist" aria-label="Project overview table views">'+tabs+'</nav>'+
    '<div id="dashboard-table-area" role="tabpanel">'+mainPanel+'</div></div>';
}
function renderDashboard(){
  const start=performance.now();
  board.insertAdjacentHTML('beforeend',dashboardOverviewHtml());
  console.info('[Performance] Dashboard render',{milliseconds:Math.round(performance.now()-start)});
  attachEvents();
  const app=document.getElementById('app');
  const switchTab=(tab,attentionFilter='')=>{
    if(!DASHBOARD_TABS.some(x=>x[0]===tab)) return;
    // Switching tabs or selecting a risk must not jump the dashboard to the table.
    // Keep the current scroll position even though render() rebuilds the view.
    const previousTop=app.scrollTop;
    const previousLeft=app.scrollLeft;
    const tableLeft=board.querySelector('.dashboard-table-section .my-view-table-scroll')?.scrollLeft||0;
    state.dashboardTab=tab;
    state.dashboardAttentionFilter=attentionFilter;
    state.dashboardPages[tab]=1;
    render();
    app.scrollTop=previousTop;
    app.scrollLeft=previousLeft;
    const restore=()=>{
      app.scrollTop=previousTop;
      app.scrollLeft=previousLeft;
      const table=board.querySelector('.dashboard-table-section .my-view-table-scroll');
      if(table) table.scrollLeft=tableLeft;
      updateMyViewScrollControls();
    };
    restore();
    requestAnimationFrame(restore);
  };
  board.querySelectorAll('[data-dashboard-tab]').forEach(btn=>btn.addEventListener('click',()=>switchTab(btn.dataset.dashboardTab)));
  board.querySelectorAll('[data-dashboard-risk-link]').forEach(el=>{
    const navigate=()=>{
      const id=el.dataset.dashboardRiskLink;
      switchTab(id==='missing-description'?'needs-attention':id,id==='missing-description'?'missing-description':'');
    };
    el.addEventListener('click',navigate);
    if(el.getAttribute('role')==='button') el.addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();navigate();}});
  });
  board.querySelector('.dashboard-clear-attention-filter')?.addEventListener('click',()=>switchTab('needs-attention',''));
  board.querySelectorAll('[data-dashboard-sort]').forEach(btn=>btn.addEventListener('click',()=>{
    const tab=state.dashboardTab,field=btn.dataset.dashboardSort,current=dashboardSortForTab(tab);
    const defaultDirection=['blocked','blockers','riskScore'].includes(field)?'desc':'asc';
    state.dashboardDraftSorts={...state.dashboardDraftSorts,[tab]:{field,direction:current.field===field?(current.direction==='asc'?'desc':'asc'):defaultDirection}};
    state.dashboardPages[tab]=1;
    const top=app.scrollTop;render();requestAnimationFrame(()=>app.scrollTop=top);
  }));
  board.querySelector('#dashboard-save-sort')?.addEventListener('click',async()=>{
    const tab=state.dashboardTab,previous=state.dashboardSavedSorts;
    state.dashboardSavedSorts={...previous,[tab]:{...dashboardSortForTab(tab)}};
    const success=await savePreferences({dashboardSavedSorts:state.dashboardSavedSorts});
    if(success){const top=app.scrollTop;render();requestAnimationFrame(()=>app.scrollTop=top);}
    else{state.dashboardSavedSorts=previous;const msg=board.querySelector('.my-view-sort-status');if(msg) msg.textContent='Unable to save sorting. Try again.';}
  });
  board.querySelectorAll('[data-dashboard-page]').forEach(btn=>btn.addEventListener('click',()=>{
    const tab=state.dashboardTab;
    const page=state.dashboardPages[tab]||1;
    const last=Number(btn.closest('[data-dashboard-page-count]')?.dataset.dashboardPageCount)||1;
    const action=btn.dataset.dashboardPage;
    const next=action==='first'?1:action==='last'?last:page+(action==='next'?1:-1);
    state.dashboardPages[tab]=Math.max(1,Math.min(last,next));
    const top=app.scrollTop,left=app.scrollLeft;
    const tableLeft=board.querySelector('.dashboard-table-section .my-view-table-scroll')?.scrollLeft||0;
    render();
    const restore=()=>{
      app.scrollTop=top;app.scrollLeft=left;
      const table=board.querySelector('.dashboard-table-section .my-view-table-scroll');
      if(table) table.scrollLeft=tableLeft;
      updateMyViewScrollControls();
    };
    restore();requestAnimationFrame(restore);
  }));
  const scroller=board.querySelector('.my-view-table-scroll');
  if(scroller){
    if(myViewScrollObserver){myViewScrollObserver.disconnect();myViewScrollObserver.observe(scroller);myViewScrollObserver.observe(scroller.querySelector('table'));}
    scroller.addEventListener('scroll',updateMyViewScrollControls,{passive:true});
    board.querySelectorAll('[data-my-view-scroll]').forEach(btn=>btn.addEventListener('click',()=>scroller.scrollBy({left:(btn.dataset.myViewScroll==='right'?1:-1)*Math.max(240,Math.round(scroller.clientWidth*.75)),behavior:'smooth'})));
    requestAnimationFrame(updateMyViewScrollControls);
  }
  board.querySelectorAll('[data-dashboard-row-key]').forEach(row=>{
    const open=e=>{
      if(e?.target?.closest?.('[data-stop-propagation], a, button, select, .priority-picker, .priority-menu')) return;
      const key=row.dataset.dashboardRowKey;
      if(!key) return;
      // Opening a chain must work even if a Full Board filter excluded this ticket.
      state.filterUser='';state.filterDue='all';state.includeWithRemarkable=true;state.showCompleted=false;
      state.searchTerm='';if(searchEl) searchEl.value='';
      state.showDashboard=false;state.showMyView=false;state.showMilestones=false;
      state.lockedKey=key;state.selectionHistory=[];state.showBlocked=false;
      state.dashboardReturnSection='dashboard:'+state.dashboardTab;
      state.revealSelectedKey=key;
      render();
    };
    row.addEventListener('click',open);
    row.addEventListener('keydown',e=>{if(e.key==='Enter'&&e.target===row){e.preventDefault();open(e);}});
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

// ── My view (independent of the project overview) ───────────────────────
function isWithRemarkableStatus(i){
  return String(i?.status||'').trim().toLowerCase()==='with remarkable';
}
const MY_VIEW_SORT_FIELDS=['key','summary','priority','dueDate','epic','status','blockers','blocked'];
function resetMyViewSort(){
  const preference=state.myViewSavedSorts?.[state.currentUserAccountId||''];
  state.myViewSort={field:MY_VIEW_SORT_FIELDS.includes(preference?.field)?preference.field:'priority',direction:preference?.direction==='desc'?'desc':'asc'};
}
function myViewSortChanged(){
  const saved=state.myViewSavedSorts?.[state.currentUserAccountId||''];
  const stored={field:MY_VIEW_SORT_FIELDS.includes(saved?.field)?saved.field:'priority',direction:saved?.direction==='desc'?'desc':'asc'};
  return state.myViewSort.field!==stored.field || state.myViewSort.direction!==stored.direction;
}
function myViewAssignedIssues(includeHiddenRemarkable=false){
  const active=(state.issues||[]).filter(i=>!isCompletedStatus(i.status));
  const id=state.currentUserAccountId||'';
  if(!id) return [];
  return active.filter(i=>i.assigneeAccountId===id && (includeHiddenRemarkable || state.includeWithRemarkable || !isWithRemarkableStatus(i)));
}
function compareMyViewIssues(a,b){
  const field=state.myViewSort.field, dir=state.myViewSort.direction==='desc'?-1:1;
  const getValue=i=>{
    if(field==='priority') return priorityRank(i.priority);
    if(field==='dueDate') return i.dueDate||'';
    if(field==='epic') return (i.epic?.key||'').toLowerCase();
    if(field==='blockers') return dashboardMyViewGraph.upstreamCount(i.key);
    if(field==='blocked') return dashboardMyViewGraph.downstreamCount(i.key);
    return String(i[field]||'').toLowerCase();
  };
  const av=getValue(a),bv=getValue(b);
  // Missing due dates are consistently last when sorting a table by due date.
  if(field==='dueDate' && (!av||!bv) && av!==bv) return !av?1:-1;
  const cmp=typeof av==='number' ? av-bv : String(av).localeCompare(String(bv),undefined,{numeric:true});
  if(cmp) return dir*cmp;
  if(field==='priority'){
    const da=a.dueDate||'9999-12-31',db=b.dueDate||'9999-12-31';
    if(da!==db) return da.localeCompare(db);
  }
  return a.key.localeCompare(b.key);
}
let dashboardMyViewGraph=null;
function myViewTableHtml(){
  const tickets=myViewAssignedIssues();
  const remarkableCount=myViewAssignedIssues(true).filter(isWithRemarkableStatus).length;
  // All active Jira issues must contribute to upstream/downstream counts,
  // including With Remarkable even if hidden by a Full board filter.
  dashboardMyViewGraph=dashboardGraphTraversal(state.issues||[]);
  const sorted=[...tickets].sort(compareMyViewIssues);
  const headers=[['key','Key'],['summary','Summary'],['priority','Priority'],['dueDate','Due date'],['epic','Parent (epic)'],['status','Status'],['blockers','Blockers'],['blocked','Blocked']];
  const headerHtml=headers.map(([field,label])=>{
    const active=state.myViewSort.field===field;
    return '<th scope="col" aria-sort="'+(active?(state.myViewSort.direction==='asc'?'ascending':'descending'):'none')+'"><button type="button" class="'+(active?'active':'')+'" data-my-view-sort="'+field+'">'+label+' <span aria-hidden="true">'+(active?(state.myViewSort.direction==='asc'?'▲':'▼'):'↕')+'</span></button></th>';
  }).join('');
  const rows=sorted.map(i=>{
    const epic=i.epic;
    const epicLabel=epic?(epic.summary?epic.summary+' ('+epic.key+')':epic.key):'';
    const epicHtml=epic?'<a href="'+esc(epic.url)+'" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="'+esc(epic.key)+'" title="'+esc(epicLabel)+'">'+esc(epicLabel)+'</a>':'—';
    return '<tr class="my-view-row dashboard-ticket" data-key="'+esc(i.key)+'" data-my-view-key="'+esc(i.key)+'" tabindex="0" title="Open dependency chain for '+esc(i.key)+'">'+
      '<td><a class="dashboard-ticket-key" href="'+esc(i.url)+'" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="'+esc(i.key)+'">'+esc(i.key)+'</a></td>'+
      '<td class="my-view-summary">'+esc(i.summary||'')+'</td>'+
      '<td><div class="my-view-priority" title="'+esc(i.priority||'Unspecified')+'">'+dashboardPriorityHtml(i)+'</div></td>'+
      '<td>'+dueDateHtml(i)+'</td>'+
      '<td class="my-view-parent">'+epicHtml+'</td>'+
      '<td><span class="status-badge" style="'+statusStyle(i.status)+'">'+esc(i.status||'—')+'</span></td>'+
      '<td><span class="my-view-count upstream">'+dashboardMyViewGraph.upstreamCount(i.key)+'</span></td>'+
      '<td><span class="my-view-count downstream">'+dashboardMyViewGraph.downstreamCount(i.key)+'</span></td>'+
    '</tr>';
  }).join('');
  const hasUser=!!state.currentUserAccountId;
  const remarkableToggle=remarkableCount
    ? '<label class="my-view-remarkable-toggle" for="my-view-remarkable"><input type="checkbox" id="my-view-remarkable"'+(state.includeWithRemarkable?' checked':'')+'><span>Include With Remarkable</span><span class="my-view-remarkable-count">('+remarkableCount+')</span></label>'
    : '';
  return '<section class="my-view-table-section"><div class="my-view-table-heading"><div><h2>Assigned work <span class="dashboard-section-count">('+sorted.length+')</span></h2><p>Active tickets assigned to the selected user. Select a row to open its dependency chain. Click a heading to change the sort.</p></div>'+
    '<div class="my-view-sort-actions">'+remarkableToggle+'<span class="my-view-sort-status">'+(myViewSortChanged()?'Sorting not saved':(state.myViewSavedSorts?.[state.currentUserAccountId||'']?'Sorting saved':'Default sorting'))+'</span><button class="my-view-save-sort" type="button" id="my-view-save-sort"'+(!hasUser || !myViewSortChanged()?' disabled':'')+'>Save sort</button></div></div>'+
    '<div class="my-view-scroll-controls" hidden><span class="my-view-scroll-hint">Scroll to see more columns</span><button type="button" class="my-view-scroll-button" data-my-view-scroll="left" aria-label="Scroll assigned work left">&#8592;</button><button type="button" class="my-view-scroll-button" data-my-view-scroll="right" aria-label="Scroll assigned work right">&#8594;</button></div>'+ 
    '<div class="my-view-table-scroll" role="region" aria-label="Assigned work table, horizontally scrollable" tabindex="0"><table class="my-view-table"><thead><tr>'+headerHtml+'</tr></thead><tbody>'+
    (rows || '<tr><td colspan="8" class="my-view-empty">'+(hasUser?'No active tickets assigned to this user.':'Choose a user above to see their tickets.')+'</td></tr>')+'</tbody></table></div></section>';
}
// The scroll buttons appear only when the table is wider than its container.
function updateMyViewScrollControls(){
  const scroller=board.querySelector('.my-view-table-scroll');
  const controls=board.querySelector('.my-view-scroll-controls');
  if(!scroller || !controls) return;
  const maxScroll=Math.max(0,scroller.scrollWidth-scroller.clientWidth);
  controls.hidden=maxScroll<=1;
  controls.querySelector('[data-my-view-scroll="left"]').disabled=scroller.scrollLeft<=1;
  controls.querySelector('[data-my-view-scroll="right"]').disabled=scroller.scrollLeft>=maxScroll-1;
}
const myViewScrollObserver=typeof ResizeObserver==='undefined' ? null : new ResizeObserver(updateMyViewScrollControls);
window.addEventListener('resize',updateMyViewScrollControls);

function renderMyView(){
  const risksActive=(state.issues||[]).filter(i=>!isCompletedStatus(i.status));
  const personalHtml='<section class="dashboard-section dashboard-personal-view" id="my-view-personal"><div class="dashboard-section-head"><div class="dashboard-section-heading"><span class="dashboard-section-title">My view: '+esc(state.currentUserName||'Select a user')+'</span><span class="dashboard-section-note">Your active tickets and deadlines</span><span class="dashboard-section-note personal-overwrite-note">Show on board overwrites your filters</span></div><div class="personal-user-change"><label for="personal-user-mapping">Change user</label>'+dashboardPersonalUserOptions()+'</div></div>'+dashboardPersonalViewHtml(risksActive)+'</section>';
  board.insertAdjacentHTML('beforeend','<div class="my-view">'+personalHtml+myViewTableHtml()+'</div>');
  const tableScroller=board.querySelector('.my-view-table-scroll');
  if(myViewScrollObserver){
    myViewScrollObserver.disconnect();
    myViewScrollObserver.observe(tableScroller);
    myViewScrollObserver.observe(tableScroller.querySelector('table'));
  }
  tableScroller.addEventListener('scroll',updateMyViewScrollControls,{passive:true});
  board.querySelectorAll('[data-my-view-scroll]').forEach(button=>button.addEventListener('click',()=>{
    const direction=button.dataset.myViewScroll==='right'?1:-1;
    tableScroller.scrollBy({left:direction*Math.max(240,Math.round(tableScroller.clientWidth*.75)),behavior:'smooth'});
  }));
  requestAnimationFrame(updateMyViewScrollControls);
  attachEvents();
  const personalUserSelect=board.querySelector('#personal-user-mapping');
  if(personalUserSelect) personalUserSelect.addEventListener('change',()=>{
    const accountId=personalUserSelect.value;
    if(!accountId){ state.currentUserAccountId=''; state.currentUserName=''; state.personalUserOverride=true; }
    else {
      const option=personalUserSelect.options[personalUserSelect.selectedIndex];
      state.currentUserAccountId=accountId; state.currentUserName=option ? option.textContent : accountId; state.personalUserOverride=true;
    }
    resetMyViewSort();
    savePreferences({personalUserAccountId:state.currentUserAccountId,personalUserName:state.currentUserName});
    render();
  });
  board.querySelectorAll('[data-personal-filter]').forEach(btn=>{
    btn.addEventListener('click',()=>{
      const filter=btn.dataset.personalFilter;
      // These actions are only offered for due-date metrics. Always replace the
      // current search and filters with the selected user's due-date filter.
      const meId=state.currentUserAccountId||'';
      state.searchTerm='';
      if(searchEl) searchEl.value='';
      state.showCompleted=false;
      state.includeWithRemarkable=true;
      state.personalTicketFilter='';
      state.filterUser=meId;
      state.filterDue=filter==='overdue'?'overdue':filter==='next7'?'next7':filter==='nextMonth'?'nextMonth':'all';
      state.showDashboard=false;
      state.showMyView=false;
      state.showMilestones=false;
      state.lockedKey=null;
      state.selectionHistory=[];
      state.showBlocked=false;
      savedFullBoardView=null;
      saveFilterPreferences();
      updateFilterControls();
      render();
      // Ensure the visible filter controls reflect the filters applied by this action.
      populateFilterUsers();
      updateFilterControls();
    });
  });
  board.querySelector('#my-view-remarkable')?.addEventListener('change',e=>{
    state.includeWithRemarkable=e.target.checked;
    saveFilterPreferences();
    updateFilterControls();
    render();
  });
  board.querySelectorAll('[data-my-view-sort]').forEach(btn=>btn.addEventListener('click',()=>{
    const field=btn.dataset.myViewSort;
    if(!MY_VIEW_SORT_FIELDS.includes(field)) return;
    const current=state.myViewSort;
    state.myViewSort={field,direction:current.field===field && current.direction==='asc'?'desc':'asc'};
    render();
  }));
  board.querySelector('#my-view-save-sort')?.addEventListener('click',async()=>{
    const id=state.currentUserAccountId;
    if(!id) return;
    const previous=state.myViewSavedSorts;
    state.myViewSavedSorts={...previous,[id]:{...state.myViewSort}};
    const success=await savePreferences({myViewSavedSorts:state.myViewSavedSorts});
    if(success){render();}
    else{
      state.myViewSavedSorts=previous;
      const message=board.querySelector('.my-view-sort-status');
      if(message) message.textContent='Unable to save sorting. Try again.';
    }
  });
  board.querySelectorAll('[data-my-view-key]').forEach(row=>{
    const open=e=>{
      if(e?.target?.closest?.('[data-stop-propagation], a, button, select, .priority-picker, .priority-menu')) return;
      const key=row.dataset.myViewKey;
      if(!key) return;
      state.showMyView=false;
      state.showDashboard=false;
      state.showMilestones=false;
      state.lockedKey=key;
      state.selectionHistory=[];
      state.showBlocked=false;
      state.dashboardReturnSection='my-view';
      state.returnMilestoneKey=null;
      state.revealSelectedKey=key;
      render();
    };
    row.addEventListener('click',open);
    row.addEventListener('keydown',e=>{if(e.key==='Enter' && e.target===row){e.preventDefault();open(e);}});
  });
  statusText.textContent='My view';
  requestAnimationFrame(()=>{
    const saved=state.scrollPositions['my-view']||{};
    document.getElementById('app').scrollTop=saved.appTop||0;
  });
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

let ticketPreviewReturnFocus=null;
function closeTicketPreviewModal(){
  const returnFocus=ticketPreviewReturnFocus;
  ticketPreviewReturnFocus=null;
  const backdrop = document.getElementById('ticket-preview-backdrop');
  if(backdrop) backdrop.remove();
  const modal = document.getElementById('ticket-preview-modal');
  if(modal) modal.remove();
  if(returnFocus?.isConnected) returnFocus.focus({preventScroll:true});
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
  ticketPreviewReturnFocus=document.activeElement;

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
      '<div class="milestone-card-top-right">' + epicHtml + (i.status ? '<span class="status-badge" style="' + statusStyle(i.status) + '">' + esc(i.status) + '</span>' : '') + '</div>' +
    '</div>' +
    '<div class="summary">' + esc(i.summary) + '</div>' +
    '<div class="card-meta">' + lazyAssigneeSelectHtml(i) + dueDateHtml(i) + '</div>' +
    '<div class="milestone-chain-meta">' +
      '<span class="my-view-count upstream" title="All active upstream blockers">← ' + dashboardGraphTraversal(state.issues||[]).upstreamCount(i.key) + ' blockers</span>' +
      '<span class="my-view-count downstream" title="All active downstream blocked tickets">Blocked ' + dashboardGraphTraversal(state.issues||[]).downstreamCount(i.key) + ' →</span>' +
      '<button type="button" class="milestone-gantt-launch" data-gantt-milestone="' + esc(i.key) + '" data-stop-propagation="1" title="Open Gantt timeline for ' + esc(i.key) + '" aria-label="Open Gantt timeline for ' + esc(i.key) + '"><svg width="17" height="17" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="M3 4v16M3 7h18M3 12h18M3 17h18"/><path d="M7 5v4h5V5M14 10v4h6v-4M8 15v4h8v-4"/></svg></button>' +
    '</div>' +
  '</article>';
}

function sortedMilestoneBlockers(milestoneKey){
  return milestoneChainItems(milestoneKey).sort((a,b)=>
    (a.chainLevel-b.chainLevel) || priorityRank(a.priority)-priorityRank(b.priority) ||
    (a.dueDate||'9999-12-31').localeCompare(b.dueDate||'9999-12-31') || a.key.localeCompare(b.key));
}
function milestoneOverviewHtml(milestones){
  function blockerItems(i){
    const blockers = sortedMilestoneBlockers(i.key);
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
            groups.get(level).map(b =>
              '<div class="milestone-blocked-item dashboard-ticket' + (isCompletedStatus(b.status) ? ' completed' : '') +
                '" data-key="' + esc(b.key) + '" data-milestone-chain="' + esc(b.key) + '" title="' + esc(b.key + ' - ' + (b.summary || '')) + '">' +
                '<span class="milestone-blocked-content">' +
                  '<span class="milestone-blocked-priority">' + priorityIconHtml(b.priority) + '</span>' +
                  '<a class="milestone-blocked-key" href="' + esc(b.url || (CFG.jiraBaseUrl + '/browse/' + b.key)) +
                  '" target="_blank" rel="noopener noreferrer" data-stop-propagation="1" data-issue-key="' +
                  esc(b.key) + '">' + esc(b.key) + '</a>' +
                  '<span class="milestone-blocked-summary">' + esc(b.summary || '') + '</span>' +
                '</span>' +
                '<span class="milestone-blocked-editor">' + lazyAssigneeSelectHtml(b) + dueDateHtml(b) + '</span>' +
              '</div>'
            ).join('') +
          '</div>';
        }).join('')
      : '<div class="milestone-blocked-empty">No blockers</div>';
    return '<div class="milestone-blocked">' +
      '<div class="milestone-blocked-head">' +
        '<span class="milestone-blocked-title">Blocked by</span>' +
        '<div class="milestone-blocked-actions"><button type="button" class="milestone-blocked-copy" data-copy-milestone="'+esc(i.key)+'" title="Copy blockers for '+esc(i.key)+' as a table" aria-label="Copy blockers for '+esc(i.key)+' as a table"'+(count?'':' disabled')+'><svg xmlns="http://www.w3.org/2000/svg" width="15" height="15" fill="none" viewBox="0 0 24 24" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="8" y="8" width="12" height="12" rx="2"/><path d="M16 8V6a2 2 0 0 0-2-2H6a2 2 0 0 0-2 2v8a2 2 0 0 0 2 2h2"/></svg></button><span class="milestone-blocked-count">' + count + '</span></div>' +
      '</div>' +
      '<div class="milestone-blocked-list">' + list + '</div>' +
    '</div>';
  }

  return '<div class="milestone-overview">' +
    '<div class="milestone-overview-header">' +
      '<span class="milestone-overview-title">Milestones</span>' +
      '<div class="milestone-overview-tools"><span class="milestone-overview-count">' + milestones.length + '</span>' +
      '<button type="button" class="milestone-project-gantt" id="milestone-project-gantt"'+(milestones.length?'':' disabled')+' title="See every milestone on one project timeline">▤ All milestones Gantt</button></div>' +
    '</div>' +
    '<div class="milestone-row">' +
      (milestones.length
        ? milestones.map(i => '<div class="milestone-item">' +
            '<div class="milestone-overview-card" data-milestone-card="' + esc(i.key) + '" data-milestone-chain="' + esc(i.key) + '">' + milestoneCardHtml(i) +
              '</div>' +
            blockerItems(i) +
          '</div>').join('')
        : '<div class="empty">No milestone tickets</div>') +
    '</div>' +
  '</div>';
}

// Copy milestone blockers as an actual HTML table (for Outlook/Gmail) with
// a tab-separated text alternative for plain-text editors.
function milestoneBlockersClipboardContent(milestoneKey){
  const milestone=state.issues.find(i=>i.key===milestoneKey);
  const blockers=sortedMilestoneBlockers(milestoneKey);
  const columns=['Level','Key','Summary','Priority','Assignee','Due date','Status'];
  const records=blockers.map(b=>[
    b.chainLevel===0?'Unblocked':'Level '+b.chainLevel,
    b.key,b.summary||'',b.priority||'Unspecified',b.assignee||'Unassigned',
    b.dueDate?formatDueDate(b.dueDate):'No due date',b.status||''
  ]);
  const textValue=String(milestone?.summary||milestoneKey)+' ('+milestoneKey+') — Blocked by\n'+
    columns.join('\t')+'\n'+records.map(r=>r.map(v=>String(v).replace(/[\t\r\n]+/g,' ')).join('\t')).join('\n');
  const css='border:1px solid #cbd5e1;padding:7px 10px;text-align:left;font:12px Arial,sans-serif;vertical-align:top;';
  const headerCells=columns.map(c=>'<th style="'+css+'background:#e2e8f0;color:#172033;font-weight:bold;">'+esc(c)+'</th>').join('');
  const rows=records.map((r,n)=>'<tr>'+r.map((value,idx)=>{
    const url=idx===1?((state.issues.find(i=>i.key===value)?.url)||CFG.jiraBaseUrl+'/browse/'+value):'';
    const content=url?'<a href="'+esc(url)+'" style="color:#4338ca;text-decoration:underline;">'+esc(value)+'</a>':esc(value);
    return '<td style="'+css+'background:'+(n%2?'#f8fafc':'#ffffff')+';">'+content+'</td>';
  }).join('')+'</tr>').join('');
  const name=milestone?.summary||milestoneKey;
  const html='<div style="font:13px Arial,sans-serif;color:#172033;"><p style="font-weight:bold;margin:0 0 8px;">'+esc(name)+' ('+esc(milestoneKey)+') — Blocked by ('+blockers.length+')</p>'+
    '<table style="border-collapse:collapse;width:100%;max-width:900px;">' +
    '<thead><tr>'+headerCells+'</tr></thead><tbody>'+rows+'</tbody></table></div>';
  return {html,text:textValue};
}
async function copyMilestoneBlockers(milestoneKey,button){
  const {html,text}=milestoneBlockersClipboardContent(milestoneKey);
  const previousLabel=button.getAttribute('aria-label');
  let copied=false;
  // Prefer both MIME types: pasting into an email retains the styled table.
  if(navigator.clipboard?.write && typeof ClipboardItem!=='undefined'){
    try{
      await navigator.clipboard.write([new ClipboardItem({
        'text/html':new Blob([html],{type:'text/html'}),
        'text/plain':new Blob([text],{type:'text/plain'})
      })]);
      copied=true;
    }catch(err){console.warn('Rich clipboard write unavailable; trying selection copy.',err);}
  }
  if(!copied){
    // The selection fallback copies the HTML table in browsers that disallow
    // ClipboardItem, without requiring the user to select any page contents.
    const temp=document.createElement('div');
    temp.contentEditable='true';
    temp.style.cssText='position:fixed;left:-99999px;top:0;width:900px;';
    temp.innerHTML=html;
    document.body.appendChild(temp);
    const selection=window.getSelection();
    const oldRange=selection?.rangeCount?selection.getRangeAt(0).cloneRange():null;
    try{
      const range=document.createRange();range.selectNodeContents(temp);
      selection.removeAllRanges();selection.addRange(range);
      copied=document.execCommand('copy');
    }catch(err){console.warn('Table selection copy unavailable.',err);}
    finally{
      selection?.removeAllRanges();
      if(oldRange) selection?.addRange(oldRange);
      temp.remove();
    }
  }
  if(!copied && navigator.clipboard?.writeText){
    try{await navigator.clipboard.writeText(text);copied=true;}catch(err){console.warn('Plain-text clipboard failed.',err);}
  }
  button.title=copied?'Blockers copied as a table':'Could not copy blockers';
  button.setAttribute('aria-label',copied?'Blockers copied': 'Copy failed; try again');
  button.classList.toggle('copied',copied);
  setTimeout(()=>{
    if(!button.isConnected) return;
    button.title='Copy blockers as an email table';
    button.setAttribute('aria-label',previousLabel||'Copy blockers as a table');
    button.classList.remove('copied');
  },2500);
}

function renderMilestoneOverview(flashKey){
  const milestones = state.displayIssues
    .filter(i => (i.labels || []).some(label => String(label).toLowerCase() === 'milestone'))
    .sort((a,b) => (!a.dueDate ? 0:1)-(!b.dueDate ? 0:1) || (a.dueDate||'').localeCompare(b.dueDate||'') || a.key.localeCompare(b.key));

  const existing = board.querySelector('.milestone-overview');
  if(existing) existing.remove();
  const wrapper = document.createElement('div');
  wrapper.innerHTML = milestoneOverviewHtml(milestones);
  board.appendChild(wrapper.firstElementChild);
  board.querySelector('#milestone-project-gantt')?.addEventListener('click',e=>{
    e.preventDefault();e.stopPropagation();
    openAllMilestonesGantt(e.currentTarget);
  });

  // Milestone elements are rendered separately from the normal board event
  // wiring, so attach the controls they contain here as well.
  attachTicketKeyModalHandlers(board);
  board.querySelectorAll('[data-gantt-milestone]').forEach(btn=>{
    btn.addEventListener('click',e=>{
      e.preventDefault();e.stopPropagation();
      openMilestoneGantt(btn.dataset.ganttMilestone,btn);
    });
  });
  board.querySelectorAll('[data-copy-milestone]').forEach(btn=>{
    btn.addEventListener('click',e=>{
      e.preventDefault();e.stopPropagation();
      copyMilestoneBlockers(btn.dataset.copyMilestone,btn);
    });
  });

  // Milestone items do not use the normal board click handlers: wire just
  // their editors so clicking an input never navigates to the dependency map.
  board.querySelectorAll('select[data-field="assignee"]').forEach(select=>{
    ['pointerdown','focus','keydown'].forEach(type=>select.addEventListener(type,()=>populateAssigneeSelect(select)));
    select.addEventListener('change',e=>{
      e.stopPropagation();
      const item=select.closest('.card, .dashboard-ticket');
      if(item){select.classList.toggle('unassigned',!select.value);stageIssueChange(item.dataset.key, 'assignee',select.value);}
    });
    select.addEventListener('click',e=>e.stopPropagation());
  });
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
    // Milestones have horizontal page scrolling, but vertical scrolling is
    // confined to the individual blocker lists.
    app.scrollTop = 0;
    const listOffsets=savedMilestoneScroll.milestoneLists || {};
    board.querySelectorAll('.milestone-item').forEach(item=>{
      const key=item.querySelector('[data-milestone-card]')?.dataset.milestoneCard;
      const list=item.querySelector('.milestone-blocked-list');
      if(key && list) list.scrollTop=listOffsets[key] || 0;
    });
    if(flashKey){
      const target = board.querySelector('.milestone-overview-card[data-milestone-card="' + CSS.escape(flashKey) + '"]');
      if(target){
        target.scrollIntoView({behavior:'smooth',block:'nearest',inline:'center'});
        target.classList.remove('milestone-flash');
        void target.offsetWidth;
        target.classList.add('milestone-flash');
        setTimeout(() => target.classList.remove('milestone-flash'), 950);
      }
    }
  });
}

// Render each level's full set of cards before displaying the board.
// Incremental batches made column heights grow under an active scrollbar and
// forced delayed scroll restoration. Editing menus are still created lazily.
// ── Render ────────────────────────────────────────────────────────────────
let boardRenderEpoch=0;
let linesRenderFrame=0;
function dependencyLinesAreVisible(){
  const app=document.getElementById('app');
  return !!(state.lockedKey && !state.showMilestones && !state.showDashboard &&
    !state.showMyView && app?.classList.contains('locked') &&
    !board.classList.contains('milestone-board') &&
    !board.classList.contains('dashboard-board') &&
    !board.classList.contains('my-view-board') &&
    document.getElementById('gantt-overlay')?.hidden !== false &&
    board.querySelector(':scope > .column'));
}
function scheduleDependencyLines(){
  // Avoid even starting an animation frame for the full board, milestones,
  // dashboard or My View. Their SVG is intentionally empty and hidden.
  if(!dependencyLinesAreVisible()){
    if(linesRenderFrame){cancelAnimationFrame(linesRenderFrame);linesRenderFrame=0;}
    return;
  }
  // Coalesce rapid resize events into a single path rebuild per frame.
  if(linesRenderFrame) return;
  const epoch=boardRenderEpoch;
  linesRenderFrame=requestAnimationFrame(()=>{
    linesRenderFrame=0;
    if(epoch===boardRenderEpoch && dependencyLinesAreVisible()) drawLines();
  });
}
function render(){
  const renderStart=performance.now();
  boardRenderEpoch++;
  if(linesRenderFrame){cancelAnimationFrame(linesRenderFrame);linesRenderFrame=0;}
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
  [...board.querySelectorAll('.column, .milestone-overview, .dashboard, .my-view, .no-active-user, .no-results')].forEach(x => x.remove());
  if(state.completedDownloadStatus === 'ready' || !state.showCompleted) hideCompletedDownloadNotice();
  board.classList.toggle('milestone-board', state.showMilestones);
  board.classList.toggle('dashboard-board', state.showDashboard);
  board.classList.toggle('my-view-board', state.showMyView);
  document.getElementById('app').classList.toggle('milestone-mode', state.showMilestones);
  document.getElementById('app').classList.toggle('dashboard-mode', state.showDashboard);
  document.getElementById('app').classList.toggle('my-view-mode', state.showMyView);
  if(toggleCompletedBtn) toggleCompletedBtn.classList.toggle('dashboard-hidden', state.showDashboard || state.showMyView);
  dependencyStatus.classList.toggle('view-hidden', state.showDashboard || state.showMilestones || state.showMyView);
  // Rebuild display data honoring the completed toggle
  computeDisplayData();
  console.debug('Dependency graph render', {issues:state.displayIssues.length, edges:state.displayEdges.length, selected:state.lockedKey});

  // Sync filter controls
  populateFilterUsers();
  updateFilterControls();
  document.querySelectorAll('.view-switch').forEach(btn => btn.classList.toggle('active', btn.dataset.view === (state.showDashboard ? 'dashboard' : state.showMyView ? 'my-view' : state.showMilestones ? 'milestone' : 'default')));

  if(state.showMyView){
    hideMiniMap();
    state.lockedKey=null;
    state.selectionHistory=[];
    state.showBlocked=false;
    syncSharedViewUrl();
    document.getElementById('app').classList.remove('locked');
    searchWrap.style.visibility='hidden';
    if(filterMenu) filterMenu.classList.remove('open');
    if(filtersBtn) filtersBtn.style.visibility='hidden';
    if(clearFiltersBtn) clearFiltersBtn.style.visibility='hidden';
    deselectBtn.classList.remove('visible');
    if(milestoneBackBtn) milestoneBackBtn.classList.remove('visible');
    renderMyView();
    return;
  }
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
    statusText.textContent = 'Project overview';
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
      'my-view':'My view',
      'unblocking':'Unblocking opportunities',
      'high-priority-risk':'High-priority risk',
      'overdue':'Overdue tickets',
      'chain-risks':'Dependency chain date risks',
      'unassigned':'Unassigned tickets',
      'missing-due':'Missing due dates',
      'circular':'Circular dependencies',
      'blocked-tickets':'Blocked tickets'
    };
    const isDashboardTabReturn=String(state.dashboardReturnSection||'').startsWith('dashboard:');
    if(isDashboardTabReturn){
      const tabId=state.dashboardReturnSection.slice('dashboard:'.length);
      dashboardBackLabels[state.dashboardReturnSection]=DASHBOARD_TABS.find(([id])=>id===tabId)?.[1]||'Project overview';
    }
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
  // When locked, the normal search filter is not run. Update the legend for
  // the selected chain rather than retaining markers from another ticket.
  if(locked){
    if(externalStatus) externalStatus.style.display=visibleIssues.some(i=>(i.externalBlockers||[]).length)?'inline-flex':'none';
    if(cycleStatus) cycleStatus.style.display=visibleIssues.some(i=>i.cycle)?'inline-flex':'none';
  }

  // Column map
  const cols = new Map();
  visibleIssues.forEach(i => { if(!cols.has(i.level)) cols.set(i.level, []); cols.get(i.level).push(i); });
  const max = visibleIssues.length ? Math.max(...visibleIssues.map(i => i.level || 0)) : 0;
  const labels = ['Unblocked', ...Array.from({length:max}, (_,n) => 'Level ' + (n+1))];
  const orders = [];
  for(let lv = 0; lv <= max; lv++) orders[lv] = [...(cols.get(lv) || [])].sort((a,b) => a.key.localeCompare(b.key));

  // The default view sorts by priority; selected chains sort by distance.
  // The old eight-pass barycenter sort was overwritten in *both* modes,
  // so avoid doing that unused O(columns × issues × edges) work.
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
      for(const previous of (state.displayIncoming.get(k)||[])){
        if(!distance.has(previous)){
          distance.set(previous,(distance.get(k)||0)+1);q.push(previous);
        }
      }
    }
    if(state.showBlocked){
      const dq = [state.lockedKey], dSeen = new Set([state.lockedKey]);
      while(dq.length){
        const k = dq.shift();
        for(const next of (state.displayOutgoing.get(k)||[])){
          if(!dSeen.has(next)){
            dSeen.add(next);
            if(!distance.has(next)) distance.set(next,-(distance.get(k)||0)-1);
            dq.push(next);
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

  // Construct the entire board off-document and install it in one operation.
  // No cards are appended later during scrolling, and scroll offsets are
  // restored in this same task, before the first visible paint.
  const columnFragment=document.createDocumentFragment();
  for(let lv=0;lv<=max;lv++){
    const col=document.createElement('section');
    col.className='column'+(locked?' unlocked':'');
    col.dataset.level=String(lv);
    const items=orders[lv];
    const cardsDiv=document.createElement('div');
    cardsDiv.className='cards'+(locked?' noscroll':'');
    if(!items.length) cardsDiv.innerHTML='<div class="empty">No tickets at this level</div>';
    else cardsDiv.innerHTML=items.map(i=>cardHtml(i,searchTerm)).join('');
    const header=document.createElement('div');
    header.className='column-header';
    header.innerHTML='<span class="column-title">'+(labels[lv]||'Level '+lv)+'</span>'+
      '<span class="column-count">'+items.length+'</span>';
    col.appendChild(header);col.appendChild(cardsDiv);
    columnFragment.appendChild(col);
  }
  board.appendChild(columnFragment);
  console.info('[Performance] Board column preparation',{milliseconds:Math.round(performance.now()-renderStart),tickets:visibleIssues.length});
  // Attach handlers and apply filtering while the full set of cards exists.
  // Never wait for scrolling, animation frames or an incremental-card batch.
  attachEvents();
  if(locked) spaceLongRoutes();
  else applySearchFilter();
  preserveBoardScrollDuringRender();
  scheduleDependencyLines();
  scheduleMiniMapUpdate();
  console.info('[Performance] Board ready',{milliseconds:Math.round(performance.now()-renderStart),tickets:visibleIssues.length});

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

  if(locked){
    statusText.textContent = visibleIssues.length.toLocaleString('en-GB') + ' tickets in chain · Esc to deselect';
  }
  return Promise.resolve();
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
  // Inactive views must not measure cards, rebuild SVG paths or clamp their
  // scroll positions: all of those force layout and can cause visible lag.
  if(!dependencyLinesAreVisible()) return;
  resetDependencyLineCanvas();

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
  const colEls = [...board.querySelectorAll(':scope > .column')];
  if(!colEls.length) return;

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

  // Read card/column geometry once before writing paths to the DOM. Reading
  // a rect after each SVG append previously forced repeated layout work on
  // large selected chains.
  const colIndexes=new Map(colEls.map((column,index)=>[column,index]));
  const colRects=colEls.map(column=>column.getBoundingClientRect());
  const cards=new Map();
  board.querySelectorAll('.column .card').forEach(card=>{
    const rect=card.getBoundingClientRect();
    cards.set(card.dataset.key,{
      column:colIndexes.get(card.closest('.column')),
      left:rect.left-br.left,right:rect.right-br.left,
      viewportRight:rect.right,y:rect.top+30-br.top
    });
  });
  const paths=document.createDocumentFragment();
  // Route the vertical leg through the whitespace gap immediately after the
  // source column. Internal cycles bend through the right-hand gutter.
  edges.forEach(e=>{
    const source=cards.get(e.from),target=cards.get(e.to);
    if(!source || !target) return;
    const fromCol=source.column,toCol=target.column;
    if(fromCol==null || toCol==null || toCol<fromCol) return;
    const sameColumn=fromCol===toCol;
    const sx=source.right,sy=source.y;
    const tx=sameColumn?target.right:target.left,ty=target.y;
    const nextRect=colRects[fromCol+1];
    const routeX=sameColumn
      ? sx+16+(e.from.length+e.to.length)%3*4
      : nextRect?((source.viewportRight+nextRect.left)/2)-br.left:sx+20;
    const d='M '+sx+' '+sy+' L '+routeX+' '+sy+
      ' L '+routeX+' '+ty+' L '+tx+' '+ty;
    const path=document.createElementNS(ns,'path');
    path.setAttribute('d',d);
    path.setAttribute('class',sameColumn?'line highlighted-line cycle-line':'line highlighted-line');
    path.dataset.from=e.from;
    path.dataset.to=e.to;
    path.setAttribute('marker-end','url(#arrow)');
    paths.appendChild(path);
  });
  const defs=document.createElementNS(ns,'defs');
  defs.innerHTML='<marker id="arrow" markerWidth="4" markerHeight="4" refX="3.5" refY="2" orient="auto">'+
    '<path d="M0,0 L4,2 L0,4 z" class="arrow"/></marker>';
  lines.appendChild(defs);
  lines.appendChild(paths);
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
  // Jira JQL does not return archived issues. A link whose source cannot be
  // retrieved is NOT verified as an active blocker. Show it in a separate,
  // clearly qualified editor section so it can be cleaned up if appropriate.
  const externalKeys=(issue?.externalBlockers || []).map(x=>x.key);
  const unavailableKeys=(issue?.unavailableBlockers || []).map(x=>x.key);
  return {
    blockedBy: [...new Set([...(issue?.blockers || []),...externalKeys])].sort(),
    blocks: (issue?.blocked || []).slice().sort(),
    unavailable: [...new Set(unavailableKeys)].sort()
  };
}

function renderDependencyList(){
  const {blockedBy, blocks, unavailable} = currentDependencyPairs();

  function row(key, source, target, isUnavailable=false){
    const issue = state.issues.find(i => i.key === key);
    const external=!issue && !!state.issues.find(i=>i.key===target)?.externalBlockers?.some(x=>x.key===source);
    const issueUrl = issue?.url || (CFG.jiraBaseUrl + '/browse/' + encodeURIComponent(key));
    const detail=isUnavailable ? 'Not returned by Jira search (possibly archived, deleted or inaccessible)'
      : external ? 'External blocker (not returned by Jira)' : (issue?.summary || '');
    return '<div class="dependency-row">' +
      '<div class="dependency-row-text"><a class="dependency-row-key" href="' + esc(issueUrl) +
      '" target="_blank" rel="noopener noreferrer" data-issue-key="' + esc(key) + '">' + esc(key) + '</a> · ' +
      esc(detail) + '</div>' +
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
    section('Blocks', blocks, false) +
    (unavailable.length ? '<div class="dependency-section blocked-by">' +
      '<div class="dependency-section-title">Unavailable linked issues (not counted as blockers)</div>' +
      '<div class="dependency-empty">These links may be archived, deleted or inaccessible. Removing one changes Jira only after Save.</div>' +
      unavailable.map(key=>row(key,key,depA.value,true)).join('') + '</div>' : '');

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
      ticketPreviewReturnFocus=link;
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

    if(state.showMilestones || state.showDashboard || state.showMyView || state.showBlocked || state.lockedKey){
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
      state.showMyView = state.startingView === 'my-view';
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
  const {byKey,outgoing,incoming}=activeDateRiskGraph();
  // Never walk through completed tickets, including when Show completed is ON.
  if(!byKey.has(startKey)) return [];
  const adjacent=direction==='downstream' ? outgoing : incoming;
  const result=[],queue=[startKey],seen=new Set([startKey]);
  for(let cursor=0;cursor<queue.length;cursor++){
    for(const next of (adjacent.get(queue[cursor])||[])){
      if(seen.has(next)) continue;
      seen.add(next);
      queue.push(next);
      result.push(byKey.get(next));
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

function attachEvents(root=board, partial=false){
  // ── Card click (select / deselect) ──
  root.querySelectorAll('.card').forEach(card => {
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
  root.querySelectorAll('.hover-lock-btn').forEach(btn => {
    btn.addEventListener('click', e => {
      e.preventDefault();
      e.stopPropagation();
      const key = btn.dataset.key;
      if(!key || !state.lockedKey) return;
      if(state.hoverLockKey === key) clearHoverLock();
      else lockHoverHighlight(key);
    });
  });

  // A selected chain's root ticket can be viewed as its own Gantt timeline.
  root.querySelectorAll('[data-gantt-chain]').forEach(btn=>{
    btn.addEventListener('click',e=>{
      e.preventDefault();e.stopPropagation();
      if(!state.lockedKey || state.lockedKey!==btn.dataset.ganttChain) return;
      openMilestoneGantt(btn.dataset.ganttChain,btn);
    });
  });

  // ── Milestone banner ─────────────────────────────────────────────────────
  // The card itself selects the normal dependency chain. The dedicated banner
  // is the separate navigation target for opening the milestone overview.
  root.querySelectorAll('.milestone-banner').forEach(banner => {
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
  root.querySelectorAll('[data-stop-propagation]').forEach(el => {
    el.addEventListener('click', e => e.stopPropagation());
  });

  // ── Editable Jira fields ──
  root.querySelectorAll('select[data-field]').forEach(select => {
    select.addEventListener('pointerdown',()=>populateAssigneeSelect(select));
    select.addEventListener('focus',()=>populateAssigneeSelect(select));
    select.addEventListener('keydown',()=>populateAssigneeSelect(select));
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
  root.querySelectorAll('[data-due-date-key]').forEach(btn => {
    btn.addEventListener('click', e => {
      e.preventDefault(); e.stopPropagation();
      openDueDateModal(btn.dataset.dueDateKey);
    });
  });

  // ── Custom priority picker with Jira icons ──
  root.querySelectorAll('.priority-picker').forEach(picker => {
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
        populatePriorityMenu(picker);
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
    // Delegation works for lazily inserted choices as well as existing menus.
    picker.querySelector('.priority-menu')?.addEventListener('click', e => {
      const option=e.target.closest('.priority-option');
      if(!option) return;
      e.stopPropagation();
      const card=picker.closest('.card, .dashboard-ticket');
      if(!card) return;
      const value=option.dataset.priority;
      stageIssueChange(card.dataset.key,'priority',value);
      const img=picker.querySelector('.priority-icon');
      if(img && CFG.jiraBaseUrl){
        img.src=CFG.jiraBaseUrl+'/images/icons/priorities/'+value.toLowerCase()+'.svg';
        img.alt=value; img.title=value;
      }
      const menu=option.closest('.priority-menu');
      if(menu) menu.querySelectorAll('.priority-option').forEach(x=>x.classList.toggle('selected',x===option));
      closePriorityPicker(picker);
      if(state.showMyView && picker.closest('.my-view-row')) render();
    });
  });


  // ── Reveal downstream / higher-level blocked cards ──
  root.querySelectorAll('.see-blocked-btn').forEach(btn => {
    btn.addEventListener('click', e => {
      e.stopPropagation();
      state.showBlocked = !state.showBlocked;
      render();
    });
  });
  // ── Edit dependency buttons ──
  root.querySelectorAll('.edit-dependency-btn').forEach(btn => {
    btn.addEventListener('click', e => {
      e.stopPropagation();
      openDependencyModal(btn.dataset.editDependency);
    });
  });

  // ── Hover → highlight chain (only while an item is selected) ──
  root.querySelectorAll('.card').forEach(card => {
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

  if(!partial){
    highlightSelectedChainDateRisks();
    updateSaveButton();
    updateHoverLockButtons();
  }
  attachTicketKeyModalHandlers(root);
}

// ── Load data ─────────────────────────────────────────────────────────────
// The Flask worker survives browser reloads. A sequence number alone (1, 2, 3…)
// repeats in each new tab/page and can accidentally reuse an older completed
// graph. Combine it with a unique ID for this page lifetime.
const jiraPageSessionId = (typeof crypto !== 'undefined' && typeof crypto.randomUUID === 'function')
  ? crypto.randomUUID()
  : Date.now().toString(36) + '_' + Math.random().toString(36).slice(2);
function jiraLoadKey(loadGeneration){ return jiraPageSessionId + ':' + String(loadGeneration); }

async function fetchGraph(mode, loadGeneration){
  const refreshToken = Date.now().toString(36) + '_' + Math.random().toString(36).slice(2);
  const started=performance.now();
  const r = await fetch('/api/dependencies?mode=' + encodeURIComponent(mode) + '&jql=' + encodeURIComponent(getActiveJql()) + '&generation=' + encodeURIComponent(jiraLoadKey(loadGeneration)) + '&refresh=' + encodeURIComponent(refreshToken), {cache:'no-store'});
  const transferred=performance.now();
  const d = await r.json();
  if(!r.ok) throw new Error(d.error || 'HTTP ' + r.status);
  console.info('[Performance] Jira response', {networkSeconds:((transferred-started)/1000).toFixed(2), jsonSeconds:((performance.now()-transferred)/1000).toFixed(2), issues:(d.issues||[]).length});
  console.log('Jira graph loaded', {issues:(d.issues || []).length, edges:(d.edges || []).length, withDueDates:(d.issues || []).filter(i => i.dueDate).length});
  return d;
}

let completedDownloadPollTimer = null;
async function pollCompletedDownload(loadGeneration = state.loadGeneration){
  if(completedDownloadPollTimer) clearInterval(completedDownloadPollTimer);
  // Always poll the background job belonging to the currently displayed Jira
  // load. This also makes calls from the Show completed toggle safe.
  loadGeneration = Number(loadGeneration);
  const generation=jiraLoadKey(loadGeneration);
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
          state.showMyView=false;
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
        state.showMyView = state.startingView === 'my-view';
        state.showMilestones = state.startingView === 'milestone';
        startupViewPending=false;
      }
    }
    await render(); updateSaveButton();
    if(loadGeneration!==state.loadGeneration) return;
    // Close & refresh from a Jira issue preview leaves the user in the same
    // Gantt, rebuilt against the refreshed Jira graph and current preferences.
    refreshOpenGanttAfterJiraLoad();
    // The optional Sitebuilder message must not hold a fully rendered Jira
    // board behind the loading overlay when the remote feed is slow.
    if(startupMessagePromise){
      await Promise.race([startupMessagePromise,new Promise(done=>setTimeout(done,250))]);
    }
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
  if(String(state.dashboardReturnSection||'').startsWith('dashboard:') && state.selectionHistory.length===0){
    const tab=state.dashboardReturnSection.slice('dashboard:'.length);
    state.dashboardReturnSection=null;state.dashboardTab=tab;state.showDashboard=true;
    state.showMyView=false;state.lockedKey=null;state.showBlocked=false;render();return;
  }
  if(state.dashboardReturnSection==='my-view' && state.selectionHistory.length===0){
    state.dashboardReturnSection=null;state.showMyView=true;state.lockedKey=null;state.showBlocked=false;render();return;
  }
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
  state.personalTicketFilter='';
  state.filterUser = filterUser.value;
  saveFilterPreferences();
  render();
});
filterDue.addEventListener('change', () => {
  state.personalTicketFilter='';
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
    state.showDashboard=sectionId!=='my-view';
    if(sectionId.startsWith('dashboard:')) state.dashboardTab=sectionId.slice('dashboard:'.length);
    state.showMyView=sectionId==='my-view';
    state.lockedKey=null;
    state.selectionHistory=[];
    state.showBlocked=false;
    state.milestoneFlashKey=null;
    render();
    requestAnimationFrame(()=>{
      const target=document.getElementById(sectionId.startsWith('dashboard:')?'dashboard-table-area':sectionId);
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
    const currentView=state.showDashboard?'dashboard':state.showMyView?'my-view':state.showMilestones?'milestone':'default';
    if(currentView==='default' && view!=='default'){
      savedFullBoardView={lockedKey:state.lockedKey,selectionHistory:JSON.parse(JSON.stringify(state.selectionHistory||[])),showBlocked:state.showBlocked,filterUser:state.filterUser,filterDue:state.filterDue,includeWithRemarkable:state.includeWithRemarkable,searchTerm:state.searchTerm,scrollPositions:JSON.parse(JSON.stringify(state.scrollPositions||{}))};
    }
    state.showDashboard=view==='dashboard';
    state.showMyView=view==='my-view';
    state.showMilestones=view==='milestone';
    if(view==='default' && savedFullBoardView){
      Object.assign(state,savedFullBoardView);
      savedFullBoardView=null;
      if(searchEl && typeof state.searchTerm==='string') searchEl.value=state.searchTerm;
    }else{
      state.lockedKey=null;
      state.selectionHistory=[];
      state.showBlocked=false;
    }
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

if(typeof ResizeObserver!=='undefined'){
  const lineResizeObserver=new ResizeObserver(()=>{
    if(dependencyLinesAreVisible()) scheduleDependencyLines();
  });
  lineResizeObserver.observe(board);
  lineResizeObserver.observe(document.getElementById('app'));
}
window.addEventListener('resize', () => { scheduleDependencyLines(); scheduleMiniMapUpdate(); });
// Do not redraw dependency SVG paths while the app scrolls. In the selected
// view the board, cards and SVG move together, so rebuilding the paths on
// every scroll frame only causes flicker.

// ── Milestone Gantt (read-only; its dates reflect the current board snapshot) ──
let ganttCurrent=null;
let ganttReturnFocus=null;
let ganttDayWidth=12;
const GANTT_DAY_MS=86400000;
function ganttDate(value){
  const match=/^(\d{4})-(\d{2})-(\d{2})/.exec(String(value||''));
  if(!match) return null;
  const ms=Date.UTC(+match[1],+match[2]-1,+match[3]);
  const date=new Date(ms);
  return date.toISOString().slice(0,10)===match[0]?ms:null;
}
function ganttDateKey(ms){return new Date(ms).toISOString().slice(0,10);}
function ganttDateLabel(ms){return new Intl.DateTimeFormat('en-GB',{day:'numeric',month:'short',year:'numeric',timeZone:'UTC'}).format(new Date(ms));}
function ganttIssueColour(status){
  if(isCompletedStatus(status))return '#16a34a';
  const value=String(status||'').toLowerCase();
  if(value.includes('block'))return '#dc2626';
  if(value.includes('review'))return '#9333ea';
  if(value==='with remarkable')return '#d97706';
  if(value.includes('progress')||value.includes('doing')||value.includes('active')||value.includes('development'))return '#2563eb';
  return '#64748b';
}
// Share one date policy between individual-task and all-milestones Gantts.
// Direct blockers can supply a start when Jira has no explicit start date;
// they need not be included as visible rows in the all-milestones chart.
function ganttScheduleForIssue(i,edges,byKey){
  const jiraStart=ganttDate(i.startDate);
  const created=ganttDate(i.created);
  const blockerDue=edges.filter(e=>e.to===i.key).map(e=>ganttDate(byKey.get(e.from)?.dueDate)).filter(n=>n!==null);
  const lastBlocker=blockerDue.length?Math.max(...blockerDue):null;
  const start=jiraStart!==null?jiraStart:lastBlocker!==null?lastBlocker+GANTT_DAY_MS:created;
  const end=ganttDate(i.dueDate);
  const source=jiraStart!==null?'Jira start date':lastBlocker!==null?'Latest blocker due + 1 day':created!==null?'Jira creation date':'Missing start date';
  const reason=end===null?'No due date':start===null?'No start or creation date':start>end?'Start falls after due date':'';
  return {source,start:start===null?null:ganttDateKey(start),end:end===null?null:ganttDateKey(end),reason};
}
function buildMilestoneGantt(milestoneKey){
  const milestone=state.displayByKey?.get(milestoneKey) || state.displayIssues.find(i=>i.key===milestoneKey);
  if(!milestone)return null;
  const blockers=milestoneChainItems(milestoneKey);
  const all=[...blockers,milestone];
  const keys=new Set(all.map(i=>i.key));
  const edges=state.displayEdges.filter(e=>keys.has(e.from)&&keys.has(e.to));
  const byKey=new Map(all.map(i=>[i.key,i]));
  const rows=all.map(i=>{
    const schedule=ganttScheduleForIssue(i,edges,byKey);
    return {key:i.key,summary:i.summary||'',status:i.status||'',assignee:i.assignee||'Unassigned',assigneeAccountId:i.assigneeAccountId||null,
      milestone:i.key===milestoneKey,...schedule,color:ganttIssueColour(i.status),level:i.chainLevel||0};
  });
  const scheduled=rows.filter(r=>!r.reason&&r.start&&r.end);
  const unscheduled=rows.filter(r=>r.reason||!r.start||!r.end);
  const isMilestone=(milestone.labels||[]).some(label=>String(label).toLowerCase()==='milestone');
  return {milestone:{key:milestone.key,summary:milestone.summary||'',isMilestone},isMilestone,rows,scheduled,unscheduled,edges};
}
// In the project plan, each milestone bar covers the work since the nearest
// preceding milestone(s), not just the milestone's direct blockers. Only this
// overview uses chain-based dates; individual task/milestone Gantts retain
// ganttScheduleForIssue's existing scheduling policy.
function ganttProjectMilestoneSchedule(issue,incoming,byKey){
  // An explicit Jira start date always wins, even when the chain begins earlier.
  const fallback=ganttScheduleForIssue(issue,[],byKey);
  if(ganttDate(issue.startDate)!==null)return fallback;

  const visited=new Set([issue.key]);
  const tasks=new Set();
  const queue=[issue.key];
  for(let idx=0;idx<queue.length;idx++){
    for(const link of (incoming.get(queue[idx])||[])){
      const blocker=byKey.get(link.from);
      if(!blocker||visited.has(blocker.key))continue;
      visited.add(blocker.key);
      if((blocker.labels||[]).some(label=>String(label).toLowerCase()==='milestone')){
        // Stop at this milestone: tasks before it belong to an earlier stage.
      }else{
        tasks.add(blocker.key);
        queue.push(blocker.key);
      }
    }
  }

  // Find the first task on each branch *after* its preceding milestone.
  // The earliest start across parallel branches is the start of this stage.
  const roots=[...tasks].filter(key=>
    !(incoming.get(key)||[]).some(link=>tasks.has(link.from)));
  // Cyclic chains may have no roots; use their tasks as a safe fallback.
  const firstTasks=roots.length?roots:[...tasks];
  let earliest=null;
  for(const key of firstTasks){
    const task=byKey.get(key);
    const schedule=ganttScheduleForIssue(task,incoming.get(key)||[],byKey);
    const start=ganttDate(schedule.start);
    if(start!==null&&(!earliest||start<earliest.start||(start===earliest.start&&key<earliest.key))){
      earliest={key,start,source:schedule.source};
    }
  }

  let start=fallback.start;
  let source=fallback.source;
  if(earliest){
    start=ganttDateKey(earliest.start);
    source='First blocker '+earliest.key+' · '+earliest.source;
  }
  const startMs=ganttDate(start),endMs=ganttDate(issue.dueDate);
  const reason=endMs===null?'No due date':startMs===null?'No start or creation date':startMs>endMs?'Start falls after due date':'';
  return {start,end:endMs===null?null:ganttDateKey(endMs),source,reason};
}
function buildAllMilestonesGantt(){
  // Use precisely the same visible milestone population as the milestone view;
  // respect the global Completed / With Remarkable and other board filters.
  const milestones=state.displayIssues
    .filter(i=>(i.labels||[]).some(label=>String(label).toLowerCase()==='milestone'))
    .sort((a,b)=>(a.dueDate||'9999-12-31').localeCompare(b.dueDate||'9999-12-31')||a.key.localeCompare(b.key));
  const keys=new Set(milestones.map(i=>i.key));
  const byKey=new Map(state.displayIssues.map(i=>[i.key,i]));
  const dateEdges=state.displayEdges.filter(e=>byKey.has(e.from)&&byKey.has(e.to));
  const incoming=new Map([...byKey.keys()].map(key=>[key,[]]));
  dateEdges.forEach(e=>incoming.get(e.to).push(e));
  const rows=milestones.map(i=>{
    const schedule=ganttProjectMilestoneSchedule(i,incoming,byKey);
    return {key:i.key,summary:i.summary||'',status:i.status||'',assignee:i.assignee||'Unassigned',assigneeAccountId:i.assigneeAccountId||null,
      milestone:true,...schedule,color:ganttIssueColour(i.status),level:0};
  });
  return {milestone:{key:'ALL-MILESTONES',summary:'All project milestones',isMilestone:true,isOverview:true},
    isMilestone:true,isOverview:true,rows,
    scheduled:rows.filter(r=>!r.reason),unscheduled:rows.filter(r=>r.reason),
    edges:state.displayEdges.filter(e=>keys.has(e.from)&&keys.has(e.to))};
}
// A compact, centred badge is used by every scheduled Gantt label.
// "Unassigned" is blue to distinguish tickets that need an owner.
function ganttAssigneeHtml(r){
  const name=String(r.assignee||'').trim();
  const unassigned=!name||name.toLowerCase()==='unassigned';
  const parts=name.split(/\s+/).filter(Boolean);
  const initials=unassigned?'U':(parts.length>1?parts[0].charAt(0)+parts[parts.length-1].charAt(0):parts[0].charAt(0)).toUpperCase();
  const label=unassigned?'Unassigned':'Assigned to '+name;
  return '<span class="gantt-assignee'+(unassigned?' unassigned':'')+'" title="'+esc(label)+'" aria-label="'+esc(label)+'">'+esc(initials)+'</span>';
}
function ganttBarTooltip(r){
  if(ganttCurrent?.isOverview)return r.key+' — '+r.summary+'\nStatus: '+(r.status||'Unspecified')+'\nStart: '+ganttDateLabel(ganttDate(r.start))+' ('+r.source+')'+'\nDue: '+ganttDateLabel(ganttDate(r.end));
  return r.key+' — '+r.summary+'\nStatus: '+(r.status||'Unspecified')+'\nStart: '+ganttDateLabel(ganttDate(r.start))+' ('+r.source+')\nDue: '+ganttDateLabel(ganttDate(r.end));
}
function updateGanttControls(){
  ganttDayWidth=[6,12,20].includes(state.ganttScale) ? state.ganttScale : 12;
  document.querySelectorAll('[data-gantt-scale]').forEach(btn=>{
    const active=Number(btn.dataset.ganttScale)===ganttDayWidth;
    btn.classList.toggle('active',active);
    btn.setAttribute('aria-pressed',String(active));
  });
  const dependencyToggle=document.getElementById('gantt-show-dependencies');
  if(dependencyToggle) dependencyToggle.checked=state.ganttShowDependencies!==false;
  const narrowToggle=document.getElementById('gantt-narrow');
  if(narrowToggle)narrowToggle.checked=state.ganttNarrow===true;
  const completedLegend=document.getElementById('gantt-legend-completed');
  if(completedLegend) completedLegend.hidden=!state.showCompleted;
  const activeLegend=document.getElementById('gantt-legend-active');
  if(activeLegend)activeLegend.hidden=false;
  const remarkableLegend=document.getElementById('gantt-legend-remarkable');
  if(remarkableLegend)remarkableLegend.hidden=false;
  const milestoneLegend=document.getElementById('gantt-legend-milestone');
  if(milestoneLegend)milestoneLegend.hidden=ganttCurrent?.isOverview===true;
  const dependencyLegend=document.getElementById('gantt-legend-dependencies');
  if(dependencyLegend) dependencyLegend.hidden=state.ganttShowDependencies===false||!ganttCurrent?.edges.length;
}
function renderGanttChart(){
  const chart=document.getElementById('gantt-chart');
  const info=document.getElementById('gantt-counts');
  if(!chart||!ganttCurrent)return;
  const d=ganttCurrent,rows=d.scheduled;
  const drawDependencies=state.ganttShowDependencies!==false;
  info.textContent=(d.isOverview?'Milestones: ':'Tasks: ')+rows.length+' scheduled · '+d.unscheduled.length+' unscheduled · '+
    d.edges.length+' direct dependencies'+(drawDependencies?'':' (hidden)')+' · '+
    (state.showCompleted?'including':'excluding')+' completed';
  const maxDate=rows.length?Math.max(...rows.map(r=>ganttDate(r.end))):null;
  const minDate=rows.length?Math.min(...rows.map(r=>ganttDate(r.start))):null;
  const today=ganttDate(localDateKey(new Date()));
  const labelWidth=state.ganttNarrow===true?300:420,headHeight=64;
  // Today is always on the timeline, even when the project is entirely in
  // the past or future. Leave enough calendar before and after it for the
  // initial scroll to place the red line comfortably inside the viewport.
  const calendarViewport=Math.max(120,chart.clientWidth-labelWidth);
  const todayGap=Math.min(190,Math.max(60,Math.floor(calendarViewport*.23)));
  const padDays=3;
  const beforeToday=Math.ceil(todayGap/ganttDayWidth)+padDays;
  const afterToday=Math.ceil(Math.max(0,calendarViewport-todayGap)/ganttDayWidth)+padDays;
  const origin=Math.min(minDate===null?today:minDate-padDays*GANTT_DAY_MS,today-beforeToday*GANTT_DAY_MS);
  const final=Math.max(maxDate===null?today:maxDate+padDays*GANTT_DAY_MS,today+afterToday*GANTT_DAY_MS);
  const days=Math.ceil((final-origin)/GANTT_DAY_MS)+1;
  const timelineWidth=days*ganttDayWidth;
  const totalWidth=labelWidth+timelineWidth;
  const monthHead=[],dayHead=[],weeks=[];
  let lastMonth='';
  for(let day=0;day<days;day++){
    const ms=origin+day*GANTT_DAY_MS,dt=new Date(ms);
    const month=dt.getUTCFullYear()+'-'+dt.getUTCMonth();
    if(month!==lastMonth){
      lastMonth=month;
      monthHead.push('<span class="gantt-month-label" style="left:'+(day*ganttDayWidth)+'px">'+
        esc(new Intl.DateTimeFormat('en-GB',{month:'short',year:'numeric',timeZone:'UTC'}).format(dt))+'</span>');
    }
    if(dt.getUTCDay()===1)weeks.push('<span class="gantt-week-line" style="left:'+(day*ganttDayWidth)+'px"></span>');
    // Compact: months only. Normal: day 5/10/15/... . Expanded: every day.
    if((ganttDayWidth===12&&dt.getUTCDate()%5===0)||ganttDayWidth===20){
      dayHead.push('<span class="gantt-day-label" style="left:'+((day+.5)*ganttDayWidth)+'px">'+dt.getUTCDate()+'</span>');
    }
  }
  const todayLeft=(today-origin)/GANTT_DAY_MS*ganttDayWidth;
  const todayMarkup='<div class="gantt-today" style="left:'+(labelWidth+todayLeft)+'px" title="Today"></div>';
  const rowMarkup=rows.map(r=>{
    const from=(ganttDate(r.start)-origin)/GANTT_DAY_MS*ganttDayWidth;
    const length=((ganttDate(r.end)-ganttDate(r.start))/GANTT_DAY_MS+1)*ganttDayWidth;
    const bar=r.milestone&&!d.isOverview?'<span class="gantt-diamond" style="left:'+(from+length-ganttDayWidth/2)+'px;background:#b45309" title="'+esc(ganttBarTooltip(r))+'"></span>':
      '<span class="gantt-bar" style="left:'+from+'px;width:'+Math.max(5,length-2)+'px;background:'+r.color+'" title="'+esc(ganttBarTooltip(r))+'"></span>';
    return '<div class="gantt-task-row">'+
      '<div class="gantt-task-label"><div class="gantt-task-info"><a href="'+esc(CFG.jiraBaseUrl+'/browse/'+r.key)+'" target="_blank" rel="noopener noreferrer" data-issue-key="'+esc(r.key)+'">'+esc(r.key)+'</a>'+
      (r.milestone&&!d.isOverview?'<span class="gantt-milestone-tag">'+(d.isMilestone?'MILESTONE':'SELECTED')+'</span>':'')+
      '<span class="gantt-task-summary" title="'+esc(r.summary)+'">'+esc(r.summary)+'</span>'+
      '<span class="gantt-task-dates">'+esc(ganttDateLabel(ganttDate(r.start)))+' – '+esc(ganttDateLabel(ganttDate(r.end)))+' · '+esc(r.source)+'</span></div>'+ganttAssigneeHtml(r)+'</div>'+
      '<div class="gantt-task-track" style="width:'+timelineWidth+'px">'+bar+'</div></div>';
  }).join('');
  chart.innerHTML='<div class="gantt-canvas'+(state.ganttNarrow===true?' gantt-narrow':'')+'" data-origin="'+origin+'" data-days="'+days+'" data-label-width="'+labelWidth+'" data-today-left="'+todayLeft+'" style="width:'+totalWidth+'px;--gantt-left:'+labelWidth+'px">'+
    '<div class="gantt-timeline-heading" style="height:'+headHeight+'px">'+
      '<div class="gantt-heading-label">'+(d.isOverview?'MILESTONE / PROJECT PLAN':'ISSUE / TASK')+' <small>'+'Start · Due · Calculation'+'</small></div>'+
      '<div class="gantt-heading-scale" style="width:'+timelineWidth+'px">'+monthHead.join('')+dayHead.join('')+'<div class="gantt-hover-guide" hidden></div><div class="gantt-hover-date" hidden></div></div></div>'+
    '<div class="gantt-task-area" style="width:'+totalWidth+'px">'+
      '<div class="gantt-calendar-overlay" style="left:'+labelWidth+'px;width:'+timelineWidth+'px">'+weeks.join('')+'</div>'+
      '<div class="gantt-hover-guide" hidden></div>'+
      '<svg class="gantt-links-svg" style="left:'+labelWidth+'px" width="'+timelineWidth+'" aria-hidden="true"><defs><marker id="gantt-arrow" markerWidth="5" markerHeight="5" refX="4" refY="2.5" orient="auto"><path d="M0 0 L5 2.5 L0 5 Z" fill="#475569"/></marker></defs></svg>'+
      rowMarkup+todayMarkup+'</div></div>';

  // Label text is allowed to wrap to any number of lines. Measure the actual
  // rendered row heights before positioning dependency arrows, so neither the
  // summary nor the connector positions are truncated by a fixed row height.
  const rowElements=[...chart.querySelectorAll('.gantt-task-row')];
  const scheduledKeys=new Map(rows.map((r,n)=>[r.key,{r,n}]));
  const svg=chart.querySelector('.gantt-links-svg');
  const area=chart.querySelector('.gantt-task-area');
  const actualHeight=area.offsetHeight;
  svg.setAttribute('height',String(actualHeight));
  svg.setAttribute('viewBox','0 0 '+timelineWidth+' '+actualHeight);
  let arrows='';
  if(drawDependencies){
    // Read the *rendered* endpoints. A milestone displayed as a diamond
    // occupies its due date, so incoming links must enter its left tip,
    // not the earlier start date of the underlying schedule. Measuring the
    // actual shape also handles the diamond's CSS rotation and every zoom.
    const endpoints=rowElements.map(row=>{
      const shape=row.querySelector('.gantt-diamond, .gantt-bar');
      const track=row.querySelector('.gantt-task-track');
      if(!shape||!track)return null;
      const rect=shape.getBoundingClientRect();
      const trackLeft=track.getBoundingClientRect().left;
      return {start:rect.left-trackLeft,end:rect.right-trackLeft};
    });
    d.edges.forEach(link=>{
      const a=scheduledKeys.get(link.from),b=scheduledKeys.get(link.to);
      if(!a||!b||!endpoints[a.n]||!endpoints[b.n])return;
      // End of the visible blocker bar/diamond -> start of the visible
      // blocked bar/diamond, including backwards (right-to-left) links.
      const x1=endpoints[a.n].end;
      const x2=endpoints[b.n].start;
      const y1=rowElements[a.n].offsetTop+rowElements[a.n].offsetHeight/2;
      const y2=rowElements[b.n].offsetTop+rowElements[b.n].offsetHeight/2;
      const forward=x2>x1+24;
      const route=forward
        ?'M'+x1+' '+y1+' H'+((x1+x2)/2)+' V'+y2+' H'+x2
        // A two-elbow detour ensures the arrow still enters the *left*
        // edge of its target, even when that edge is behind the blocker.
        :'M'+x1+' '+y1+' H'+(x1+12)+' V'+((y1+y2)/2)+' H'+Math.max(1,x2-12)+' V'+y2+' H'+x2;
      arrows+='<path d="'+route+'" fill="none" stroke="#475569" stroke-width="1.5" stroke-linejoin="round" marker-end="url(#gantt-arrow)" opacity=".75"/>';
    });
  }
  svg.insertAdjacentHTML('beforeend',arrows);
  attachTicketKeyModalHandlers(chart);

  const missing=document.getElementById('gantt-unscheduled');
  const missingRows=d.unscheduled.map(r=>'<div class="gantt-unscheduled-item">'+
    '<a href="'+esc(CFG.jiraBaseUrl+'/browse/'+r.key)+'" target="_blank" rel="noopener noreferrer" data-issue-key="'+esc(r.key)+'">'+esc(r.key)+'</a>'+
    '<span title="'+esc(r.summary)+'">'+esc(r.summary)+'</span>'+
    '<strong>'+esc(r.reason||'No valid schedule')+'</strong></div>').join('');
  missing.innerHTML='<div class="gantt-unscheduled-heading">Unscheduled ('+d.unscheduled.length+')</div>'+
    (missingRows||'<div class="gantt-unscheduled-empty">'+(d.isOverview?'All milestones have valid start and due dates.':'All tickets have a valid start and due date.')+'</div>')+
    '<p class="gantt-schedule-notes">'+(d.isOverview?'Milestone bars show start through due date. Start: Jira start date → first blocker after the preceding milestone (blockers use Jira start, previous blocker due + 1 day, or creation) → milestone creation date. Blocker tasks are not displayed.':'Start: Jira start date → day after latest direct blocker due date → Jira creation date. Tickets without a due date or with start after due date appear here.')+'</p>';
  attachTicketKeyModalHandlers(missing);
}
function scrollGanttToToday(){
  const chart=document.getElementById('gantt-chart');
  const canvas=chart?.querySelector('.gantt-canvas');
  if(!canvas)return;
  const labelWidth=Number(canvas.dataset.labelWidth);
  const todayLeft=Number(canvas.dataset.todayLeft);
  if(!Number.isFinite(todayLeft)||!Number.isFinite(labelWidth))return;
  // Reserve a visible gap immediately after the sticky task-label column.
  const calendarViewport=Math.max(120,chart.clientWidth-labelWidth);
  const gap=Math.min(190,Math.max(60,Math.floor(calendarViewport*.23)));
  chart.scrollLeft=Math.max(0,todayLeft-gap);
  chart.scrollTop=0;
}
function closeMilestoneGantt(){
  const overlay=document.getElementById('gantt-overlay');
  if(!overlay||overlay.hidden)return;
  if(document.getElementById('ticket-preview-modal'))closeTicketPreviewModal();
  overlay.hidden=true;
  document.body.classList.remove('gantt-open');
  ganttCurrent=null;
  // Refresh the selected chain's connections if its layout changed while
  // the full-screen Gantt was open; no hidden redraws run under the overlay.
  scheduleDependencyLines();
  if(ganttReturnFocus?.isConnected)ganttReturnFocus.focus({preventScroll:true});
  ganttReturnFocus=null;
}
function openMilestoneGantt(key,button){
  openGanttData(buildMilestoneGantt(key),button);
}
function openAllMilestonesGantt(button){
  openGanttData(buildAllMilestonesGantt(),button);
}
function openGanttData(data,button){
  if(!data)return;
  ganttCurrent=data;
  ganttReturnFocus=button||document.activeElement;
  const overlay=document.getElementById('gantt-overlay');
  const kind=data.isOverview?'Project plan · milestones only':data.isMilestone?'Milestone timeline':'Selected chain timeline';
  overlay.querySelector('.gantt-eyebrow').textContent=kind;
  document.getElementById('gantt-title').textContent=data.isOverview?'All milestones · project plan':data.milestone.key+' · '+data.milestone.summary;
  document.getElementById('gantt-export-status').textContent='';
  overlay.hidden=false;
  document.body.classList.add('gantt-open');
  updateGanttControls();
  renderGanttChart();
  scrollGanttToToday();
  document.getElementById('gantt-close').focus();
}
function refreshOpenGanttAfterJiraLoad(){
  if(!ganttCurrent||document.getElementById('gantt-overlay').hidden)return;
  const previousKey=ganttCurrent.milestone.key;
  const updated=ganttCurrent.isOverview?buildAllMilestonesGantt():buildMilestoneGantt(previousKey);
  if(!updated)return;
  const viewport=document.getElementById('gantt-chart');
  const left=viewport.scrollLeft,top=viewport.scrollTop;
  ganttCurrent=updated;
  document.getElementById('gantt-title').textContent=updated.isOverview?'All milestones · project plan':updated.milestone.key+' · '+updated.milestone.summary;
  updateGanttControls();
  renderGanttChart();
  viewport.scrollLeft=left;viewport.scrollTop=top;
  document.getElementById('gantt-export-status').textContent='Refreshed from Jira.';
}
async function exportMilestoneGanttPdf(){
  if(!ganttCurrent)return;
  const btn=document.getElementById('gantt-export');
  const status=document.getElementById('gantt-export-status');
  btn.disabled=true;status.textContent='Generating complete PDF…';
  try{
    const response=await fetch('/api/gantt-pdf',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({milestone:ganttCurrent.milestone,rows:ganttCurrent.rows,edges:state.ganttShowDependencies!==false?ganttCurrent.edges:[],scale:state.ganttScale,narrow:state.ganttNarrow===true})});
    if(!response.ok){
      const err=await response.json().catch(()=>({}));
      throw new Error(err.error||'PDF generation failed ('+response.status+')');
    }
    const pdf=await response.blob(),url=URL.createObjectURL(pdf);
    const link=document.createElement('a');
    link.href=url;link.download=ganttCurrent.isOverview?'all_milestones_gantt.pdf':ganttCurrent.milestone.key+'_gantt.pdf';
    document.body.appendChild(link);link.click();link.remove();
    setTimeout(()=>URL.revokeObjectURL(url),30000);
    status.textContent='PDF download started.';
  }catch(err){status.textContent='PDF error: '+err.message;}
  finally{btn.disabled=false;}
}
function hideGanttHoverGuide(){
  const chart=document.getElementById('gantt-chart');
  if(!chart)return;
  chart.querySelectorAll('.gantt-hover-guide,.gantt-hover-date').forEach(el=>{el.hidden=true;});
}
function updateGanttHoverGuide(e){
  const chart=document.getElementById('gantt-chart');
  const canvas=chart?.querySelector('.gantt-canvas');
  if(!canvas||!ganttCurrent)return;
  // The issue column is sticky, so exclude its visible area even when
  // horizontal scrolling has moved the underlying timeline beneath it.
  const viewportX=e.clientX-chart.getBoundingClientRect().left;
  const labelWidth=Number(canvas.dataset.labelWidth);
  if(viewportX<labelWidth){hideGanttHoverGuide();return;}
  // Scrolling affects the pointer's date but not the content coordinates.
  const x=viewportX+chart.scrollLeft;
  const days=Number(canvas.dataset.days);
  const day=Math.floor((x-labelWidth)/ganttDayWidth);
  if(day<0||day>=days){hideGanttHoverGuide();return;}
  const guideX=(day+.5)*ganttDayWidth;
  const headingGuide=canvas.querySelector('.gantt-heading-scale .gantt-hover-guide');
  const areaGuide=canvas.querySelector('.gantt-task-area .gantt-hover-guide');
  const dateLabel=canvas.querySelector('.gantt-hover-date');
  if(!headingGuide||!areaGuide||!dateLabel)return;
  headingGuide.style.left=guideX+'px';headingGuide.hidden=false;
  areaGuide.style.left=(labelWidth+guideX)+'px';areaGuide.hidden=false;
  dateLabel.style.left=guideX+'px';
  dateLabel.textContent=ganttDateLabel(Number(canvas.dataset.origin)+day*GANTT_DAY_MS);
  dateLabel.hidden=false;
}
function initMilestoneGantt(){
  document.getElementById('gantt-close').addEventListener('click',closeMilestoneGantt);
  document.getElementById('gantt-export').addEventListener('click',exportMilestoneGanttPdf);
  const ganttViewport=document.getElementById('gantt-chart');
  ganttViewport.addEventListener('pointermove',updateGanttHoverGuide);
  ganttViewport.addEventListener('pointerleave',hideGanttHoverGuide);
  ganttViewport.addEventListener('scroll',hideGanttHoverGuide,{passive:true});
  document.getElementById('gantt-overlay').addEventListener('click',e=>{if(e.target.id==='gantt-overlay')closeMilestoneGantt();});
  document.querySelectorAll('[data-gantt-scale]').forEach(btn=>btn.addEventListener('click',()=>{
    state.ganttScale=Number(btn.dataset.ganttScale)||12;
    savePreferences({ganttScale:state.ganttScale});
    updateGanttControls();renderGanttChart();
    scrollGanttToToday();
  }));
  document.getElementById('gantt-narrow').addEventListener('change',e=>{
    state.ganttNarrow=e.target.checked;
    savePreferences({ganttNarrow:state.ganttNarrow});
    updateGanttControls();renderGanttChart();
    scrollGanttToToday();
  });
  document.getElementById('gantt-show-dependencies').addEventListener('change',e=>{
    state.ganttShowDependencies=e.target.checked;
    savePreferences({ganttShowDependencies:state.ganttShowDependencies});
    const viewport=document.getElementById('gantt-chart');
    const left=viewport.scrollLeft,top=viewport.scrollTop;
    updateGanttControls();renderGanttChart();
    viewport.scrollLeft=left;viewport.scrollTop=top;
  });
  document.addEventListener('keydown',e=>{
    if(document.getElementById('gantt-overlay').hidden)return;
    // A Jira preview is a nested dialog; Escape closes that first, not the Gantt.
    if(document.getElementById('ticket-preview-modal'))return;
    if(e.key==='Escape'){e.preventDefault();e.stopImmediatePropagation();closeMilestoneGantt();}
    if(e.key==='Tab'){
      const focusables=[...document.getElementById('gantt-overlay').querySelectorAll('button:not([disabled]),a[href]')].filter(el=>el.getClientRects().length);
      if(!focusables.length)return;
      const first=focusables[0],last=focusables[focusables.length-1];
      if(e.shiftKey&&document.activeElement===first){e.preventDefault();last.focus();}
      else if(!e.shiftKey&&document.activeElement===last){e.preventDefault();first.focus();}
    }
  },true);
}
initMilestoneGantt();

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
