#!/usr/bin/env python3
"""Stable launcher and side-by-side updater for Jira Dependency Map."""
import ctypes
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
import zipfile
from pathlib import Path

import requests

GITHUB_REPO = os.environ.get(
    "JIRA_DEP_MAP_GITHUB_REPO", "EdyerWarwick/jira-dependencies-map"
)
APP_ASSET = "Jira-Dependency-Map-win64.zip"
CHECKSUM_ASSET = APP_ASSET + ".sha256"
APP_EXE = "Jira-Dependency-Map.exe"
PORT = 5001

LOCAL_APP_DIR = Path(
    os.environ.get("LOCALAPPDATA", str(Path.home()))
) / "JiraDependencyMap"
VERSIONS_DIR = LOCAL_APP_DIR / "versions"
CURRENT_FILE = LOCAL_APP_DIR / "current.json"
DOWNLOADS_DIR = LOCAL_APP_DIR / "downloads"
LOG_FILE = LOCAL_APP_DIR / "launcher.log"
VERSION_RE = re.compile(r"^v?(\d+)\.(\d+)\.(\d+)$", re.IGNORECASE)


def log(message):
    try:
        LOCAL_APP_DIR.mkdir(parents=True, exist_ok=True)
        with LOG_FILE.open("a", encoding="utf-8") as handle:
            handle.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')} {message}\n")
    except OSError:
        pass


def version_tuple(value):
    match = VERSION_RE.fullmatch(str(value or "").strip())
    return tuple(map(int, match.groups())) if match else None


def version_text(value):
    parsed = version_tuple(value)
    return ".".join(map(str, parsed)) if parsed else None


def acquire_single_instance():
    if os.name != "nt":
        return None
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    handle = kernel32.CreateMutexW(None, False, "Local\\JiraDependencyMapLauncher")
    if not handle:
        raise ctypes.WinError(ctypes.get_last_error())
    if ctypes.get_last_error() == 183:  # ERROR_ALREADY_EXISTS
        kernel32.CloseHandle(handle)
        return False
    return handle


def latest_stable_release():
    response = requests.get(
        f"https://api.github.com/repos/{GITHUB_REPO}/releases",
        params={"per_page": 100, "t": int(time.time())},
        headers={
            "Accept": "application/vnd.github+json",
            "Cache-Control": "no-cache",
            "X-GitHub-Api-Version": "2022-11-28",
        },
        timeout=15,
    )
    response.raise_for_status()
    candidates = []
    for release in response.json():
        if release.get("draft") or release.get("prerelease"):
            continue
        parsed = version_tuple(release.get("tag_name"))
        if parsed:
            candidates.append((parsed, release))
    return max(candidates, default=(None, None), key=lambda item: item[0])[1]


def release_asset(release, name):
    return next(
        (asset for asset in release.get("assets", []) if asset.get("name") == name),
        None,
    )


def download_bytes(asset, timeout=60):
    response = requests.get(
        asset["browser_download_url"],
        headers={"Accept": "application/octet-stream", "Cache-Control": "no-cache"},
        timeout=timeout,
    )
    response.raise_for_status()
    return response.content


def expected_checksum(release, zip_asset):
    checksum_asset = release_asset(release, CHECKSUM_ASSET)
    if not checksum_asset:
        raise RuntimeError(f"Release is missing {CHECKSUM_ASSET}.")
    text = download_bytes(checksum_asset).decode("ascii", errors="strict")
    match = re.search(r"\b([0-9a-fA-F]{64})\b", text)
    if not match:
        raise RuntimeError("The release checksum file is invalid.")
    expected = match.group(1).lower()

    github_digest = str(zip_asset.get("digest") or "")
    if github_digest.lower().startswith("sha256:"):
        api_digest = github_digest.split(":", 1)[1].strip().lower()
        if api_digest != expected:
            raise RuntimeError("GitHub's digest does not match the checksum asset.")
    return expected


def download_zip(asset, destination, expected_sha256):
    destination.parent.mkdir(parents=True, exist_ok=True)
    part = destination.with_suffix(destination.suffix + ".part")
    digest = hashlib.sha256()
    size = 0
    try:
        with requests.get(
            asset["browser_download_url"],
            headers={"Accept": "application/octet-stream", "Cache-Control": "no-cache"},
            stream=True,
            timeout=(15, 180),
        ) as response:
            response.raise_for_status()
            with part.open("wb") as handle:
                for chunk in response.iter_content(1024 * 1024):
                    if not chunk:
                        continue
                    handle.write(chunk)
                    digest.update(chunk)
                    size += len(chunk)
                handle.flush()
                os.fsync(handle.fileno())

        advertised_size = int(asset.get("size") or 0)
        if advertised_size and size != advertised_size:
            raise RuntimeError(
                f"Download size was {size} bytes; expected {advertised_size}."
            )
        if digest.hexdigest().lower() != expected_sha256:
            raise RuntimeError("The downloaded ZIP failed its SHA-256 check.")
        os.replace(part, destination)
    except Exception:
        try:
            part.unlink()
        except OSError:
            pass
        raise


def safe_extract(zip_path, destination):
    destination_root = destination.resolve()
    with zipfile.ZipFile(zip_path) as archive:
        for info in archive.infolist():
            target = (destination / info.filename).resolve()
            if os.path.commonpath([str(destination_root), str(target)]) != str(
                destination_root
            ):
                raise RuntimeError("The release ZIP contains an unsafe path.")
        archive.extractall(destination)


def installed_exe(version):
    return VERSIONS_DIR / version / APP_EXE


def read_current_version():
    try:
        data = json.loads(CURRENT_FILE.read_text(encoding="utf-8"))
        version = version_text(data.get("version"))
        if version and installed_exe(version).is_file():
            return version
    except (OSError, ValueError, TypeError):
        pass
    return discover_latest_installed()


def discover_latest_installed():
    candidates = []
    try:
        for child in VERSIONS_DIR.iterdir():
            parsed = version_tuple(child.name)
            if parsed and installed_exe(child.name).is_file():
                candidates.append((parsed, child.name))
    except OSError:
        pass
    return max(candidates, default=(None, None), key=lambda item: item[0])[1]


def write_current(version):
    LOCAL_APP_DIR.mkdir(parents=True, exist_ok=True)
    temporary = CURRENT_FILE.with_suffix(".json.tmp")
    temporary.write_text(
        json.dumps({"version": version}, indent=2) + "\n", encoding="utf-8"
    )
    os.replace(temporary, CURRENT_FILE)


def launch_app(version, restart=False):
    executable = installed_exe(version)
    if not executable.is_file():
        raise RuntimeError(f"Installed application {version} is missing.")
    env = os.environ.copy()
    env["JIRA_DEP_MAP_MANAGED_VERSION"] = version
    if restart:
        env["JIRA_DEP_MAP_RESTART"] = "1"
    return subprocess.Popen(
        [str(executable)],
        cwd=str(executable.parent),
        env=env,
        close_fds=True,
        creationflags=getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0),
    )


def wait_for_health(process, expected_version, timeout=90):
    deadline = time.monotonic() + timeout
    url = f"http://127.0.0.1:{PORT}/api/update-health"
    while time.monotonic() < deadline:
        if process.poll() is not None:
            return False
        try:
            response = requests.get(
                url,
                params={"ts": time.time_ns()},
                headers={"Cache-Control": "no-cache"},
                timeout=2,
            )
            data = response.json()
            if (
                response.ok
                and data.get("ok") is True
                and version_text(data.get("version")) == expected_version
                and int(data.get("pid") or 0) == process.pid
            ):
                return True
        except (requests.RequestException, ValueError, TypeError):
            pass
        time.sleep(0.5)
    return False


def install_release(release, version):
    zip_asset = release_asset(release, APP_ASSET)
    if not zip_asset or not zip_asset.get("browser_download_url"):
        raise RuntimeError(f"Release v{version} is missing {APP_ASSET}.")

    expected = expected_checksum(release, zip_asset)
    archive = DOWNLOADS_DIR / f"{version}.zip"
    download_zip(zip_asset, archive, expected)

    final_dir = VERSIONS_DIR / version
    staging_dir = VERSIONS_DIR / f".{version}-staging-{os.getpid()}"
    shutil.rmtree(staging_dir, ignore_errors=True)
    staging_dir.mkdir(parents=True, exist_ok=False)
    try:
        safe_extract(archive, staging_dir)
        executable = staging_dir / APP_EXE
        if not executable.is_file() or executable.stat().st_size < 1024:
            raise RuntimeError(f"The release ZIP does not contain {APP_EXE}.")
        if final_dir.exists():
            shutil.rmtree(final_dir)
        os.replace(staging_dir, final_dir)
    except Exception:
        shutil.rmtree(staging_dir, ignore_errors=True)
        raise
    finally:
        try:
            archive.unlink()
        except OSError:
            pass
def cleanup_versions(current_version):
   """Remove every installed application version except the active one."""
    current_dir = VERSIONS_DIR / current_version
    if not installed_exe(current_version).is_file():
        return
        
    try:
        for child in VERSIONS_DIR.iterdir():
            
           if child == current_dir or not child.is_dir():
                continue
            # Remove old semantic-version directories and abandoned staging
            # directories, but leave unrelated folders untouched.
            if version_tuple(child.name) or child.name.startswith("."):
                shutil.rmtree(child, ignore_errors=True)
            
    except OSError:
        pass

    candidates.sort(reverse=True)
    keep = {VERSIONS_DIR / current_version}
    if previous_version and previous_version != current_version:
        keep.add(VERSIONS_DIR / previous_version)
    else:
        for _, path in candidates:
            if path not in keep:
                keep.add(path)
                break

    for _, path in candidates:
        if path not in keep:
            shutil.rmtree(path, ignore_errors=True)


def run():
    mutex = acquire_single_instance()
    if mutex is False:
        return 0

    LOCAL_APP_DIR.mkdir(parents=True, exist_ok=True)
    VERSIONS_DIR.mkdir(parents=True, exist_ok=True)
    current = read_current_version()

    try:
        release = latest_stable_release()
        latest = version_text(release.get("tag_name")) if release else None
    except Exception as exc:
        log(f"Release check failed: {exc}")
        release = None
        latest = None

    if latest and (not current or version_tuple(latest) > version_tuple(current)):
        try:
            if not installed_exe(latest).is_file():
                install_release(release, latest)
            process = launch_app(latest)
            if wait_for_health(process, latest):
                write_current(latest)
                cleanup_versions(latest)
                log(f"Activated version {latest}.")
                return 0
            try:
                process.terminate()
                process.wait(timeout=5)
            except (OSError, subprocess.TimeoutExpired):
                try:
                    process.kill()
                except OSError:
                    pass
            shutil.rmtree(VERSIONS_DIR / latest, ignore_errors=True)
            raise RuntimeError("The new version did not pass its startup health check.")
        except Exception as exc:
            if latest != current:
                shutil.rmtree(VERSIONS_DIR / latest, ignore_errors=True)
            log(f"Update to {latest} failed: {exc}")

    if current:
        try:
            # Also remove versions retained by earlier launcher releases.
            cleanup_versions(current)
            launch_app(current)
            return 0
        except Exception as exc:
            log(f"Could not launch current version {current}: {exc}")

    message = (
        "Jira Dependency Map could not be installed or started.\n\n"
        f"See the launcher log:\n{LOG_FILE}"
    )
    if os.name == "nt":
        ctypes.windll.user32.MessageBoxW(None, message, "Jira Dependency Map", 0x10)
    return 1


if __name__ == "__main__":
    raise SystemExit(run())
