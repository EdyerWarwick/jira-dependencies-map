# Jira Dependency Map — reliable side-by-side Windows updates

This version uses a stable launcher and installs each application release into
its own local version directory. The running EXE is never overwritten.

## Release layout

Each GitHub Release contains:

- `Jira-Dependency-Map.exe` — the small stable launcher
- `Jira-Dependency-Map-win64.zip` — the PyInstaller `--onedir` application
- `Jira-Dependency-Map-win64.zip.sha256` — mandatory SHA-256 checksum

The launcher installs releases under:

```text
%LOCALAPPDATA%\JiraDependencyMap\
    Jira-Dependency-Map.exe
    current.json
    launcher.log
    versions\
        1.0.0\
            Jira-Dependency-Map.exe
            _internal\...
        1.0.1\
            Jira-Dependency-Map.exe
            _internal\...
```

## Update behaviour

On each launch, the launcher:

1. Finds the highest stable GitHub Release.
2. Downloads the application ZIP to a `.part` file.
3. Checks the GitHub asset size and mandatory SHA-256 checksum.
4. Safely extracts it into a staging directory.
5. Atomically moves the staging directory to `versions\<version>`.
6. Starts the new version and verifies `/api/update-health`, including its
   version and process ID.
7. Writes `current.json` only after the health check succeeds.
8. Keeps the current and previous version for rollback.

If downloading, extraction, startup, or health checking fails, the launcher
records the error in `launcher.log` and starts the previously selected version.

## Compatibility with the old updater

The launcher release asset keeps the name `Jira-Dependency-Map.exe`. An older
installation can therefore download it using the previous updater. When the old
updater starts that file, the launcher installs and starts the matching
versioned application; the application's health endpoint then lets the old
updater complete successfully.

## Configuration

The repository defaults to:

```text
EdyerWarwick/jira-dependencies-map
```

Override it at runtime with `JIRA_DEP_MAP_GITHUB_REPO` if required.

## Creating a release

Commit these files, then create and push a semantic version tag:

```powershell
git tag v1.0.1
git push origin v1.0.1
```

GitHub Actions builds both executables, creates the ZIP and checksum, and
uploads all three release assets.

For a manual `workflow_dispatch` build, files are available as a workflow
artifact but are not attached to a GitHub Release.

## Local development

```powershell
python -m pip install -r requirements.txt
python jira_dependency_map_v33.py
```

The application starts at `http://localhost:5001`. The launcher only manages
frozen release builds.
