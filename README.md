# Jira Dependency Map — Windows EXE

This package is based on the supplied v33 application.

## What is included

- `jira_dependency_map_v33.py` — the application source
- `jira_dependency_map.spec` — PyInstaller build definition
- `.github/workflows/build-release.yml` — Windows GitHub Actions build/release
- `requirements.txt` — Python dependencies

## Security model

The Jira email/API key is stored in the current Windows user's Windows Credential Manager.

The credential is not embedded in the executable and is not sent to the browser. The Jira Basic Authentication value is generated in memory when a Jira request is made.

The executable update process downloads the latest GitHub Release executable and, when GitHub provides an asset SHA-256 digest, verifies the downloaded bytes before installing the update.

## One required configuration

Before building the first release, change this line in `jira_dependency_map_v33.py`:

    GITHUB_REPO="YOUR-ORG/YOUR-REPO"

to the actual GitHub repository, for example:

    GITHUB_REPO="your-org/jira-dependency-map"

The executable then checks that repository's latest GitHub Release when it starts.

## Creating the first release

1. Create a GitHub repository.
2. Add the files from this package.
3. Set `GITHUB_REPO` in `jira_dependency_map_v33.py`.
4. Commit and push.
5. Create and push a version tag, for example:

       git tag v1.0.0
       git push origin v1.0.0

6. GitHub Actions builds the Windows executable on a Windows runner.
7. The workflow attaches `Jira-Dependency-Map.exe` to the GitHub Release.

GitHub Actions artifacts can also be retained separately from releases, which is useful for testing builds before publishing a release.

## Updating the application

For a new release:

    git tag v1.0.1
    git push origin v1.0.1

A new Windows executable is built and attached to the release.

Existing users do not need to reinstall it. On their next launch, the application checks the latest release, downloads a newer executable when the version is newer, verifies the digest when available, exits the old process, replaces it, and starts the new executable.

Windows Credential Manager is independent of the executable, so saved Jira credentials remain available after an update.

## Local development

Install the dependencies:

    python -m pip install -r requirements.txt

Run:

    python jira_dependency_map_v33.py

The app starts on:

    http://localhost:5001

The source file deliberately remains usable as a normal Python application; the GitHub updater is only active when running from a frozen PyInstaller executable.
