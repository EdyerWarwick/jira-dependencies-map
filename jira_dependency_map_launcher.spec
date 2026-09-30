# -*- mode: python ; coding: utf-8 -*-

from pathlib import Path

project_dir = Path(SPECPATH)
icon_file = project_dir / "assets" / "jira-dependency-map.ico"

if not icon_file.is_file():
    raise FileNotFoundError(f"Launcher icon not found: {icon_file}")


a = Analysis(
    [str(project_dir / "jira_dependency_map_launcher.py")],
    pathex=[str(project_dir)],
    binaries=[],
    datas=[],
    hiddenimports=[],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
)

pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.datas,
    [],
    name="Jira-Dependency-Map",
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=False,
    console=False,
    icon=str(icon_file),
)
