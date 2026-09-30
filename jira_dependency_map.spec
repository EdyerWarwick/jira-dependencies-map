# -*- mode: python ; coding: utf-8 -*-

from pathlib import Path
from PyInstaller.utils.hooks import collect_submodules

project_dir = Path(SPECPATH)
tray_icon = project_dir / "assets" / "tray-icon.png"

if not tray_icon.is_file():
    raise FileNotFoundError(f"Tray icon not found: {tray_icon}")

a = Analysis(
    [str(project_dir / "jira_dependency_map_v33.py")],
    pathex=[str(project_dir)],
    binaries=[],
    datas=[(str(tray_icon), "assets")],
    hiddenimports=collect_submodules("pystray"),
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
    [],
    exclude_binaries=True,
    name="Jira-Dependency-Map",
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=False,
    console=False,
)

coll = COLLECT(
    exe,
    a.binaries,
    a.datas,
    strip=False,
    upx=False,
    name="Jira-Dependency-Map",
)
