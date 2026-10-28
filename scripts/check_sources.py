"""Validate the tracked source inventory and pinned dependency configuration."""

import json
from pathlib import Path
import re
import subprocess
import tomllib
from urllib.parse import urlparse


TOP_LEVEL = {
    "BianchiIX.lean", "Audit.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json",
    "README.md", "LICENSE", ".gitignore", ".gitattributes", ".github/workflows/verify.yml",
    "scripts/check_sources.py", "scripts/fetch_mathlib_cache.py",
}


def lean_code(text):
    """Remove nested Lean comments while retaining strings and token boundaries."""
    output = []
    i = 0
    while i < len(text):
        if text.startswith("/-", i):
            depth = 1
            i += 2
            while depth and i < len(text):
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("Unterminated block comment")
            output.append(" ")
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            output.append(" ")
        elif text[i] == '"':
            start = i
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            output.append(text[start:i])
        else:
            output.append(text[i])
            i += 1
    return "".join(output)


def main():
    root = Path(__file__).resolve().parents[1]
    tracked = subprocess.check_output(["git", "ls-files", "-z"], cwd=root).decode().split("\0")
    tracked = [p for p in tracked if p]
    errors = []
    modules = set()
    sources = {}
    sensitive = re.compile(
        r"\b[A-Za-z]:[\\/]|/(?:Users|home|root)/[\w.-]+|"
        r"gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|"
        r"AKIA[A-Z0-9]{16}|-----BEGIN [A-Z ]*PRIVATE KEY-----"
    )
    for name in tracked:
        path = root / name
        if path.is_symlink():
            errors.append(f"Tracked symbolic link: {name}")
        if name not in TOP_LEVEL and not (name.startswith("BianchiIX/") and name.endswith(".lean")):
            errors.append(f"Unexpected tracked file: {name}")
        text = path.read_text(encoding="utf-8")
        if sensitive.search(text):
            errors.append(f"Possible machine path or credential in {name}")
        if name.endswith(".lean"):
            code = lean_code(text)
            sources[name] = code
            if name != "Audit.lean" and re.search(r"\b(?:sorry|admit|axiom)\b", code):
                errors.append(f"Proof placeholder or axiom declaration in {name}")
            if name.startswith("BianchiIX/"):
                modules.add(name[:-5].replace("/", "."))
    if not modules:
        errors.append("No proof modules are tracked")
    imported = set(re.findall(r"^import\s+(BianchiIX\.[\w.]+)\s*$",
                              sources.get("BianchiIX.lean", ""), re.M))
    if imported != modules:
        errors.append(f"Root import inventory differs: {sorted(imported ^ modules)}")
    for name, code in sources.items():
        for dependency in re.findall(r"^import\s+(BianchiIX\.[\w.]+)\s*$", code, re.M):
            if dependency not in modules:
                errors.append(f"Missing project import {dependency} in {name}")
    config = tomllib.loads((root / "lakefile.toml").read_text(encoding="utf-8"))
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = {p["name"]: p for p in manifest["packages"]}
    for package in packages.values():
        url = urlparse(package.get("url", ""))
        if (package.get("type") != "git" or url.scheme != "https" or url.netloc != "github.com"
                or not re.fullmatch(r"[0-9a-f]{40}", package.get("rev", ""))):
            errors.append(f"Nonportable or unpinned dependency: {package['name']}")
    for requirement in config.get("require", []):
        locked = packages.get(requirement["name"], {})
        if requirement.get("rev") != locked.get("rev") or requirement.get("git") != locked.get("url"):
            errors.append(f"Dependency lock mismatch: {requirement['name']}")
    missing = TOP_LEVEL - set(tracked)
    if missing:
        errors.append(f"Missing distribution files: {sorted(missing)}")
    if errors:
        raise SystemExit("\n".join(errors))
    print(f"Source checks passed: {len(modules)} proof modules, {len(tracked)} tracked files, "
          f"{len(packages)} pinned dependencies.")


if __name__ == "__main__":
    main()
