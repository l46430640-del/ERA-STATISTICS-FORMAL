"""Fetch the pinned upstream cache for the project's explicit mathlib imports."""

import os
from pathlib import Path
import re
import subprocess


def main():
    root = Path(__file__).resolve().parents[1]
    modules = set()
    for path in (root / "BianchiIX").rglob("*.lean"):
        modules.update(re.findall(r"^import\s+(Mathlib(?:\.[\w]+)*)\s*$",
                                  path.read_text(encoding="utf-8"), re.M))
    if not modules:
        raise SystemExit("No mathlib imports were found.")
    env = {**os.environ, "MATHLIB_NO_CACHE_ON_UPDATE": "1"}
    print(f"Fetching the upstream cache for {len(modules)} explicit imports and their dependencies.",
          flush=True)
    subprocess.run(["lake", "exe", "cache", "get", *sorted(modules)],
                   cwd=root, env=env, check=True)


if __name__ == "__main__":
    main()
