"""Run every machine check of this repository and report the results.

Usage: python verification/run_all.py
Exits with status 0 only if every check passes. Each check prints its own details.
"""
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
CHECKS = sorted(p.name for p in HERE.glob("check_*.py"))


def main():
    failed = []
    for name in CHECKS:
        print(f"== {name}", flush=True)
        result = subprocess.run([sys.executable, name], cwd=HERE, timeout=7200)
        if result.returncode != 0:
            failed.append(name)
    print()
    for name in CHECKS:
        print(("FAIL  " if name in failed else "pass  ") + name)
    if failed:
        sys.exit(1)
    print(f"All {len(CHECKS)} checks passed.")


if __name__ == "__main__":
    main()
