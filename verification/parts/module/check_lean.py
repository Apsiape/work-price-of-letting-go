"""Compile the Lean 4 proofs in verification/lean against Mathlib and audit their axioms.

Mathlib is found, in order, at:
  1. the directory in the environment variable MATHLIB_DIR (a Mathlib v4.30.0 checkout with its cache);
  2. verification/lean/.lake/packages/mathlib (after `lake exe cache get` in verification/lean);
  3. a sibling checkout ../../lean-mathlib-v4.30.0 of this repository.
Each file must compile with no error and no warning, every theorem and lemma must have a `#print axioms` line, and every
one may depend only on the axioms propext, Classical.choice and Quot.sound (in particular, no sorryAx).
If no Mathlib is found the check reports SKIPPED and fails, so a passing run always includes the proofs.
"""
from pathlib import Path
import os
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
LEAN = HERE / "lean"
FILES = sorted(p for p in LEAN.glob("*.lean") if p.name != "lakefile.lean")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def mathlib_root():
    candidates = []
    if os.environ.get("MATHLIB_DIR"):
        candidates.append(Path(os.environ["MATHLIB_DIR"]))
    candidates.append(LEAN / ".lake" / "packages" / "mathlib")
    candidates.append(HERE.parent.parent / "lean-mathlib-v4.30.0")
    for c in candidates:
        if (c / "lakefile.lean").exists() and (c / ".lake" / "build" / "lib").exists():
            return c
    return None


def main():
    root = mathlib_root()
    if root is None:
        print("SKIPPED: no Mathlib v4.30.0 with a built cache was found; see verification/README.md.")
        sys.exit(1)
    failed = []
    total = 0
    for f in FILES:
        run = subprocess.run(["lake", "env", "lean", str(f)], cwd=root, capture_output=True, text=True,
                             errors="replace", timeout=3600)
        out = run.stdout + run.stderr
        problems = [l for l in out.splitlines() if re.search(r"\b(error|warning)\b", l)]
        axioms = re.findall(r"'([\w.']+)' depends on axioms: \[([^\]]*)\]", out)
        free = re.findall(r"'([\w.']+)' does not depend on any axioms", out)
        text = f.read_text(encoding="utf-8")
        declared = re.findall(r"^(?:theorem|lemma) ([\w']+)", text, re.M)
        printed = {name.split(".")[-1] for name, _ in axioms} | {name.split(".")[-1] for name in free}
        bad = [a for _, line in axioms for a in (x.strip() for x in line.split(",")) if a and a not in ALLOWED]
        missing = [d for d in declared if d not in printed]
        ok = run.returncode == 0 and not problems and not bad and not missing
        total += len(declared)
        print(("  ok    " if ok else "  FAIL  ") + f"{f.name}: {len(declared)} theorems, axioms within "
              f"{{propext, Classical.choice, Quot.sound}}" + ("" if ok else f"  {problems[:3]} {bad[:3]} {missing[:3]}"))
        if not ok:
            failed.append(f.name)
    if failed:
        sys.exit(1)
    print(f"All {len(FILES)} Lean files ({total} theorems) compiled against Mathlib at {root}.")


if __name__ == "__main__":
    main()
