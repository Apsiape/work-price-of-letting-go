"""Build the manuscript from scratch with pdflatex and BibTeX, and refuse to finish on any unresolved warning.

Usage: python paper/build.py   (run from the repository root or from paper/)

The build directory is deleted first, so every build starts from nothing. The PDF date and trailer
identifier are fixed, so two builds with the same TeX installation produce byte-identical files.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
OUT = HERE / "build"
if OUT.exists():
    shutil.rmtree(OUT)
OUT.mkdir()
ENV = {**os.environ, "SOURCE_DATE_EPOCH": "1791504000", "FORCE_SOURCE_DATE": "1"}


def run(cmd, cwd=HERE, env=ENV):
    result = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, errors="replace", timeout=900)
    if result.returncode:
        print("\n".join(result.stdout.splitlines()[-45:]))
        raise SystemExit(f"Command failed: {' '.join(cmd)}")
    return result


latex = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "-output-directory=build", "main.tex"]
run(latex)
# BibTeX runs in build/, next to the .aux file, with paper/ on its search path for refs.bib.
run(["bibtex", "main"], cwd=OUT, env={**ENV, "BIBINPUTS": str(HERE) + os.pathsep})
blg = (OUT / "main.blg").read_text(errors="replace")
for _ in range(5):
    run(latex)
    log = (OUT / "main.log").read_text(errors="replace")
    if "Rerun to get" not in log:
        break
warnings = [line for line in log.splitlines() if any(s in line for s in (
    "undefined", "Overfull", "multiply defined", "Rerun to get", "Citation", "Float too large"
))]
warnings += [line for line in blg.splitlines() if line.startswith("Warning--") or "error message" in line]
if warnings:
    print("\n".join(warnings))
    raise SystemExit("Unresolved manuscript build warnings; inspect paper/build/main.log and paper/build/main.blg.")
pages = re.search(r"Output written on .*?\((\d+) pages", log.replace("\n", ""))
shutil.copy2(OUT / "main.pdf", HERE / "main.pdf")
print(f"Built paper/main.pdf ({pages.group(1) if pages else '?'} pages); no undefined references or citations, "
      "duplicate labels, overfull boxes, floats too large for the page or BibTeX warnings.")
