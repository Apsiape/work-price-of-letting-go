"""Build the manuscript from scratch with pdflatex and BibTeX, and refuse to finish on any unresolved warning.

Usage: python paper/build.py   (run from the repository root or from paper/)

Generated TeX outputs in build/tex are cleared first, so every build starts from nothing. The PDF date and trailer
identifier are fixed, so two builds with the same TeX installation produce byte-identical files.
"""
from pathlib import Path
import os
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
OUT = HERE / "build" / "tex"
assert OUT.resolve() == (HERE.resolve() / "build" / "tex")
assert OUT.resolve().is_relative_to(HERE.resolve())
OUT.mkdir(parents=True, exist_ok=True)
for generated in OUT.iterdir():
    if generated.is_file() and generated.suffix in {".aux", ".bbl", ".blg", ".log", ".out", ".toc", ".pdf"}:
        generated.unlink()
ENV = {**os.environ, "SOURCE_DATE_EPOCH": "1793142000", "FORCE_SOURCE_DATE": "1"}
# Prefer the freshly generated bibliography over the checked-in release copy.
ENV["TEXINPUTS"] = str(OUT) + os.pathsep + os.environ.get("TEXINPUTS", "")
for name in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "BLIS_NUM_THREADS"):
    ENV[name] = "1"


def run(cmd, cwd=HERE, env=ENV):
    result = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, errors="replace", timeout=900)
    if result.returncode:
        print("\n".join(result.stdout.splitlines()[-45:]))
        raise SystemExit(f"Command failed: {' '.join(cmd)}")
    return result


latex = ["pdflatex", "-no-shell-escape", "-recorder", "-interaction=nonstopmode", "-halt-on-error", "-output-directory=build/tex", "main.tex"]
run(latex)
# BibTeX runs in build/, next to the .aux file, with paper/ on its search path for refs.bib.
run(["bibtex", "main"], cwd=OUT, env={**ENV, "BIBINPUTS": str(HERE) + os.pathsep})
blg = (OUT / "main.blg").read_text(errors="replace")
for _ in range(5):
    run(latex)
    log = (OUT / "main.log").read_text(errors="replace")
    if "Rerun to get" not in log and "There were undefined" not in log:
        break
warnings = [line for line in log.splitlines() if re.search(
    r"(?:LaTeX(?: Font)?|Package .+|Class .+) Warning:|undefined|Overfull|Underfull|multiply defined|Rerun to get|Citation|Float too large|ignored error|Missing character", line, re.I)]
warnings += [line for line in blg.splitlines() if line.startswith("Warning--") or "error message" in line]
if warnings:
    print("\n".join(warnings))
    raise SystemExit("Unresolved manuscript build warnings; inspect paper/build/main.log and paper/build/main.blg.")
pages = re.search(r"Output written on .*?\((\d+) pages", log.replace("\n", ""))
shutil.copy2(OUT / "main.pdf", HERE / "main.pdf")
shutil.copy2(OUT / "main.bbl", HERE / "main.bbl")
print(f"Built paper/main.pdf ({pages.group(1) if pages else '?'} pages); no undefined references or citations, "
      "duplicate labels, overfull boxes, floats too large for the page or BibTeX warnings.")
