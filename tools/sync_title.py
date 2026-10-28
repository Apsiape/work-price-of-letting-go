"""Copy the paper's title from its one source, paper/sections/title.tex, into every other place it appears.

Usage (from the repository root):
    python tools/sync_title.py            # rewrite the title in README.md, verification/README.md,
                                          # CITATION.cff and .zenodo.json
    python tools/sync_title.py --check    # change nothing; exit 1 if any place disagrees with title.tex
    python tools/sync_title.py --github   # also set the GitHub repository description (needs gh)

The PDF (title page and PDF metadata) reads title.tex directly, so rebuild with python paper/build.py.
Only the paper's own title is touched: the titles of the companion papers and of the letter are left alone.
"""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "paper" / "sections" / "title.tex"
REPO = "Apsiape/work-price-of-letting-go"


def read_title():
    tex = SOURCE.read_text(encoding="utf-8")
    m = re.search(r"\\newcommand\{\\papertitle\}\{(.*)\}\s*$", tex, re.M)
    if not m:
        raise SystemExit(f"No \\newcommand{{\\papertitle}}{{...}} line in {SOURCE}")
    title = m.group(1).replace("---", "\u2014").replace("--", "\u2013").replace("~", " ")
    if any(c in title for c in "\\{}$"):
        raise SystemExit("Write the title in plain text: no TeX macros, braces or math in \\papertitle.")
    return title


def places(title):
    """(file, pattern, replacement) for every place the title lives; each pattern must match exactly once."""
    q = title.replace('"', '\\"')
    return [
        ("README.md", r"\A# .*$", f"# {title}"),
        ("verification/README.md", r"\A# Verification package for \*.*\*$", f"# Verification package for *{title}*"),
        ("CITATION.cff", r"^title: \".*\"$", f'title: "{q}"'),
        ("CITATION.cff", r"^(preferred-citation:\n  type: generic\n  title: )\".*\"$", None),
        (".zenodo.json", r"\A\{\n  \"title\": \".*\",$", '{\n  "title": "' + q + '",'),
    ], q


def main():
    title = read_title()
    check = "--check" in sys.argv
    rows, q = places(title)
    bad = []
    for name, pattern, repl in rows:
        path = ROOT / name
        text = path.read_text(encoding="utf-8")
        rx = re.compile(pattern, re.M)
        hits = rx.findall(text)
        if len(hits) != 1:
            raise SystemExit(f"{name}: expected one title line for /{pattern}/, found {len(hits)}")
        if repl is None:
            new = rx.sub(lambda m: m.group(1) + f'"{q}"', text)
        else:
            new = rx.sub(lambda m: repl, text)
        if new != text:
            bad.append(name)
            if not check:
                path.write_text(new, encoding="utf-8", newline="\n")
    if check:
        if bad:
            print("Title differs from paper/sections/title.tex in: " + ", ".join(sorted(set(bad))))
            sys.exit(1)
        print(f"Title is consistent everywhere: {title}")
    else:
        print(("Updated: " + ", ".join(sorted(set(bad)))) if bad else "Already consistent.", "Title:", title)
    if "--github" in sys.argv:
        subprocess.run(["gh", "repo", "edit", REPO, "--description", title], check=True)
        print("GitHub repository description set.")


if __name__ == "__main__":
    main()
