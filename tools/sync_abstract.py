"""Copy the paper's abstract from its one source, the abstract environment of paper/sections/00_front.tex, into
README.md, CITATION.cff and .zenodo.json, and check that every surface says the same thing within arXiv's limit.

Usage (from the repository root):
    python tools/sync_abstract.py            # rewrite the abstract in README.md, CITATION.cff and .zenodo.json
    python tools/sync_abstract.py --check    # change nothing; exit 1 if any surface differs from the paper's
                                             # abstract after normalization, or if a version exceeds 1920 characters

The TeX source is the arXiv submission string: its whitespace is collapsed to single spaces and its length is
counted against arXiv's limit of 1920 characters. The other surfaces carry the same text in plain form, with the
mathematics normalized explicitly: $k_{\\mathrm B}T\\ln3$ becomes "k_B T ln 3" in README.md and CITATION.cff, and
"k<sub>B</sub>T ln 3" in the HTML of .zenodo.json. Any TeX the normalizer does not know stops the script, so a new
macro in the abstract cannot slip through unconverted.
"""
from pathlib import Path
import html
import json
import re
import sys
import textwrap

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "paper" / "sections" / "00_front.tex"
LIMIT = 1920
BS = "\\"

ACCENTS = {BS + "~a": "ã", BS + "~o": "õ", BS + "'e": "é", BS + "'a": "á",
           BS + '"o': "ö", BS + '"u': "ü", BS + "`e": "è"}
MATH = [(r"k_{" + BS + "mathrm B}T", "k_B T"), (BS + "ln", " ln "), (BS + "log", " log "), (BS + ",", " ")]


def tex_abstract():
    tex = SOURCE.read_text(encoding="utf-8")
    m = re.search(re.escape(BS + "begin{abstract}") + r"(.*?)" + re.escape(BS + "end{abstract}"), tex, re.S)
    if not m:
        raise SystemExit(f"No abstract environment in {SOURCE}")
    return " ".join(m.group(1).split())


def tex_to_plain(tex):
    out = []
    for i, part in enumerate(re.split(r"\$", tex)):
        if i % 2:                                            # mathematics
            for old, new in MATH:
                part = part.replace(old, new)
            part = part.replace("{", "").replace("}", "")
        else:                                                # text
            for old, new in ACCENTS.items():
                part = part.replace("{" + old + "}", new).replace(old, new)
            part = part.replace("---", "—").replace("--", "–").replace("~", " ").replace(BS + "%", "%")
        if BS in part:
            raise SystemExit(f"Unconverted TeX in the abstract: {part!r}; extend the normalizer in {__file__}")
        out.append(part)
    return " ".join("".join(out).split())


def plain_to_html(plain):
    return html.escape(plain, quote=False).replace("k_B T", "k<sub>B</sub>T")


def html_to_plain(text):
    return " ".join(html.unescape(text.replace("k<sub>B</sub>T", "k_B T")).split())


# Each surface: how to find the abstract, and how to write it back.
README_START = "This is a draft of version 1.0.0. Its DOI will be added here when it is released.\n\n"
README_END = "\n\nAll rates are optimal asymptotic work rates"


def readme_get(text):
    i, j = text.index(README_START) + len(README_START), text.index(README_END)
    return " ".join(text[i:j].split())


def readme_put(text, plain):
    i, j = text.index(README_START) + len(README_START), text.index(README_END)
    return text[:i] + "\n".join(textwrap.wrap(plain, 118, break_on_hyphens=False)) + text[j:]


CFF_BLOCK = re.compile(r"^abstract: >-\n((?:  .*\n)+)", re.M)


def cff_get(text):
    m = CFF_BLOCK.search(text)
    if not m:
        raise SystemExit("CITATION.cff: no 'abstract: >-' block")
    return " ".join(m.group(1).split())


def cff_put(text, plain):
    body = "\n".join(textwrap.wrap(plain, 112, initial_indent="  ", subsequent_indent="  ", break_on_hyphens=False))
    return CFF_BLOCK.sub(lambda m: "abstract: >-\n" + body + "\n", text, count=1)


def zenodo_get(text):
    desc = json.loads(text)["description"]
    m = re.match(r"<p>(.*?)</p>", desc, re.S)
    return html_to_plain(m.group(1))


def zenodo_put(text, plain):
    data = json.loads(text)
    desc = data["description"]
    m = re.match(r"<p>(.*?)</p>", desc, re.S)
    data["description"] = "<p>" + plain_to_html(plain) + "</p>" + desc[m.end():]
    return json.dumps(data, ensure_ascii=False, indent=2) + "\n"


SURFACES = [("README.md", readme_get, readme_put), ("CITATION.cff", cff_get, cff_put),
            (".zenodo.json", zenodo_get, zenodo_put)]


def main():
    check = "--check" in sys.argv
    tex = tex_abstract()
    plain = tex_to_plain(tex)
    bad = []
    for name, get, put in SURFACES:
        path = ROOT / name
        text = path.read_text(encoding="utf-8")
        if get(text) != plain:
            bad.append(name)
            if not check:
                new = put(text, plain)
                if get(new) != plain:
                    raise SystemExit(f"{name}: rewriting did not reproduce the abstract")
                path.write_text(new, encoding="utf-8", newline="\n")
    too_long = [what for what, n in (("TeX (arXiv) abstract", len(tex)), ("plain abstract", len(plain))) if n > LIMIT]
    print(f"TeX abstract, the arXiv submission string: {len(tex)} characters; plain form: {len(plain)}; "
          f"limit {LIMIT}.")
    if too_long:
        print("Too long: " + ", ".join(too_long))
    if check:
        if bad:
            print("Abstract differs from paper/sections/00_front.tex in: " + ", ".join(bad))
        if bad or too_long:
            sys.exit(1)
        print("The abstract is the same on every surface.")
    else:
        print(("Updated: " + ", ".join(bad)) if bad else "Already consistent.")
        if too_long:
            sys.exit(1)


if __name__ == "__main__":
    main()
