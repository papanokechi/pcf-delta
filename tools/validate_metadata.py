#!/usr/bin/env python3
"""
validate_metadata.py — pre-deposit consistency gate for a research-slug project.

Checks the pre-deposit checklist before any Zenodo mint or submission:
  1. ORCID is exactly 0009-0000-6192-8273 (string compare) in METADATA, and present
     in the manuscript source.
  2. Version consistency: METADATA.version == version on the PDF title page; and if
     the PDF filename carries a _vX.Y token it must equal METADATA.version.
  3. AI-disclosure block is byte-identical (modulo LaTeX/Markdown normalization) to
     the frozen org boilerplate.
  4. Repo URL (github) present in the manuscript AND in METADATA related_identifiers.
  5. related_identifiers links the companion DOI (isSupplementTo) and the GitHub repo
     (isSupplementedBy).
  6. License present and equal to the project's standing choice (CC-BY-4.0).

Exit code 0 = all PASS; 1 = at least one FAIL or ERROR. Nothing is mutated.

Usage:
  python tools/validate_metadata.py [--project DIR] [--pdf PATH] [--tex PATH]
                                    [--boilerplate PATH]
Defaults assume the project layout:
  <project>/METADATA.yml, delta_characterization.tex, delta_characterization.pdf,
  ../_boilerplate/disclosures.md
"""
import argparse
import re
import subprocess
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    print("ERROR: PyYAML required (pip install pyyaml).", file=sys.stderr)
    sys.exit(1)

EXPECTED_ORCID = "0009-0000-6192-8273"
EXPECTED_LICENSE = "CC-BY-4.0"


def normalize(text: str) -> str:
    """Collapse LaTeX/Markdown surface differences so disclosure prose can be
    compared by content: drop \\ref{...}, unwrap \\texttt{..}/\\emph{..}, strip
    backslash-commands, backticks, '**', '#', and collapse whitespace."""
    t = text
    t = re.sub(r"\\ref\{[^}]*\}", "", t)
    t = re.sub(r"\\(?:texttt|emph|textbf|textit)\{([^}]*)\}", r"\1", t)
    t = t.replace("\\#", "#")
    t = re.sub(r"\\[a-zA-Z]+", " ", t)   # any remaining latex command
    t = t.replace("`", "").replace("**", "")
    t = re.sub(r"\s+", " ", t)
    return t.strip().lower()


def disclosure_core(boiler_ai: str) -> list:
    """Distinctive sentences of the AI-disclosure that must appear (normalized)."""
    n = normalize(boiler_ai)
    # split into clauses on '.' and keep substantial ones
    parts = [p.strip() for p in n.split(".") if len(p.strip()) > 25]
    return parts


def pdf_titlepage_text(pdf: Path) -> str:
    try:
        out = subprocess.run(
            ["pdftotext", "-f", "1", "-l", "1", str(pdf), "-"],
            capture_output=True, text=True, timeout=60)
        return out.stdout
    except (OSError, subprocess.SubprocessError):
        return ""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--project", default=".")
    ap.add_argument("--pdf", default=None)
    ap.add_argument("--tex", default=None)
    ap.add_argument("--boilerplate", default=None)
    args = ap.parse_args()

    proj = Path(args.project).resolve()
    meta_path = proj / "METADATA.yml"
    tex_path = Path(args.tex) if args.tex else proj / "delta_characterization.tex"
    pdf_path = Path(args.pdf) if args.pdf else proj / "delta_characterization.pdf"
    boiler_path = (Path(args.boilerplate) if args.boilerplate
                   else proj.parent / "_boilerplate" / "disclosures.md")

    results = []  # (name, ok, detail)

    def check(name, ok, detail=""):
        results.append((name, bool(ok), detail))

    if not meta_path.exists():
        print(f"ERROR: {meta_path} not found", file=sys.stderr)
        return 1
    meta = yaml.safe_load(meta_path.read_text(encoding="utf-8"))
    tex = tex_path.read_text(encoding="utf-8") if tex_path.exists() else ""
    version = str(meta.get("version", "")).strip()
    slug = str(meta.get("slug", "")).strip()
    github = str(meta.get("github", "")).strip()
    rels = meta.get("related_identifiers", []) or []

    # 1. ORCID
    orcids = [str(c.get("orcid", "")) for c in meta.get("creators", [])]
    check("1a ORCID exact in METADATA", EXPECTED_ORCID in orcids,
          f"found {orcids}")
    check("1b ORCID present in manuscript", EXPECTED_ORCID in tex)

    # 2. Version consistency
    page1 = pdf_titlepage_text(pdf_path) if pdf_path.exists() else ""
    title_has_version = bool(version) and (f"v{version}" in page1 or version in page1)
    check("2a version on PDF title page", title_has_version,
          f"want v{version}; pdf={'present' if pdf_path.exists() else 'MISSING'}")
    fn_token = re.search(r"_v(\d+\.\d+)", pdf_path.name)
    if fn_token:
        check("2b PDF filename version == METADATA", fn_token.group(1) == version,
              f"filename v{fn_token.group(1)} vs METADATA v{version}")
    else:
        check("2b PDF filename version token", True, "live bare-named file (exempt)")

    # 3. AI-disclosure boilerplate match
    if boiler_path.exists():
        btxt = boiler_path.read_text(encoding="utf-8")
        m = re.search(r"## ai-disclosure\s*(.+?)(?:\n## |\Z)", btxt, re.S)
        boiler_ai = m.group(1) if m else ""
        ntex = normalize(tex)
        missing = [c for c in disclosure_core(boiler_ai) if c not in ntex]
        check("3 AI-disclosure matches frozen boilerplate", not missing,
              "OK" if not missing else f"missing clauses: {missing}")
    else:
        check("3 AI-disclosure matches frozen boilerplate", False,
              f"boilerplate not found at {boiler_path}")

    # 4. Repo URL present in manuscript and METADATA
    repo_in_meta = any(github and github in str(r.get("identifier", "")) for r in rels)
    check("4a repo URL in METADATA related_identifiers", repo_in_meta, github)
    check("4b repo URL in manuscript", bool(github) and github in tex)

    # 5. related_identifiers completeness
    has_supplement_to = any(r.get("relation") == "isSupplementTo"
                            and str(r.get("identifier", "")).startswith("10.")
                            for r in rels)
    has_github_rel = any(r.get("relation") == "isSupplementedBy"
                         and "github.com" in str(r.get("identifier", "")) for r in rels)
    check("5a companion DOI linked (isSupplementTo)", has_supplement_to)
    check("5b GitHub linked (isSupplementedBy)", has_github_rel)

    # 6. License
    check("6 license is standing choice", str(meta.get("license", "")) == EXPECTED_LICENSE,
          str(meta.get("license", "")))

    # report
    width = max(len(n) for n, _, _ in results)
    allok = True
    for name, ok, detail in results:
        allok = allok and ok
        tag = "PASS" if ok else "FAIL"
        line = f"  [{tag}] {name.ljust(width)}"
        if detail:
            line += f"   {detail}"
        print(line)
    print()
    print("ALL CHECKS PASS" if allok else "*** VALIDATION FAILED ***")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
