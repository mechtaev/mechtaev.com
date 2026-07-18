#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = [
#     "jinja2",
# ]
# ///
"""Render cv_template.tex.j2 with data from ../data.json and compile the
result to PDF with latexmk. Part of the mechtaev.com build (see Makefile)."""

import datetime
import json
import re
import subprocess
import sys
from pathlib import Path

from jinja2 import Environment, FileSystemLoader

ROOT = Path(__file__).parent
NAME = "Sergey Mechtaev"
MONTHS = ["Jan", "Feb", "Mar", "Apr", "May", "Jun",
          "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

# ----------------------------------------------------------------- text

LATEX_SPECIALS = {
    "&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#", "_": r"\_",
    "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}",
    "^": r"\textasciicircum{}", "\\": r"\textbackslash{}",
}


def strip_cjk(s: str) -> str:
    """Drop CJK alternatives like 'NSFC/国家自然科学基金' -> 'NSFC'."""
    parts = [p for p in s.split("/") if not re.search(r"[一-鿿]", p)]
    return "/".join(parts) or s


def esc(s) -> str:
    s = strip_cjk(str(s))
    s = "".join(LATEX_SPECIALS.get(c, c) for c in s)
    s = re.sub(r'"([^"]*)"', r"``\1''", s)   # straight -> curly quotes
    return s.strip()


# ---------------------------------------------------------------- dates

def fmt_my(d: dict) -> str:
    return f"{MONTHS[d['month'] - 1]} {d['year']}"


def fmt_range(start: dict, end: dict | None) -> str:
    if end is None:
        return f"{fmt_my(start)} -- present"
    a, b = sorted([(start["year"], start["month"]), (end["year"], end["month"])])
    if a == b:
        return f"{MONTHS[a[1] - 1]} {a[0]}"
    return f"{MONTHS[a[1] - 1]} {a[0]} -- {MONTHS[b[1] - 1]} {b[0]}"


# -------------------------------------------------------------- context

def build_context(data: dict) -> dict:
    general = data["general"]
    current = data["employment"][0]

    links = [
        {"url": f"mailto:{general['work_email']}", "text": esc(general["work_email"])},
        {"url": general["website"], "text": esc(general["website"].removeprefix("https://"))},
        {"url": f"https://{general['github']}", "text": esc(general["github"])},
        {"url": general["scholar"], "text": "Google Scholar"},
    ]

    education = [{
        "degree": esc(e["degree"]),
        "university": esc(e["university"]),
        "faculty": esc(e["faculty"]),
        "dates": f"{e['start']['year']} -- {e['end']['year']}",
        "thesis": esc(e["thesis"]),
        "supervisor": esc(e["supervisor"]),
    } for e in data["education"]]

    employment = [{
        "employer": esc(e["employer"]),
        "location": esc(e["location"]),
        "rows": [{"title": esc(h["title"]),
                  "dates": fmt_range(h["start"], h.get("end"))}
                 for h in e["history"]],
    } for e in data["employment"]]

    awards, grants, deployments = [], [], []
    for a in data["achievements"]:
        item = {"year": a.get("year", ""), "description": esc(a["description"])}
        if a["type"] == "award":
            awards.append(item | {"title": esc(a["title"])})
        elif a["type"] == "grant":
            grants.append(item | {"funder": esc(a["funder"]), "call": esc(a["call"])})
        else:
            deployments.append(item | {"title": esc(a["title"])})

    marks = {"equal": "*", "joint": "*", "corresponding": r"\dag"}
    publications = []
    for p in data["publications"]:
        names = []
        for a in p["authors"]:
            n = esc(a["name"])
            if a["name"] == NAME:
                n = rf"\me{{{n}}}"
            if a["authorship"] in marks:
                n += rf"\textsuperscript{{{marks[a['authorship']]}}}"
            names.append(n)
        authors = " and ".join(names) if len(names) <= 2 else \
            ", ".join(names[:-1]) + ", and " + names[-1]
        if "venue" in p:
            venue_line = rf"\emph{{{esc(p['venue'])}}}"
            # a comma in venue_short means a thesis-style venue, where the
            # abbreviation would just repeat the venue
            if "," not in p["venue_short"]:
                venue_line += f" ({esc(p['venue_short'])})"
            venue_line += f", {p['year']}"
        else:
            venue_line = f"Preprint, {p['year']}"
        publications.append({
            "authors": authors,
            "title": esc(p["title"]),
            "venue_line": venue_line,
            "awards": esc("; ".join(p["awards"])) if p.get("awards") else "",
        })

    teaching = [{
        "role": esc(t["role"]),
        "title": esc(t["title"]),
        "institution": esc(t["institution"]),
        "dates": fmt_range(t["start"], t.get("end")),
    } for t in data["teaching"]]

    students = []
    for s in data["group"]:
        start = min(s["history"], key=lambda h: (h["start"]["year"], h["start"]["month"]))["start"]
        ends = [h["end"] for h in s["history"] if h.get("end")]
        if ends:
            dates = fmt_range(start, max(ends, key=lambda d: (d["year"], d["month"])))
        elif s["alumni"]:
            dates = fmt_my(start)
        else:
            dates = fmt_range(start, None)
        detail_parts = []
        if s.get("thesis"):
            detail_parts.append(rf"Thesis: \emph{{{esc(s['thesis'])}}}.")
        if s.get("note"):
            detail_parts.append(esc(s["note"]) + ".")
        if s.get("first_job"):
            detail_parts.append(f"First position: {esc(s['first_job'])}.")
        students.append({
            "name": esc(s["name"]),
            "position": esc(s["history"][0]["position"]),
            "host": esc(s["host"]),
            "dates": dates,
            "detail": " ".join(detail_parts),
        })

    service_order = ["Co-chair", "Program committee"]
    service = []
    for role in service_order:
        entries = [s for s in data["service"] if s["role"] == role]
        if entries:
            venues = ", ".join(f"{esc(s['venue_short'])}'{s['year'] % 100:02d}"
                               for s in entries)
            service.append({"role": esc(role), "venues": venues})

    return {
        "name": esc(NAME),
        "title_line": f"{esc(current['history'][0]['title'])}, {esc(current['employer'])}",
        "address": esc(general["work_address"]),
        "links": links,
        "education": education,
        "employment": employment,
        "awards": awards,
        "grants": grants,
        "deployments": deployments,
        "publications": publications,
        "teaching": teaching,
        "students": students,
        "service": service,
        "updated": datetime.date.today().strftime("%B %Y"),
    }


# ------------------------------------------------------------------ main

def main() -> None:
    data_path = Path(sys.argv[1]) if len(sys.argv) > 1 \
        else ROOT.parent / "data.json"
    data = json.loads(data_path.read_text())

    env = Environment(
        loader=FileSystemLoader(ROOT),
        block_start_string=r"\BLOCK{", block_end_string="}",
        variable_start_string=r"\VAR{", variable_end_string="}",
        comment_start_string=r"\#{", comment_end_string="}",
        trim_blocks=True,
        autoescape=False,
    )
    tex = env.get_template("cv_template.tex.j2").render(build_context(data))

    out = ROOT / "sergey_mechtaev_cv.tex"
    out.write_text(tex)
    subprocess.run(["latexmk", "-pdf", "-interaction=nonstopmode", out.name],
                   cwd=ROOT, check=True, capture_output=True)
    subprocess.run(["latexmk", "-c", out.name], cwd=ROOT, capture_output=True)
    print(out.with_suffix(".pdf"))


if __name__ == "__main__":
    main()
