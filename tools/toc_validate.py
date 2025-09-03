#!/usr/bin/env python3
"""
Parallel validator for Markdown TOC blocks delimited by:
  <!-- TOC START --> ... <!-- TOC END -->

Checks per file:
1) Presence of TOC if headings exist
2) TOC anchors resolve to existing headings
3) TOC content matches regenerated TOC (diff)

Exits non-zero when issues are found.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional, Tuple

from toc_generator import (
    TOC_START,
    TOC_END,
    extract_headings,
    generate_toc,
    slugify,
)


MD_EXTENSIONS = {".md", ".markdown"}


def find_toc_block_idx(lines: List[str]) -> Optional[Tuple[int, int]]:
    start = None
    for i, line in enumerate(lines):
        if line.strip() == TOC_START:
            start = i
            break
    if start is None:
        return None
    for j in range(start + 1, len(lines)):
        if lines[j].strip() == TOC_END:
            return start, j
    return None


@dataclass
class ValidationIssue:
    kind: str
    detail: str


@dataclass
class ValidationResult:
    path: Path
    ok: bool
    issues: List[ValidationIssue]


def validate_file(path: Path, max_level: int) -> ValidationResult:
    issues: List[ValidationIssue] = []
    try:
        content = path.read_text(encoding="utf-8")
    except Exception as exc:
        return ValidationResult(path=path, ok=False, issues=[ValidationIssue("read_error", str(exc))])

    lines = content.splitlines(True)
    headings = extract_headings(lines)
    block = find_toc_block_idx(lines)

    if headings and not block:
        issues.append(ValidationIssue("missing_toc", "Headings present but TOC block not found"))
        return ValidationResult(path=path, ok=False, issues=issues)

    if not headings:
        # No headings → TOC not required
        return ValidationResult(path=path, ok=True, issues=[])

    assert block is not None
    s, e = block
    toc_lines = lines[s : e + 1]

    # Validate anchors
    heading_texts = [h.text for h in headings if h.level <= max_level]
    heading_anchors = {slugify(t) for t in heading_texts}
    link_pattern = re.compile(r"\]\(#(?P<anchor>[^)]+)\)")
    anchors_in_toc = [m.group("anchor") for line in toc_lines for m in link_pattern.finditer(line)]
    for a in anchors_in_toc:
        if a not in heading_anchors:
            issues.append(ValidationIssue("invalid_anchor", f"Anchor not found in headings: #{a}"))

    # Content equivalence with regenerated TOC
    regenerated = generate_toc(headings, max_level=max_level)
    # Wrap with context for exact comparison
    regenerated_block = regenerated
    if toc_lines != regenerated_block:
        issues.append(ValidationIssue("mismatch", "TOC content differs from regenerated output"))

    return ValidationResult(path=path, ok=(len(issues) == 0), issues=issues)


def iter_markdown_files(roots: Iterable[Path]) -> Iterable[Path]:
    for root in roots:
        if root.is_file() and root.suffix.lower() in MD_EXTENSIONS:
            yield root
            continue
        for p in root.rglob("*"):
            if p.is_file() and p.suffix.lower() in MD_EXTENSIONS and not any(seg.startswith(".") for seg in p.parts):
                yield p


def is_numbered_topic_path(path: Path) -> bool:
    parts = path.parts
    for seg in parts:
        if re.match(r"^\d+\.", seg):
            return True
    if "docs" in parts and "Refactor" in parts:
        return True
    return False


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Validate Markdown TOC blocks")
    parser.add_argument("paths", nargs="*", default=["."], help="Paths to scan (files or directories)")
    parser.add_argument("--max-level", type=int, default=4)
    parser.add_argument("--all", action="store_true", help="Do not restrict to numbered topic directories")
    parser.add_argument("--workers", type=int, default=os.cpu_count() or 4)
    args = parser.parse_args(argv)

    roots = [Path(p).resolve() for p in args.paths]
    candidates = list(iter_markdown_files(roots))
    if not args.all:
        candidates = [p for p in candidates if is_numbered_topic_path(p)]

    total = len(candidates)
    failures: List[ValidationResult] = []

    def _work(p: Path) -> ValidationResult:
        return validate_file(p, max_level=args.max_level)

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = {ex.submit(_work, p): p for p in candidates}
        for fut in concurrent.futures.as_completed(futs):
            res = fut.result()
            if not res.ok:
                failures.append(res)

    print(f"Validated files: {total}")
    print(f"Failures: {len(failures)}")
    if failures:
        for res in failures[:200]:
            rel = os.path.relpath(str(res.path), os.getcwd())
            print(f"FAIL {rel}")
            for issue in res.issues:
                print(f"  - {issue.kind}: {issue.detail}")
        if len(failures) > 200:
            print(f"... and {len(failures) - 200} more")
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())


