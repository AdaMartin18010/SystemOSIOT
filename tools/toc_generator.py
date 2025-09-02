#!/usr/bin/env python3
"""
Multithreaded Markdown TOC generator/updater.

Features:
- Scans target directories for .md files
- Extracts existing headings without modifying them
- Inserts or updates a TOC block between markers:
  <!-- TOC START --> and <!-- TOC END -->
- Places TOC below the first H1 if present; otherwise at file start
- Skips files that would be unchanged
- Supports dry-run and apply modes
- Parallel processing with ThreadPoolExecutor

Notes:
- Respects existing heading text and numbering
- Generates anchor links compatible with GitHub/Git-style slugs
- UTF-8 safe; preserves original newlines
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, List, Optional, Tuple


TOC_START = "<!-- TOC START -->"
TOC_END = "<!-- TOC END -->"
MD_EXTENSIONS = {".md", ".markdown"}


HEADING_PATTERN = re.compile(r"^(?P<indent>\s{0,3})(?P<hash>#{1,6})\s+(?P<text>.+?)\s*$")


def slugify(text: str) -> str:
    """Create a GitHub-like slug for Markdown anchors.

    We: lower-case, strip, remove punctuation except dashes and spaces,
    replace spaces with dashes, collapse repeats. Retain CJK characters.
    """
    t = text.strip().lower()
    # Remove inline links/images markup when used as heading text
    t = re.sub(r"!\[[^\]]*\]\([^)]*\)", "", t)
    t = re.sub(r"\[[^\]]*\]\([^)]*\)", lambda m: m.group(0).split("](")[0][1:], t)
    # Remove code backticks
    t = t.replace("`", "")
    # Keep unicode letters/numbers including CJK; replace others except space and hyphen
    t = re.sub(r"[^\w\-\s\u4e00-\u9fff]", "", t, flags=re.UNICODE)
    t = re.sub(r"\s+", "-", t)
    t = re.sub(r"-+", "-", t)
    return t


@dataclass
class Heading:
    level: int
    text: str
    line_index: int


def extract_headings(lines: List[str]) -> List[Heading]:
    headings: List[Heading] = []
    for idx, line in enumerate(lines):
        m = HEADING_PATTERN.match(line)
        if not m:
            continue
        level = len(m.group("hash"))
        text = m.group("text").strip()
        # Exclude headings inside TOC block
        headings.append(Heading(level=level, text=text, line_index=idx))
    return headings


def find_toc_block(lines: List[str]) -> Optional[Tuple[int, int]]:
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
    # Unclosed block; treat as absent
    return None


def generate_toc(headings: List[Heading], max_level: int) -> List[str]:
    items: List[str] = []
    for h in headings:
        if h.level > max_level:
            continue
        anchor = slugify(h.text)
        indent = "  " * (h.level - 1)  # 2 spaces per level below H1
        items.append(f"{indent}- [{h.text}](#{anchor})")
    if not items:
        return []
    toc_lines = [TOC_START, "", *items, "", TOC_END]
    return [l + ("\n" if not l.endswith("\n") else "") for l in toc_lines]


def insert_or_update_toc(original: str, max_level: int) -> Tuple[str, bool]:
    lines = original.splitlines(True)  # keepends
    headings = extract_headings(lines)
    headings = [h for h in headings if not (lines[h.line_index].strip() == TOC_START or lines[h.line_index].strip() == TOC_END)]
    if not headings:
        return original, False

    toc_lines = generate_toc(headings, max_level=max_level)
    if not toc_lines:
        return original, False

    block = find_toc_block(lines)
    if block:
        s, e = block
        new_lines = lines[:s] + toc_lines + lines[e + 1 :]
        updated = new_lines != lines
        return ("".join(new_lines), updated)

    # Insert TOC after first H1 if present; else at start with a blank line after
    first_h1_idx = next((h.line_index for h in headings if h.level == 1), None)
    insertion_idx = 0
    if first_h1_idx is not None:
        # place after heading and any immediate blank line
        insertion_idx = first_h1_idx + 1
        while insertion_idx < len(lines) and lines[insertion_idx].strip() == "":
            insertion_idx += 1
        # Insert with a blank line before and after
        toc_block = ["\n"] + toc_lines + ["\n"]
    else:
        toc_block = toc_lines + ["\n"]

    new_lines = lines[:insertion_idx] + toc_block + lines[insertion_idx:]
    updated = new_lines != lines
    return ("".join(new_lines), updated)


def file_hash(content: str) -> str:
    return hashlib.sha256(content.encode("utf-8")).hexdigest()


@dataclass
class ProcessResult:
    path: Path
    changed: bool
    skipped_reason: Optional[str] = None


def process_file(path: Path, max_level: int, apply: bool) -> ProcessResult:
    try:
        original = path.read_text(encoding="utf-8")
    except Exception as exc:
        return ProcessResult(path=path, changed=False, skipped_reason=f"read_error: {exc}")

    updated_text, changed = insert_or_update_toc(original, max_level=max_level)
    if not changed:
        return ProcessResult(path=path, changed=False, skipped_reason="no_change")

    if apply:
        try:
            path.write_text(updated_text, encoding="utf-8", newline="\n")
        except Exception as exc:
            return ProcessResult(path=path, changed=False, skipped_reason=f"write_error: {exc}")
    return ProcessResult(path=path, changed=True)


def iter_markdown_files(roots: Iterable[Path]) -> Iterable[Path]:
    for root in roots:
        if root.is_file() and root.suffix.lower() in MD_EXTENSIONS:
            yield root
            continue
        for p in root.rglob("*"):
            if not p.is_file():
                continue
            if p.suffix.lower() not in MD_EXTENSIONS:
                continue
            # Skip common non-content files
            if any(seg.startswith(".") for seg in p.parts):
                continue
            yield p


def is_numbered_topic_path(path: Path) -> bool:
    # Enforce targeting paths whose top-level dir starts with a number and dot or is under docs/Refactor
    parts = path.parts
    try:
        # Find segment after repo root by locating first segment that looks like n.xxx
        for seg in parts:
            if re.match(r"^\d+\.", seg):
                return True
        # Also allow docs/Refactor
        if "docs" in parts and "Refactor" in parts:
            return True
    except Exception:
        pass
    return False


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Multithreaded Markdown TOC generator/updater")
    parser.add_argument("paths", nargs="*", default=["."], help="Paths to scan (files or directories)")
    parser.add_argument("--max-level", type=int, default=4, help="Max heading level to include (1-6)")
    parser.add_argument("--apply", action="store_true", help="Write changes to files; default is dry-run")
    parser.add_argument("--all", action="store_true", help="Do not restrict to numbered topic directories")
    parser.add_argument("--workers", type=int, default=os.cpu_count() or 4, help="Number of worker threads")
    args = parser.parse_args(argv)

    roots = [Path(p).resolve() for p in args.paths]
    candidates = list(iter_markdown_files(roots))

    if not args.all:
        candidates = [p for p in candidates if is_numbered_topic_path(p)]

    if not candidates:
        print("No markdown files matched the selection.")
        return 0

    changed = 0
    skipped_nochange = 0
    skipped_errors = 0

    def _work(p: Path) -> ProcessResult:
        return process_file(p, max_level=args.max_level, apply=args.apply)

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as ex:
        fut_to_path = {ex.submit(_work, p): p for p in candidates}
        for fut in concurrent.futures.as_completed(fut_to_path):
            res = fut.result()
            rel = os.path.relpath(str(res.path), os.getcwd())
            if res.changed:
                changed += 1
                print(("APPLIED  " if args.apply else "DRY-RUN ") + rel)
            else:
                if res.skipped_reason == "no_change":
                    skipped_nochange += 1
                else:
                    skipped_errors += 1
                print(f"SKIP    {rel}  ({res.skipped_reason})")

    mode = "apply" if args.apply else "dry-run"
    print("\nSummary:")
    print(f"  Mode: {mode}")
    print(f"  Files considered: {len(candidates)}")
    print(f"  Changed: {changed}")
    print(f"  Unchanged: {skipped_nochange}")
    print(f"  Errors: {skipped_errors}")

    return 0


if __name__ == "__main__":
    sys.exit(main())


