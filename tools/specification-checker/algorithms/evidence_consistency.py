import re
from pathlib import Path


EVIDENCE_PATTERN = re.compile(r"E-\d{4}-\d{4}")


def extract_evidence_keys_from_file(path: Path) -> set[str]:
    text = path.read_text(encoding="utf-8", errors="ignore")
    return set(EVIDENCE_PATTERN.findall(text))


def scan_analysis_and_references(root: Path) -> tuple[set[str], set[str]]:
    analysis_dir = root / "Analysis"
    refs_file = root / "docs" / "Refactor" / "references.md"

    analysis_keys: set[str] = set()
    for md in analysis_dir.glob("*.md"):
        analysis_keys |= extract_evidence_keys_from_file(md)

    reference_keys: set[str] = set()
    if refs_file.exists():
        reference_keys = extract_evidence_keys_from_file(refs_file)

    return analysis_keys, reference_keys


def report_inconsistencies(analysis_keys: set[str], reference_keys: set[str]) -> dict:
    return {
        "missing_in_references": sorted(list(analysis_keys - reference_keys)),
        "unused_in_analysis": sorted(list(reference_keys - analysis_keys)),
        "analysis_total": len(analysis_keys),
        "references_total": len(reference_keys),
    }


def main() -> None:
    root = Path(__file__).resolve().parents[3]
    analysis_keys, reference_keys = scan_analysis_and_references(root)
    report = report_inconsistencies(analysis_keys, reference_keys)
    import json
    print(json.dumps(report, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()


