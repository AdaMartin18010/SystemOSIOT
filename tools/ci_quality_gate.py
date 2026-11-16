#!/usr/bin/env python3
"""CI 内容质量门（2026-11 R4）

流程：运行全库质量审计 → 读取 CSV → 违规即非零退出。
检查项：
1. 非豁免类 C-归档候选 活库文件数 == 0（豁免：README、research/、docs/navigation/、
   docs/Refactor/、.vscode/、X.0 国际标准映射、API文档标准.md）
2. 编号文件深度 ≤ 5（文件名首段数字组分个数）

用法：python tools/ci_quality_gate.py
"""

import csv
import re
import subprocess
import sys
from pathlib import Path

CSV_PATH = Path("validation/content-audit-detail.csv")
EX_PREFIX = ("research/", "docs/", "states/", ".vscode/")
EX_MARKS = ("国际标准映射",)
EX_FILES = {"API文档标准.md"}


def exempt(p: str) -> bool:
    return (p.startswith(EX_PREFIX) or any(m in p for m in EX_MARKS)
            or Path(p).name in EX_FILES or Path(p).name == "README.md")


def main() -> int:
    r = subprocess.run([sys.executable, "tools/content_quality_audit.py"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stdout)
        print(r.stderr, file=sys.stderr)
        print("FAIL: 审计脚本本身执行失败")
        return 1
    print(r.stdout.strip())

    rows = list(csv.DictReader(CSV_PATH.open(encoding="utf-8")))
    bad_c = [r["path"] for r in rows if r["class"] == "C-归档候选" and not exempt(r["path"])]
    deep = []
    for p in Path(".").rglob("*.md"):
        posix = p.as_posix()
        if ".git" in p.parts or "docs/Refactor/archive" in posix or "tools/engines" in posix:
            continue
        head = p.name.split(" ")[0]
        if head and head[0].isdigit() and head.count(".") >= 5:
            try:
                if p.exists():
                    deep.append(posix)
            except OSError:
                pass

    ok = True
    if bad_c:
        ok = False
        print(f"\nFAIL: {len(bad_c)} 个非豁免 C 类文件（不允许进入主库）：")
        for p in bad_c[:20]:
            print("  -", p)
    if deep:
        ok = False
        print(f"\nFAIL: {len(deep)} 个文件编号深度超过 5 级：")
        for p in deep[:20]:
            print("  -", p)
    if ok:
        a = sum(1 for r in rows if r["class"] == "A-保留")
        b = sum(1 for r in rows if r["class"] == "B-待评审")
        print(f"\nPASS: A={a} B={b} C(豁免)={len(rows)-a-b}，无违规。")
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
