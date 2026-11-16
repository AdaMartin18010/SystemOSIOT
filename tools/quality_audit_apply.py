#!/usr/bin/env python3
"""内容质量审计执行器（2026-11 Phase Q-exec）

读取 validation/content-audit-detail.csv，将 C-归档候选 文件 git mv 至
docs/Refactor/archive/2026-quality-audit/<原相对路径>（不删除，可恢复）。

规则：
- 豁免：research/（过程性报告）、docs/navigation/、.vscode/、API文档标准.md、
  以及一切 README.md（保留为目录骨架，事后追加治理注记）。
- 其余 C 类全部归档；被抽空的内容目录若留有 README 则保留并注记，否则创建桩 README。
- 不执行 git commit。

用法：python tools/quality_audit_apply.py [--dry-run]
"""

import csv
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

CSV_PATH = Path("validation/content-audit-detail.csv")
ARCHIVE_ROOT = Path("docs/Refactor/archive/2026-quality-audit")
EXEMPT_PREFIXES = ("research/", "docs/navigation/", "docs/Refactor/", ".vscode/")
EXEMPT_FILES = {"API文档标准.md"}
EXEMPT_MARKS = ("国际标准映射",)  # 对齐核心层永不自动归档，走人工/B 类评审

DRY = "--dry-run" in sys.argv


def git_mv(src: Path, dst: Path) -> None:
    dst.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["git", "mv", str(src), str(dst)], check=True)


def main() -> None:
    rows = list(csv.DictReader(CSV_PATH.open(encoding="utf-8")))
    targets = []
    for r in rows:
        p = r["path"]
        if r["class"] != "C-归档候选":
            continue
        if p.startswith(EXEMPT_PREFIXES) or Path(p).name in EXEMPT_FILES \
                or Path(p).name == "README.md" or any(m in p for m in EXEMPT_MARKS):
            continue
        if not Path(p).exists():
            continue
        targets.append(p)

    moved_dirs = defaultdict(int)
    for p in targets:
        src = Path(p)
        dst = ARCHIVE_ROOT / p
        moved_dirs[str(src.parent).replace("\\", "/")] += 1
        if DRY:
            print(f"DRY  {p} -> {dst}")
        else:
            git_mv(src, dst)

    notes = []
    if not DRY:
        (ARCHIVE_ROOT / "README.md").write_text(
            "# 质量审计归档（2026-11-17）\n\n"
            "> 来源：`tools/content_quality_audit.py` 全库分诊中判为 **C-归档候选** 的文件。\n"
            "> 判定标准：实质信号（引用/公式/图码表/参考文献）不足且带模板特征"
            "（占位符/自指证明提纲/模板对/重复目录）。\n"
            "> 本目录按原相对路径存放，恢复方式：`git mv \"<本目录下路径>\" \"<原路径>\"`。\n"
            "> 明细与得分见 `validation/content-audit-detail.csv`、报告见 "
            "`research/2026-content-quality-audit.md`。\n",
            encoding="utf-8")

        # 目录注记：被移走文件的目录，保留/创建 README 指向归档
        for d, cnt in sorted(moved_dirs.items()):
            dpath = Path(d)
            readme = dpath / "README.md"
            note = ("\n## 质量治理注记（2026-11）\n\n"
                    f"本目录原 {cnt} 个内容文件经全库质量审计归类为模板填充（C 类），"
                    f"已整体归档至 `docs/Refactor/archive/2026-quality-audit/{d}/`"
                    "（原相对路径不变，可恢复）。保留本 README 作为目录骨架。\n")
            if readme.exists():
                txt = readme.read_text(encoding="utf-8", errors="ignore")
                if "质量治理注记（2026-11）" not in txt:
                    readme.write_text(txt.rstrip() + "\n" + note, encoding="utf-8")
                    notes.append(f"annotated {d}/README.md (+{cnt})")
            else:
                dpath.mkdir(parents=True, exist_ok=True)
                readme.write_text(f"# {dpath.name}\n" + note, encoding="utf-8")
                notes.append(f"created {d}/README.md (+{cnt})")

        # 清理空目录（仅剩 README 的保留）
        removed = 0
        for d in sorted(moved_dirs, key=lambda x: -x.count("/")):
            dpath = Path(d)
            if dpath.exists() and dpath.is_dir():
                left = list(dpath.iterdir())
                if not left:
                    dpath.rmdir()
                    removed += 1
        print(f"moved={len(targets)} empty_dirs_removed={removed}")
        for n in notes:
            print(" ", n)
    else:
        print(f"DRY total={len(targets)}")


if __name__ == "__main__":
    main()
