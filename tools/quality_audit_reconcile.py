#!/usr/bin/env python3
"""质量审计对账（2026-11 Phase Q-reconcile）

在修正占位符误判（排除 Markdown 链接文本）后重跑审计，对归档执行双向对账：
1. 恢复：归档区中重分类为 A/B 的文件 → git mv 回原路径。
2. 补归档：新判为 C 的活库文件 → git mv 入归档区（豁免规则同 apply）。
3. 注记同步：重写受影响目录 README 的「质量治理注记（2026-11）」为最终计数。

用法：python tools/quality_audit_reconcile.py [--dry-run]
（须先运行 tools/content_quality_audit.py 生成最新 CSV）
"""

import csv
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from content_quality_audit import audit_file  # noqa: E402

CSV_PATH = Path("validation/content-audit-detail.csv")
ARCHIVE_ROOT = Path("docs/Refactor/archive/2026-quality-audit")
EXEMPT_PREFIXES = ("research/", "docs/navigation/", "docs/Refactor/", ".vscode/")
EXEMPT_FILES = {"API文档标准.md"}
EXEMPT_MARKS = ("国际标准映射",)
MARKER = "## 质量治理注记（2026-11）"
DRY = "--dry-run" in sys.argv
NOTES_ONLY = "--notes-only" in sys.argv

# 人工抽审裁定为归档的文件（永远不回滚）
BYPASS = {
    "1.系统理论/1.2 批判分析/1.2.7 认识论批判.md",
    "1.系统理论/1.2 批判分析/1.2.8 方法论批判.md",
    "1.系统理论/1.2 批判分析/1.2.9 方法论创新.md",
    "1.系统理论/1.2 批判分析/1.2.10 范式转换分析.md",
    "1.系统理论/1.2 批判分析/1.2.11 未来范式预测.md",
    "1.系统理论/1.2 批判分析/1.2.12 跨文化比较研究.md",
    "1.系统理论/1.2 批判分析/1.2.13 分析哲学基础.md",
    "1.系统理论/1.2 批判分析/1.2.14 深度哲学分析.md",
    "1.系统理论/1.2 批判分析/1.2.15 严格逻辑论证体系.md",
    "7.容器与微服务/7.1 知识梳理/Firecracker未来趋势多云边缘子主题/子主题递归细化.md",
    "7.容器与微服务/7.1 知识梳理/Firecracker未来趋势多云边缘子主题/Firecracker未来趋势子主题.md",
    "7.容器与微服务/7.1 知识梳理/Firecracker未来趋势多云边缘子主题/输入门.md",
}


def archive_rule(rec: dict) -> bool:
    """R1 抽审标准：真占位符 / 自指证明提纲≥10 / 模板对且近零引用 → 不归回。"""
    return (int(rec["placeholders"]) > 0 or int(rec["proof_tmpl"]) >= 10
            or ("模板对" in rec["flags"] and int(rec["citations"]) <= 1))


def git_mv(src: Path, dst: Path) -> None:
    dst.parent.mkdir(parents=True, exist_ok=True)
    try:
        subprocess.run(["git", "mv", str(src), str(dst)], check=True)
    except subprocess.CalledProcessError as e:
        print(f"  ! 失败（跳过）: {src} -> {dst}: {e}", file=sys.stderr)


def main() -> None:
    cls = {r["path"]: r["class"] for r in csv.DictReader(CSV_PATH.open(encoding="utf-8"))}

    def classify(rel: str, src: Path) -> str:
        if rel in cls:
            return cls[rel]
        return audit_file(src)["class"]  # 归档区文件现场重判

    def exempt(p: str) -> bool:
        return (p.startswith(EXEMPT_PREFIXES) or Path(p).name in EXEMPT_FILES
                or Path(p).name == "README.md" or any(m in p for m in EXEMPT_MARKS))

    restored, moved = [], []
    # 1) 恢复误归档 / 2) 补归档新 C（--notes-only 时跳过移动，仅同步注记）
    if not NOTES_ONLY and ARCHIVE_ROOT.exists():
        for f in sorted(ARCHIVE_ROOT.rglob("*.md")):
            rel = f.relative_to(ARCHIVE_ROOT).as_posix()
            if f.name == "README.md":
                continue
            rec = audit_file(f)
            if rel in BYPASS:
                continue
            if rec["class"] in ("A-保留", "B-待评审") and not archive_rule(rec):
                dst = Path(rel)
                if not DRY:
                    git_mv(f, dst)
                restored.append(rel)
    # 2) 补归档新 C
    if not NOTES_ONLY:
        for p, c in sorted(cls.items()):
            if c != "C-归档候选" or exempt(p):
                continue
            src = Path(p)
            if src.exists():
                if not DRY:
                    git_mv(src, ARCHIVE_ROOT / p)
                moved.append(p)

    print(f"restored={len(restored)}")
    for r in restored:
        print("  R", r)
    print(f"moved={len(moved)}")
    for m in moved:
        print("  M", m)

    # 3) 注记同步
    if DRY:
        return
    dirs = set()
    for f in ARCHIVE_ROOT.rglob("*.md"):
        if f.name == "README.md":
            continue
        dirs.add(f.relative_to(ARCHIVE_ROOT).parent.as_posix())
    synced = 0
    for d in sorted(dirs):
        dpath = Path(d)
        n = len([f for f in (ARCHIVE_ROOT / d).glob("*.md") if f.name != "README.md"])
        if n == 0:
            continue
        readme = dpath / "README.md"
        note = (f"\n{MARKER}\n\n本目录 {n} 个内容文件经全库质量审计（2026-11-17，修正链接文本误判后）"
                f"归类为模板填充（C 类），已归档至 `docs/Refactor/archive/2026-quality-audit/{d}/`"
                "（原相对路径不变，`git mv` 可恢复）。保留本 README 作为目录骨架。\n")
        if readme.exists():
            txt = readme.read_text(encoding="utf-8", errors="ignore")
            cut = txt.find("\n" + MARKER)
            base = txt[:cut] if cut != -1 else txt.rstrip()
            readme.write_text(base.rstrip() + "\n" + note, encoding="utf-8")
        else:
            dpath.mkdir(parents=True, exist_ok=True)
            readme.write_text(f"# {dpath.name}\n" + note, encoding="utf-8")
        synced += 1
    # 清空目录
    removed = 0
    for root in sorted(dirs, key=lambda x: -x.count("/")):
        dpath = Path(root)
        if dpath.is_dir() and not any(dpath.iterdir()):
            dpath.rmdir()
            removed += 1
    print(f"notes_synced={synced} empty_dirs_removed={removed}")


if __name__ == "__main__":
    main()
