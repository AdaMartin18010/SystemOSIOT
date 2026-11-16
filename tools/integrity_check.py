#!/usr/bin/env python3
"""仓库完整性自检（hermes 每轮 loop 的第一道闸，2026-11-17 事故后设立）

检查项：
1. HEAD 跟踪文件在工作树中消失（MISSING）→ 立即失败（疑同步盘/安全软件删文件）
2. 归档区规模异常（质量审计归档 <150 → 警告）
3. git status 是否干净（有残留改动 → 警告，提示先提交或处理）

用法：python tools/integrity_check.py [--json]
退出码：0 = 干净；1 = 有 MISSING（须先恢复）；2 = 仅警告
"""

import json
import subprocess
import sys
from pathlib import Path


def main() -> int:
    tracked = subprocess.run(
        ["git", "ls-tree", "-r", "--name-only", "HEAD"],
        capture_output=True, text=True, check=True).stdout.splitlines()
    missing = []
    for f in tracked:
        p = Path(f)
        try:
            if not p.exists():
                missing.append(f)
        except OSError:
            missing.append(f)

    qa = Path("docs/Refactor/archive/2026-quality-audit")
    qa_count = sum(1 for x in qa.rglob("*.md")) if qa.exists() else 0

    dirty = subprocess.run(
        ["git", "status", "--porcelain"],
        capture_output=True, text=True, check=True).stdout.strip().splitlines()

    result = {
        "tracked_files": len(tracked),
        "missing": missing,
        "quality_audit_archive_md": qa_count,
        "archive_warning": qa_count < 150,
        "dirty_paths": len(dirty),
    }
    if "--json" in sys.argv:
        print(json.dumps(result, ensure_ascii=False, indent=1))
    else:
        print(f"tracked={result['tracked_files']} missing={len(missing)} "
              f"qa_archive_md={qa_count} dirty={len(dirty)}")

    if missing:
        print("\nFAIL: 以下跟踪文件在工作树中消失（恢复协议："
              "git checkout HEAD -- <路径>，并检查 OneDrive/杀毒软件）：")
        for m in missing[:30]:
            print("  -", m)
        return 1
    if result["archive_warning"]:
        print(f"WARN: 质量审计归档仅 {qa_count} 个 md（预期约 196），请核对。")
    if dirty:
        print(f"WARN: 有 {len(dirty)} 个未提交改动。")
    return 2 if (result["archive_warning"] or dirty) else 0


if __name__ == "__main__":
    sys.exit(main())
