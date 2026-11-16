#!/usr/bin/env python3
"""
治理 7.容器与微服务 与 8.网络系统 的编号冲突与深度违规。
运行前请确保仓库无未提交冲突；本脚本仅做 git mv / 内容替换 / README 更新。
"""

import os
import re
import subprocess
import sys
from pathlib import Path
from urllib.parse import quote

REPO_ROOT = Path(__file__).resolve().parent.parent

# 受保护、禁止修改的路径
PROTECTED_PATHS = [
    "research/2026-alignment-plan.md",
    "validation/",
    "docs/Refactor/cleanup-queue.md",
    "8.网络系统/8.1 知识梳理/",
]

# 归档目录
ARCHIVE_DIR = REPO_ROOT / "docs/Refactor/archive/2026-phase0/domain78-renumber"


def is_protected(path: Path) -> bool:
    rel = path.relative_to(REPO_ROOT).as_posix()
    for p in PROTECTED_PATHS:
        if rel == p or rel.startswith(p.rstrip("/") + "/"):
            return True
    return False


def git_mv(src: Path, dst: Path) -> None:
    rel_src = src.relative_to(REPO_ROOT).as_posix()
    rel_dst = dst.relative_to(REPO_ROOT).as_posix()
    subprocess.run(["git", "mv", rel_src, rel_dst], cwd=REPO_ROOT, check=True)


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def write_text(path: Path, content: str) -> None:
    path.write_text(content, encoding="utf-8")


# ---------------------------------------------------------------------------
# 1. 重命名计划
# ---------------------------------------------------------------------------

def plan():
    moves = []

    # ---- 7.0 国际标准映射 ----
    d7_0 = REPO_ROOT / "7.容器与微服务/7.0 国际标准映射"
    moves.append((d7_0 / "7.0.1 术语标准化对照表.md", d7_0 / "7.0.5 术语标准化对照表.md"))
    moves.append((d7_0 / "7.0.2 文档格式标准.md", d7_0 / "7.0.6 文档格式标准.md"))
    moves.append((d7_0 / "7.0.3 引用规范标准.md", d7_0 / "7.0.7 引用规范标准.md"))

    # ---- 7.5 多表征 ----
    d7_5 = REPO_ROOT / "7.容器与微服务/7.5 多表征"
    moves.append((d7_5 / "7.5.1 架构对比表.md", d7_5 / "7.5.4 架构对比表.md"))
    moves.append((d7_5 / "7.5.2 流程图.md", d7_5 / "7.5.5 流程图.md"))
    moves.append((d7_5 / "7.5.3 多角度表达.md", d7_5 / "7.5.6 多角度表达.md"))

    # ---- 7.6 形式语义 ----
    d7_6 = REPO_ROOT / "7.容器与微服务/7.6 形式语义"
    moves.append((d7_6 / "7.6.1 服务语义.md", d7_6 / "7.6.4 服务语义.md"))
    moves.append((d7_6 / "7.6.2 边缘计算集成.md", d7_6 / "7.6.5 边缘计算集成.md"))
    moves.append((d7_6 / "7.6.3 量子计算准备.md", d7_6 / "7.6.6 量子计算准备.md"))

    # ---- 8.3 形式化结构 ----
    d8_3 = REPO_ROOT / "8.网络系统/8.3 形式化结构"
    moves.append((d8_3 / "8.3.6 结构部分小结与批判.md", d8_3 / "8.3.7 结构部分小结与批判.md"))
    moves.append((d8_3 / "8.3.7 结构知识图谱.md", d8_3 / "8.3.8 结构知识图谱.md"))

    # ---- 8.4 形式化证明 ----
    d8_4 = REPO_ROOT / "8.网络系统/8.4 形式化证明"
    moves.append((d8_4 / "8.4.7 证明部分小结与批判.md", d8_4 / "8.4.8 证明部分小结与批判.md"))
    moves.append((d8_4 / "8.4.8 证明与社会-伦理的关系.md", d8_4 / "8.4.9 证明与社会-伦理的关系.md"))
    moves.append((d8_4 / "8.4.8 证明知识图谱.md", d8_4 / "8.4.10 证明知识图谱.md"))

    # ---- 8.5 多表征 ----
    d8_5 = REPO_ROOT / "8.网络系统/8.5 多表征"
    moves.append((d8_5 / "8.5.5 图形化模型.md", d8_5 / "8.5.9 图形化模型.md"))
    moves.append((d8_5 / "8.5.6 表格与数据结构.md", d8_5 / "8.5.10 表格与数据结构.md"))
    moves.append((d8_5 / "8.5.7 多模态与跨学科表征.md", d8_5 / "8.5.11 多模态与跨学科表征.md"))
    moves.append((d8_5 / "8.5.7 多表征小结与批判.md", d8_5 / "8.5.12 多表征小结与批判.md"))
    moves.append((d8_5 / "8.5.7 网络系统多模态表达与未来展望.md", d8_5 / "8.5.13 网络系统多模态表达与未来展望.md"))
    moves.append((d8_5 / "8.5.8 多表征知识图谱.md", d8_5 / "8.5.14 多表征知识图谱.md"))

    # ---- 8.6 形式语义 ----
    d8_6 = REPO_ROOT / "8.网络系统/8.6 形式语义"
    moves.append((d8_6 / "8.6.1 协议语义.md", d8_6 / "8.6.12 协议语义.md"))
    moves.append((d8_6 / "8.6.2 数据流语义.md", d8_6 / "8.6.13 数据流语义.md"))
    moves.append((d8_6 / "8.6.2 语义模型.md", d8_6 / "8.6.14 语义模型.md"))
    moves.append((d8_6 / "8.6.3 语义分析方法.md", d8_6 / "8.6.15 语义分析方法.md"))
    moves.append((d8_6 / "8.6.4 语义与结构-证明的关系.md", d8_6 / "8.6.16 语义与结构-证明的关系.md"))
    moves.append((d8_6 / "8.6.5 语义等价性与互操作性.md", d8_6 / "8.6.17 语义等价性与互操作性.md"))
    moves.append((d8_6 / "8.6.6 语义安全性与伦理问题.md", d8_6 / "8.6.18 语义安全性与伦理问题.md"))
    moves.append((d8_6 / "8.6.7 语义部分小结与批判.md", d8_6 / "8.6.19 语义部分小结与批判.md"))
    moves.append((d8_6 / "8.6.8 语义知识图谱.md", d8_6 / "8.6.20 语义知识图谱.md"))

    # ---- 8.7 系统运行时语义 ----
    d8_7 = REPO_ROOT / "8.网络系统/8.7 系统运行时语义"
    moves.append((d8_7 / "8.7.1 状态转移.md", d8_7 / "8.7.9 状态转移.md"))
    moves.append((d8_7 / "8.7.2 异常处理.md", d8_7 / "8.7.10 异常处理.md"))
    moves.append((d8_7 / "8.7.3 运行时监控.md", d8_7 / "8.7.11 运行时监控.md"))
    moves.append((d8_7 / "8.7.4 典型异常与应对.md", d8_7 / "8.7.12 典型异常与应对.md"))
    moves.append((d8_7 / "8.7.5 运行时动态与演化.md", d8_7 / "8.7.13 运行时动态与演化.md"))
    moves.append((d8_7 / "8.7.6 未来趋势与挑战.md", d8_7 / "8.7.14 未来趋势与挑战.md"))
    moves.append((d8_7 / "8.7.7 运行时语义的跨界应用.md", d8_7 / "8.7.15 运行时语义的跨界应用.md"))
    moves.append((d8_7 / "8.7.8 运行时语义知识图谱.md", d8_7 / "8.7.16 运行时语义知识图谱.md"))

    # ---- 8.8 综合专题与前沿展望 ----
    d8_8 = REPO_ROOT / "8.网络系统/8.8 综合专题与前沿展望"
    moves.append((d8_8 / "8.8.1 网络系统的跨域集成与协同机制.md", d8_8 / "8.8.49 网络系统的跨域集成与协同机制.md"))
    moves.append((d8_8 / "8.8.2 网络系统的智能化与自主演化.md", d8_8 / "8.8.50 网络系统的智能化与自主演化.md"))
    moves.append((d8_8 / "8.8.3 网络系统的安全治理与多方协作.md", d8_8 / "8.8.51 网络系统的安全治理与多方协作.md"))
    moves.append((d8_8 / "8.8.4 网络系统的伦理挑战与社会影响.md", d8_8 / "8.8.52 网络系统的伦理挑战与社会影响.md"))
    moves.append((d8_8 / "8.8.5 网络系统的未来趋势与前沿展望.md", d8_8 / "8.8.53 网络系统的未来趋势与前沿展望.md"))

    return moves


# ---------------------------------------------------------------------------
# 2. 执行 git mv
# ---------------------------------------------------------------------------

def execute_moves(moves):
    print(f"[INFO] 执行 {len(moves)} 次 git mv ...")
    for src, dst in moves:
        if not src.exists():
            print(f"[WARN] 源文件不存在，跳过: {src}")
            continue
        if dst.exists():
            print(f"[WARN] 目标文件已存在，跳过: {dst}")
            continue
        git_mv(src, dst)
    print("[INFO] git mv 完成")


# ---------------------------------------------------------------------------
# 3. 7.8 深度违规合并
# ---------------------------------------------------------------------------

def merge_7_8():
    d = REPO_ROOT / "7.容器与微服务/7.8 形式语义与递归语义分析"
    parent = d / "7.8.2.1 FSM建模与验证实践.md"
    children = [
        d / "7.8.2.1.1 CTL-LTL性质与熔断验证.md",
        d / "7.8.2.1.2 SPIN模型检测实践.md",
        d / "7.8.2.1.3 UPPAAL实时模型检测.md",
        d / "7.8.2.1.4 PRISM概率模型检测.md",
    ]

    if not parent.exists():
        print("[ERROR] 7.8 父文件不存在")
        return

    parent_content = read_text(parent)
    # 去掉父文件末尾可能的空行，保留一个换行
    parent_content = parent_content.rstrip() + "\n\n"

    merged_note = (
        "\n---\n\n"
        "> **Phase 0 治理合并说明**：以下四个原深度为 6 的子文件（7.8.2.1.1–7.8.2.1.4）"
        "已按内容并入本文件作为二级章节，原文件归档于 `docs/Refactor/archive/2026-phase0/domain78-renumber/`。"
        "合并后本文件最大编号深度恢复为 5，符合内容治理规则。\n\n"
    )
    parent_content += merged_note

    archived = []
    for child in children:
        if not child.exists():
            print(f"[WARN] 子文件不存在: {child}")
            continue
        content = read_text(child)
        title, body = split_title_and_body(content)
        # 移除子文件自身的 TOC
        body = remove_toc(body)
        # 标题升级：子文件 H1 → 父文件 H2，其余 +1
        body = bump_headers(body, 1)
        section = f"## {title}\n\n{body.lstrip()}\n\n"
        parent_content += section

        # 归档
        archive_path = ARCHIVE_DIR / child.relative_to(REPO_ROOT)
        archive_path.parent.mkdir(parents=True, exist_ok=True)
        git_mv(child, archive_path)
        archived.append(child.name)

    write_text(parent, parent_content)
    print(f"[INFO] 7.8 合并完成，归档: {archived}")


def split_title_and_body(content: str):
    """返回 (标题文本, 剩余内容)。标题为第一个 # 行。"""
    lines = content.splitlines()
    title = ""
    body_lines = []
    found = False
    for line in lines:
        if not found and line.startswith("# "):
            title = line[2:].strip()
            found = True
            continue
        body_lines.append(line)
    return title, "\n".join(body_lines)


def remove_toc(content: str) -> str:
    """移除 <!-- TOC START --> ... <!-- TOC END --> 块。"""
    pattern = re.compile(r"<!--\s*TOC\s*START\s*-->.*?<!--\s*TOC\s*END\s*-->", re.DOTALL)
    return pattern.sub("", content)


def bump_headers(content: str, levels: int) -> str:
    """将 markdown 标题提升/降低指定级数（正数=加 #，即层级更深）。不在代码块内处理。"""
    lines = content.splitlines()
    in_code = False
    result = []
    for line in lines:
        stripped = line.lstrip()
        if stripped.startswith("```"):
            in_code = not in_code
        if not in_code and re.match(r"^#{1,6}\s+", line):
            result.append("#" * levels + line)
        else:
            result.append(line)
    return "\n".join(result)


# ---------------------------------------------------------------------------
# 4. 内容自洽：H1 / 自引用 / 锚点
# ---------------------------------------------------------------------------

def update_file_headers_and_refs(moves):
    """对每个移动后的文件，更新 H1 标题，并做旧编号→新编号的文本替换。"""
    old_to_new = {}
    for src, dst in moves:
        old_name = src.name
        new_name = dst.name
        old_to_new[old_name] = new_name
        # 编号映射
        old_num = extract_number(old_name)
        new_num = extract_number(new_name)
        if old_num and new_num:
            old_to_new[old_num] = new_num

    # 7.8 子文件已归档，但其旧编号仍需全局替换
    d78 = REPO_ROOT / "7.容器与微服务/7.8 形式语义与递归语义分析"
    old_to_new["7.8.2.1.1 CTL-LTL性质与熔断验证.md"] = "7.8.2.1 FSM建模与验证实践.md"
    old_to_new["7.8.2.1.2 SPIN模型检测实践.md"] = "7.8.2.1 FSM建模与验证实践.md"
    old_to_new["7.8.2.1.3 UPPAAL实时模型检测.md"] = "7.8.2.1 FSM建模与验证实践.md"
    old_to_new["7.8.2.1.4 PRISM概率模型检测.md"] = "7.8.2.1 FSM建模与验证实践.md"
    for old_n, new_n in [
        ("7.8.2.1.1", "7.8.2.1"),
        ("7.8.2.1.2", "7.8.2.1"),
        ("7.8.2.1.3", "7.8.2.1"),
        ("7.8.2.1.4", "7.8.2.1"),
    ]:
        old_to_new[old_n] = new_n

    # 收集所有需要扫描的 markdown 文件
    md_files = list(REPO_ROOT.rglob("*.md"))
    for path in md_files:
        if is_protected(path):
            continue
        content = read_text(path)
        new_content = replace_old_refs(content, old_to_new)
        # 如果这是被移动的文件，确保 H1 与文件名一致
        rel_path = path.relative_to(REPO_ROOT)
        for src, dst in moves:
            if path == dst:
                new_content = sync_h1_to_filename(new_content, dst.name)
                break
        # 父文件也更新 H1（保持不变即可）
        if path == d78 / "7.8.2.1 FSM建模与验证实践.md":
            new_content = sync_h1_to_filename(new_content, "7.8.2.1 FSM建模与验证实践.md")
        if new_content != content:
            write_text(path, new_content)
            print(f"[INFO] 更新内容: {rel_path}")


def extract_number(filename: str) -> str:
    m = re.match(r"(\d+\.\d+(?:\.\d+)*)", filename)
    return m.group(1) if m else ""


def sync_h1_to_filename(content: str, filename: str) -> str:
    """将文件的第一个 # 标题改为文件名去掉 .md 后的文本。"""
    title = filename.replace(".md", "")
    lines = content.splitlines()
    for i, line in enumerate(lines):
        if line.startswith("# "):
            lines[i] = f"# {title}"
            break
    return "\n".join(lines)


def replace_old_refs(content: str, old_to_new: dict) -> str:
    """替换内容中的旧文件名/旧编号。使用词边界保护编号，避免误改 1.8.x 等。"""
    # 按长度降序，避免短编号先替换
    items = sorted(old_to_new.items(), key=lambda x: len(x[0]), reverse=True)
    for old, new in items:
        if old.endswith(".md"):
            # 文件名替换：支持原文件名（未编码）与 URL 编码形式
            encoded_old = quote(old, safe="/")
            encoded_new = quote(new, safe="/")
            content = content.replace(old, new)
            if encoded_old != old:
                content = content.replace(encoded_old, encoded_new)
        else:
            # 编号替换：使用词边界，仅替换形如 7.8.2.1.1 的独立编号
            pattern = re.compile(r"\b" + re.escape(old) + r"\b")
            content = pattern.sub(new, content)
    return content


# ---------------------------------------------------------------------------
# 5. README 目录结构更新
# ---------------------------------------------------------------------------

def update_readmes():
    readme_dirs = [
        REPO_ROOT / "7.容器与微服务/7.0 国际标准映射",
        REPO_ROOT / "7.容器与微服务/7.5 多表征",
        REPO_ROOT / "7.容器与微服务/7.6 形式语义",
        REPO_ROOT / "7.容器与微服务/7.8 形式语义与递归语义分析",
        REPO_ROOT / "8.网络系统/8.3 形式化结构",
        REPO_ROOT / "8.网络系统/8.4 形式化证明",
        REPO_ROOT / "8.网络系统/8.5 多表征",
        REPO_ROOT / "8.网络系统/8.6 形式语义",
        REPO_ROOT / "8.网络系统/8.7 系统运行时语义",
        REPO_ROOT / "8.网络系统/8.8 综合专题与前沿展望",
    ]
    for d in readme_dirs:
        readme = d / "README.md"
        if not readme.exists():
            continue
        content = read_text(readme)
        new_content = refresh_directory_structure(content, d)
        if new_content != content:
            write_text(readme, new_content)
            print(f"[INFO] 更新 README: {readme.relative_to(REPO_ROOT)}")

    # 7.8 目录索引文件
    idx = REPO_ROOT / "7.容器与微服务/7.8 形式语义与递归语义分析/7.8 形式语义与递归语义分析目录索引.md"
    if idx.exists():
        content = read_text(idx)
        new_content = refresh_7_8_index(content)
        if new_content != content:
            write_text(idx, new_content)
            print(f"[INFO] 更新目录索引: {idx.relative_to(REPO_ROOT)}")


def refresh_directory_structure(content: str, directory: Path) -> str:
    """替换 README 中 `## 目录结构` 之后到下一个 ## 之前的内容为当前文件列表。"""
    files = sorted([f for f in directory.iterdir() if f.is_file() and f.name.endswith(".md") and f.name != "README.md"])
    lines = [f"- **{f.name.replace('.md', '')}**" for f in files]
    new_section = "## 目录结构\n\n" + "\n".join(lines) + "\n\n"
    pattern = re.compile(r"(## 目录结构\n\n).*?(?=\n## |\n---|$)", re.DOTALL)
    return pattern.sub(new_section, content, count=1)


def refresh_7_8_index(content: str) -> str:
    """7.8 目录索引：简洁列出当前合法文件，并说明 7.8.2.1.x 已合并。"""
    d = REPO_ROOT / "7.容器与微服务/7.8 形式语义与递归语义分析"
    files = sorted([f for f in d.iterdir() if f.is_file() and f.name.endswith(".md")])
    lines = ["# 7.8 形式语义与递归语义分析 目录索引", "",
             "> 2026-07-02 Phase 0 清理后，原深度 > 5 的递归文件已合并为以下父文件。"
             "原 7.8.2.1.1–7.8.2.1.4 四个文件已作为 `7.8.2.1 FSM建模与验证实践.md` 的二级章节并入，"
             "原文件归档于 `docs/Refactor/archive/2026-phase0/domain78-renumber/`。", ""]
    for f in files:
        name = f.name.replace(".md", "")
        if " " in name:
            encoded = quote(f.name, safe="/")
            lines.append(f"- [{name}]({encoded})")
        else:
            lines.append(f"- {name}")
    lines.append("")
    lines.append("---")
    lines.append("")
    lines.append("> 本目录索引已按 Phase 0 治理规则（最大前缀深度 ≤ 5）更新，"
                 "后续新增子主题需遵守该规则。")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# 6. docs/toc.md 更新
# ---------------------------------------------------------------------------

def update_toc(moves):
    toc = REPO_ROOT / "docs/toc.md"
    if not toc.exists():
        return
    content = read_text(toc)
    old_to_new = {}
    for src, dst in moves:
        old_to_new[src.name] = dst.name
    # 7.8 子文件在 toc 中可能没有链接，但安全起见映射到父文件
    d78 = REPO_ROOT / "7.容器与微服务/7.8 形式语义与递归语义分析"
    for child in [
        "7.8.2.1.1 CTL-LTL性质与熔断验证.md",
        "7.8.2.1.2 SPIN模型检测实践.md",
        "7.8.2.1.3 UPPAAL实时模型检测.md",
        "7.8.2.1.4 PRISM概率模型检测.md",
    ]:
        old_to_new[child] = "7.8.2.1 FSM建模与验证实践.md"

    new_content = content
    for old_name, new_name in old_to_new.items():
        encoded_old = quote(old_name, safe="/")
        encoded_new = quote(new_name, safe="/")
        new_content = new_content.replace(encoded_old, encoded_new)
        # 若存在未编码形式也替换
        new_content = new_content.replace(old_name, new_name)

    if new_content != content:
        write_text(toc, new_content)
        print("[INFO] 更新 docs/toc.md")


# ---------------------------------------------------------------------------
# 7. 验证
# ---------------------------------------------------------------------------

def verify():
    print("\n[INFO] 开始验证...")
    errors = []

    # 检查目标目录无编号冲突
    check_dirs = [
        REPO_ROOT / "7.容器与微服务/7.0 国际标准映射",
        REPO_ROOT / "7.容器与微服务/7.5 多表征",
        REPO_ROOT / "7.容器与微服务/7.6 形式语义",
        REPO_ROOT / "7.容器与微服务/7.8 形式语义与递归语义分析",
        REPO_ROOT / "8.网络系统/8.3 形式化结构",
        REPO_ROOT / "8.网络系统/8.4 形式化证明",
        REPO_ROOT / "8.网络系统/8.5 多表征",
        REPO_ROOT / "8.网络系统/8.6 形式语义",
        REPO_ROOT / "8.网络系统/8.7 系统运行时语义",
        REPO_ROOT / "8.网络系统/8.8 综合专题与前沿展望",
    ]
    for d in check_dirs:
        nums = {}
        for f in d.iterdir():
            if f.is_file() and f.name.endswith(".md") and f.name != "README.md":
                num = extract_number(f.name)
                if num in nums:
                    errors.append(f"编号冲突 {d.name}: {num} 出现在 {nums[num].name} 与 {f.name}")
                else:
                    nums[num] = f

    # 检查 8.8.25-48 文件仍然存在
    d8_8 = REPO_ROOT / "8.网络系统/8.8 综合专题与前沿展望"
    for i in range(25, 49):
        found = False
        for f in d8_8.iterdir():
            if f.is_file() and f.name.startswith(f"8.8.{i} "):
                found = True
                break
        if not found:
            errors.append(f"8.8.{i} 文件缺失（toc.md 硬约束）")

    # 检查 toc.md 中 8.8.25-48 链接目标存在
    toc = REPO_ROOT / "docs/toc.md"
    toc_content = read_text(toc)
    for i in range(25, 49):
        pattern = f"8.8%20%E7%BB%BC%E5%90%88%E4%B8%93%E9%A2%98%E4%B8%8E%E5%89%8D%E6%B2%BF%E5%B1%95%E6%9C%9B/8.8.{i}%20"
        # 简化：检查是否有任意链接指向 8.8.i
        if f"8.8.{i}" not in toc_content:
            errors.append(f"toc.md 中缺少 8.8.{i} 链接")

    # 检查 7.8 深度 ≤ 5
    d78 = REPO_ROOT / "7.容器与微服务/7.8 形式语义与递归语义分析"
    for f in d78.rglob("*.md"):
        num = extract_number(f.name)
        if num and num.count(".") > 4:
            errors.append(f"深度违规: {f.relative_to(REPO_ROOT)} 编号 {num}")

    if errors:
        print("[FAIL] 验证发现错误:")
        for e in errors:
            print(f"  - {e}")
        return False
    print("[PASS] 验证通过：编号唯一、8.8.25-48 保留、7.8 深度 ≤ 5")
    return True


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

def main():
    moves = plan()
    execute_moves(moves)
    merge_7_8()
    update_file_headers_and_refs(moves)
    update_readmes()
    update_toc(moves)
    ok = verify()
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
