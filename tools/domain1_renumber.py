#!/usr/bin/env python3
"""Governance renumbering for 1.系统理论 subdirectories 1.3–1.7.

This script:
1. git-mv files to new unique sequential numbers.
2. Updates H1 titles, self-reference numbers, and TOC anchors inside moved files.
3. Updates the per-directory README.md indexes.
4. Fixes cross-file links in 1.系统理论/README.md.
"""

import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(".")

def run_git_mv(src, dst):
    # Run from repo root with relative paths.
    subprocess.run(["git", "mv", str(src), str(dst)], check=True)

def anchor_no_dots(num):
    return num.replace(".", "")

def update_file_content(path, old_num, new_num, title_without_num=None):
    """Update H1, self-references and TOC anchors for a single renumbered file."""
    text = path.read_text(encoding="utf-8")
    old_nd = anchor_no_dots(old_num)
    new_nd = anchor_no_dots(new_num)

    # 1. H1 title: if line starts with "# {old_num} ", replace the number.
    h1_pattern = re.compile(rf"^(# )({re.escape(old_num)})( .*)$", re.MULTILINE)
    if h1_pattern.search(text):
        text = h1_pattern.sub(rf"\g<1>{new_num}\g<3>", text)
    elif title_without_num:
        # Prepend new number to the existing H1 title.
        title_re = re.compile(rf"^(# )({re.escape(title_without_num)}.*)$", re.MULTILINE)
        text = title_re.sub(rf"\g<1>{new_num} \g<2>", text)
    else:
        # Fallback: prepend new number to the first H1 line.
        text = re.sub(r"^(# )(.+)$", rf"\g<1>{new_num} \g<2>", text, count=1, flags=re.MULTILINE)

    # 2. TOC / self-reference anchors: (](#{old_num_without_dots}...)
    text = text.replace(f"](#{old_nd}-", f"](#{new_nd}-")
    text = text.replace(f"](#{old_nd})", f"](#{new_nd})")

    # 3. Plain number self-references with word boundaries, but only exact old_num.
    text = re.sub(rf"\b{re.escape(old_num)}\b", new_num, text)

    path.write_text(text, encoding="utf-8")


def build_mapping(dir_name, ordered_tuples):
    """ordered_tuples: list of (old_basename, new_basename, title_without_num or None)."""
    mappings = []
    for old_bn, new_bn, title_no_num in ordered_tuples:
        src = ROOT / "1.系统理论" / dir_name / old_bn
        dst = ROOT / "1.系统理论" / dir_name / new_bn
        old_num = old_bn.split()[0]
        new_num = new_bn.split()[0]
        mappings.append((src, dst, old_num, new_num, title_no_num))
    return mappings


def do_renames_and_updates(mappings):
    for src, dst, old_num, new_num, title_no_num in mappings:
        if src != dst:
            run_git_mv(src, dst)
        # Even if path unchanged, ensure content is consistent.
        update_file_content(dst, old_num, new_num, title_no_num)


def update_directory_readme(dir_name, new_files_info):
    """Rewrite the directory README index list."""
    readme_path = ROOT / "1.系统理论" / dir_name / "README.md"
    text = readme_path.read_text(encoding="utf-8")

    # Build new index block.
    lines = ["## 目录结构", ""]
    for num, title, desc in new_files_info:
        lines.append(f"- **{num} {title}** - {desc}")
    lines.append("")
    new_block = "\n".join(lines)

    # Replace existing 目录结构 section.
    pattern = re.compile(r"## 目录结构\n.*?(?=\n## |\Z)", re.DOTALL)
    if pattern.search(text):
        text = pattern.sub(new_block, text)
    else:
        # Insert after first heading if no section found.
        text = text + "\n" + new_block

    readme_path.write_text(text, encoding="utf-8")


def update_domain_readme(renumbered_targets):
    """Fix cross-file links in 1.系统理论/README.md."""
    path = ROOT / "1.系统理论" / "README.md"
    text = path.read_text(encoding="utf-8")

    for dir_name, old_bn, new_bn in renumbered_targets:
        old_url = f"./{dir_name.replace(' ', '%20')}/{old_bn.replace(' ', '%20')}"
        new_url = f"./{dir_name.replace(' ', '%20')}/{new_bn.replace(' ', '%20')}"
        text = text.replace(old_url, new_url)

    path.write_text(text, encoding="utf-8")


# ---------------------------------------------------------------------------
# 1.3 形式化结构
# ---------------------------------------------------------------------------
map_13 = build_mapping("1.3 形式化结构", [
    ("1.3.1 形式化定义.md", "1.3.1 形式化定义.md", "形式化定义"),
    ("1.3.1 数学基础.md", "1.3.2 数学基础.md", "数学基础 / Mathematical Foundations"),
    ("1.3.2 形式化语言.md", "1.3.3 形式化语言.md", "形式化语言 / Formal Language"),
    ("1.3.2 结构模型.md", "1.3.4 结构模型.md", "结构模型"),
    ("1.3.3 公理化体系.md", "1.3.5 公理化体系.md", "公理化体系 / Axiomatic System"),
    ("1.3.3 结构图与表.md", "1.3.6 结构图与表.md", "结构图与表"),
    ("1.3.4 完备性分析.md", "1.3.7 完备性分析.md", "完备性分析 / Completeness Analysis"),
    ("1.3.4 高级数学基础.md", "1.3.8 高级数学基础.md", "高级数学基础"),
    ("1.3.5 前沿数学理论.md", "1.3.9 前沿数学理论.md", "前沿数学理论"),
    ("1.3.5 语义模型构建.md", "1.3.10 语义模型构建.md", "系统理论语义模型构建 / Semantic Model Construction for System Theory"),
])

readme_13 = [
    ("1.3.1", "形式化定义", "系统理论的形式化数学定义"),
    ("1.3.2", "数学基础", "系统理论的数学基础"),
    ("1.3.3", "形式化语言", "系统理论的形式化语言"),
    ("1.3.4", "结构模型", "系统的结构模型和表示"),
    ("1.3.5", "公理化体系", "系统理论的公理化体系"),
    ("1.3.6", "结构图与表", "系统结构的图形和表格表示"),
    ("1.3.7", "完备性分析", "系统理论形式化体系的完备性分析"),
    ("1.3.8", "高级数学基础", "系统理论的高级数学基础"),
    ("1.3.9", "前沿数学理论", "系统理论的前沿数学理论"),
    ("1.3.10", "语义模型构建", "系统理论的语义模型构建"),
]

# ---------------------------------------------------------------------------
# 1.4 形式化证明
# ---------------------------------------------------------------------------
map_14 = build_mapping("1.4 形式化证明", [
    ("1.4.1 命题与定理.md", "1.4.1 命题与定理.md", "系统理论命题与定理 / Propositions and Theorems in System Theory"),
    ("1.4.2 证明方法建立.md", "1.4.2 证明方法建立.md", "证明方法建立 / Proof Method Establishment"),
    ("1.4.2 证明过程.md", "1.4.3 证明过程.md", "证明过程"),
    ("1.4.3 定理证明.md", "1.4.4 定理证明.md", "定理证明 / Theorem Proof"),
    ("1.4.3 证明符号与规范.md", "1.4.5 证明符号与规范.md", "证明符号与规范"),
    ("1.4.4 证明验证.md", "1.4.6 证明验证.md", "证明验证 / Proof Verification"),
    ("1.4.5 证明优化.md", "1.4.7 证明优化.md", "证明优化 / Proof Optimization"),
    ("1.4.6 证明自动化.md", "1.4.8 证明自动化.md", "证明自动化 / Proof Automation"),
    ("1.4.7 逻辑完备性证明.md", "1.4.9 逻辑完备性证明.md", "逻辑完备性证明 / Logical Completeness Proof"),
    ("1.4.8 严格证明理论.md", "1.4.10 严格证明理论.md", "严格证明理论"),
    ("1.4.8 公理独立性验证.md", "1.4.11 公理独立性验证.md", "公理独立性验证 / Axiom Independence Verification"),
    ("1.4.9 严格形式化证明体系.md", "1.4.12 严格形式化证明体系.md", "严格形式化证明体系"),
])

readme_14 = [
    ("1.4.1", "命题与定理", "系统理论的基本命题和定理体系"),
    ("1.4.2", "证明方法建立", "形式化证明方法的建立与分类"),
    ("1.4.3", "证明过程", "形式化证明的具体步骤和过程"),
    ("1.4.4", "定理证明", "系统理论核心定理的证明"),
    ("1.4.5", "证明符号与规范", "证明中使用的符号和规范"),
    ("1.4.6", "证明验证", "形式化证明的正确性验证"),
    ("1.4.7", "证明优化", "形式化证明的优化方法"),
    ("1.4.8", "证明自动化", "形式化证明的自动化技术"),
    ("1.4.9", "逻辑完备性证明", "系统理论逻辑完备性证明"),
    ("1.4.10", "严格证明理论", "系统理论的严格证明理论"),
    ("1.4.11", "公理独立性验证", "系统理论公理的独立性验证"),
    ("1.4.12", "严格形式化证明体系", "系统理论的严格形式化证明体系"),
]

# ---------------------------------------------------------------------------
# 1.5 多表征
# ---------------------------------------------------------------------------
map_15 = build_mapping("1.5 多表征", [
    ("1.5.1 概念图.md", "1.5.1 概念图.md", "概念图"),
    ("1.5.1 概念图构建.md", "1.5.2 概念图构建.md", "概念图构建 / Concept Map Construction"),
    ("1.5.2 形式化图表.md", "1.5.3 形式化图表.md", "形式化图表 / Formal Diagrams"),
    ("1.5.2 结构表.md", "1.5.4 结构表.md", "结构表"),
    ("1.5.3 数学符号.md", "1.5.5 数学符号.md", "数学符号"),
    ("1.5.3 可视化表征.md", "1.5.6 可视化表征.md", "可视化表征 / Visual Representation"),
    ("1.5.4 交互式显示.md", "1.5.7 交互式显示.md", "交互式显示 / Interactive Display"),
    ("1.5.5 多模态表征.md", "1.5.8 多模态表征.md", "多模态表征 / Multi-Modal Representation"),
    ("多表征案例与结构图递归补全.md", "1.5.9 多表征案例与结构图递归补全.md", "多表征案例与结构图递归补全"),
])

readme_15 = [
    ("1.5.1", "概念图", "系统理论概念和关系的图形化表示"),
    ("1.5.2", "概念图构建", "概念图构建方法与工具"),
    ("1.5.3", "形式化图表", "系统理论的形式化图表表示"),
    ("1.5.4", "结构表", "系统结构和数据的表格化表示"),
    ("1.5.5", "数学符号", "系统性质的数学符号表示"),
    ("1.5.6", "可视化表征", "系统理论的可视化表征方法"),
    ("1.5.7", "交互式显示", "系统理论知识的交互式显示"),
    ("1.5.8", "多模态表征", "系统理论的多模态表征方法"),
    ("1.5.9", "多表征案例与结构图递归补全", "多表征案例与结构图补全"),
]

# ---------------------------------------------------------------------------
# 1.6 形式语义
# ---------------------------------------------------------------------------
map_16 = build_mapping("1.6 形式语义", [
    ("1.6.1 语义定义.md", "1.6.1 语义定义.md", "语义定义 / Semantic Definition"),
    ("1.6.2 语义模型.md", "1.6.2 语义模型.md", "语义模型"),
    ("1.6.2 语义关系.md", "1.6.3 语义关系.md", "语义关系 / Semantic Relations"),
    ("1.6.3 语义分析方法.md", "1.6.4 语义分析方法.md", "语义分析方法"),
    ("1.6.3 语义验证.md", "1.6.5 语义验证.md", "语义验证 / Semantic Verification"),
    ("1.6.4 语义与结构-证明的关系.md", "1.6.6 语义与结构-证明的关系.md", "语义与结构-证明的关系"),
    ("1.6.5 递归语义分析与模型检验展望.md", "1.6.7 递归语义分析与模型检验展望.md", "递归语义分析与模型检验展望"),
    ("1.6.12 完整语义理论体系.md", "1.6.8 完整语义理论体系.md", "完整语义理论体系"),
    ("AI辅助与自动化递归补全.md", "1.6.9 AI辅助与自动化递归补全.md", "AI辅助与自动化递归补全"),
])

readme_16 = [
    ("1.6.1", "语义定义", "系统概念的形式语义定义"),
    ("1.6.2", "语义模型", "系统理论的语义模型"),
    ("1.6.3", "语义关系", "系统理论的语义关系"),
    ("1.6.4", "语义分析方法", "系统理论的语义分析方法"),
    ("1.6.5", "语义验证", "系统语义的正确性验证"),
    ("1.6.6", "语义与结构-证明的关系", "语义、结构与证明的关系"),
    ("1.6.7", "递归语义分析与模型检验展望", "递归语义分析与模型检验展望"),
    ("1.6.8", "完整语义理论体系", "系统理论的完整语义理论体系"),
    ("1.6.9", "AI辅助与自动化递归补全", "形式语义的AI辅助与自动化递归补全"),
]

# ---------------------------------------------------------------------------
# 1.7 递归展望与参考文献
# ---------------------------------------------------------------------------
map_17 = build_mapping("1.7 递归展望与参考文献", [
    ("1.7.1 未来发展趋势.md", "1.7.1 未来发展趋势.md", "未来发展趋势"),
    ("1.7.1 发展趋势预测.md", "1.7.2 发展趋势预测.md", "发展趋势预测 / Development Trend Prediction"),
    ("1.7.2 AI辅助与自动化.md", "1.7.3 AI辅助与自动化.md", "AI辅助与自动化"),
    ("1.7.2 研究前沿分析.md", "1.7.4 研究前沿分析.md", "研究前沿分析 / Research Frontier Analysis"),
    ("1.7.3 跨领域融合与创新.md", "1.7.5 跨领域融合与创新.md", "跨领域融合与创新"),
    ("1.7.3 参考文献体系.md", "1.7.6 参考文献体系.md", "参考文献体系 / Reference System"),
    ("1.7.4 批判分析.md", "1.7.7 批判分析.md", "批判分析"),
    ("1.7.4 引用关系建立.md", "1.7.8 引用关系建立.md", "引用关系建立 / Citation Relationship Establishment"),
    ("1.7.5 知识图谱构建.md", "1.7.9 知识图谱构建.md", "知识图谱构建 / Knowledge Graph Construction"),
])

readme_17 = [
    ("1.7.1", "未来发展趋势", "系统理论的未来发展方向和趋势"),
    ("1.7.2", "发展趋势预测", "系统理论发展趋势的预测方法"),
    ("1.7.3", "AI辅助与自动化", "AI技术在系统理论中的应用"),
    ("1.7.4", "研究前沿分析", "系统理论研究前沿分析"),
    ("1.7.5", "跨领域融合与创新", "系统理论与其他领域的融合"),
    ("1.7.6", "参考文献体系", "系统理论的参考文献体系"),
    ("1.7.7", "批判分析", "对系统理论的批判性分析和反思"),
    ("1.7.8", "引用关系建立", "系统理论的引用关系建立"),
    ("1.7.9", "知识图谱构建", "系统理论知识图谱构建"),
]

# Cross-file links in 1.系统理论/README.md that point to renumbered files.
# Format: (directory_name, old_basename, new_basename)
cross_links = [
    ("1.3 形式化结构", "1.3.1 形式化定义.md", "1.3.1 形式化定义.md"),  # unchanged but keep for completeness
    ("1.4 形式化证明", "1.4.1 命题与定理.md", "1.4.1 命题与定理.md"),
    ("1.5 多表征", "1.5.1 概念图.md", "1.5.1 概念图.md"),
    ("1.6 形式语义", "1.6.1 语义定义.md", "1.6.1 语义定义.md"),
]


def main():
    # 1. Renames + content updates
    do_renames_and_updates(map_13)
    do_renames_and_updates(map_14)
    do_renames_and_updates(map_15)
    do_renames_and_updates(map_16)
    do_renames_and_updates(map_17)

    # 2. README indexes
    update_directory_readme("1.3 形式化结构", readme_13)
    update_directory_readme("1.4 形式化证明", readme_14)
    update_directory_readme("1.5 多表征", readme_15)
    update_directory_readme("1.6 形式语义", readme_16)
    update_directory_readme("1.7 递归展望与参考文献", readme_17)

    # 3. Cross-file links
    update_domain_readme(cross_links)

    print("Domain 1.3–1.7 renumbering completed.")


if __name__ == "__main__":
    main()
