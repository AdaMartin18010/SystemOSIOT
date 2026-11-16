#!/usr/bin/env python3
"""SystemOSIOT 内容质量审计（2026-11 Phase Q）

对全库 Markdown 做实质密度分诊：
- 实质信号：引用（DOI/RFC/URL）、数学公式、mermaid/代码块、数据表、参考文献小节、标准组织关键词
- 模板惩罚：未填占位符（[定理名称] 类）、自指式证明提纲 bullet、规范说明+扩展方向模板对、重复目录、TODO 标记、
  「已形式化验证」类无工件支撑的声称（违反 content-governance-rules.md 第 4 条）

输出：
- research/2026-content-quality-audit.md   摘要报告（分类分布、维度矩阵、最差文件清单）
- validation/content-audit-detail.csv      逐文件明细

用法：python tools/content_quality_audit.py
"""

import csv
import re
from collections import defaultdict
from pathlib import Path

ROOT = Path(".")
ARCHIVE_MARK = "docs/Refactor/archive"
DETAIL_CSV = Path("validation/content-audit-detail.csv")
REPORT_MD = Path("research/2026-content-quality-audit.md")

CIT_RE = re.compile(r"(10\.\d{4,9}/[-._;()/:A-Za-z0-9]+|RFC\s?-?\s?\d{3,5}\b|https?://[^\s)>]+)", re.I)
MATH_RE = re.compile(r"(\$\$[^$]+\$\$|\$[^$\n]{1,120}\$|\\(frac|sum|prod|forall|exists|Rightarrow|Leftarrow|leq|geq|subset|models|vdash))",
                     re.MULTILINE)
STD_ORG_RE = re.compile(r"\b(POSIX|IEEE|IETF|ISO|IEC|3GPP|NIST|ETSI|ITU|ACM|USENIX|OMG|INCOSE|PCI|USB-IF|OASIS)\b")
PLACEHOLDER_RE = re.compile(r"[\[［【]([^\]］】]{1,18})[\]］】]")
PH_KEYWORDS = ("名称", "定理", "引理", "步骤", "前提", "结论", "陈述", "证明", "内容", "标题",
               "方法", "算法", "问题", "性质", "结果", "数据", "类型", "框架", "模型", "系统",
               "技术", "工具", "协议", "结构", "功能", "模块", "章节", "部分")
PROOF_TMPL_RE = re.compile(r"^\s*[-*]\s+\*\*[^*]{2,24}(证明|性质|机制|策略|方法|步骤)\*\*[:：]\s*证明", re.MULTILINE)
TODO_RE = re.compile(r"待补充|待完善|待扩展|待定|TODO|TBD")
REFSEC_RE = re.compile(r"^#{1,3}\s.*(参考文献|References|延伸阅读|权威来源|来源链接)", re.MULTILINE)
DIRONLY_RE = re.compile(r"^#{1,3}\s*目录\s*$", re.MULTILINE)
FALSE_CLAIM_RE = re.compile(r"已(完成|通过)(了)?(形式化)?(验证|证明)|严格证明完毕|(TLC|模型检验|模型检测|定理证明器)(已)?(通过|完成)")


def count_placeholders(text: str) -> int:
    """统计未填占位符，但排除 Markdown 链接/图片的方括号文本（如 [系统](url)）。"""
    n = 0
    for m in PLACEHOLDER_RE.finditer(text):
        tail = text[m.end():m.end() + 1]
        if tail in ("(", "（", "["):
            continue
        if is_placeholder(m.group(1)):
            n += 1
    return n


def is_placeholder(inner: str) -> bool:
    s = inner.strip()
    if not (1 <= len(s) <= 18):
        return False
    return any(k in s for k in PH_KEYWORDS)


def audit_file(path: Path) -> dict:
    text = path.read_text(encoding="utf-8", errors="ignore")
    lines = text.splitlines()
    n = len(lines)

    cits = set(CIT_RE.findall(text))
    math = len(MATH_RE.findall(text))
    mermaid = text.count("```mermaid")
    code = max(0, len(re.findall(r"^```[A-Za-z][A-Za-z0-9]*\s*$", text, re.M)) - mermaid)
    tables = sum(1 for l in lines if l.strip().startswith("|"))
    # 占位符扫描需排除 mermaid 代码块（节点语法 A[标签] 会被误识为占位符）
    text_wo_mermaid = re.sub(r"```mermaid.*?```", "", text, flags=re.DOTALL)
    placeholders = count_placeholders(text_wo_mermaid)
    proof_tmpl = len(PROOF_TMPL_RE.findall(text))
    todos = len(TODO_RE.findall(text))
    toc_marks = text.count("<!-- TOC START -->")
    dir_sections = len(DIRONLY_RE.findall(text))
    dup_toc = (toc_marks >= 1 and dir_sections >= 1) or toc_marks >= 2
    refsec = bool(REFSEC_RE.search(text))
    false_claim = bool(FALSE_CLAIM_RE.search(text)) and "tools/" not in text
    std_orgs = len(set(STD_ORG_RE.findall(text)))

    sub = (min(20, 4 * len(cits)) + min(15, int(math * 1.5)) + min(10, 3 * mermaid)
           + min(8, tables // 15) + min(10, 2 * code) + min(8, int(std_orgs * 1.5))
           + (5 if refsec and len(cits) >= 3 else 0))
    pen = min(45, placeholders * 8 + proof_tmpl * 2 + todos * 4
              + (10 if ("规范说明" in text and "扩展方向" in text) else 0)
              + (8 if dup_toc else 0) + (15 if false_claim else 0))
    score = max(0, sub - pen)

    if score >= 20 or len(cits) >= 6:
        cls = "A-保留"
    elif score >= 10:
        cls = "B-待评审"
    else:
        cls = "C-归档候选"

    flags = []
    if placeholders:
        flags.append(f"占位符x{placeholders}")
    if proof_tmpl:
        flags.append(f"证明提纲x{proof_tmpl}")
    if dup_toc:
        flags.append("重复目录")
    if false_claim:
        flags.append("无工件形式化声称")
    if "规范说明" in text and "扩展方向" in text:
        flags.append("模板对")
    if todos:
        flags.append(f"TODOx{todos}")

    return {
        "path": str(path).replace("\\", "/"), "lines": n, "score": score, "class": cls,
        "citations": len(cits), "math": math, "mermaid": mermaid, "code": code,
        "tables": tables, "placeholders": placeholders, "proof_tmpl": proof_tmpl,
        "flags": ";".join(flags),
    }


def main() -> None:
    files = [p for p in ROOT.rglob("*.md")
             if ".git" not in p.parts and not p.is_symlink()
             and "tools/engines" not in str(p).replace("\\", "/")]
    live, archived = [], []
    for p in files:
        posix = str(p).replace("\\", "/")
        (archived if ARCHIVE_MARK in posix else live).append(p)

    rows = []
    skipped = []
    for p in sorted(live):
        try:
            rows.append(audit_file(p))
        except OSError:
            skipped.append(str(p).replace("\\", "/"))
    with DETAIL_CSV.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    def dim_key(r):
        parts = r["path"].split("/")
        domain = parts[0]
        dim = parts[1] if len(parts) > 2 else "(根)"
        return domain, dim

    agg = defaultdict(list)
    for r in rows:
        agg[dim_key(r)].append(r)

    n_a = sum(1 for r in rows if r["class"] == "A-保留")
    n_b = sum(1 for r in rows if r["class"] == "B-待评审")
    n_c = sum(1 for r in rows if r["class"] == "C-归档候选")

    worst = sorted(rows, key=lambda r: (r["score"], -r["lines"]))[:25]
    guns = [r for r in rows if "无工件形式化声称" in r["flags"]]
    ph_files = sorted((r for r in rows if r["placeholders"] >= 3),
                      key=lambda r: -r["placeholders"])[:15]

    L = []
    L.append("# SystemOSIOT 内容质量审计报告（2026-11-17）\n")
    L.append("> 方法：逐文件计算实质信号得分（引用/公式/图码表/参考文献/标准组织词）减去模板惩罚")
    L.append("> （占位符/自指证明提纲/模板对/重复目录/TODO/无工件形式化声称）。")
    L.append("> 明细见 `validation/content-audit-detail.csv`。本报告仅分诊，不执行处置。\n")
    L.append("## 1. 总量与分类\n")
    L.append(f"- 活库文件：{len(rows)}（另有归档区 {len(archived)} 个不参与分类；第三方工具包跳过 {len(skipped)} 个）")
    L.append(f"- **A-保留**：{n_a}（{n_a/len(rows)*100:.1f}%）　**B-待评审**：{n_b}（{n_b/len(rows)*100:.1f}%）　**C-归档候选**：{n_c}（{n_c/len(rows)*100:.1f}%）\n")
    L.append("## 2. 域×维度分类矩阵（C 占比 / 平均得分）\n")
    L.append("| 域 | 维度目录 | 文件数 | C占比 | 均分 |")
    L.append("|---|---|---|---|---|")
    for (dom, dim), rs in sorted(agg.items()):
        c = sum(1 for r in rs if r["class"] == "C-归档候选")
        avg = sum(r["score"] for r in rs) / len(rs)
        L.append(f"| {dom} | {dim} | {len(rs)} | {c/len(rs)*100:.0f}% | {avg:.1f} |")
    L.append("\n## 3. 最差 25 文件（得分升序）\n")
    L.append("| 文件 | 行数 | 得分 | 标记 |")
    L.append("|---|---|---|---|")
    for r in worst:
        L.append(f"| {r['path']} | {r['lines']} | {r['score']} | {r['flags'] or '-'} |")
    L.append("\n## 4. 冒烟项\n")
    L.append(f"### 4.1 无工件支撑的形式化声称（违反治理规则第 4 条）：{len(guns)} 个\n")
    for r in guns[:20]:
        L.append(f"- {r['path']}（{r['flags']}）")
    if len(guns) > 20:
        L.append(f"- …其余 {len(guns)-20} 个见 CSV")
    L.append(f"\n### 4.2 占位符 ≥3 的文件：{len(ph_files)} 个（Top）\n")
    for r in ph_files:
        L.append(f"- {r['path']}：占位符 x{r['placeholders']}")
    L.append("\n## 5. 与用户选项的映射建议\n")
    L.append("- **选项 1（审计瘦身）**：C 类直接归档；B 类抽审后定去留。")
    L.append("- **选项 2（骨架保留血肉重写）**：以各域 A 类中得分最高者为核心，每域每维度合并重写为一个深文件。")
    L.append("- **选项 3（形式化工件为核心）**：markdown 中的证明/验证一律指回 tools/ 工件；4.1 清单必须优先处理（删除声称或补工件）。")
    REPORT_MD.write_text("\n".join(L) + "\n", encoding="utf-8")
    print(f"live={len(rows)} A={n_a} B={n_b} C={n_c} archived={len(archived)}")
    print(f"report={REPORT_MD} csv={DETAIL_CSV}")


if __name__ == "__main__":
    main()
