# SystemOSIOT 项目指南（AGENTS.md）


<!-- TOC START -->

- [SystemOSIOT 项目指南（AGENTS.md）](#systemosiot-项目指南agentsmd)
  - [1. 项目定位](#1-项目定位)
  - [2. Agent 入口（按角色）](#2-agent-入口按角色)
  - [3. 铁律（与治理规则、hermes 手册一致）](#3-铁律与治理规则hermes-手册一致)
  - [4. 质量审计体系（2026-11 质量分诊后生效）](#4-质量审计体系2026-11-质量分诊后生效)
  - [5. 形式化工件与 CI](#5-形式化工件与-ci)
  - [6. 目录速览](#6-目录速览)
  - [7. 当前状态与已知风险（2026-11-17）](#7-当前状态与已知风险2026-11-17)

<!-- TOC END -->

> 本文件是**人类维护者与 AI agent（含 hermes）的共同入口**，与 `README.md`（对外介绍）、
> `docs/content-governance-rules.md`（治理规则）、`docs/hermes-runbook.md`（hermes 运行手册）
> 保持同步；任何机制变更须同时更新四处。

## 1. 项目定位

- **知识梳理/研究型知识库**（Knowledge Curation, not Engineering Build）：概念结构化、
  跨视角映射、形式化定义与证明、批判分析、国际标准对齐。
- 八大主题域：`1.系统理论` `2.操作系统` `3.物联网嵌入式系统` `4.分布式系统`
  `5.集群系统` `6.P2P系统` `7.容器与微服务` `8.网络系统`。
- 统一维度骨架：`X.0 国际标准映射`（对齐核心，最高保护级）· `X.1` 知识梳理 ·
  `X.2` 批判分析 · `X.3` 形式化结构 · `X.4` 形式化证明 · `X.5` 多表征 ·
  `X.6` 形式语义 · `X.7/X.8` 运行时语义与扩展专题。

## 2. Agent 入口（按角色）

| 角色 | 每轮先读 |
|---|---|
| hermes / 自动化 agent | `docs/hermes-runbook.md` → `states/hermes-state.json` → `states/journal.md` 末尾 → `states/task-queue.yaml` |
| 人类维护者 | 本文件 → `docs/Refactor/cleanup-queue.md`（治理日志）→ `research/2026-alignment-plan.md`（路线图） |

## 3. 铁律（与治理规则、hermes 手册一致）

1. **只移动不删除**：清理一律 `git mv` 到 `docs/Refactor/archive/<批次>/`；删除仅限保留期满的归档批次且须 journal 记录。
2. **不 `git push`**。commit 规范：`hermes(<task-id>): <摘要>` 或常规描述；一任务一提交。
3. **编号唯一、目录深度 ≤ 5**；文件名 = `编号 + 主题词`；禁止"子主题递归细化"式命名。
4. **形式化工件纪律**：Markdown 不得声称"已形式化验证/已通过模型检验"，除非 `tools/` 下存在
   对应可执行工件且本地或 CI 跑通（`.v/.thy/.lean/.tla/.als/.smt2/...`）。
5. **引用可核**：标准/论文须标全称、版本或年份、官方链接或 DOI、访问日期。
6. 影响 >20 个文件的操作：先写计划与回滚方式到 `states/journal.md`（或清理队列）再执行。

## 4. 质量审计体系（2026-11 质量分诊后生效）

```bash
python tools/content_quality_audit.py    # 全库实质密度分诊 → research/2026-content-quality-audit.md + validation/content-audit-detail.csv
python tools/quality_audit_apply.py      # 执行 C 类归档（含豁免；--dry-run 预览）
python tools/quality_audit_reconcile.py  # 双向对账/补归档/注记同步（--notes-only 只同步注记；--restore 手动恢复）
python tools/ci_quality_gate.py          # CI 质量门：非豁免 C=0 且编号深度≤5
python tools/integrity_check.py          # 每轮第一道闸：跟踪文件失踪/归档异常/脏树
python tools/toc_generator.py --all --apply . && python tools/toc_validate.py --all .   # 文件内 TOC 再生成与校验
```

**审计豁免清单（canonical，改这里须同步三个脚本）**：README（全库）、`research/`、`docs/`、
`states/`、`.vscode/`、`X.0 国际标准映射`（任意路径含此段）、`API文档标准.md`。
脚本内对应常量：`tools/ci_quality_gate.py: EX_PREFIX/EX_MARKS/EX_FILES`、
`tools/quality_audit_apply.py` 与 `tools/quality_audit_reconcile.py: EXEMPT_PREFIXES/EXEMPT_MARKS`。

**审计分级**：A-保留 / B-待评审 / C-归档候选（C 除豁免类外必须清零；B 由抽审标准裁决：
真占位符、无来源预测性内容、递归填充 → 归档）。

## 5. 形式化工件与 CI

- 工件目录 `tools/`：`lean-verification` `coq-verification` `isabelle-verification`
  `tla-specifications` `uppaal-models` `nusmv-models` `prism-models` `spin-models`
  `alloy-models` `smt-examples` `cvc5-examples`。
- 缺口登记：`validation/standard-compliance-mapping.yaml` 尾部 `dangling_artifact_register`；
  审计台账：`validation/formal-artifacts-gap-audit.md`。
- CI：`.github/workflows/toc-ci.yml`（TOC 一致性 + 内容质量门）、
  `formal-verification-gate.yml`（形式化工件验证）。
- pre-commit：`.githooks/pre-commit` 对暂存 md 跑 TOC 校验（须用真实 CLI，见 §4）。

## 6. 目录速览

```
X.<域>/            八大域（编号目录 + 0X-* 英语概念树 + README）
docs/              治理与导航：content-governance-rules / international-baseline /
                   hermes-runbook / toc.md / navigation/ / Refactor/（清理队列+归档）
states/            hermes 运行态：hermes-state.json / journal.md / task-queue.yaml /
                   queue/{cpu,gpu}/ 作业卡 / runners/ 车道 worker
tools/             治理与形式化脚本（§4/§5）
validation/        合规映射 yaml + 缺口审计 + 审计明细 CSV
research/          阶段报告与计划（2026-alignment-plan.md 为总纲）
Analysis/          跨域映射
docs/Refactor/archive/   归档区（git mv 可恢复；批次 README 说明）
```

## 7. 当前状态与已知风险（2026-11-17）

- 基线：活库 ~636 md（A≈330 / B≈175 / 其余为豁免类），归档 ~350；质量门 PASS。
- **已知风险**：`E:\_src` 疑被 OneDrive/安全软件管控，曾两波文件失踪（已恢复，零丢失）。
  处置：每轮先跑 `integrity_check.py`；失踪按 `docs/hermes-runbook.md` §5 恢复协议。
- **用户挂起项**（`states/hermes-state.json: parked_user_items`）：WSL Coq/Isabelle、
  UPPAAL 许可证、GPU 端点配置、同步盘排查——hermes 不得每轮升级提醒。
