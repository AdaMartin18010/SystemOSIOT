# 1.0 系统理论 — 国际标准映射


<!-- TOC START -->

- [1.0 系统理论 — 国际标准映射](#10-系统理论--国际标准映射)
  - [1. 目的](#1-目的)
  - [2. 主要对标标准](#2-主要对标标准)
  - [3. 详细映射子文档](#3-详细映射子文档)
  - [4. 标准条款映射表](#4-标准条款映射表)
  - [5. 覆盖缺口与补齐计划](#5-覆盖缺口与补齐计划)
  - [6. 形式化工件链接](#6-形式化工件链接)
  - [7. 维护记录](#7-维护记录)
  - [质量治理注记（2026-11）](#质量治理注记2026-11)

<!-- TOC END -->

## 1. 目的

将系统理论模块的内容与国际权威标准、知识体系、建模语言进行条款级映射，识别覆盖缺口并规划补齐路径。

## 2. 主要对标标准

| 标准/知识体系 | 版本 | 官方链接/DOI | 对应项目章节 |
|---|---|---|---|
| ISO/IEC/IEEE 15288 | 2023 | <https://www.iso.org/standard/81702.html> | 全模块 |
| INCOSE Systems Engineering Handbook | 5th Ed., 2023 | <https://www.incose.org/products-and-publications/se-handbook> | 全模块 |
| SEBoK | v2.13 (2025) | <https://sebokwiki.org/> | 1.1, 1.5 |
| OMG SysML v2 / KerML | v2.0 (2025) | <https://www.omg.org/spec/SysML/> | 1.3, 1.5, 1.6 |
| ISO/IEC/IEEE 24641 | 2023 | <https://www.iso.org/standard/79111.html> | 1.3, 1.5 |
| ISO/IEC/IEEE 42010 | 2022 | <https://www.iso.org/standard/77394.html> | 1.3, 1.5 |
| ISO/IEC/IEEE 24641 | 2023 | <https://www.iso.org/standard/79111.html> | 1.3, 1.5 |

## 3. 详细映射子文档

| 子文档 | 内容 |
|---|---|
| [1.0.1 ISO/IEC/IEEE 15288:2023 映射](1.0.1%20ISO-IEC-IEEE-15288-2023.md) | 四大过程组与项目七维框架的详细映射 |
| [1.0.2 SEBoK 映射](../../docs/Refactor/archive/2026-quality-audit/1.系统理论/1.0%20国际标准映射/1.0.2%20SEBoK.md) | SEBoK 七大部分与项目模块对照 |
| [1.0.3 SysML v2 / KerML 映射](1.0.3%20SysML-v2.md) | 标准建模语言与多表征/形式化结构对接 |
| [1.0.4 ISO/IEC/IEEE 42010:2022 架构描述映射](../../docs/Refactor/archive/2026-quality-audit/1.系统理论/1.0%20国际标准映射/1.0.4%20ISO-IEC-IEEE-42010-2022%20架构描述标准映射.md) | 视点/视图/模型种类与系统架构内容映射 |
| [1.0.5 ISO/IEC/IEEE 24641:2023 MBSSE 映射](1.0.5%20ISO-IEC-IEEE-24641-MBSE%20方法工具映射.md) | 基于模型的系统与软件工程方法工具映射 |
| [1.0.6 INCOSE SE Handbook 5th + SEBoK 映射](1.0.6%20INCOSE-SE-Handbook-5th%20知识体系映射.md) | SE 流程与知识体系映射 |

## 4. 标准条款映射表

| 标准条款 | 条款标题 | 项目覆盖章节 | 证据文件 | 覆盖状态 |
|---|---|---|---|---|
| ISO/IEC/IEEE 15288:2023 6.4.1 | Stakeholder Requirements Definition | 1.1 知识梳理 | 待补充 | 未覆盖 |
| ISO/IEC/IEEE 15288:2023 6.4.2 | System Requirements Definition | 1.3 形式化结构 | 待补充 | 部分覆盖 |
| ISO/IEC/IEEE 15288:2023 6.4.3 | System Architecture Design | 1.3, 1.5 | 待补充 | 部分覆盖 |
| ISO/IEC/IEEE 15288:2023 6.4.4 | Implementation | 1.6, 1.8 | 待补充 | 未覆盖 |
| ISO/IEC/IEEE 15288:2023 6.4.5 | Integration | 1.8 系统运行时语义 | 待补充 | 未覆盖 |
| ISO/IEC/IEEE 15288:2023 6.4.6 | Verification | 1.4 形式化证明 | `tools/coq-verification/SystemTheory.v` | 部分覆盖 |
| ISO/IEC/IEEE 15288:2023 6.4.7 | Transition | — | 待补充 | 未覆盖 |
| ISO/IEC/IEEE 15288:2023 6.4.8 | Validation | 1.4, 1.6 | 待补充 | 部分覆盖 |
| ISO/IEC/IEEE 42010:2022 5.3 | Stakeholder / Concern | 1.1, 1.2 | 待补充 | 未覆盖 |
| ISO/IEC/IEEE 42010:2022 5.4 | Viewpoint | 1.5 | 待补充 | 未覆盖 |
| ISO/IEC/IEEE 42010:2022 5.5 | View / Model Kind | 1.3, 1.5 | 待补充 | 部分覆盖 |
| ISO/IEC/IEEE 42010:2022 5.6 | Architecture Framework / ADL | 1.5 | 待补充 | 未覆盖 |
| ISO/IEC/IEEE 24641:2023 6.2 | Plan MBSSE | 1.1 | 待补充 | 未覆盖 |
| ISO/IEC/IEEE 24641:2023 6.3 | Build Models | 1.3, 1.4, 1.5 | 待补充 | 部分覆盖 |
| ISO/IEC/IEEE 24641:2023 6.4 | Perform MBSSE | 1.2, 1.6, 1.8 | 待补充 | 部分覆盖 |
| INCOSE SE Handbook 5th Ch. 5 | Decision / Risk / CM / Measurement | 1.2, 1.3, 1.4 | 待补充 | 未覆盖 |
| INCOSE SE Handbook 5th Ch. 6 | Integration / Transition / Operation / Maintenance | 1.8 | 待补充 | 未覆盖 |

## 5. 覆盖缺口与补齐计划

1. **生命周期过程映射不完整**：需将 15288 的 30 个技术过程与项目管理过程逐一映射到七维框架。
2. **SysML v2 视图缺失**：当前多表征以 Mermaid 为主，需补充 SysML v2 / KerML 标准视图。
3. **形式化深度不足**：`SystemTheory.v` 中的定理多为 trivial encoding，需引入范畴论/层论/拓扑斯进行非平凡形式化或明确标注教学级别。
4. **ISO/IEC/IEEE 42010 视点-视图-模型种类三层结构缺失**：`1.5 多表征` 未按 42010 重新组织，缺少视点定义与多视图一致性规则。
5. **MBSSE 方法工具映射不完整**：`1.3 形式化结构` 与 `1.5 多表征` 未明确模型作为“主要知识源”的地位，缺少模型 V&V 与模型转换规则。
6. **INCOSE SE Handbook 技术管理过程缺失**：决策管理、风险管理、配置管理、度量过程在 `1.2` / `1.3` / `1.4` 中均未覆盖。

## 6. 形式化工件链接

| 工件 | 路径 | 说明 |
|---|---|---|
| Coq 系统理论 | `tools/coq-verification/SystemTheory.v` | 系统理论基本定义 |
| Lean 4 类型论示例 | `tools/lean-verification/SimpleTypeTheory.lean` | 算术表达式类型安全 |
| Isabelle/HOL 语义示例 | `tools/isabelle-verification/IMP_BigStep.thy` | IMP 大步语义 |

## 7. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建映射骨架 | Kimi Code CLI |
| 2026-07 | 新增 1.0.4 / 1.0.5 / 1.0.6 标准映射，更新主要对标标准与覆盖缺口 | Kimi Code CLI |

## 质量治理注记（2026-11）

本目录 2 个内容文件经全库质量审计（2026-11-17，修正链接文本误判后）归类为模板填充（C 类），已归档至 `docs/Refactor/archive/2026-quality-audit/1.系统理论/1.0 国际标准映射/`（原相对路径不变，`git mv` 可恢复）。保留本 README 作为目录骨架。
