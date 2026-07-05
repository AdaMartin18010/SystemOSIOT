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

## 3. 详细映射子文档

| 子文档 | 内容 |
|---|---|
| [1.0.1 ISO/IEC/IEEE 15288:2023 映射](1.0.1%20ISO-IEC-IEEE-15288-2023.md) | 四大过程组与项目七维框架的详细映射 |
| [1.0.2 SEBoK 映射](1.0.2%20SEBoK.md) | SEBoK 七大部分与项目模块对照 |
| [1.0.3 SysML v2 / KerML 映射](1.0.3%20SysML-v2.md) | 标准建模语言与多表征/形式化结构对接 |

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

## 5. 覆盖缺口与补齐计划

1. **生命周期过程映射不完整**：需将 15288 的 30 个技术过程与项目管理过程逐一映射到七维框架。
2. **SysML v2 视图缺失**：当前多表征以 Mermaid 为主，需补充 SysML v2 / KerML 标准视图。
3. **形式化深度不足**：`SystemTheory.v` 中的定理多为 trivial encoding，需引入范畴论/层论/拓扑斯进行非平凡形式化或明确标注教学级别。

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
