# SystemOSIOT 形式化工件悬空审计

> 审计日期：2026-07-02
> 审计范围：全项目声称使用 Coq / Isabelle/HOL / Lean / TLA+ / 模型检验器 / SMT 的章节
> 审计结论：**形式化工件严重不足，大量“已形式化验证”声明缺乏可执行证据。**

## 1. 现有可执行工件

| 路径 | 引擎 | 状态 | 备注 |
|---|---|---|---|
| `tools/coq-verification/SystemTheory.v` | Coq 8.19+ | ✅ 可执行 | 系统理论基本定义与 trivial theorem |

## 2. 声称支持但缺失的工件

### 2.1 Coq

| 声称位置/主题 | 缺失文件 | 说明 |
|---|---|---|
| 操作系统调度证明 | `2.4 形式化证明/*.v` | 未找到任何 OS 相关 `.v` |
| 分布式系统共识证明 | `4.4 形式化证明/*.v` | 未找到任何分布式共识 `.v` |
| 容器编排一致性证明 | `7.4 形式化证明/*.v` | 未找到任何容器相关 `.v` |
| 网络协议正确性证明 | `8.4 形式化证明/*.v` | 未找到任何网络协议 `.v` |

### 2.2 Isabelle/HOL

| 声称位置/主题 | 缺失文件 | 说明 |
|---|---|---|
| 系统理论高阶逻辑证明 | `tools/isabelle-verification/*.thy` | 目录不存在 |
| 操作系统语义 | `2.7 形式证明/*.thy` | 目录/文件不存在 |
| 程序语义与类型安全 | 任意 `.thy` | 全项目未找到 |

### 2.3 Lean 4

| 声称位置/主题 | 缺失文件 | 说明 |
|---|---|---|
| 类型论基础 | `tools/lean-verification/*.lean` | 目录不存在 |
| 现代数学基础形式化 | 任意 `.lean` | 全项目未找到 |

### 2.4 TLA+

| 声称位置/主题 | 缺失文件 | 说明 |
|---|---|---|
| 分布式系统时序规范 | `*.tla` | 全项目未找到 |
| Raft 一致性规范 | `4.7 系统运行时语义/*.tla` | 未找到 |
| K8s Deployment 规范 | `7.7 运行时调度语义分析/*.tla` | 未找到 |
| 网络协议握手规范 | `8.7 系统运行时语义/*.tla` | 未找到 |

### 2.5 模型检验器

| 引擎 | 扩展名 | 缺失文件 | 说明 |
|---|---|---|---|
| NuSMV / nuXmv | `.smv` | 全项目未找到 | CTL/LTL 验证声明无工件 |
| PRISM | `.prism` | 全项目未找到 | 概率模型检验声明无工件 |
| UPPAAL | `.xml` / `.q` | 全项目未找到 | 实时系统验证声明无工件 |
| Alloy | `.als` | 全项目未找到 | 架构一致性声明无工件 |
| SPIN | `.pml` | 全项目未找到 | 并发协议验证声明无工件 |

### 2.6 SMT / 约束求解

| 引擎 | 扩展名 | 缺失文件 | 说明 |
|---|---|---|---|
| Z3 | `.smt2` | 全项目未找到 | SMT 验证声明无工件 |
| CVC5 | `.smt2` | 全项目未找到 | 未声明但可补充 |

## 3. 悬空映射（来自 `standard-compliance-mapping.yaml`）

`validation/standard-compliance-mapping.yaml` 声明了以下工件，但经审计大部分不存在：

| 声明工件路径 | 对应标准条款 | 存在状态 |
|---|---|---|
| `requirements/formal_contracts.v` | ISO/IEC/IEEE 15288 6.4.2.1 | ❌ 不存在 |
| `design/contract_specifications.tla` | ISO/IEC/IEEE 15288 6.4.2.1 | ❌ 不存在 |
| `specifications/formal_requirements.tla` | ISO/IEC/IEEE 15288 6.4.2.2 | ❌ 不存在 |
| `verification/proof_scripts/*.v` | ISO/IEC/IEEE 15288 6.4.2.3 | ❌ 不存在 |
| `verification/model_checking/*.tla` | ISO/IEC/IEEE 15288 6.4.2.3 | ❌ 不存在 |
| `implementation/hoare_annotations.h` | ISO/IEC/IEEE 12207 7.2.2.1 | ❌ 不存在 |
| `verification/refinement_proofs.v` | ISO/IEC/IEEE 12207 7.2.2.1 | ❌ 不存在 |
| `models/alloy_models/*.als` | ISO/IEC/IEEE 42010 6.3.1 | ❌ 不存在 |
| `risk/formal_risk_models.tla` | ISO/IEC/IEEE 42010 6.3.2 | ❌ 不存在 |
| `requirements/formal_safety_requirements.tla` | IEC 61508 7.4.2.2 | ❌ 不存在 |
| `models/safety_models/*.smv` | ISO 26262 6.4.2.2 | ❌ 不存在 |
| `verification/requirements_to_code_fidelity.v` | DO-178C 6.4.2.1 | ❌ 不存在 |

## 4. 修复优先级

| 优先级 | 工件类型 | 建议首批补齐数量 | 负责模块 |
|---|---|---|---|
| P0 | TLA+ 规范 | 3（Raft、K8s Deployment、QUIC 握手） | 4, 7, 8 |
| P0 | Coq 证明升级 | 1（SystemTheory.v 去 trivial 化或标注） | 1 |
| P1 | Lean 4 示例 | 2（类型论基础、程序语义） | 1 |
| P1 | Isabelle/HOL 示例 | 1（Concrete Semantics 风格小语言） | 1, 2 |
| P1 | UPPAAL 实时案例 | 1（IoT 调度/能耗） | 3 |
| P2 | NuSMV/PRISM/Alloy | 各 1 | 2, 3, 7 |
| P2 | SMT-LIB 示例 | 2 | 1, 7 |

## 5. 建议行动

1. 立即在 `validation/standard-compliance-mapping.yaml` 中标注所有悬空工件为 `missing`，并关联到本审计。
2. 禁止在新增 Markdown 中宣称“已形式化验证”除非同时提交可运行工件。
3. 优先完成 P0 级工件，使形式化验证 CI 门禁真正可运行。
4. 将本审计结果链接到各模块的 `X.0 国际标准映射/README.md` 中。
