# SystemOSIOT 形式化工件审计

> 审计日期：2026-07-02  
> 更新日期：2026-07-02（Phase 2 后）  
> 审计范围：全项目声称使用 Coq / Isabelle/HOL / Lean / TLA+ / 模型检验器 / SMT 的章节

## 1. 已创建/可执行工件

| 路径 | 引擎 | 内容 | 状态 |
|---|---|---|---|
| `tools/coq-verification/SystemTheory.v` | Coq 8.19+ | 系统理论基本定义与 trivial theorem | ✅ 可执行 |
| `tools/tla-specifications/Raft.tla` + `Raft.cfg` | TLA+ / TLC | Raft 共识简化模型（Leader 选举、日志复制、安全性质） | ✅ 已创建，待运行 TLC |
| `tools/tla-specifications/Kubernetes.tla` + `Kubernetes.cfg` | TLA+ / TLC | Kubernetes Pod 生命周期与 Deployment 滚动更新模型 | ✅ 已创建，待运行 TLC |
| `tools/lean-verification/SimpleTypeTheory.lean` | Lean 4 | 算术表达式语言、大步语义、类型安全证明 | ✅ 已创建，待运行 `lean` |
| `tools/isabelle-verification/IMP_BigStep.thy` | Isabelle/HOL | IMP 命令式语言大步语义与确定性证明 | ✅ 已创建，待运行 Isabelle |
| `tools/coq-verification/FLP_Sketch.v` | Coq | FLP 异步系统模型与定理陈述草图 | ✅ 已创建，完整证明待补充 |

## 2. 仍缺失的工件

### 2.1 Coq

| 声称位置/主题 | 缺失文件 | 说明 |
|---|---|---|
| 操作系统调度证明 | `2.4 形式化证明/*.v` | 未找到任何 OS 相关 `.v` |
| 分布式系统共识证明 | `4.4 形式化证明/*.v` | 已创建 TLA+ 草图，但无 Coq 证明 |
| 容器编排一致性证明 | `7.4 形式化证明/*.v` | 已创建 TLA+ 草图，但无 Coq 证明 |
| 网络协议正确性证明 | `8.4 形式化证明/*.v` | 未找到任何网络协议 `.v` |

### 2.2 Isabelle/HOL

| 声称位置/主题 | 缺失文件 | 说明 |
|---|---|---|
| 系统理论高阶逻辑证明 | `tools/isabelle-verification/SystemTheory.thy` | 仅存在 IMP 语义示例 |
| 操作系统语义 | `2.7 形式证明/*.thy` | 目录/文件不存在 |
| 霍尔逻辑/分离逻辑 | `tools/isabelle-verification/*Hoare*.thy` | 未创建 |

### 2.3 Lean 4

| 声称位置/主题 | 缺失文件 | 说明 |
|---|---|---|
| 现代数学基础形式化 | `tools/lean-verification/*Math*.lean` | 仅存在类型论入门示例 |
| 系统理论形式化 | `tools/lean-verification/*System*.lean` | 未创建 |

### 2.4 TLA+

| 声称位置/主题 | 缺失文件 | 说明 |
|---|---|---|
| 网络协议握手规范 | `8.7 系统运行时语义/*.tla` | 未找到 |
| QUIC/TCP 状态机 | `8.7 系统运行时语义/*.tla` | 未找到 |

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
| `verification/model_checking/*.tla` | ISO/IEC/IEEE 15288 6.4.2.3 | ⚠️ 部分存在：`tools/tla-specifications/*.tla` |
| `implementation/hoare_annotations.h` | ISO/IEC/IEEE 12207 7.2.2.1 | ❌ 不存在 |
| `verification/refinement_proofs.v` | ISO/IEC/IEEE 12207 7.2.2.1 | ❌ 不存在 |
| `models/alloy_models/*.als` | ISO/IEC/IEEE 42010 6.3.1 | ❌ 不存在 |
| `risk/formal_risk_models.tla` | ISO/IEC/IEEE 42010 6.3.2 | ❌ 不存在 |
| `requirements/formal_safety_requirements.tla` | IEC 61508 7.4.2.2 | ❌ 不存在 |
| `models/safety_models/*.smv` | ISO 26262 6.4.2.2 | ❌ 不存在 |
| `verification/requirements_to_code_fidelity.v` | DO-178C 6.4.2.1 | ❌ 不存在 |

## 4. 后续优先级

| 优先级 | 工件类型 | 建议补齐 | 负责模块 |
|---|---|---|---|
| P0 | 运行并修复 TLA+ 规范 | Raft、Kubernetes 模型在 TLC 中通过 | 4, 7 |
| P0 | 运行并修复 Lean/Isabelle/Coq 示例 | 确保所有示例可被对应工具加载 | 1, 2 |
| P1 | 网络协议 TLA+ 规范 | QUIC/TCP 握手、BGP/OSPF 状态机 | 8 |
| P1 | UPPAAL 实时案例 | IoT 调度/能耗、容器实时性 | 3 |
| P2 | NuSMV/PRISM/Alloy | 各 1 个示例 | 2, 3, 7 |
| P2 | SMT-LIB 示例 | 约束求解小例 | 1, 7 |

## 5. 建议行动

1. 在 CI 中安装 TLA+ Toolbox、Lean 4、Isabelle2024、Coq 8.19+，实现形式化验证门禁。  
2. 禁止在新增 Markdown 中宣称“已形式化验证”除非同时提交可运行工件。  
3. 优先完成 P0 级工件运行验证，修复语法/逻辑错误。  
4. 将本审计结果链接到各模块的 `X.0 国际标准映射/README.md` 中。
