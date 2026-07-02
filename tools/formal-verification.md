# SystemOSIOT 形式化工件总览

本目录包含可直接运行的形式化验证工件，覆盖定理证明、模型检验、SMT 求解与概率模型检验。

## 工件清单与验证状态

| 路径 | 引擎 | 内容 | 本地验证方式 | 状态 |
|---|---|---|---|---|
| `tools/lean-verification/SimpleTypeTheory.lean` | Lean 4 | 算术表达式类型系统与类型安全 | `lean SimpleTypeTheory.lean` | ✅ 通过 |
| `tools/coq-verification/SystemTheory.v` | Coq 8.19+ | 系统理论基本定义与定理 | `coqc SystemTheory.v` | WSL 待运行 |
| `tools/coq-verification/FLP_Sketch.v` | Coq | FLP 不可能性定理陈述草图 | `coqc FLP_Sketch.v` | WSL 待运行 |
| `tools/isabelle-verification/IMP_BigStep.thy` | Isabelle/HOL 2024 | IMP 大步语义与确定性 | `isabelle build -D .` | 待运行 |
| `tools/tla-specifications/Raft.tla` + `Raft.cfg` | TLA+ / TLC | Raft 共识安全性质 | `java -jar tla2tools.jar -config Raft.cfg Raft.tla` | ✅ 通过 |
| `tools/tla-specifications/Kubernetes.tla` + `Kubernetes.cfg` | TLA+ / TLC | K8s Deployment 滚动更新约束 | `java -jar tla2tools.jar -config Kubernetes.cfg Kubernetes.tla` | ✅ 通过 |
| `tools/tla-specifications/QUIC.tla` + `QUIC.cfg` | TLA+ / TLC | QUIC/TCP 握手安全性质 | `java -jar tla2tools.jar -config QUIC.cfg QUIC.tla` | ✅ 通过 |
| `tools/uppaal-models/IoT_Scheduling.xml` | UPPAAL 5.0 | 物联网实时调度时间自动机 | `verifyta IoT_Scheduling.xml` | 需许可证 |
| `tools/nusmv-models/Mutex.smv` | NuSMV 2.6 | 互斥协议 CTL 验证 | `NuSMV Mutex.smv` | ✅ 通过 |
| `tools/alloy-models/Kubernetes_Architecture.als` | Alloy 6.2 | K8s 架构一致性 | `java -jar alloy.jar exec Kubernetes_Architecture.als` | ✅ 通过 |
| `tools/smt-examples/Container_Resource_Allocation.smt2` | Z3 4.13 | 容器资源分配 | `z3 Container_Resource_Allocation.smt2` | ✅ 通过 |
| `tools/cvc5-examples/Scheduling_Constraints.smt2` | CVC5 1.3.4 | 调度约束（多求解器兼容） | `cvc5 Scheduling_Constraints.smt2` | ✅ 通过 |
| `tools/prism-models/IoT_Reliability.prism` | PRISM 4.10.1 | 物联网传感器可靠性 DTMC | `prism IoT_Reliability.prism -pf "P=? [ F state=dead ]"` | WSL 待运行 |
| `tools/spin-models/Mutex.pml` | SPIN 6.5 | 互斥协议 Promela 验证 | `spin -a Mutex.pml && gcc -o pan pan.c && ./pan -a` | WSL 待运行 |

## 本地运行环境

### Windows 原生工具

- Lean 4：已安装并可用。
- Z3： portable 位于 `tools/engines/z3-4.13.0-x64-win/bin/z3.exe`。
- NuSMV： portable 位于 `tools/engines/NuSMV-2.6.0-win64/bin/NuSMV.exe`。
- Alloy 6.2： jar 位于 `tools/engines/alloy.jar`。
- TLA+ Tools： jar 位于 `tools/engines/tla2tools.jar`。

### WSL / Linux 工具

PRISM、CVC5、SPIN、Coq 已通过 WSL（Ubuntu 24.04）安装/下载到 `tools/engines/`；UPPAAL 与 Isabelle 因许可证/网络原因尚未在本地完成验证。

## CI 说明

见 `.github/workflows/formal-verification.yml`（如已创建）。在 CI 中建议：

1. 使用 `ubuntu-latest`。
2. 通过 apt 安装 `coq`、`default-jre`、`build-essential`、`bison`、`flex`。
3. 下载 PRISM / CVC5 / UPPAAL / Isabelle / Alloy / NuSMV / Z3 / TLA+ / SPIN 的二进制包。
4. 运行上表中的命令并收集退出码。

## 注意事项

- Markdown 中禁止声称“已形式化验证”除非本表显示对应工件已通过验证。
- 新增形式化工件必须同时更新本表与 `validation/formal-artifacts-gap-audit.md`。
