# SystemOSIOT 全面对齐国际权威基线：对称差与补全计划（2026）

> 版本：1.0（用户已确认批准全量执行，治理优先）
> 基线：`docs/international-baseline.md` v1.4.0（2026-07-05）
> 治理依据：`docs/content-governance-rules.md`（Phase 0 基线）
> 审计依据：`validation/formal-artifacts-gap-audit.md`（2026-07-05 版）
> 追踪方式：本文档任务表 + `docs/Refactor/cleanup-queue.md` 清理队列

## 1. 现状全景（8 域 × 维度矩阵）

统一维度骨架：`X.0 国际标准映射` · `X.1 知识梳理` · `X.2 批判分析` · `X.3 形式化结构` · `X.4 形式化证明` · `X.5 多表征` · `X.6 形式语义` · `X.7/X.8 运行时语义与扩展专题`。

| 域 | 英语概念树叶子 | X.0 映射 | 覆盖评级 |
|---|---|---|---|
| 1 系统理论 | 8 分支（多为空壳 README） | 3 文件 | 中 |
| 2 操作系统 | 进程/内存/文件/设备 + Linux 内核 11 + 网络栈 7 + 外设 10 + 接口 6 | 2（条款级 309 行） | 厚 |
| 3 物联网嵌入式 | 基础 + 嵌入式 Linux 4 + RTOS 8 + 接口 3 + 决策树 3 | 2 | 中 |
| 4 分布式系统 | 仅 `01-distributed-basics.md` | 1（157 行） | 最薄 |
| 5 集群系统 | 仅 `01-cluster-basics.md` | 2 | 最薄 |
| 6 P2P 系统 | 仅 README（无实质叶子） | 2 | 最薄 |
| 7 容器与微服务 | 容器/微服务/网格 + 调度 9 + 递归语义分析 | 4+3 规范 | 厚（治理最差） |
| 8 网络系统 | 知识梳理 41 + 六维度 + 8.8 前沿专题 48 | 3（分层映射） | 最厚 |

辅助层：`Analysis/`（16 份跨域映射）、`docs/`（导航/基线/治理）、`validation/`（合规映射 + 审计 + 结果）、`tools/`（Lean/Coq/Isabelle/TLA+/UPPAAL/NuSMV/Alloy/PRISM/SPIN/Z3/CVC5）、`research/`（12 份阶段报告）。

## 2. 对称差 Δ

### Δ1 结构治理差（现状 Δ 治理规范）

| # | 问题 | 位置 |
|---|---|---|
| Δ1.1 | 同号多名（编号冲突） | 域 1 全套（1.3/1.4/1.5/1.6/1.7 双系列）、2.6.4、4.6.5、7.0.x/7.5.x/7.6.x 双系列、8.3.6、8.4.7/8.4.8、8.5.5–8.5.8、8.6.x、8.7.x 多组 |
| Δ1.2 | 编号错位 | `8.1 知识梳理` 41 个文件用 `1.8.x` 前缀，且 `1.8.1`/`8.1.1` 核心概念并存 |
| Δ1.3 | 维度不一致 | `2.4 形式化证明` 与 `2.7 形式证明` 并存；`7.2 批判性分析` 他域为「批判分析」；仅域 1 有 `1.7 递归展望`；扩展维度各域不齐 |
| Δ1.4 | 深度违规（>5 级） | `7.1.1.1.x`、`7.1.6.2.1.x`、`7.3.2.x`、`7.4.1.x`、`7.8.2.1.x`、`2.8.4/` |
| Δ1.5 | 根目录散件 | `7.容器与微服务/` 下 20+ 非编号规划/报告文件与 2 个非编号目录 |
| Δ1.6 | 冗余主题目录 | 根级旧目录 `7.容器微服务/` 与正式目录并存 |
| Δ1.7 | 跨域重复 | 域 4 内嵌容器微服务文件（4.2.4/4.3.4/4.4.4/4.5.4/4.6.5）与域 7 重复 |
| Δ1.8 | 挂起遗留 | `docs/Refactor/` 前沿主题编号目录（量子/脑机接口/认知计算等，双系列编号，各仅 stub）；`states/` 空目录 |

### Δ2 内容对称差（vs 国际基线）

**A∖B（缺失/薄弱，按执行优先级）**：

- **域 4 分布式（最薄）**：分布式事务（2PC/3PC/Saga/TCC）、时钟与排序（Lamport/Vector/HLC）、CRDT、共识族（VR/Zab/Multi-Paxos/EPaxos；BFT：HotStuff/Tendermint）、存储（Dynamo/Spanner/Calvin）、一致性哈希、幂等/恰好一次、消息语义、纠删码；PACELC/Linearizability 条款级映射。
- **域 6 P2P**：Chord/Kademlia/Pastry 理论化、libp2p/IPFS 栈、PoW/PoS 与 BFT 区块链形式化、Sybil/Eclipse 防御、激励博弈、Erasure-coded 存储、P2P 流媒体/WebRTC。
- **域 5 集群**：Slurm 24.11/25.05、K8s gang/coscheduling、MPI 4.1 集合通信、容错 C/R（DMTCP）、Roofline/Amdahl、EAR/Green500 能耗、Apptainer、拓扑感知调度。
- **域 3 物联网**：ISO/IEC 30141:2024、NIST SP 800-213A 映射文件；Matter/Thread、IEC 62443、LwM2M、OSCORE/EDHOC；无线栈（BLE/LoRaWAN/NB-IoT/Zigbee/802.15.4）；工业实时以太网（EtherCAT/Profinet/TSN-for-IIoT）；IEC 61508/ISO 26262 条款级映射。
- **域 1 系统理论**：INCOSE SE Handbook v5、ISO 42010/24641 映射；`01-system-theory` 6 个空壳分支；数字工程（ISO 23247）、NASA HB、MBSE 流程。
- **域 2 操作系统**：VFS/日志文件系统形式化与深度叶子；锁/RCU 同步形式化；虚拟化（KVM/hypervisor）域内缺失；能效调度（EAS/RAPL）。
- **域 7 容器**：Istio/Envoy 与 Cilium/eBPF 数据面、Wasm 容器（runwasi/WAMR）、机密容器（Kata/CoCo）、Gateway API、多集群（Karmada/OCM）、GitOps（OpenGitOps）、OpenTelemetry、FinOps。
- **域 8 网络**：6G/IMT-2030、量子互联网、IETF Green、ETSI NFV、SRv6 uSID/压缩、MQTT over QUIC、RPKI ROV 部署度量。

**B∖A（项目已超前，需反向收编进基线）**：算力网络/CFN（ITU-T Y.2501）、AP6、数字孪生网络（Y.3090）、NTN、确定性 IP、SRv6+、东数西算 → 在 baseline 增设「前沿扩展」区并标注成熟度（draft/标准）。

### Δ3 形式化工件差（源自 gap-audit）

- **悬空声明 10 项**（yaml 声称但不存在）：`requirements/formal_contracts.v`、`design/contract_specifications.tla`、`specifications/formal_requirements.tla`、`verification/proof_scripts/*.v`、`implementation/hoare_annotations.h`、`verification/refinement_proofs.v`、`risk/formal_risk_models.tla`、`requirements/formal_safety_requirements.tla`、`models/safety_models/*.smv`、`verification/requirements_to_code_fidelity.v`。
- **待验证 4 项**：`OSScheduler.v`、`OSMemory.v`、`OS_Scheduler.thy`（工具链未装）、UPPAAL `IoT_Scheduling.xml`/`RTOS_Schedulability.xml`（缺学术许可证）。
- **缺失证明**：Hoare/分离逻辑、Paxos/2PC/CRDT 的 TLA+、RMA/EDF 可调度性（Coq/Isabelle）、VFS/文件系统模型、网络协议活性扩展。
- **CI 未接入**形式化验证门禁。

## 3. 执行计划（阶段 → 任务 → 验收）

### Phase 0 治理与审计闭环（P0，治理优先）

| 任务 | 内容 | 验收 | 状态 |
|---|---|---|---|
| 0-A | 归档域 7 散件（20+ 文件与 2 目录）至 `docs/Refactor/archive/2026-phase0/`；处置旧目录 `7.容器微服务/`、`docs/Refactor/` 前沿 stub、`states/` | 域 7 根仅剩编号目录 + README；根级无冗余主题目录 | 进行中 |
| 0-B | yaml 悬空映射逐条登记处置（建工件或标 planned） | 映射文件无「声称存在但实际不存在」的工件 | 进行中 |
| 0-C | 编号唯一化：8.1 的 41 文件重编号 + 重复核心概念合并 | 8.1 全部文件 8.1.x 唯一编号，README/链接同步 | 进行中 |
| 0-D | 其余域编号冲突合并（1.3–1.7、2.6.4、4.6.5、7.0/7.5/7.6、8.3–8.7）；>5 级深度合并（7.1.x、7.3.2、7.4.1、7.8.2、2.8.4） | 全库同目录编号唯一；深度 ≤5 | 待办（见清理队列） |
| 0-E | 跨域重复处置（域 4 容器微服务文件 → 并入域 7 或改交叉引用）；基线版本季度核查（K8s v1.34、Slurm 25.05、IEEE 802.11bn、3GPP R19） | 无重复内容双份维护；baseline 版本注释更新 | 待办 |

### Phase 1 国际映射补齐

每域 X.0 扩至 ≥5 个条款级映射文件，按 4→6→5→3→1→2→7→8 顺序；baseline 增设「前沿扩展」区。验收：每文件含标准号/版本/官方链接/访问日期，双向链接正文。

### Phase 2 内容缺口补齐

按 Δ2 清单逐域补叶子主题（六维度模板）；`0X-*` 概念树叶子每域 ≥5 实质文件。验收：六维度矩阵无缺格；新内容挂 X.0 来源。

### Phase 3 形式化工件

补 Hoare/分离逻辑（Isabelle）、Paxos 与 2PC（TLA+）、RMA/EDF 可调度性（Coq）、VFS 模型（Alloy）；装工具链复验 4 项待验证工件；接入 GitHub Actions 门禁。验收：审计表全 ✅ 且 CI 绿色；悬空声明清零。

### Phase 4 验证与报告

全库链接/深度扫描；审计与基线版本升级；产出 `research/2026-alignment-completion-report.md`。

## 4. 风险与依赖

- UPPAAL 学术许可证需用户注册；Coq/Isabelle 工具链需安装（WSL）。
- 标准版本动态：K8s 每年 3 个大版本、3GPP R19、IEEE 802 系列年更新 → 季度核查机制化。
- 归档不删除：所有治理操作仅移动不删除，保留 git 历史可追溯。

## 5. 进度记录

| 日期 | 事项 |
|---|---|
| 2026-07 | 计划经用户确认（批准全量执行、治理优先、计划落盘）；启动 Phase 0 |
