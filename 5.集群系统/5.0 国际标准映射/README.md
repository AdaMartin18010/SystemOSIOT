# 5.0 集群系统 — 国际标准映射


<!-- TOC START -->

- [5.0 集群系统 — 国际标准映射](#50-集群系统--国际标准映射)
  - [1. 主要对标标准](#1-主要对标标准)
  - [2. 标准条款映射表](#2-标准条款映射表)
  - [3. 覆盖缺口与补齐计划](#3-覆盖缺口与补齐计划)
  - [5. 形式化工件链接](#5-形式化工件链接)
  - [6. 维护记录](#6-维护记录)

<!-- TOC END -->

## 1. 主要对标标准

| 标准/规范/基准 | 版本 | 官方链接/DOI | 对应项目章节 |
|---|---|---|---|
| MPI Standard | 4.0 (2021-06-09) | <https://www.mpi-forum.org/docs/mpi-4.0/mpi40-report.pdf> | 5.1, 5.3, 5.6 |
| OpenMP API | 5.2 (2021-11) / 6.0 (2024-11) | <https://www.openmp.org/specifications/> | 5.1, 5.6, 5.7 |
| Slurm Workload Manager | 25.11 / 25.05 | <https://slurm.schedmd.com/> | 5.1, 5.7 |
| Kubernetes | v1.33 | <https://v1-33.docs.kubernetes.io/> | 5.1, 5.7 |
| OGF JSDL | v1.0 (GFD.56) | <https://ogf.org/documents/GFD.56.pdf> | 5.1, 5.7 |
| OGF DRMAA | v2.2 (GFD-R-P.230/231) | <https://www.drmaa.org/documents.php> | 5.1, 5.7 |
| HPCG Benchmark | 3.1+ | <https://www.hpcg-benchmark.org/> | 5.1, 5.2, 5.5 |
| Graph500 Benchmark | 3.0+ | <https://graph500.org/> | 5.1, 5.2, 5.5 |
| ISO/IEC/IEEE 24765 | 2017 (Ed. 2) | <https://www.iso.org/standard/71952.html> | 5.1, 5.3 |
| ETSI MEC | GS MEC 003 V4.1.1 (2025-05) | <https://www.etsi.org/technologies/multi-access-edge-computing> | 5.1, 5.7 |
| NIST Big Data Reference Architecture | SP 1500-6 | <https://www.nist.gov/programs-projects/nist-big-data-interoperability-framework-nbdif> | 5.1, 5.3 |
| NIST Cloud Computing Reference Architecture | SP 500-292 | <https://www.nist.gov/publications/nist-cloud-computing-reference-architecture> | 5.1, 5.3 |
| NIST Cloud Computing Definition | SP 800-145 | <https://csrc.nist.gov/publications/detail/sp/800-145/final> | 5.1, 5.2 |
| POSIX.1 (IEEE Std 1003.1) | 2024 Edition | <https://pubs.opengroup.org/onlinepubs/9799919799/> | 5.1, 5.7 |
| UEFI / ACPI | UEFI 2.10 / ACPI 6.5 | <https://uefi.org/specifications> | 5.1, 5.7 |
| InfiniBand Architecture | IBTA Specs | <https://www.infinibandta.org/> | 5.1, 5.6 |
| UCX (Unified Communication X) | 1.18+ | <https://openucx.org/> | 5.1, 5.6 |
| Compute Express Link (CXL) | CXL 3.1 | <https://www.computeexpresslink.org/> | 5.1, 5.7 |
| PCI Express (PCIe) | 6.0 / 5.0 | <https://pcisig.com/specifications> | 5.1, 5.7 |

> 注：NIST SP 500-292 的标题为 *NIST Cloud Computing Reference Architecture*；NIST Big Data Reference Architecture 对应 NIST SP 1500-6。二者在集群系统语境下分别对应云集群参考架构与大数据集群参考架构。

## 2. 标准条款映射表

> 详细条款级映射可进一步参见：
>
> - [5.0.1 MPI 与 HPC 标准映射](5.0.1%20MPI%20与%20HPC%20标准映射.md)
> - [5.0.2 集群调度与资源管理标准映射](5.0.2%20集群调度与资源管理标准映射.md)

| 标准条款 | 条款标题 | 项目覆盖章节 | 证据文件 | 覆盖状态 |
|---|---|---|---|---|
| MPI 4.0 第3章 | Point-to-Point Communication | 5.1, 5.6 | [5.1.1 基本概念](../5.1%20知识梳理/5.1.1%20基本概念.md)、[5.0.1 MPI 与 HPC 标准映射](5.0.1%20MPI%20与%20HPC%20标准映射.md) | 部分覆盖 |
| MPI 4.0 第5章 | Collective Communication | 5.1, 5.3, 5.6 | [5.0.1 MPI 与 HPC 标准映射](5.0.1%20MPI%20与%20HPC%20标准映射.md) | 未覆盖 |
| MPI 4.0 第7章 | Process Topologies | 5.1, 5.3 | [5.1.1 基本概念](../5.1%20知识梳理/5.1.1%20基本概念.md)、[5.0.1 MPI 与 HPC 标准映射](5.0.1%20MPI%20与%20HPC%20标准映射.md) | 未覆盖 |
| MPI 4.0 第11章 | One-Sided Communication | 5.1, 5.6 | [5.0.1 MPI 与 HPC 标准映射](5.0.1%20MPI%20与%20HPC%20标准映射.md) | 未覆盖 |
| OpenMP 5.2/6.0 第11章 | Worksharing-Loop Constructs | 5.1, 5.7 | [5.0.1 MPI 与 HPC 标准映射](5.0.1%20MPI%20与%20HPC%20标准映射.md) | 未覆盖 |
| Slurm 25.11 Scheduling | Partitions, QoS, Backfill, Preemption | 5.1, 5.7 | [5.7.1 运行时行为与调度模型](../5.7%20系统运行时语义/5.7.1%20运行时行为与调度模型.md)、[5.0.2 集群调度与资源管理标准映射](5.0.2%20集群调度与资源管理标准映射.md) | 部分覆盖 |
| Kubernetes v1.33 Scheduling | kube-scheduler、Scheduling Framework、Pod Affinity/Anti-affinity | 5.1, 5.7 | [5.7.1 运行时行为与调度模型](../5.7%20系统运行时语义/5.7.1%20运行时行为与调度模型.md)、[5.0.2 集群调度与资源管理标准映射](5.0.2%20集群调度与资源管理标准映射.md) | 部分覆盖 |
| OGF JSDL v1.0 (GFD.56) | Job Submission Description Language | 5.1, 5.7 | [5.0.2 集群调度与资源管理标准映射](5.0.2%20集群调度与资源管理标准映射.md) | 未覆盖 |
| OGF DRMAA v2.2 | Job Submission, Monitoring and Control | 5.1, 5.7 | [5.0.2 集群调度与资源管理标准映射](5.0.2%20集群调度与资源管理标准映射.md) | 未覆盖 |
| HPCG 3.1 | High Performance Conjugate Gradients Benchmark | 5.1, 5.2, 5.5 | [5.0.1 MPI 与 HPC 标准映射](5.0.1%20MPI%20与%20HPC%20标准映射.md) | 未覆盖 |
| Graph500 3.0 | Large-scale Graph Search Benchmark | 5.1, 5.2, 5.5 | [5.0.1 MPI 与 HPC 标准映射](5.0.1%20MPI%20与%20HPC%20标准映射.md) | 未覆盖 |
| ISO/IEC/IEEE 24765:2017 | Systems and Software Engineering Vocabulary | 5.1, 5.3 | [5.1.1 基本概念](../5.1%20知识梳理/5.1.1%20基本概念.md) | 部分覆盖 |
| ETSI GS MEC 003 V4.1.1 | MEC Framework and Reference Architecture | 5.1, 5.7 | [5.0.2 集群调度与资源管理标准映射](5.0.2%20集群调度与资源管理标准映射.md) | 未覆盖 |
| NIST SP 500-292 | Cloud Computing Reference Architecture | 5.1, 5.3 | [5.3.1 形式化定义](../5.3%20形式化结构/5.3.1%20形式化定义.md) | 部分覆盖 |
| NIST SP 800-145 | Cloud Computing Definition | 5.1, 5.2 | [5.2.1 主要争议](../5.2%20批判分析/5.2.1%20主要争议.md) | 部分覆盖 |
| POSIX.1 (IEEE Std 1003.1) | Process/Thread Management & Resource Limits | 5.1, 5.7 | [5.7.2 典型运行时机制分析](../5.7%20系统运行时语义/5.7.2%20典型运行时机制分析.md) | 部分覆盖 |

## 3. 覆盖缺口与补齐计划

1. **MPI 4.0 条款级形式化缺失**：当前 `5.1` 仅涉及通用集群概念，需在第 `5.1/5.3/5.6` 中补充 MPI 点对点、集合通信、进程拓扑、One-sided 通信的形式化定义与语义。
   行动：依据 MPI 4.0 第 3、5、7、11 章，在 `5.0.1` 中建立条款原文与项目知识点的逐项映射，并在 `5.3/5.6` 补充形式化结构。

2. **OpenMP 共享内存并行语义空白**：项目尚未覆盖 OpenMP 5.2/6.0 的 worksharing-loop、task、target offload 等构造与集群节点内并行执行的关联。
   行动：在 `5.1` 增加 OpenMP 与 MPI 混合编程（MPI+X）章节；在 `5.6` 补充 OpenMP 调度语义。

3. **Slurm/Kubernetes 调度策略形式化不足**：`5.7.1` 仅列出静态/动态/负载均衡/优先级调度模型，未与 Slurm 的 Backfill、Preemption、QoS 以及 Kubernetes Scheduling Framework 的扩展点逐项对照。
   行动：在 `5.0.2` 中完成 Slurm、Kubernetes、JSDL、DRMAA 的条款映射，并在 `5.7` 补充调度策略的竞争比/排队论分析。

4. **HPC 基准与能效评估体系缺失**：项目未系统覆盖 HPCG、Graph500、TOP500/Green500 的指标体系及其对集群设计的影响。
   行动：在 `5.2/5.5` 增加 HPCG、Graph500、Green500 的批判分析与多表征（表格、公式、对比图）。

5. **互连与硬件抽象层标准未纳入**：InfiniBand/UCX、CXL、PCIe、UEFI/ACPI 等集群硬件互连与启动标准尚未在项目中有专门章节。
   行动：在 `5.1` 增加集群互连与内存池化（CXL、UCX、InfiniBand）章节；在 `5.7` 补充运行时 RDMA/共享内存语义。

## 5. 形式化工件链接

| 工件 | 路径 | 说明 |
|---|---|---|
| MPI 集合通信 TLA+ 规范 | `tools/tla-specifications/MPI_Collectives.tla`（待创建） | 集合通信正确性规约 |
| Slurm 调度排队模型 | `tools/automated-proof/slurm_queue_model.py`（待创建） | Backfill / QoS 策略模拟 |
| Kubernetes 调度 TLA+ 规范 | `tools/tla-specifications/KubernetesScheduler.tla`（待创建） | Pod 调度与资源约束 |
| HPCG/Graph500 多表征数据 | `5.集群系统/5.5 多表征/`（待补充） | 基准指标表与对比图 |

## 6. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建映射骨架 | Kimi Code CLI |
| 2026-07-02 | 补充 MPI/HPC、调度与资源管理详细映射，扩展主要对标标准与缺口计划 | Kimi Code CLI |
