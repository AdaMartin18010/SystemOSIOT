# 5.0 集群系统 — 国际标准映射

## 1. 主要对标标准与基准

| 标准/基准/工具 | 版本 | 官方链接/DOI | 对应项目章节 |
|---|---|---|---|
| MPI Standard | 4.1 (2023) | <https://www.mpi-forum.org/docs/mpi-4.1/mpi41-report.pdf> | 5.1, 5.3, 5.6 |
| Slurm Workload Manager | 24.11 / 25.05 | <https://slurm.schedmd.com/> | 5.1, 5.3, 5.7 |
| TOP500 / Green500 | 2025-06 | <https://top500.org/> | 5.1, 5.2, 5.5 |
| Energy Aware Runtime (EAR) | v7.0 | <https://www.ear.energy/> | 5.2, 5.6, 5.7 |
| Kubernetes / HPC 混合调度 | v1.33 | <https://kubernetes.io/> | 5.1, 5.7 |

## 2. 标准/基准映射表

| 来源 | 核心内容 | 项目覆盖章节 | 证据文件 | 覆盖状态 |
|---|---|---|---|---|
| MPI 4.1 第7章 | Process Topologies | 5.1 | 待补充 | 未覆盖 |
| MPI 4.1 第8章 | MPI Environmental Management | 5.1 | 待补充 | 未覆盖 |
| Slurm 24.11 | Scheduling, QoS, Preemption, Backfill | 5.1, 5.7 | 待补充 | 未覆盖 |
| Green500 Jun 2025 | Energy Efficiency Metrics | 5.2, 5.5 | 待补充 | 未覆盖 |
| EAR v7.0 | Power capping & energy optimization | 5.2, 5.7 | 待补充 | 未覆盖 |

## 3. 覆盖缺口与补齐计划

1. 重构集群模块，区分 HPC/HA/LB/Storage/K8s 集群。
2. 增加 MPI 4.1 进程拓扑、集合通信、One-sided 通信形式化描述。
3. 增加 Slurm 架构、调度策略、能耗管理章节。
4. 用排队论或在线算法分析负载均衡竞争比。

## 4. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建映射骨架 | Kimi Code CLI |
