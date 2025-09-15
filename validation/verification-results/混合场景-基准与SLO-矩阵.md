# 虚拟化 × 容器混合场景：基准与 SLO 矩阵

## 1. 目标

- 为 VM、容器、容器 in VM 三类形态建立可复现基准与 SLO 映射，支撑容量规划与回归验证。

## 2. 指标与工具

- 计算：吞吐/延迟/尾延迟、上下文切换、运行队列长度（perf/eBPF/pssched）。
- 内存：命中率、缺页中断、内存带宽（pcm, perf, pressure stall）。
- 存储：IOPS/吞吐/延迟分位（fio）。
- 网络：PPS/延迟/抖动（iperf3, pktgen, qperf）。
- 虚拟化：vCPU 就绪、co-stop、ballooning、TPS（vCenter/esxtop）。

## 3. 矩阵（示例）

| 场景 | 工作负载 | 目标 SLO | 基线 | 当前 | 偏差 | 备注 |
|---|---|---|---|---|---|---|
| 裸机-OS | CPU 密集 | p99 < 5ms | 参考基线 | 待测 | - | 绑核/频率固定 |
| VM | 同上 | p99 < 8ms | 裸机+Δ | 待测 | - | 超配比 ≤ 1.2 |
| 容器 | 同上 | p99 < 6ms | 裸机+δ | 待测 | - | cgroup 上限/共享核 |
| 容器 in VM | 同上 | p99 < 9ms | VM+δ | 待测 | - | 叠加开销评估 |
| 网络 NSX×CNI | 东西向 | p99 < 1ms | 参考基线 | 待测 | - | 微分段策略生效 |

## 4. 方法

1) 固定时钟、频率与电源策略；记录 NUMA 拓扑与亲和。
2) 每项变更（内核、驱动、策略）触发回归跑矩阵，并更新趋势图。
3) 对超 SLO 的项进行根因分析（跨层时间线：vCenter 事件 ↔ Guest eBPF）。

## 5. 产出

- 趋势图、回归报告、容量规划建议、变更闸口阈值。

---

### 附录：采集配置清单（示例）

- 时间同步：NTP/PTP，记录偏移与抖动；统一时区与时间戳格式。
- vCenter：性能计数器（vCPU 就绪、co-stop、内存压缩/balloon/TPS）、迁移/快照事件订阅。
- Guest：node-exporter、perf/eBPF（采样频率、事件集）、pressure stall、irq/softirq 统计。
- 容器：cAdvisor/CRI 指标、cgroup v2 统计、镜像与容器元数据标签。
- 网络：iperf3/pktgen 参数、队列与 offload 配置（GRO/GSO/TSO/RPS/RFS）。
- 存储：fio 作业文件、块设备调度器、写缓存/对齐策略、vSAN SPBM 策略快照。
