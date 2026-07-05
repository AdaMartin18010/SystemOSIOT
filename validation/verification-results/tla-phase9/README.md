# TLA+ 验证日志索引

> 位置：`validation/verification-results/tla-phase9/`
> 工具：TLC Model Checker（`tools/tla-specifications/tla2tools.jar`）

## Phase 4：操作系统 / RTOS 形式化工件验证结果

| 模型 | 配置 | 生成状态数 | 不同状态数 | 结果 | 日志 |
|---|---|---|---|---|---|
| `OS_ProcessStateMachine.tla` | `OS_ProcessStateMachine.cfg` | 337 | 112 | ✅ 通过 | [`OS_ProcessStateMachine.log`](./OS_ProcessStateMachine.log) |
| `OS_PageFault.tla` | `OS_PageFault.cfg` | 61 | 19 | ✅ 通过 | [`OS_PageFault.log`](./OS_PageFault.log) |
| `OS_SchedulerFairness.tla` | `OS_SchedulerFairness.cfg` | 19 | 10 | ✅ 通过 | [`OS_SchedulerFairness.log`](./OS_SchedulerFairness.log) |
| `FreeRTOS_TaskScheduler.tla` | `FreeRTOS_TaskScheduler.cfg` | 73 | 22 | ✅ 通过 | [`FreeRTOS_TaskScheduler.log`](./FreeRTOS_TaskScheduler.log) |

## Phase 9：网络 / IoT / 容器形式化工件验证结果

| 模型 | 配置 | 生成状态数 | 不同状态数 | 结果 | 日志 |
|---|---|---|---|---|---|
| `Raft.tla` | `Raft.cfg` | 102679 | 22977 | ✅ 通过 | [`Raft.log`](./Raft.log) |
| `Kubernetes.tla` | `Kubernetes.cfg` | 3322 | 594 | ✅ 通过 | [`Kubernetes.log`](./Kubernetes.log) |
| `QUIC.tla` | `QUIC.cfg` | 5 | 5 | ✅ 通过 | [`QUIC.log`](./QUIC.log) |
| `TCP_CongestionControl.tla` | `TCP_CongestionControl.cfg` | 1737 | 592 | ✅ 通过 | [`TCP_CongestionControl.log`](./TCP_CongestionControl.log) |
| `BGP_PathSelection.tla` | `BGP_PathSelection.cfg` | 49078 | 8186 | ✅ 通过 | [`BGP_PathSelection.log`](./BGP_PathSelection.log) |
| `OSPF_LinkState.tla` | `OSPF_LinkState.cfg` | 1132793 | 168844 | ✅ 通过 | [`OSPF_LinkState.log`](./OSPF_LinkState.log) |

## 复现命令

```bash
cd tools/tla-specifications
java -cp tla2tools.jar tlc2.TLC <ModelName> -config <ModelName>.cfg -nowarning
```

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-05 | Phase 9 网络/IoT/容器 TLA+ 验证日志 | Kimi Code CLI |
| 2026-07-06 | Phase 4 OS/RTOS TLA+ 验证日志 | Kimi Code CLI |
