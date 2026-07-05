# UPPAAL 实时系统验证模型


<!-- TOC START -->

- [UPPAAL 实时系统验证模型](#uppaal-实时系统验证模型)
  - [文件清单](#文件清单)
  - [运行方式](#运行方式)
  - [与项目模块的关联](#与项目模块的关联)
  - [扩展计划](#扩展计划)
  - [维护记录](#维护记录)

<!-- TOC END -->

> 位置：`tools/uppaal-models/`
> 用途：为物联网、嵌入式系统提供时间自动机模型，验证实时调度与能耗约束。
> 工具：UPPPAAL Model Checker（<https://uppaal.org/）。>

## 文件清单

| 文件 | 内容 | 状态 |
|---|---|---|
| `IoT_Scheduling.xml` | 物联网传感器节点周期性采样-处理-传输-睡眠模型 | 已创建，待 UPPAAL 验证 |

## 运行方式

1. 下载 UPPAAL：<https://uppaal.org/>
2. 打开 `IoT_Scheduling.xml`。
3. 在 Verifier 中运行以下查询：
   - `A[] not deadlock`
   - `A[] node.t <= PERIOD`
   - `A[] node.deadline_miss == 0`

## 与项目模块的关联

- 对应 `3.物联网嵌入式系统/3.7 系统运行时语义` 中的实时调度分析。
- 对应 `validation/formal-artifacts-gap-audit.md` 中缺失的 UPPAAL 工件。

## 扩展计划

1. 增加多节点通信与冲突模型。
2. 增加能耗约束（电池容量、 duty cycle）。
3. 与 `3.0 国际标准映射` 中的 IEC 62443 / NIST SP 800-213 安全需求结合。

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建 IoT 实时调度 UPPAAL 模型 | Kimi Code CLI |
