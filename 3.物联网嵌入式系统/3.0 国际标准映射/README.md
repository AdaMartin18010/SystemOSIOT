# 3.0 物联网嵌入式系统 — 国际标准映射

## 1. 主要对标标准

| 标准/规范 | 版本 | 官方链接/DOI | 对应项目章节 |
|---|---|---|---|
| ISO/IEC 30141 | 2024 (Edition 2) | <https://www.iso.org/standard/88800.html> | 3.1, 3.3 |
| IEC 62443-2-1 | 2024 | <https://webstore.iec.ch/en/publication/62883> | 3.1, 3.2, 3.7 |
| NIST SP 800-213 / 800-213A | 2024 | <https://csrc.nist.gov/publications/detail/sp/800/213/final> | 3.1, 3.2, 3.7 |
| MQTT | v5.0 (OASIS) | <https://docs.oasis-open.org/mqtt/mqtt/v5.0/mqtt-v5.0.html> | 3.1, 3.6, 3.7 |
| Matter / Thread | 1.4 / 1.4 | <https://csa-iot.org/all-solutions/matter/> | 3.1, 3.5, 3.7 |
| CoAP | RFC 7252/8323 | <https://doi.org/10.17487/RFC7252> | 3.1, 3.6 |
| LwM2M | 1.2 | <https://omaspecworks.org/what-is-oma-specworks/iot/lightweight-m2m-lwm2m/> | 3.1, 3.6 |

## 2. 标准条款映射表

| 标准条款 | 条款标题 | 项目覆盖章节 | 证据文件 | 覆盖状态 |
|---|---|---|---|---|
| ISO/IEC 30141:2024 5 | IoT Reference Architecture | 3.1 知识梳理 | 待补充 | 部分覆盖 |
| ISO/IEC 30141:2024 6 | Trustworthiness | 3.2 批判分析 | 待补充 | 未覆盖 |
| IEC 62443-2-1:2024 | Asset owner security requirements | 3.2, 3.7 | 待补充 | 未覆盖 |
| NIST SP 800-213A | IoT Device Cybersecurity Requirement Catalog | 3.2, 3.7 | 待补充 | 未覆盖 |
| MQTT v5.0 2.2 | Control Packets | 3.1, 3.6 | 待补充 | 部分覆盖 |
| Matter 1.4 Core | Device Attestation | 3.1, 3.5 | 待补充 | 未覆盖 |

## 3. 覆盖缺口与补齐计划

1. 重构参考架构章节，对齐 ISO/IEC 30141:2024 的 Digital Entity / Physical Entity / IoT Device 视图。
2. 增加 IEC 62443 安全等级 (SL0–SL4) 与 NIST SP 800-213A 需求目录映射。
3. 增加 MQTT v5.0 Properties、Matter/Thread、LwM2M 1.2 协议形式化状态机。
4. 引入 UPPAAL 时间自动机对实时调度/能耗管理做案例验证。

## 5. 形式化工件链接

| 工件 | 路径 | 说明 |
|---|---|---|
| IoT 实时调度 UPPAAL | `tools/uppaal-models/IoT_Scheduling.xml` | 传感器节点周期性采样-处理-传输-睡眠时间自动机 |

## 6. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建映射骨架 | Kimi Code CLI |
