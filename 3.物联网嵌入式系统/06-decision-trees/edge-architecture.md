# 边缘计算架构决策树


<!-- TOC START -->

- [边缘计算架构决策树](#边缘计算架构决策树)
  - [1. 决策树](#1-决策树)
  - [2. 架构模式对比](#2-架构模式对比)
  - [3. 选型因素](#3-选型因素)
  - [4. 关键技术与栈](#4-关键技术与栈)
  - [5. 相关文件](#5-相关文件)
  - [国际权威来源链接 | International Authoritative Sources](#国际权威来源链接--international-authoritative-sources)

<!-- TOC END -->

> **目标**：为 IoT/嵌入式系统选择“云-边-端”分层架构：纯云端、网关聚合、边缘推理、分布式边缘。

---

## 1. 决策树

```mermaid
graph TD
    A[设备数量与数据量] -->|少量, 数据小, 实时性低| B[直连云]
    A -->|多设备, 协议异构, 需协议转换| C[边缘网关聚合]
    A -->|高实时, 大数据, 本地决策| D[边缘计算节点]
    A -->|广域分布, 自治, 协同| E[分布式边缘/雾计算]

    B --> B1[设备 → 云 API]
    C --> C1[设备 → 网关 → 云]
    D --> D1[设备 → 边缘节点 → 云]
    E --> E1[多边缘节点协同]
```

---

## 2. 架构模式对比

| 模式 | 延迟 | 带宽 | 成本 | 复杂度 | 自治性 |
|------|------|------|------|--------|--------|
| 直连云 | 高 | 高 | 低 | 低 | 低 |
| 边缘网关 | 中 | 中 | 中 | 中 | 中 |
| 边缘计算 | 低 | 低 | 中 | 高 | 高 |
| 分布式边缘 | 低 | 低 | 高 | 高 | 很高 |

---

## 3. 选型因素

| 因素 | 偏向边缘侧 | 偏向云端 |
|------|-----------|----------|
| 实时性 | 要求高 | 可容忍 |
| 数据隐私 | 敏感 | 可上传 |
| 网络带宽 | 有限/贵 | 充裕 |
| 算力需求 | 高（AI 推理） | 低 |
| 运维复杂度 | 可接受 | 希望简单 |

---

## 4. 关键技术与栈

| 层级 | 技术 |
|------|------|
| 端侧 | MCU + RTOS / Embedded Linux, MQTT/CoAP |
| 网关 | Embedded Linux + Docker/containerd, EdgeX Foundry / KubeEdge |
| 边缘节点 | Kubernetes / K3s, GPU/TPU, 时序数据库 |
| 云 | IoT Hub, Data Lake, AI 训练 |

---

## 5. 相关文件

- [协议选择决策树](./protocol-selection.md)
- [Linux vs RTOS 决策树](./linux-vs-rtos.md)
- [跨域映射](../../Analysis/操作系统-网络-嵌入式-接口跨域映射.md)

## 国际权威来源链接 | International Authoritative Sources

- [ISO/IEC 30141:2024 — IoT Reference Architecture](https://www.iso.org/standard/88800.html)
- [IEC 62443-2-1:2024 — IACS Security Requirements](https://webstore.iec.ch/en/publication/62883)
- [NIST SP 800-213 / 800-213A — IoT Device Cybersecurity Guidance](https://csrc.nist.gov/publications/detail/sp/800/213/final)
- [OASIS MQTT v5.0 Specification](https://docs.oasis-open.org/mqtt/mqtt/v5.0/mqtt-v5.0.html)
- [RFC 7252 — The Constrained Application Protocol (CoAP)](https://doi.org/10.17487/RFC7252)
- [项目国际化权威标准基线 — 3. 物联网嵌入式系统](../../../docs/international-baseline.md)
