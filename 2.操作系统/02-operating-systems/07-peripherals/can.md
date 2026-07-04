# CAN 总线


<!-- TOC START -->

- [CAN 总线](#can-总线)
  - [1. CAN 基础](#1-can-基础)
  - [2. 帧格式](#2-帧格式)
    - [2.1 标准帧（CAN 2.0A）](#21-标准帧can-20a)
    - [2.2 扩展帧（CAN 2.0B）](#22-扩展帧can-20b)
    - [2.3 CAN FD](#23-can-fd)
  - [3. 位时序](#3-位时序)
  - [4. Linux SocketCAN](#4-linux-socketcan)
    - [4.1 核心结构](#41-核心结构)
    - [4.2 用户态使用](#42-用户态使用)
- [配置 CAN 接口](#配置-can-接口)
- [发送](#发送)
- [接收](#接收)
    - [4.3 编程接口](#43-编程接口)
  - [5. 物理层](#5-物理层)
  - [6. 场景分析](#6-场景分析)
  - [7. 术语表](#7-术语表)
  - [8. 相关文件](#8-相关文件)
  - [国际权威来源链接 / Authoritative Sources](#国际权威来源链接--authoritative-sources)

<!-- TOC END -->

> **权威来源**：ISO 11898, Linux Kernel `net/can/`, SocketCAN Docs。
>
> **目标**：系统讲解 CAN 协议、帧格式、位时序、SocketCAN、汽车/工业应用场景。

---

## 1. CAN 基础

| 特性 | 说明 |
|------|------|
| 信号线 | CAN_H, CAN_L（差分） |
| 拓扑 | 总线型 |
| 仲裁 | CSMA/CD+AMP（载波监听多路访问/冲突检测+仲裁） |
| 优先级 | ID 越小优先级越高 |
| 距离 | 最高 1 Mbps @ 40m，40 kbps @ 1km |

---

## 2. 帧格式

### 2.1 标准帧（CAN 2.0A）

| 字段 | 长度 | 说明 |
|------|------|------|
| SOF | 1 bit | 帧起始 |
| Identifier | 11 bit | 标识符 |
| RTR | 1 bit | 远程帧标志 |
| IDE | 1 bit | 扩展帧标志 |
| DLC | 4 bit | 数据长度码（0~8） |
| Data | 0~8 byte | 数据 |
| CRC | 15 bit | 循环冗余校验 |
| ACK | 2 bit | 应答 |
| EOF | 7 bit | 帧结束 |

### 2.2 扩展帧（CAN 2.0B）

- Identifier 29 bit。

### 2.3 CAN FD

| 特性 | 说明 |
|------|------|
| 数据段波特率 | 最高 8 Mbps 或更高 |
| 数据长度 | 0~64 byte |
| 兼容 | 可与 CAN 2.0 共存 |

---

## 3. 位时序

| 段 | 说明 |
|----|------|
| SYNC_SEG | 同步段 |
| PROP_SEG | 传播段 |
| PHASE_SEG1 | 相位缓冲段 1 |
| PHASE_SEG2 | 相位缓冲段 2 |
| SJW | 同步跳转宽度 |

---

## 4. Linux SocketCAN

### 4.1 核心结构

| 数据结构 | 源码 | 说明 |
|----------|------|------|
| `struct net_device` | `include/linux/netdevice.h` | CAN 网络设备 |
| `struct can_frame` | `include/linux/can.h` | CAN 帧 |
| `struct canfd_frame` | `include/linux/can.h` | CAN FD 帧 |

### 4.2 用户态使用

```bash
# 配置 CAN 接口
ip link set can0 type can bitrate 500000
ip link set can0 up

# 发送
cansend can0 123#DEADBEEF

# 接收
candump can0
```

### 4.3 编程接口

```c
struct sockaddr_can addr;
struct can_frame frame;
int s = socket(PF_CAN, SOCK_RAW, CAN_RAW);
strcpy(ifr.ifr_name, "can0");
ioctl(s, SIOCGIFINDEX, &ifr);
addr.can_family = AF_CAN;
addr.can_ifindex = ifr.ifr_ifindex;
bind(s, (struct sockaddr *)&addr, sizeof(addr));
```

---

## 5. 物理层

| 参数 | 典型值 |
|------|--------|
| 终端电阻 | 120 Ω（总线两端） |
| 特性阻抗 | 120 Ω |
| 拓扑 | 干线 + 短支线 |
| 最大节点数 | 理论 110，实际数十 |

---

## 6. 场景分析

| 场景 | 关键参数 | 验证指标 |
|------|----------|----------|
| 汽车 ECU 通信 | 波特率 500k, 采样点 | 总线负载 |
| 工业控制 | 波特率 250k, 终端电阻 | 误码率 |
| 机器人 | CAN FD 2M/5M | 实时性 |
| 电池管理 BMS | 多节点，ID 分配 | 仲裁延迟 |

---

## 7. 术语表

| 中文 | 英文 | 一句话定义 |
|------|------|------------|
| CAN | Controller Area Network | 控制器局域网总线 |
| CAN FD | CAN with Flexible Data-rate | 可变数据速率 CAN |
| SOF | Start Of Frame | 帧起始 |
| DLC | Data Length Code | 数据长度码 |
| CRC | Cyclic Redundancy Check | 循环冗余校验 |
| ACK | Acknowledge | 应答 |
| SocketCAN | SocketCAN | Linux 中 CAN 的网络接口框架 |

---

## 8. 相关文件

- [外设概念树](./peripheral-concept-tree.md)
- [外设总线选择决策树](./decision-tree-peripheral-bus.md)

## 国际权威来源链接 / Authoritative Sources

- [ISO 11898-1:2015 - CAN Data Link Layer and Physical Signaling](https://www.iso.org/standard/63648.html)
- [Bosch CAN Specification 2.0](https://www.bosch-semiconductors.com/us/ip-modules/can-protocol/can-2-0.html)
- [Linux SocketCAN documentation](https://docs.kernel.org/networking/can.html)
- [CAN in Automation (CiA)](https://www.can-cia.org/)
