# 操作系统 / Operating Systems


<!-- TOC START -->

- [操作系统 / Operating Systems](#操作系统--operating-systems)
  - [📚 领域概览 / Domain Overview](#-领域概览--domain-overview)
  - [🏗️ 领域架构 / Domain Architecture](#️-领域架构--domain-architecture)
    - [核心子领域](#核心子领域)
    - [新增概念分析体系](#新增概念分析体系)
  - [🔗 技术关联 / Technical Relationships](#-技术关联--technical-relationships)
    - [前置知识](#前置知识)
    - [相关技术](#相关技术)
    - [应用场景](#应用场景)
  - [📖 学习路径 / Learning Path](#-学习路径--learning-path)
    - [初级 (Beginner)](#初级-beginner)
    - [中级 (Intermediate)](#中级-intermediate)
    - [高级 (Advanced)](#高级-advanced)
  - [🛠️ 实践项目 / Practical Projects](#️-实践项目--practical-projects)
    - [推荐项目](#推荐项目)
    - [开发环境](#开发环境)
  - [📚 推荐资源 / Recommended Resources](#-推荐资源--recommended-resources)
    - [经典教材](#经典教材)
    - [在线资源](#在线资源)
  - [🔄 更新日志 / Update Log](#-更新日志--update-log)

<!-- TOC END -->

## 📚 领域概览 / Domain Overview

操作系统是SystemOSIOT项目的核心领域之一，专注于现代操作系统的设计、实现和优化。本领域涵盖了从传统单机操作系统到分布式操作系统的完整技术栈。

## 🏗️ 领域架构 / Domain Architecture

### 核心子领域

```text
02-operating-systems/
├── 00-concept-atlas/           # 概念图谱：概念树、属性-关系、机制组合、依赖树、决策树
├── 01-process-management/      # 进程管理
├── 02-memory-management/       # 内存管理
├── 03-file-systems/            # 文件系统
├── 04-device-management/       # 设备管理
├── 05-linux-kernel/            # Linux 内核实现专题
├── 06-networking/              # OS 网络子系统（socket/epoll/io_uring/eBPF/XDP）
├── 07-peripherals/             # 外设与总线（PCIe/USB/I2C/SPI/UART/GPIO/CAN）
├── 08-interfaces/              # 接口与抽象层（系统调用/ABI/ELF/POSIX/HAL/BSP/设备树）
└── README.md                   # 本文件
```

### 新增概念分析体系

本目录已按统一模板建立以下六类概念分析工件：

1. [概念树](./00-concept-atlas/concept-tree-os.md)
2. [属性-关系映射](./00-concept-atlas/attribute-relationship-map-os.md)
3. [机制组合树](./00-concept-atlas/mechanism-composition-tree-os.md)
4. [依赖树](./00-concept-atlas/dependency-tree-os.md)
5. [场景分析树 / 决策树](./00-concept-atlas/scenario-analysis-tree-os.md)
6. [国际来源映射](./00-concept-atlas/source-mapping-os.md)

### 新增专题索引

#### 05-linux-kernel / Linux 内核实现
- [Linux 源码地图](./05-linux-kernel/linux-source-map.md)
- [进程调度 Linux](./05-linux-kernel/process-scheduling-linux.md)
- [内存管理 Linux](./05-linux-kernel/memory-management-linux.md)
- [VFS 与文件系统 Linux](./05-linux-kernel/vfs-filesystems-linux.md)
- [设备与驱动 Linux](./05-linux-kernel/devices-drivers-linux.md)
- [安全机制 Linux](./05-linux-kernel/security-linux.md)

#### 06-networking / OS 网络子系统
- [Linux 网络协议栈](./06-networking/linux-network-stack.md)
- [Socket 与多路复用](./06-networking/socket-and-multiplexing.md)
- [Netfilter / eBPF / XDP](./06-networking/netfilter-ebpf-xdp.md)
- [内核卸载](./06-networking/kernel-offload.md)
- [流量控制](./06-networking/traffic-control.md)
- [网络命名空间](./06-networking/network-namespace.md)

#### 07-peripherals / 外设与总线
- [外设概念树](./07-peripherals/peripheral-concept-tree.md)
- [中断与 DMA](./07-peripherals/interrupts-and-dma.md)
- [外设总线决策树](./07-peripherals/decision-tree-peripheral-bus.md)
- [I2C](./07-peripherals/i2c.md)
- [PCIe](./07-peripherals/pcie.md)
- [USB](./07-peripherals/usb.md)
- [SPI](./07-peripherals/spi.md)
- [UART](./07-peripherals/uart.md)
- [GPIO](./07-peripherals/gpio.md)
- [CAN](./07-peripherals/can.md)

#### 08-interfaces / 接口与抽象层
- [系统调用接口](./08-interfaces/syscall-interface.md)
- [ABI 与 API](./08-interfaces/abi-api.md)
- [内核-用户边界](./08-interfaces/kernel-user-boundary.md)
- [POSIX 映射](./08-interfaces/posix-mapping.md)
- [HAL / BSP / 设备树](./08-interfaces/hal-bsp-device-tree.md)
- [跨层映射](./08-interfaces/cross-layer-mapping.md)

## 🔗 技术关联 / Technical Relationships

### 前置知识

- [系统理论基础](../../1.系统理论/01-system-theory/01-fundamentals/README.md)
- [系统架构设计](../../1.系统理论/01-system-theory/02-architecture/README.md)

### 相关技术

- [分布式系统](../../4.分布式系统/README.md)
- [容器与微服务](../../7.容器与微服务/README.md)
- [网络系统](../../8.网络系统/README.md)

### 应用场景

- 企业级服务器操作系统
- 嵌入式实时操作系统
- 云计算平台操作系统
- 移动设备操作系统

## 📖 学习路径 / Learning Path

### 初级 (Beginner)

1. 操作系统基本概念
2. 进程和线程管理
3. 内存管理基础
4. 文件系统入门

### 中级 (Intermediate)

1. 内核设计和实现
2. 设备驱动开发
3. 系统性能优化
4. 安全机制设计

### 高级 (Advanced)

1. 分布式操作系统
2. 虚拟化技术深度应用
3. 实时系统设计
4. 操作系统安全审计

## 🛠️ 实践项目 / Practical Projects

### 推荐项目

- 简单操作系统内核开发
- 设备驱动程序编写
- 文件系统实现
- 进程调度器设计

### 开发环境

- Linux开发环境
- QEMU模拟器
- GCC编译工具链
- GDB调试工具

## 📚 推荐资源 / Recommended Resources

### 经典教材

- 《操作系统概念》- Abraham Silberschatz
- 《现代操作系统》- Andrew S. Tanenbaum
- 《深入理解计算机系统》- Randal E. Bryant

### 在线资源

- Linux内核文档
- OSDev Wiki
- MIT 6.828操作系统课程

## 🔄 更新日志 / Update Log

- **2024-12-19**: 创建领域README文件
- **2025-07-05**: 新增 00-concept-atlas 概念图谱、05-linux-kernel、06-networking、07-peripherals、08-interfaces 专题，补齐 OS/网络/外设/接口/决策树与国际来源映射
- **2026-07-05**: 完成 Linux kernel（VFS/设备/安全）、networking（kernel-offload/tc/netns）、peripherals（PCIe/USB/SPI/UART/GPIO/CAN）、interfaces（ABI/API/内核-用户边界）等剩余专题索引
- **计划**: 继续完善各子领域内容

---

> 操作系统是计算机系统的核心，掌握操作系统技术是理解现代计算系统的基础。
> Operating systems are the core of computer systems. Mastering operating system technology is the foundation for understanding modern computing systems.
