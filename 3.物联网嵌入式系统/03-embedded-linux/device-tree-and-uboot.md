# Device Tree 与 U-Boot 启动映射


<!-- TOC START -->

- [Device Tree 与 U-Boot 启动映射](#device-tree-与-u-boot-启动映射)
  - [1. 启动链概览](#1-启动链概览)
  - [2. U-Boot 关键阶段](#2-u-boot-关键阶段)
    - [2.1 常用命令](#21-常用命令)
  - [3. Device Tree 结构](#3-device-tree-结构)
    - [3.1 典型节点](#31-典型节点)
  - [4. Linux 启动时解析](#4-linux-启动时解析)
  - [5. U-Boot 与 Device Tree 的关系](#5-u-boot-与-device-tree-的关系)
  - [6. 标准与源码映射](#6-标准与源码映射)
  - [7. 相关文件](#7-相关文件)
  - [国际权威来源链接 | International Authoritative Sources](#国际权威来源链接--international-authoritative-sources)

<!-- TOC END -->

> **目标**：建立嵌入式 Linux 启动链中 U-Boot 与 Device Tree 的角色、数据结构与流程映射。

---

## 1. 启动链概览

```mermaid
graph LR
    RESET[SoC Reset] --> BL1[Boot ROM]
    BL1 --> BL2[SPL / MLO]
    BL2 --> UBOOT[U-Boot]
    UBOOT --> DTB[Device Tree Blob]
    DTB --> KERNEL[zImage/Image]
    KERNEL --> ROOTFS[Rootfs]
```

---

## 2. U-Boot 关键阶段

| 阶段 | 文件 | 功能 |
|------|------|------|
| SPL | `spl/` | 初始化 DDR、时钟、加载完整 U-Boot |
| U-Boot Proper | `common/`, `cmd/`, `drivers/` | 外设初始化、命令行、加载内核 |
| FIT Image | `uImage.itb` | 内核 + DTB + ramdisk 打包 |

### 2.1 常用命令

```text
setenv bootargs 'console=ttyS0,115200 root=/dev/mmcblk0p2 rw'
load mmc 0:1 ${kernel_addr_r} zImage
load mmc 0:1 ${fdt_addr_r} board.dtb
bootz ${kernel_addr_r} - ${fdt_addr_r}
```

---

## 3. Device Tree 结构

| 组件 | 说明 |
|------|------|
| DTS | Device Tree Source，人类可读源码 |
| DTB | Device Tree Blob，二进制 blob |
| DTC | Device Tree Compiler，编译器 |
| DTBO | Device Tree Overlay，运行时覆盖 |
| binding | 绑定文档，定义节点属性 |

### 3.1 典型节点

```dts
/ {
    model = "MyBoard";
    compatible = "vendor,myboard";

    cpus {
        cpu@0 { compatible = "arm,cortex-a53"; };
    };

    memory@80000000 {
        device_type = "memory";
        reg = <0x0 0x80000000 0x0 0x20000000>;
    };

    uart0: serial@10000000 {
        compatible = "ns16550a";
        reg = <0x10000000 0x100>;
        interrupts = <10>;
        clocks = <&clk_uart0>;
    };
};
```

---

## 4. Linux 启动时解析

| 函数 | 作用 |
|------|------|
| `setup_machine_fdt()` | 选择 machine_desc |
| `unflatten_device_tree()` | 反扁平化 DTB 为 device_node 树 |
| `of_platform_populate()` | 为节点创建 platform_device |
| `driver_probe()` | 匹配 compatible 并加载驱动 |

---

## 5. U-Boot 与 Device Tree 的关系

| 关系 | 说明 |
|------|------|
| U-Boot 可自带 DTB | 同一份 U-Boot 支持多板型 |
| 内核携带 DTB | Linux 构建时打包 |
| 运行时修改 | `fdt set` 命令修改 bootargs |
| Overlay | U-Boot 应用 DTBO 扩展硬件 |

---

## 6. 标准与源码映射

| 标准/源码 | Linux/ARM 文档 |
|-----------|----------------|
| Devicetree Spec | devicetree.org |
| U-Boot | `doc/` 目录、README |
| Linux 绑定 | `Documentation/devicetree/bindings/` |
| ARM Booting | `Documentation/arm/booting.rst` |

---

## 7. 相关文件

- [嵌入式 Linux 启动流程](./embedded-linux-bootflow.md)
- [HAL/BSP/设备树映射](../../../2.操作系统/02-operating-systems/08-interfaces/hal-bsp-device-tree.md)

## 国际权威来源链接 | International Authoritative Sources

- [Devicetree Specification](https://devicetree-specification.readthedocs.io/en/stable/)
- [U-Boot Documentation](https://u-boot.readthedocs.io/en/latest/)
- [Linux Kernel Documentation — Device Tree Bindings](https://docs.kernel.org/devicetree/bindings/)
- [Linux Kernel Documentation — ARM Booting](https://docs.kernel.org/arm/booting.html)
- [ARM Architecture Reference Manual](https://developer.arm.com/documentation)
- [RISC-V Privileged Spec](https://riscv.org/technical/specifications/)
- [项目国际化权威标准基线 — 3. 物联网嵌入式系统](../../../docs/international-baseline.md)
