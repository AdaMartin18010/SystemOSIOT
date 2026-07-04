# 网络命名空间与虚拟网络

> **权威来源**：Linux Kernel Networking, kernel.org `Documentation/networking/netns/`, LWN.net。
>
> **目标**：系统讲解 Linux network namespace、veth、bridge、macvlan/ipvlan、SR-IOV 与容器网络模型。

---

## 1. Network Namespace

### 1.1 隔离资源

| 资源 | 是否隔离 |
|------|----------|
| 网络设备 | 是 |
| IP 地址/路由表 | 是 |
| iptables/nftables 规则 | 是 |
| /proc/net /sys/class/net | 是 |
| 监听端口 | 是 |
| 套接字 | 是 |
| 物理网卡 | 否（需 move 进入 netns） |

### 1.2 创建与管理

```bash
# 创建
ip netns add ns1

# 进入
ip netns exec ns1 bash

# 查看
ip netns list

# 将物理网卡移入 netns
ip link set eth1 netns ns1
```

---

## 2. veth pair

```mermaid
graph LR
    NS1[Netns A] -->|veth0| BR[Bridge]
    BR -->|veth1| NS2[Netns B]
```

- 成对出现，一端在 netns，另一端在 root netns 或 bridge。
- 包从一端进入，从另一端发出。

---

## 3. Linux Bridge

| 概念 | 说明 |
|------|------|
| bridge | 二层交换机 |
| STP | 生成树协议 |
| VLAN filtering | 基于 VLAN 的端口隔离 |
| fdb | 转发数据库 |

```bash
ip link add br0 type bridge
ip link set br0 up
ip link set veth1 master br0
```

---

## 4. macvlan / ipvlan

### 4.1 macvlan

| 模式 | 说明 |
|------|------|
| bridge | 同宿主 macvlan 间可通信 |
| vepa | 所有流量经过外部交换机 |
| passthrough | 物理网卡直接交给一个容器 |
| private | 隔离模式 |

### 4.2 ipvlan

| 模式 | 说明 |
|------|------|
| L2 | 与 macvlan bridge 类似，共享 MAC |
| L3 | 三层路由，共享 MAC |

- ipvlan 适合高密度容器，避免 MAC 地址耗尽。

---

## 5. SR-IOV

| 概念 | 说明 |
|------|------|
| PF | Physical Function，完整网卡功能 |
| VF | Virtual Function，轻量虚拟网卡 |
| IOMMU | 隔离 VF DMA |

- VF 可直接透传给容器/VM，接近裸机性能。

---

## 6. 容器网络模型对比

| 模型 | 性能 | 隔离 | 适用 |
|------|------|------|------|
| veth + bridge | 中 | L2 | 默认容器网络 |
| macvlan | 高 | L2 | 需要独立 MAC |
| ipvlan | 高 | L3/L2 | 高密度容器 |
| SR-IOV | 极高 | 硬件 | NFV/HPC |
| overlay (VXLAN) | 中 | L2 over L3 | 跨主机容器 |

---

## 7. CNI 映射

| CNI 插件 | 底层机制 |
|----------|----------|
| bridge | veth + linux bridge |
| macvlan | macvlan |
| ipvlan | ipvlan |
| host-device | 物理网卡 move |
| sriov | SR-IOV VF |
| calico | veth + BGP/route |
| flannel | VXLAN/host-gw |
| cilium | eBPF + vxlan/direct-routing |

---

## 8. 场景分析

| 场景 | 方案 | 关键参数 | 验证指标 |
|------|------|----------|----------|
| 单主机容器 | veth+bridge | 子网，NAT | 连通性 |
| 需要独立 IP | macvlan | 父接口，模式 | 广播域隔离 |
| 高密度微服务 | ipvlan L3 | 路由 | ARP 表规模 |
| 5G/NFV | SR-IOV | VF 数量，NUMA | 吞吐接近裸机 |
| 跨主机 Pod | CNI overlay | VXLAN/BGP | 跨节点延迟 |

---

## 9. 术语表

| 中文 | 英文 | 一句话定义 |
|------|------|------------|
| netns | Network Namespace | 隔离网络栈的 Linux 命名空间 |
| veth | Virtual Ethernet | 成对虚拟网卡 |
| bridge | Linux Bridge | 二层软件交换机 |
| macvlan | MAC VLAN | 每个接口独立 MAC 的虚拟网络 |
| ipvlan | IP VLAN | 共享宿主 MAC 的虚拟网络 |
| SR-IOV | Single Root I/O Virtualization | 网卡硬件虚拟化 |
| CNI | Container Network Interface | 容器网络接口标准 |

---

## 10. 相关文件

- [Linux 网络协议栈](./linux-network-stack.md)
- [操作系统场景分析树](../00-concept-atlas/scenario-analysis-tree-os.md)
