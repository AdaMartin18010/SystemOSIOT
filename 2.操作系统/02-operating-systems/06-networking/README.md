# 06-networking / OS 网络子系统


<!-- TOC START -->

- [06-networking / OS 网络子系统](#06-networking--os-网络子系统)
  - [文件列表](#文件列表)
  - [跨域衔接](#跨域衔接)
  - [返回](#返回)

<!-- TOC END -->

本目录从操作系统内核视角解析网络：socket 状态机、TCP/IP 数据路径、I/O 多路复用、内核卸载、流量控制、网络命名空间与 eBPF/XDP。

## 文件列表

- [linux-network-stack.md](./linux-network-stack.md) — Linux 网络协议栈数据路径
- [socket-and-multiplexing.md](./socket-and-multiplexing.md) — socket 状态机与 select/poll/epoll/io_uring 决策树
- [netfilter-ebpf-xdp.md](./netfilter-ebpf-xdp.md) — netfilter、conntrack、eBPF、XDP
- [kernel-offload.md](./kernel-offload.md) — NAPI、GRO/GSO/TSO、RPS/RFS/XPS、多队列 NIC
- [traffic-control.md](./traffic-control.md) — tc qdisc、流量整形与调度
- [network-namespace.md](./network-namespace.md) — veth、bridge、macvlan/ipvlan、SR-IOV、CNI 映射
- [high-performance-networking.md](./high-performance-networking.md) — 高性能网络路径选择

## 跨域衔接

- [8.网络系统 / Linux 网络协议栈实现映射](../../../8.网络系统/08-network-systems/02-os-network-implementation/linux-network-implementation-map.md)
- [8.网络系统 / 概念图](../../../8.网络系统/8.5%20多表征/8.5.1%20概念图.md)

## 返回

- [返回操作系统总览](../README.md)
