# 高性能网络路径选择


<!-- TOC START -->

- [高性能网络路径选择](#高性能网络路径选择)
  - [1. 性能优化层次](#1-性能优化层次)
  - [2. 选择决策树](#2-选择决策树)
  - [3. 内核优化机制速查](#3-内核优化机制速查)
  - [4. 与 8.网络系统 的衔接](#4-与-8网络系统-的衔接)
  - [5. 相关文件](#5-相关文件)
  - [国际权威来源链接 / Authoritative Sources](#国际权威来源链接--authoritative-sources)

<!-- TOC END -->

> **范围说明**：当前深度止于 Linux 内核网络优化（NAPI/GRO/GSO/RPS/RFS/XPS/epoll/io_uring/eBPF/XDP）。RDMA/DPDK/SmartNIC kernel bypass 仅在文末列出，不做深入展开，如需可单独补充。

---

## 1. 性能优化层次

```mermaid
graph LR
    APP[应用层] -->|io_uring/epoll| SYSCALL[系统调用优化]
    SYSCALL -->|批量/零拷贝| KERNEL[内核协议栈]
    KERNEL -->|NAPI/GRO/GSO/RPS/RFS/XPS| OFFLOAD[软硬卸载]
    OFFLOAD -->|eBPF/XDP| FASTPATH[快速路径]
    FASTPATH -->|可选| BYPASS[DPDK/RDMA/SmartNIC]
```

---

## 2. 选择决策树

| 场景 | 推荐技术 | 关键参数 |
|------|----------|----------|
| 10k+ 并发连接 | epoll / io_uring | `somaxconn`, `tcp_max_syn_backlog`, `fs.aio-max-nr` |
| 高吞吐文件/网络混合 | io_uring | SQ/CQ 大小、注册 buffer、polling |
| 多核网络负载不均 | RPS/RFS/XPS | `rps_cpus`, `rps_flow_cnt`, `xps_cpus` |
| 小包高 PPS | GRO/GSO/TSO + NAPI | `napi_weight`, `gro_flush_timeout` |
| 防火墙/负载均衡 | eBPF/XDP | prog type、map size、verifier |
| 极低延迟（<10µs） | DPDK/RDMA/SmartNIC | 需单独专题 |

---

## 3. 内核优化机制速查

| 机制 | 作用 | 配置入口 |
|------|------|----------|
| NAPI | 轮询降低中断开销 | 驱动 `napi_struct` |
| GRO | 接收侧小包聚合 | `ethtool -K gro on` |
| GSO/TSO | 发送侧大包分段卸载 | `ethtool -K tso on` |
| RPS | 软件 RSS，把包分发到多核 | `/sys/class/net/ethX/queues/rx-*/rps_cpus` |
| RFS | 根据流把包送到处理核 | `rps_flow_cnt` |
| XPS | 发送队列 CPU 绑定 | `queues/tx-*/xps_cpus` |

---

## 4. 与 8.网络系统 的衔接

- OSI/TCP/IP 概念见 `8.网络系统/8.1 知识梳理/`
- Linux 实现映射见 `8.网络系统/08-network-systems/02-os-network-implementation/linux-network-implementation-map.md`
- 协议形式化语义见 `8.网络系统/8.6 形式语义/`

---

## 5. 相关文件

- [Linux 网络协议栈](./linux-network-stack.md)
- [Socket 与多路复用](./socket-and-multiplexing.md)
- [Netfilter / eBPF / XDP](./netfilter-ebpf-xdp.md)
- [内核卸载](./kernel-offload.md)

## 国际权威来源链接 / Authoritative Sources

- [Linux Scaling - RPS/RFS/XPS](https://docs.kernel.org/networking/scaling.html)
- [Linux Segmentation Offloads](https://docs.kernel.org/networking/segmentation-offloads.html)
- [Linux XDP documentation](https://docs.kernel.org/networking/xdp.html)
- [Linux io_uring documentation](https://docs.kernel.org/io_uring/)
- [io_uring paper by Jens Axboe (PDF)](https://kernel.dk/io_uring.pdf)
- [Linux epoll(7) manual](https://man7.org/linux/man-pages/man7/epoll.7.html)
- [Cilium BPF/XDP Reference Guide](https://docs.cilium.io/en/latest/bpf/)
