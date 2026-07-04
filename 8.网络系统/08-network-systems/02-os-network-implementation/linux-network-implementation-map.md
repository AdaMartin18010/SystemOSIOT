# Linux 网络协议栈实现映射


<!-- TOC START -->

- [Linux 网络协议栈实现映射](#linux-网络协议栈实现映射)
  - [1. OSI / TCP/IP → Linux 子系统映射](#1-osi-tcpip-linux-子系统映射)
  - [2. 协议 → 数据结构/函数映射](#2-协议-数据结构函数映射)
  - [3. Socket API → 内核路径](#3-socket-api-内核路径)
  - [4. 数据包收发路径](#4-数据包收发路径)
    - [4.1 接收路径](#41-接收路径)
    - [4.2 发送路径](#42-发送路径)
  - [5. 标准映射](#5-标准映射)
  - [6. 相关文件](#6-相关文件)
  - [国际权威来源链接 / Authoritative Sources](#国际权威来源链接-authoritative-sources)

<!-- TOC END -->

> **目标**：把 `8.网络系统/` 中 OSI/TCP/IP 概念映射到 `2.操作系统/` 的 Linux `net/` 子系统实现。

---

## 1. OSI / TCP/IP → Linux 子系统映射

| OSI 层 | TCP/IP 层 | Linux 子系统 | 关键源码 |
|--------|-----------|--------------|----------|
| 应用层 | 应用层 | Socket API | `net/socket.c` |
| 表示层 | - | - | - |
| 会话层 | - | - | - |
| 传输层 | 传输层 | TCP/UDP | `net/ipv4/tcp.c`, `net/ipv4/udp.c` |
| 网络层 | 网络层 | IP / ICMP / 路由 | `net/ipv4/ip_input.c`, `net/ipv4/route.c` |
| 数据链路层 | 链路层 | Ethernet / Bridge / VLAN | `net/ethernet/`, `net/bridge/` |
| 物理层 | 链路层 | NIC Driver / PHY | `drivers/net/` |

---

## 2. 协议 → 数据结构/函数映射

| 协议 | 数据结构 | 核心函数 | 源码 |
|------|----------|----------|------|
| TCP | `struct tcp_sock` | `tcp_v4_rcv()`, `tcp_sendmsg()` | `net/ipv4/tcp_ipv4.c`, `net/ipv4/tcp.c` |
| UDP | `struct udp_sock` | `udp_rcv()`, `udp_sendmsg()` | `net/ipv4/udp.c` |
| IP | `struct sk_buff` + IP 头 | `ip_rcv()`, `ip_local_deliver()`, `ip_queue_xmit()` | `net/ipv4/ip_input.c`, `net/ipv4/ip_output.c` |
| ICMP | - | `icmp_rcv()`, `icmp_reply()` | `net/ipv4/icmp.c` |
| ARP | `struct neighbour` | `arp_rcv()` | `net/ipv4/arp.c` |
| Ethernet | `struct sk_buff` + eth 头 | `eth_type_trans()` | `net/ethernet/eth.c` |
| Bridge | `struct net_bridge` | `br_handle_frame()` | `net/bridge/br_input.c` |
| VLAN | `struct vlan_ethhdr` | `vlan_do_receive()` | `net/8021q/vlan_core.c` |

---

## 3. Socket API → 内核路径

| POSIX API | Linux 系统调用 | 内核入口函数 |
|-----------|----------------|--------------|
| `socket()` | `sys_socket()` | `__sys_socket()` |
| `bind()` | `sys_bind()` | `inet_bind()` |
| `listen()` | `sys_listen()` | `inet_listen()` |
| `accept()` | `sys_accept4()` | `inet_accept()` |
| `connect()` | `sys_connect()` | `tcp_v4_connect()` |
| `send()` | `sys_sendto()` | `tcp_sendmsg()` / `udp_sendmsg()` |
| `recv()` | `sys_recvfrom()` | `tcp_recvmsg()` / `udp_recvmsg()` |
| `setsockopt()` | `sys_setsockopt()` | `tcp_setsockopt()` / `ip_setsockopt()` |

---

## 4. 数据包收发路径

### 4.1 接收路径

```
NIC RX
  → 网卡驱动 napi_poll()
  → netif_receive_skb()
  → __netif_receive_skb_core()
  → ptype_base 分发
  → ip_rcv()
  → tcp_v4_rcv()
  → socket receive queue
  → 唤醒用户态 recv()
```

### 4.2 发送路径

```
send()
  → tcp_sendmsg()
  → tcp_write_xmit()
  → ip_queue_xmit()
  → dev_queue_xmit()
  → ndo_start_xmit()
  → NIC TX
```

---

## 5. 标准映射

| 标准 | Linux 实现 | 覆盖状态 |
|------|------------|----------|
| [RFC 791](https://datatracker.ietf.org/doc/html/rfc791) IP | `net/ipv4/` | 已覆盖 |
| [RFC 793](https://datatracker.ietf.org/doc/html/rfc793) TCP | `net/ipv4/tcp*.c` | 已覆盖 |
| [RFC 768](https://datatracker.ietf.org/doc/html/rfc768) UDP | `net/ipv4/udp.c` | 已覆盖 |
| [RFC 826](https://datatracker.ietf.org/doc/html/rfc826) ARP | `net/ipv4/arp.c` | 已覆盖 |
| [RFC 792](https://datatracker.ietf.org/doc/html/rfc792) ICMP | `net/ipv4/icmp.c` | 已覆盖 |
| [IEEE 802.1Q](https://standards.ieee.org/standard/802.1Q-2024.html) VLAN | `net/8021q/` | 已覆盖 |
| POSIX Socket | `net/socket.c` | 已覆盖 |

---

## 6. 相关文件

- [Linux 网络协议栈](../../../2.操作系统/02-operating-systems/06-networking/linux-network-stack.md)
- [Socket 与多路复用](../../../2.操作系统/02-operating-systems/06-networking/socket-and-multiplexing.md)
- [操作系统-网络-嵌入式-接口跨域映射](../../Analysis/操作系统-网络-嵌入式-接口跨域映射.md)

## 国际权威来源链接 / Authoritative Sources

- [RFC 791 - Internet Protocol](https://datatracker.ietf.org/doc/html/rfc791)
- [RFC 793 - Transmission Control Protocol](https://datatracker.ietf.org/doc/html/rfc793)
- [RFC 768 - User Datagram Protocol](https://datatracker.ietf.org/doc/html/rfc768)
- [RFC 792 - Internet Control Message Protocol](https://datatracker.ietf.org/doc/html/rfc792)
- [RFC 826 - Address Resolution Protocol](https://datatracker.ietf.org/doc/html/rfc826)
- [RFC 8200 - IPv6](https://datatracker.ietf.org/doc/html/rfc8200)
- [IEEE 802.1Q-2024 VLAN](https://standards.ieee.org/standard/802.1Q-2024.html)
- [POSIX.1-2024 Socket API](https://pubs.opengroup.org/onlinepubs/9799919799/)
- [Linux netdev subsystem documentation](https://docs.kernel.org/process/maintainer-netdev.html)
- [Linux Kernel Networking (Rami Rosen)](https://www.apress.com/gp/book/9781430261964)
