# 网络系统国际来源映射 / Network Systems International Source Mapping


<!-- TOC START -->

- [网络系统国际来源映射 / Network Systems International Source Mapping](#网络系统国际来源映射-network-systems-international-source-mapping)
  - [1. 网络模型与分层架构](#1-网络模型与分层架构)
  - [2. 传输层与路由协议](#2-传输层与路由协议)
  - [3. 应用层协议与安全](#3-应用层协议与安全)
  - [4. 软件定义网络与可编程网络](#4-软件定义网络与可编程网络)
  - [5. 形式化方法与模型检验](#5-形式化方法与模型检验)
  - [6. 网络科学与数学基础](#6-网络科学与数学基础)
  - [7. Linux 网络工程实现](#7-linux-网络工程实现)
  - [维护记录](#维护记录)

<!-- TOC END -->

> 将 `8.网络系统/` 的核心概念、协议、算法与安全机制锚定到国际权威标准、RFC、教材与工程文档。

---

## 1. 网络模型与分层架构

| 概念 | 来源类型 | 来源 | 链接/位置 | 覆盖章节 |
|---|---|---|---|---|
| OSI Basic Reference Model | 国际标准 | [ISO/IEC 7498-1](https://www.iso.org/standard/20269.html) | <https://www.iso.org/standard/20269.html> | 8.1, 8.5 |
| TCP/IP Host Requirements | RFC | [RFC 1122](https://datatracker.ietf.org/doc/html/rfc1122)/1123 | <https://datatracker.ietf.org/doc/html/rfc1122> | 8.1, 8.6, 8.7 |
| Internet Protocol (IPv4) | RFC | [RFC 791](https://datatracker.ietf.org/doc/html/rfc791) | <https://datatracker.ietf.org/doc/html/rfc791> | 8.1, 8.6 |
| Internet Protocol (IPv6) | RFC | [RFC 8200](https://datatracker.ietf.org/doc/html/rfc8200) | <https://datatracker.ietf.org/doc/html/rfc8200> | 8.1, 8.6 |
| Ethernet MAC/PHY | 标准 | [IEEE 802.3-2022](https://standards.ieee.org/standard/802.3-2022.html) | <https://standards.ieee.org/standard/802.3-2022.html> | 8.1, 8.5 |
| VLAN Bridging | 标准 | [IEEE 802.1Q-2024](https://standards.ieee.org/standard/802.1Q-2024.html) | <https://standards.ieee.org/standard/802.1Q-2024.html> | 8.1, 8.5 |
| Wireless LAN | 标准 | [IEEE 802.11-2024](https://standards.ieee.org/standard/802.11-2024.html) | <https://standards.ieee.org/standard/802.11-2024.html> | 8.1, 8.5, 8.8 |

## 2. 传输层与路由协议

| 概念 | 来源类型 | 来源 | 链接/位置 | 覆盖章节 |
|---|---|---|---|---|
| Transmission Control Protocol (TCP) | RFC | [RFC 793](https://datatracker.ietf.org/doc/html/rfc793) | <https://datatracker.ietf.org/doc/html/rfc793> | 8.1, 8.6, 8.7 |
| TCP Congestion Control | RFC | [RFC 5681](https://datatracker.ietf.org/doc/html/rfc5681) | <https://datatracker.ietf.org/doc/html/rfc5681> | 8.1, 8.7 |
| User Datagram Protocol (UDP) | RFC | [RFC 768](https://datatracker.ietf.org/doc/html/rfc768) | <https://datatracker.ietf.org/doc/html/rfc768> | 8.1, 8.6 |
| Internet Control Message Protocol (ICMP) | RFC | [RFC 792](https://datatracker.ietf.org/doc/html/rfc792) | <https://datatracker.ietf.org/doc/html/rfc792> | 8.1, 8.6 |
| Address Resolution Protocol (ARP) | RFC | [RFC 826](https://datatracker.ietf.org/doc/html/rfc826) | <https://datatracker.ietf.org/doc/html/rfc826> | 8.1, 8.6 |
| QUIC Transport Protocol | RFC | [RFC 9000](https://datatracker.ietf.org/doc/html/rfc9000)/9001/9002/9114 | <https://datatracker.ietf.org/doc/html/rfc9000> | 8.1, 8.6, 8.7 |
| BGP-4 | RFC | [RFC 4271](https://datatracker.ietf.org/doc/html/rfc4271) | <https://datatracker.ietf.org/doc/html/rfc4271> | 8.1, 8.3 |
| OSPFv2 | RFC | [RFC 2328](https://datatracker.ietf.org/doc/html/rfc2328) | <https://datatracker.ietf.org/doc/html/rfc2328> | 8.1, 8.3 |

## 3. 应用层协议与安全

| 概念 | 来源类型 | 来源 | 链接/位置 | 覆盖章节 |
|---|---|---|---|---|
| HTTP Semantics / HTTP/1.1 / HTTP/3 | RFC | [RFC 9110](https://datatracker.ietf.org/doc/html/rfc9110)/9112/9114 | <https://datatracker.ietf.org/doc/html/rfc9110> | 8.1, 8.6 |
| TLS 1.3 | RFC | [RFC 8446](https://datatracker.ietf.org/doc/html/rfc8446) | <https://datatracker.ietf.org/doc/html/rfc8446> | 8.1, 8.2, 8.8 |
| DNS Concepts / Implementation | RFC | [RFC 1034](https://datatracker.ietf.org/doc/html/rfc1034)/1035 | <https://datatracker.ietf.org/doc/html/rfc1034> | 8.1, 8.6 |
| DNS Clarifications | RFC | [RFC 2181](https://datatracker.ietf.org/doc/html/rfc2181) | <https://datatracker.ietf.org/doc/html/rfc2181> | 8.1, 8.6 |
| Zero Trust Architecture | 框架 | [NIST SP 800-207](https://csrc.nist.gov/publications/detail/sp/800/207/final) | <https://csrc.nist.gov/publications/detail/sp/800/207/final> | 8.2, 8.8 |
| [NIST Cybersecurity Framework](https://www.nist.gov/cyberframework) | 框架 | CSF 2.0 | <https://www.nist.gov/cyberframework> | 8.2, 8.8 |
| EU AI Act | 法规 | 2024 | <https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32024R1689> | 8.8 |

## 4. 软件定义网络与可编程网络

| 概念 | 来源类型 | 来源 | 链接/位置 | 覆盖章节 |
|---|---|---|---|---|
| [OpenFlow](https://opennetworking.org/software-defined-standards/) | 协议 | ONF [OpenFlow](https://opennetworking.org/software-defined-standards/) 1.5.1 | <https://opennetworking.org/software-defined-standards/> | 8.8 |
| P4 / [P4Runtime](https://p4.org/) | 语言/接口 | [P4-16](https://p4.org/) / v1.4.1 | <https://p4.org/> | 8.8 |
| 5G-Advanced / [3GPP](https://www.3gpp.org/specifications) | 标准 | [3GPP](https://www.3gpp.org/specifications) Release 18 | <https://www.3gpp.org/specifications> | 8.8 |

## 5. 形式化方法与模型检验

| 概念 | 来源类型 | 来源 | 链接/位置 | 覆盖章节 |
|---|---|---|---|---|
| TLA+ / 时序逻辑 | 教材/工具 | Lamport, *Specifying Systems* | <https://lamport.azurewebsites.net/tla/book.html> | 8.3, 8.4, 8.6 |
| Principles of Model Checking | 教材 | Baier & Katoen | <https://mitpress.mit.edu/9780262026499/principles-of-model-checking/> | 8.4, 8.6 |
| QUIC/TCP 握手 TLA+ | 工件 | `tools/tla-specifications/QUIC.tla` | 项目内 | 8.6, 8.7 |

## 6. 网络科学与数学基础

| 概念 | 来源类型 | 来源 | 链接/位置 | 覆盖章节 |
|---|---|---|---|---|
| Network Science | 教材 | Barabási, *Network Science* | <http://networksciencebook.com/> | 8.1, 8.8 |
| Networks: An Introduction | 教材 | Newman | <https://academic.oup.com/book/5324> | 8.1, 8.8 |
| A Mathematical Theory of Communication | 论文 | Shannon (1948) | <https://doi.org/10.1002/j.1538-7305.1948.tb01338.x> | 8.1, 8.8 |
| Shortest Paths | 论文 | Dijkstra (1959) | <https://doi.org/10.1007/BF01386390> | 8.4, 8.8 |
| Max Flow | 论文 | Ford & Fulkerson (1956) | <https://doi.org/10.4153/CJM-1956-045-5> | 8.4, 8.8 |

## 7. Linux 网络工程实现

| 概念 | 来源类型 | 来源 | 链接/位置 | 覆盖章节 |
|---|---|---|---|---|
| Linux Kernel Networking | 教材 | Rami Rosen | Apress | 8.5, 8.6 |
| Linux netdev 维护者文档 | 文档 | Linux Kernel | <https://docs.kernel.org/process/maintainer-netdev.html> | 8.6, 8.7 |
| eBPF / XDP | 文档 | Linux Kernel | <https://docs.kernel.org/bpf/>, <https://docs.kernel.org/networking/xdp.html> | 8.6, 8.8 |
| Traffic Control (tc) | 文档 | Linux Kernel | <https://docs.kernel.org/networking/sched/> | 8.6, 8.7 |
| sk_buff / net_device | 源码 | Linux Kernel | `include/linux/skbuff.h`, `net/core/dev.c` | 8.5, 8.6 |

---

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-05 | 建立网络系统概念→国际来源映射表 | Kimi Code CLI |
