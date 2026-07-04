# 网络分层 → 权威来源映射 / Network Layer → Authoritative Source Mapping

> 将 OSI/TCP/IP 分层模型中的每一层、关键协议与机制锚定到国际权威标准、RFC 与工程文档。

---

## 1. 物理层 / Physical Layer

| 概念/机制 | 来源类型 | 来源 | 链接 |
|---|---|---|---|
| 物理层接口与信号 | 国际标准 | ISO/IEC 7498-1 | <https://www.iso.org/standard/20269.html> |
| Ethernet PHY | 标准 | IEEE 802.3-2022 | <https://standards.ieee.org/standard/802.3-2022.html> |
| Wireless PHY | 标准 | IEEE 802.11-2024 | <https://standards.ieee.org/standard/802.11-2024.html> |
| 5G NR PHY | 标准 | 3GPP TS 38.300 | <https://www.3gpp.org/specifications> |
| NIC / DMA / SR-IOV | 规范 | PCI-SIG PCIe Base Spec | <https://pcisig.com/specifications> |

## 2. 数据链路层 / Data Link Layer

| 概念/机制 | 来源类型 | 来源 | 链接 |
|---|---|---|---|
| 数据链路层服务 | 国际标准 | ISO/IEC 7498-1 | <https://www.iso.org/standard/20269.html> |
| Ethernet MAC / LLC | 标准 | IEEE 802.3-2022 | <https://standards.ieee.org/standard/802.3-2022.html> |
| VLAN / Bridging | 标准 | IEEE 802.1Q-2024 | <https://standards.ieee.org/standard/802.1Q-2024.html> |
| WLAN MAC | 标准 | IEEE 802.11-2024 | <https://standards.ieee.org/standard/802.11-2024.html> |
| ARP | RFC | RFC 826 | <https://datatracker.ietf.org/doc/html/rfc826> |
| Linux `net_device` / NAPI | 源码/文档 | Linux Kernel `net/core/dev.c`, `include/linux/netdevice.h` | <https://docs.kernel.org/networking/driver.html> |

## 3. 网络层 / Network Layer

| 概念/机制 | 来源类型 | 来源 | 链接 |
|---|---|---|---|
| 网络层服务 | 国际标准 | ISO/IEC 7498-1 | <https://www.iso.org/standard/20269.html> |
| IPv4 | RFC | RFC 791 | <https://datatracker.ietf.org/doc/html/rfc791> |
| IPv6 | RFC | RFC 8200 | <https://datatracker.ietf.org/doc/html/rfc8200> |
| ICMP | RFC | RFC 792 | <https://datatracker.ietf.org/doc/html/rfc792> |
| Host Requirements | RFC | RFC 1122/1123 | <https://datatracker.ietf.org/doc/html/rfc1122> |
| IPsec Architecture | RFC | RFC 4301 | <https://datatracker.ietf.org/doc/html/rfc4301> |
| BGP-4 | RFC | RFC 4271 | <https://datatracker.ietf.org/doc/html/rfc4271> |
| OSPFv2 | RFC | RFC 2328 | <https://datatracker.ietf.org/doc/html/rfc2328> |
| MPLS | RFC | RFC 3031 | <https://datatracker.ietf.org/doc/html/rfc3031> |
| SRv6 | RFC | RFC 8402/8986 | <https://datatracker.ietf.org/doc/html/rfc8402> |
| Linux IP / Routing | 源码/文档 | Linux Kernel `net/ipv4/`, `net/ipv6/` | <https://docs.kernel.org/networking/> |

## 4. 传输层 / Transport Layer

| 概念/机制 | 来源类型 | 来源 | 链接 |
|---|---|---|---|
| 传输层服务 | 国际标准 | ISO/IEC 7498-1 | <https://www.iso.org/standard/20269.html> |
| TCP | RFC | RFC 793 | <https://datatracker.ietf.org/doc/html/rfc793> |
| UDP | RFC | RFC 768 | <https://datatracker.ietf.org/doc/html/rfc768> |
| TCP Congestion Control | RFC | RFC 5681 | <https://datatracker.ietf.org/doc/html/rfc5681> |
| TCP Fast Open | RFC | RFC 7413 | <https://datatracker.ietf.org/doc/html/rfc7413> |
| BBR Congestion Control | RFC | RFC 8312 | <https://datatracker.ietf.org/doc/html/rfc8312> |
| SCTP | RFC | RFC 4960 | <https://datatracker.ietf.org/doc/html/rfc4960> |
| QUIC | RFC | RFC 9000/9001/9002 | <https://datatracker.ietf.org/doc/html/rfc9000> |
| DTLS | RFC | RFC 9147 | <https://datatracker.ietf.org/doc/html/rfc9147> |
| Linux TCP/UDP | 源码/文档 | Linux Kernel `net/ipv4/tcp*.c`, `net/ipv4/udp.c` | <https://docs.kernel.org/networking/> |

## 5. 应用层 / Application Layer

| 概念/机制 | 来源类型 | 来源 | 链接 |
|---|---|---|---|
| 应用层服务 | 国际标准 | ISO/IEC 7498-1 | <https://www.iso.org/standard/20269.html> |
| HTTP Semantics / HTTP/1.1 | RFC | RFC 9110/9112 | <https://datatracker.ietf.org/doc/html/rfc9110> |
| HTTP/3 | RFC | RFC 9114 | <https://datatracker.ietf.org/doc/html/rfc9114> |
| HTTP/2 | RFC | RFC 7540/7541 | <https://datatracker.ietf.org/doc/html/rfc7540> |
| TLS 1.3 | RFC | RFC 8446 | <https://datatracker.ietf.org/doc/html/rfc8446> |
| DNS Concepts / Implementation | RFC | RFC 1034/1035 | <https://datatracker.ietf.org/doc/html/rfc1034> |
| DNSSEC | RFC | RFC 4033/4034/4035 | <https://datatracker.ietf.org/doc/html/rfc4033> |
| DoH / DoT | RFC | RFC 8484 / RFC 7858 | <https://datatracker.ietf.org/doc/html/rfc8484> |
| WebSocket | RFC | RFC 6455 | <https://datatracker.ietf.org/doc/html/rfc6455> |
| MQTT v5.0 | 标准 | OASIS MQTT | <https://docs.oasis-open.org/mqtt/mqtt/v5.0/mqtt-v5.0.html> |
| CoAP | RFC | RFC 7252 | <https://datatracker.ietf.org/doc/html/rfc7252> |

## 6. 安全、管理与可编程网络 / Security, Management & Programmable Networks

| 概念/机制 | 来源类型 | 来源 | 链接 |
|---|---|---|---|
| Zero Trust Architecture | 框架 | NIST SP 800-207 | <https://csrc.nist.gov/publications/detail/sp/800/207/final> |
| Cybersecurity Framework | 框架 | NIST CSF 2.0 | <https://www.nist.gov/cyberframework> |
| Security & Privacy Controls | 框架 | NIST SP 800-53 Rev. 5 | <https://csrc.nist.gov/publications/detail/sp/800/53/rev-5/final> |
| MITRE ATT&CK | 知识库 | MITRE | <https://attack.mitre.org/> |
| RPKI / ROA | RFC | RFC 6480/6482/6487 | <https://datatracker.ietf.org/doc/html/rfc6480> |
| BGPsec | RFC | RFC 8205 | <https://datatracker.ietf.org/doc/html/rfc8205> |
| ROV | RFC | RFC 6811 | <https://datatracker.ietf.org/doc/html/rfc6811> |
| IKEv2 | RFC | RFC 7296 | <https://datatracker.ietf.org/doc/html/rfc7296> |
| OpenFlow | 协议 | ONF OpenFlow 1.5.1 | <https://opennetworking.org/software-defined-standards/> |
| P4 / P4Runtime | 语言/接口 | P4.org | <https://p4.org/> |
| CNI Spec | 规范 | CNCF | <https://www.cni.dev/docs/spec/> |
| Linux eBPF / XDP / tc | 文档 | Linux Kernel | <https://docs.kernel.org/bpf/>, <https://docs.kernel.org/networking/xdp.html> |

---

## 7. 跨层映射到项目章节

| 分层 | 主要项目章节 |
|---|---|
| 物理层 | 8.1/1.8.21, 8.5/8.5.1, 8.8 |
| 数据链路层 | 8.1/1.8.21, 8.5/8.5.1, 8.6/8.6.1 |
| 网络层 | 8.1/1.8.21, 8.1/1.8.22, 8.3/8.3.1, 8.6/8.6.1, 8.8 |
| 传输层 | 8.1/1.8.21, 8.6/8.6.1, 8.7/8.7.1, 8.8 |
| 应用层 | 8.1/1.8.21, 8.1/1.8.22, 8.6/8.6.1, 8.8 |
| 安全/可编程网络 | 8.2, 8.8, advanced-protocol-security-standards.md |

---

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-05 | 建立 OSI/TCP/IP 分层 → 权威来源映射表 | Kimi Code CLI |
