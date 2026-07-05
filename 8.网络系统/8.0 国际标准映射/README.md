# 8.0 网络系统 — 国际标准映射


<!-- TOC START -->

- [8.0 网络系统 — 国际标准映射](#80-网络系统--国际标准映射)
  - [1. 主要对标标准与 RFC](#1-主要对标标准与-rfc)
  - [2. 标准/RFC 映射表](#2-标准rfc-映射表)
  - [3. 覆盖缺口与补齐计划](#3-覆盖缺口与补齐计划)
  - [5. 形式化工件链接](#5-形式化工件链接)
  - [6. 维护记录](#6-维护记录)
  - [国际权威来源链接 | International Authoritative Sources](#国际权威来源链接--international-authoritative-sources)

<!-- TOC END -->

> 详细概念 → 来源映射请见 [`source-mapping-network.md`](./source-mapping-network.md)。
> 分层（OSI/TCP/IP）→ 来源映射请见 [`layered-source-mapping.md`](./layered-source-mapping.md)。
> 高级协议、安全增强与新型网络标准请见 [`advanced-protocol-security-standards.md`](./advanced-protocol-security-standards.md)。

## 1. 主要对标标准与 RFC

| 标准/RFC | 版本 | DOI/链接 | 对应项目章节 |
|---|---|---|---|
| [ISO/IEC 7498-1](https://www.iso.org/standard/20269.html) | OSI Basic Reference Model | <https://www.iso.org/standard/20269.html> | 8.1, 8.5 |
| IP / TCP / Host Requirements | [RFC 791](https://datatracker.ietf.org/doc/html/rfc791)/793/1122/1123 | <https://datatracker.ietf.org/doc/html/rfc1122> | 8.1, 8.6, 8.7 |
| UDP / ICMP / ARP / IPv6 | [RFC 768](https://datatracker.ietf.org/doc/html/rfc768)/792/826/8200 | <https://datatracker.ietf.org/doc/html/rfc8200> | 8.1, 8.6 |
| TCP Congestion Control | [RFC 5681](https://datatracker.ietf.org/doc/html/rfc5681) | <https://datatracker.ietf.org/doc/html/rfc5681> | 8.1, 8.7 |
| HTTP | [RFC 9110](https://datatracker.ietf.org/doc/html/rfc9110)/9112/9113/9114 | <https://datatracker.ietf.org/doc/html/rfc9110> | 8.1, 8.6 |
| TLS | [RFC 8446](https://datatracker.ietf.org/doc/html/rfc8446) (TLS 1.3) | <https://datatracker.ietf.org/doc/html/rfc8446> | 8.1, 8.2, 8.8 |
| DNS | [RFC 1034](https://datatracker.ietf.org/doc/html/rfc1034)/1035/2181 | <https://datatracker.ietf.org/doc/html/rfc1034> | 8.1, 8.6 |
| QUIC | [RFC 9000](https://datatracker.ietf.org/doc/html/rfc9000)/9001/9002/9114 | DOI: 10.17487/RFC9000 | 8.1, 8.6, 8.7 |
| BGP | [RFC 4271](https://datatracker.ietf.org/doc/html/rfc4271)/4456/4760/7752/9107/9552 | DOI: 10.17487/RFC4271 | 8.1, 8.3, 8.6 |
| OSPF | [RFC 2328](https://datatracker.ietf.org/doc/html/rfc2328)/5340 | DOI: 10.17487/RFC2328 | 8.1, 8.3, 8.6 |
| [IEEE 802.3](https://standards.ieee.org/standard/802.3-2022.html) Ethernet | [IEEE 802.3-2022](https://standards.ieee.org/standard/802.3-2022.html) | <https://standards.ieee.org/standard/802.3-2022.html> | 8.1, 8.5 |
| [IEEE 802.1Q](https://standards.ieee.org/standard/802.1Q-2024.html) VLAN | [IEEE 802.1Q-2024](https://standards.ieee.org/standard/802.1Q-2024.html) | <https://standards.ieee.org/standard/802.1Q-2024.html> | 8.1, 8.5 |
| IEEE 802.11 | [IEEE 802.11-2024](https://standards.ieee.org/standard/802.11-2024.html) | <https://standards.ieee.org/standard/802.11-2024.html> | 8.1, 8.5, 8.8 |
| [OpenFlow](https://opennetworking.org/software-defined-standards/) | 1.5.1 | <https://opennetworking.org/software-defined-standards/> | 8.8 |
| P4 / [P4Runtime](https://p4.org/) | [P4-16](https://p4.org/) / v1.4.1 | <https://p4.org/> | 8.8 |
| [3GPP](https://www.3gpp.org/specifications) 5G-Advanced / IEEE 802.11be / ETSI MEC | Release 18 / 802.11be-2024 / MEC | <https://www.3gpp.org/specifications> | 8.8 |
| [NIST SP 800-207](https://csrc.nist.gov/publications/detail/sp/800/207/final) | Zero Trust Architecture | <https://csrc.nist.gov/publications/detail/sp/800/207/final> | 8.2, 8.8 |

## 2. 标准/RFC 映射表

| 来源 | 核心内容 | 项目覆盖章节 | 证据文件 | 覆盖状态 |
|---|---|---|---|---|
| [ISO/IEC 7498-1](https://www.iso.org/standard/20269.html) | OSI Basic Reference Model | 8.1, 8.5 | 8.1/1.8.20 | 已覆盖 |
| [RFC 791](https://datatracker.ietf.org/doc/html/rfc791)/793/1122 | IPv4 / TCP / host requirements | 8.1, 8.6 | 8.1/1.8.21, 8.6/8.6.1 | 已覆盖 |
| [RFC 768](https://datatracker.ietf.org/doc/html/rfc768)/792/826/8200 | UDP / ICMP / ARP / IPv6 | 8.1, 8.6 | 8.1/1.8.21 | 已覆盖 |
| [RFC 5681](https://datatracker.ietf.org/doc/html/rfc5681) | TCP congestion control | 8.1, 8.7 | 8.1/1.8.21 | 已覆盖 |
| [RFC 9110](https://datatracker.ietf.org/doc/html/rfc9110)/9112/9113/9114 | HTTP semantics / messaging / caching / alt-svc | 8.1, 8.6 | 8.1/1.8.21 | 已覆盖 |
| [RFC 8446](https://datatracker.ietf.org/doc/html/rfc8446) | TLS 1.3 | 8.1, 8.2, 8.8 | 8.1/1.8.22 | 已覆盖 |
| [RFC 1034](https://datatracker.ietf.org/doc/html/rfc1034)/1035/2181 | DNS concepts / implementation / clarifications | 8.1, 8.6 | 8.1/1.8.22 | 已覆盖 |
| [RFC 1122](https://datatracker.ietf.org/doc/html/rfc1122) | Host requirements (link, IP, TCP) | 8.1, 8.6 | 8.1/1.8.21 | 已覆盖 |
| [RFC 9000](https://datatracker.ietf.org/doc/html/rfc9000) | QUIC transport protocol | 8.1, 8.6, 8.7, 8.8 | tools/tla-specifications/QUIC.tla, 8.8/8.8.25 | 已覆盖 |
| [RFC 4271](https://datatracker.ietf.org/doc/html/rfc4271) | BGP-4 path selection | 8.1, 8.3 | 8.1/1.8.22 | 已覆盖 |
| [RFC 2328](https://datatracker.ietf.org/doc/html/rfc2328) | OSPFv2 Dijkstra/LSA | 8.1, 8.3 | 8.1/1.8.22 | 已覆盖 |
| [IEEE 802.3-2022](https://standards.ieee.org/standard/802.3-2022.html) | Ethernet MAC/PHY | 8.1, 8.5 | 8.1/1.8.21 | 已覆盖 |
| [IEEE 802.1Q-2024](https://standards.ieee.org/standard/802.1Q-2024.html) | VLAN bridging | 8.1, 8.5 | 8.1/1.8.21 | 已覆盖 |
| [IEEE 802.11-2024](https://standards.ieee.org/standard/802.11-2024.html) | WLAN MAC/PHY | 8.1, 8.5 | 8.5/8.5.1, advanced-protocol-security-standards.md | 已覆盖 |
| [P4-16](https://p4.org/) Language Spec | Protocol-independent packet processing | 8.8 | 8.0 国际标准映射, 8.8/8.8.31 | 已覆盖 |
| 分层权威来源映射 | OSI/TCP/IP 各层 → 标准/RFC/工程文档 | 8.0, 8.1–8.8 | [layered-source-mapping.md](./layered-source-mapping.md) | 已覆盖 |
| [NIST SP 800-207](https://csrc.nist.gov/publications/detail/sp/800/207/final) | Zero Trust principles | 8.2, 8.8 | 8.2/8.2.x, advanced-protocol-security-standards.md | 部分覆盖 |
| DNSSEC / DoH / DoT | DNS security & privacy | 8.2, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.27 | 已覆盖 |
| RPKI / BGPsec / ROV | BGP security extensions | 8.2, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.26 | 已覆盖 |
| IPsec / IKEv2 | VPN / tunnel security | 8.2, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.28 | 已覆盖 |
| HTTP/2 / WebSocket | Application layer protocols | 8.1, 8.6 | 8.1/1.8.21, advanced-protocol-security-standards.md | 已覆盖 |
| MPLS / SRv6 / EVPN | Routing & traffic engineering | 8.3, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.29 | 已覆盖 |
| VXLAN / Geneve / CNI | Data center network virtualization | 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.30 | 已覆盖 |
| WebSocket / HTTP/2 | Full-duplex Web channels and multiplexing | 8.6, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.33 | 已覆盖 |
| TCP Fast Open / BBR / MPTCP / SCTP / DCCP | Transport layer enhancements and alternatives | 8.1, 8.7, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.34 | 已覆盖 |
| MQTT v5.0 / CoAP | IoT publish-subscribe and constrained REST protocols | 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.35 | 已覆盖 |
| TLS 1.3 / PKI | Modern TLS handshake, certificates and deployment | 8.2, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.36 | 已覆盖 |
| SNMP / NetFlow / IPFIX / sFlow | Network observability and telemetry | 8.7, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.37 | 已覆盖 |
| TSN / 802.1AS / DetNet | Time-sensitive networking and deterministic Ethernet | 8.5, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.38 | 已覆盖 |
| Zero Trust / SASE / SDP | Zero trust architecture and network access security | 8.2, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.39 | 已覆盖 |
| AIOps / 异常检测 / 智能流量工程 | Network AI and intelligent operations | 8.7, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.40 | 已覆盖 |
| CSA / TI / STIX / TAXII / MITRE ATT&CK | Cyber situation awareness and threat intelligence | 8.2, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.41 | 已覆盖 |
| NTN / Starlink / 3GPP NR-NTN | Satellite internet and non-terrestrial networks | 8.5, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.42 | 已覆盖 |
| Deterministic IP / SRv6+ / AP6 | Deterministic IP, network slicing and IPv6+ telemetry | 8.3, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.43 | 已覆盖 |
| RDMA / RoCE / DCB | High-speed data center networks | 8.5, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.44 | 已覆盖 |
| SOC / SIEM / SOAR | Security operations, log correlation and response orchestration | 8.2, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.45 | 已覆盖 |
| IBN / YANG / Network Digital Twin | Intent-based networking, YANG modeling and digital twin | 8.3, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.46 | 已覆盖 |
| CFN / Computing-aware Routing / 东数西算 | Computing force network and computing-network convergence | 8.3, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.47 | 已覆盖 |
| SD-WAN / SASE / MEF 70 | Software-defined WAN and secure access service edge | 8.2, 8.8 | advanced-protocol-security-standards.md, 8.8/8.8.48 | 已覆盖 |

## 3. 覆盖缺口与补齐计划

1. **RFC 引用规范化**：全模块知识点标注 RFC 编号/DOI/版本，删除无来源推测。
2. ~~QUIC 独立专章~~：已新增 `8.8/8.8.25 QUIC 协议深度分析.md`。
3. ~~BGP 安全~~：已新增 `8.8/8.8.26 BGP 安全与 RPKI.md`。
4. ~~可编程网络~~：OpenFlow/P4 专题已补齐；形式化语义仍可作为后续 Phase 9 工件。
5. **零信任架构**：增加 [NIST SP 800-207](https://csrc.nist.gov/publications/detail/sp/800/207/final) 映射。
6. ~~高级安全协议~~：DNSSEC/DoH/DoT、RPKI/BGPsec/ROV、IPsec/IKEv2 专题已补齐。
7. ~~数据中心与可编程网络~~：VXLAN/Geneve/CNI/OpenFlow/P4 专题已补齐。
8. ~~移动通信与边缘网络~~：3GPP 5G/802.11be/ETSI MEC 专题已补齐。
9. ~~WebSocket / HTTP/2~~：已新增 `8.8/8.8.33 WebSocket 与 HTTP/2：全双工与多路复用.md`。
10. ~~传输层增强~~：已新增 `8.8/8.8.34 传输层演进：TCP Fast Open、BBR、MPTCP、SCTP 与 DCCP.md`。
11. ~~物联网协议~~：已新增 `8.8/8.8.35 物联网协议：MQTT v5.0 与 CoAP.md`。
12. ~~TLS 1.3 / PKI~~：已新增 `8.8/8.8.36 TLS 1.3 与密码学工程：握手、证书与部署.md`。
13. ~~网络可观测性~~：已新增 `8.8/8.8.37 网络可观测性与遥测：SNMP、NetFlow、IPFIX 与 sFlow.md`。
14. ~~TSN / 确定性以太网~~：已新增 `8.8/8.8.38 时间敏感网络与确定性以太网：TSN、802.1AS 与 DetNet.md`。
15. ~~零信任 / SASE / SDP~~：已新增 `8.8/8.8.39 零信任架构与网络访问安全：NIST SP 800-207、SASE 与 SDP.md`。
16. ~~AIOps / 智能流量工程~~：已新增 `8.8/8.8.40 网络人工智能与智能运维：AIOps、异常检测与流量工程.md`。
17. ~~网络安全态势感知与威胁情报~~：已新增 `8.8/8.8.41 网络安全态势感知与威胁情报.md`。
18. ~~卫星互联网 / NTN~~：已新增 `8.8/8.8.42 卫星互联网与非地面网络：NTN、Starlink 与 3GPP NR-NTN.md`。
19. ~~确定性 IP / SRv6+ / AP6~~：已新增 `8.8/8.8.43 确定性 IP 与 SRv6+：网络切片、随流检测与 AP6.md`。
20. ~~高速数据中心网络~~：已新增 `8.8/8.8.44 高速数据中心网络：RDMA、RoCE 与 DCB.md`。
21. ~~SOC / SIEM / SOAR~~：已新增 `8.8/8.8.45 网络安全运营中心与 SIEM：日志、告警与响应编排.md`。
22. ~~IBN / YANG / Network Digital Twin~~：已新增 `8.8/8.8.46 意图驱动网络与数字孪生：IBN、YANG 与网络数字孪生.md`。
23. ~~CFN / Computing-aware Routing / 东数西算~~：已新增 `8.8/8.8.47 算力网络与算网融合：CFN、算力路由与东数西算.md`。
24. ~~SD-WAN / SASE / MEF 70~~：已新增 `8.8/8.8.48 软件定义广域网与安全访问服务边缘：SD-WAN 与 SASE 工程实践.md`。

## 5. 形式化工件链接

| 工件 | 路径 | 说明 |
|---|---|---|
| QUIC/TCP 握手 TLA+ | `tools/tla-specifications/QUIC.tla` + `QUIC.cfg` | 传输层握手状态机与安全性质 |

## 6. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建映射骨架 | Kimi Code CLI |
| 2026-07-05 | 补齐以太网/IP/TCP/UDP/HTTP/TLS/DNS/OSI/[IEEE 802.3](https://standards.ieee.org/standard/802.3-2022.html)/802.1Q 权威来源与链接 | Kimi Code CLI |
| 2026-07-05 | 向 8.1/8.6/8.7/8.8 关键章节批量追加 RFC/ISO/IEEE/NIST 权威来源链接 | Kimi Code CLI |
| 2026-07-05 | 向 8.1–8.8 全部 154 个 Markdown 文件追加国际权威来源链接，覆盖核心概念、批判分析、形式化结构/证明/语义、运行时语义与综合专题 | Kimi Code CLI |
| 2026-07-05 | 新增高级协议与安全标准映射表，覆盖 DNSSEC/DoH/DoT、RPKI/BGPsec、IPsec/IKEv2、MPLS/SRv6、VXLAN/Geneve、5G/802.11be/MEC | Kimi Code CLI |
| 2026-07-05 | 新增 QUIC/HTTP/3 深度分析专题（8.8.25）与 BGP 安全/RPKI 专题（8.8.26），更新映射表证据与覆盖状态 | Kimi Code CLI |
| 2026-07-05 | 新增 DNS 安全（DNSSEC/DoH/DoT，8.8.27）与 IPsec/IKEv2 VPN 安全（8.8.28）专题，更新映射表覆盖状态 | Kimi Code CLI |
| 2026-07-05 | 新增 MPLS/SRv6/EVPN 路由专题（8.8.29）与 VXLAN/Geneve/CNI 数据中心网络专题（8.8.30），更新映射表覆盖状态 | Kimi Code CLI |
| 2026-07-05 | 新增可编程网络 OpenFlow/P4 专题（8.8.31）与 5G/边缘计算/Wi-Fi 7 专题（8.8.32），更新映射表覆盖状态 | Kimi Code CLI |
| 2026-07-05 | 新增 WebSocket/HTTP/2（8.8.33）、传输层演进（8.8.34）、物联网协议 MQTT/CoAP（8.8.35）、TLS 1.3/PKI（8.8.36）专题，更新映射表覆盖状态 | Kimi Code CLI |
| 2026-07-05 | 新增网络可观测性（8.8.37）、TSN/DetNet（8.8.38）、零信任/SASE/SDP（8.8.39）、AIOps（8.8.40）、态势感知与威胁情报（8.8.41）、卫星互联网/NTN（8.8.42）、确定性 IP/SRv6+（8.8.43）、RDMA/RoCE（8.8.44）专题，更新映射表覆盖状态 | Kimi Code CLI |
| 2026-07-05 | 新增 SOC/SIEM/SOAR（8.8.45）、IBN/YANG/数字孪生（8.8.46）、算力网络/东数西算（8.8.47）、SD-WAN/SASE（8.8.48）专题，更新映射表覆盖状态 | Kimi Code CLI |

## 国际权威来源链接 | International Authoritative Sources

- [ISO/IEC 7498-1 — OSI Basic Reference Model](https://www.iso.org/standard/20269.html)
- [RFC 1122 — Host Requirements](https://datatracker.ietf.org/doc/html/rfc1122)
- [RFC 791 — Internet Protocol (IPv4)](https://datatracker.ietf.org/doc/html/rfc791)
- [RFC 793 — Transmission Control Protocol (TCP)](https://datatracker.ietf.org/doc/html/rfc793)
- [RFC 8200 — Internet Protocol, Version 6 (IPv6)](https://datatracker.ietf.org/doc/html/rfc8200)
- [RFC 5681 — TCP Congestion Control](https://datatracker.ietf.org/doc/html/rfc5681)
- [IEEE 802.3-2022 — Ethernet](https://standards.ieee.org/standard/802.3-2022.html)
- [IEEE 802.1Q-2024 — VLAN Bridging](https://standards.ieee.org/standard/802.1Q-2024.html)
- [NIST SP 800-207 — Zero Trust Architecture](https://csrc.nist.gov/publications/detail/sp/800/207/final)
- [NIST Cybersecurity Framework](https://www.nist.gov/cyberframework)
- [RFC 8446 — TLS 1.3](https://datatracker.ietf.org/doc/html/rfc8446)
- [NIST AI Risk Management Framework](https://www.nist.gov/itl/ai-risk-management-framework)
- [EU AI Act](https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32024R1689)
- [3GPP Specifications](https://www.3gpp.org/specifications)
- [Lamport, L. Specifying Systems (TLA+)](https://lamport.azurewebsites.net/tla/book.html)
