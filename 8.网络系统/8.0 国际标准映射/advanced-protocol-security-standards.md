# 网络高级协议与安全标准映射 / Advanced Protocol & Security Standards Mapping


<!-- TOC START -->

- [网络高级协议与安全标准映射 / Advanced Protocol & Security Standards Mapping](#网络高级协议与安全标准映射-advanced-protocol-security-standards-mapping)
  - [1. 传输层增强与新型传输协议](#1-传输层增强与新型传输协议)
  - [2. 网络安全与隐私增强](#2-网络安全与隐私增强)
  - [3. 路由与流量工程扩展](#3-路由与流量工程扩展)
  - [4. 应用层协议扩展](#4-应用层协议扩展)
  - [5. 数据中心与软件定义网络](#5-数据中心与软件定义网络)
  - [6. 移动通信与边缘网络](#6-移动通信与边缘网络)
  - [覆盖状态与补齐计划](#覆盖状态与补齐计划)
  - [维护记录](#维护记录)

<!-- TOC END -->

> 覆盖 `8.网络系统/` 中尚未在核心映射表中展开的进阶协议、安全增强机制与新型网络标准。

---

## 1. 传输层增强与新型传输协议

| 概念 | 来源类型 | 来源 | 链接/位置 | 覆盖章节 |
|---|---|---|---|---|
| TCP Fast Open | RFC | [RFC 7413](https://datatracker.ietf.org/doc/html/rfc7413) | <https://datatracker.ietf.org/doc/html/rfc7413> | 8.1, 8.7 |
| TCP BBR Congestion Control | RFC / Draft | [RFC 8312](https://datatracker.ietf.org/doc/html/rfc8312) / BBR | <https://datatracker.ietf.org/doc/html/rfc8312> | 8.1, 8.7 |
| Multipath TCP (MPTCP) | RFC | [RFC 8684](https://datatracker.ietf.org/doc/html/rfc8684) | <https://datatracker.ietf.org/doc/html/rfc8684> | 8.1, 8.8 |
| SCTP | RFC | [RFC 4960](https://datatracker.ietf.org/doc/html/rfc4960) | <https://datatracker.ietf.org/doc/html/rfc4960> | 8.1, 8.8 |
| DCCP | RFC | [RFC 4340](https://datatracker.ietf.org/doc/html/rfc4340) | <https://datatracker.ietf.org/doc/html/rfc4340> | 8.1, 8.8 |
| Datagram Transport Layer Security (DTLS) | RFC | [RFC 9147](https://datatracker.ietf.org/doc/html/rfc9147) | <https://datatracker.ietf.org/doc/html/rfc9147> | 8.2, 8.8 |

## 2. 网络安全与隐私增强

| 概念 | 来源类型 | 来源 | 链接/位置 | 覆盖章节 |
|---|---|---|---|---|
| DNSSEC | RFC | [RFC 4033](https://datatracker.ietf.org/doc/html/rfc4033)/4034/4035 | <https://datatracker.ietf.org/doc/html/rfc4033> | 8.1, 8.2 |
| DNS-over-HTTPS (DoH) | RFC | [RFC 8484](https://datatracker.ietf.org/doc/html/rfc8484) | <https://datatracker.ietf.org/doc/html/rfc8484> | 8.2, 8.8 |
| DNS-over-TLS (DoT) | RFC | [RFC 7858](https://datatracker.ietf.org/doc/html/rfc7858) | <https://datatracker.ietf.org/doc/html/rfc7858> | 8.2, 8.8 |
| RPKI / ROA | RFC | [RFC 6480](https://datatracker.ietf.org/doc/html/rfc6480)/6482/6487 | <https://datatracker.ietf.org/doc/html/rfc6480> | 8.2, 8.8 |
| BGPsec | RFC | [RFC 8205](https://datatracker.ietf.org/doc/html/rfc8205) | <https://datatracker.ietf.org/doc/html/rfc8205> | 8.2, 8.8 |
| Route Origin Validation (ROV) | RFC | [RFC 6811](https://datatracker.ietf.org/doc/html/rfc6811) | <https://datatracker.ietf.org/doc/html/rfc6811> | 8.2, 8.8 |
| IPsec Architecture | RFC | [RFC 4301](https://datatracker.ietf.org/doc/html/rfc4301) | <https://datatracker.ietf.org/doc/html/rfc4301> | 8.2, 8.8 |
| IKEv2 | RFC | [RFC 7296](https://datatracker.ietf.org/doc/html/rfc7296) | <https://datatracker.ietf.org/doc/html/rfc7296> | 8.2, 8.8 |
| TLS Certificate Compression | RFC | [RFC 8879](https://datatracker.ietf.org/doc/html/rfc8879) | <https://datatracker.ietf.org/doc/html/rfc8879> | 8.2, 8.8 |
| OAuth 2.0 | RFC | [RFC 6749](https://datatracker.ietf.org/doc/html/rfc6749) | <https://datatracker.ietf.org/doc/html/rfc6749> | 8.8 |
| JSON Web Token (JWT) | RFC | [RFC 7519](https://datatracker.ietf.org/doc/html/rfc7519) | <https://datatracker.ietf.org/doc/html/rfc7519> | 8.8 |
| NIST SP 800-53 | 框架 | Rev. 5 | <https://csrc.nist.gov/publications/detail/sp/800-53/rev-5/final> | 8.2, 8.8 |

## 3. 路由与流量工程扩展

| 概念 | 来源类型 | 来源 | 链接/位置 | 覆盖章节 |
|---|---|---|---|---|
| IS-IS | RFC | [RFC 1195](https://datatracker.ietf.org/doc/html/rfc1195)/5308 | <https://datatracker.ietf.org/doc/html/rfc1195> | 8.1, 8.3 |
| MPLS Architecture | RFC | [RFC 3031](https://datatracker.ietf.org/doc/html/rfc3031) | <https://datatracker.ietf.org/doc/html/rfc3031> | 8.1, 8.3 |
| Segment Routing IPv6 (SRv6) | RFC | [RFC 8402](https://datatracker.ietf.org/doc/html/rfc8402)/8986 | <https://datatracker.ietf.org/doc/html/rfc8402> | 8.3, 8.8 |
| BGP FlowSpec | RFC | [RFC 8955](https://datatracker.ietf.org/doc/html/rfc8955) | <https://datatracker.ietf.org/doc/html/rfc8955> | 8.3, 8.8 |
| EVPN | RFC | [RFC 7432](https://datatracker.ietf.org/doc/html/rfc7432)/8365 | <https://datatracker.ietf.org/doc/html/rfc7432> | 8.3, 8.8 |

## 4. 应用层协议扩展

| 概念 | 来源类型 | 来源 | 链接/位置 | 覆盖章节 |
|---|---|---|---|---|
| HTTP/2 | RFC | [RFC 7540](https://datatracker.ietf.org/doc/html/rfc7540)/7541 | <https://datatracker.ietf.org/doc/html/rfc7540> | 8.1, 8.6 |
| WebSocket | RFC | [RFC 6455](https://datatracker.ietf.org/doc/html/rfc6455) | <https://datatracker.ietf.org/doc/html/rfc6455> | 8.1, 8.6 |
| CoAP | RFC | [RFC 7252](https://datatracker.ietf.org/doc/html/rfc7252) | <https://datatracker.ietf.org/doc/html/rfc7252> | 8.8 |
| MQTT v5.0 | 标准 | OASIS | <https://docs.oasis-open.org/mqtt/mqtt/v5.0/mqtt-v5.0.html> | 8.8 |
| gRPC / HTTP/3 | 框架/协议 | gRPC / [RFC 9114](https://datatracker.ietf.org/doc/html/rfc9114) | <https://github.com/grpc/grpc>, <https://datatracker.ietf.org/doc/html/rfc9114> | 8.8 |

## 5. 数据中心与软件定义网络

| 概念 | 来源类型 | 来源 | 链接/位置 | 覆盖章节 |
|---|---|---|---|---|
| VXLAN | RFC | [RFC 7348](https://datatracker.ietf.org/doc/html/rfc7348) | <https://datatracker.ietf.org/doc/html/rfc7348> | 8.8 |
| Geneve | RFC | [RFC 8926](https://datatracker.ietf.org/doc/html/rfc8926) | <https://datatracker.ietf.org/doc/html/rfc8926> | 8.8 |
| SR-IOV | 规范 | PCI-SIG | <https://pcisig.com/specifications> | 8.8 |
| CNI Spec | 规范 | CNCF | <https://www.cni.dev/docs/spec/> | 8.8 |

## 6. 移动通信与边缘网络

| 概念 | 来源类型 | 来源 | 链接/位置 | 覆盖章节 |
|---|---|---|---|---|
| 5G System Architecture | 标准 | [3GPP](https://www.3gpp.org/specifications) TS 23.501 | <https://www.3gpp.org/specifications> | 8.8 |
| 5G NR Protocol Stack | 标准 | [3GPP](https://www.3gpp.org/specifications) TS 38.300 | <https://www.3gpp.org/specifications> | 8.8 |
| MEC Framework | 标准 | ETSI MEC | <https://www.etsi.org/technologies/multi-access-edge-computing> | 8.8 |
| Wi-Fi 7 (802.11be) | 标准 | [IEEE 802.11be](https://standards.ieee.org/standard/802.11be-2024.html) | <https://standards.ieee.org/standard/802.11be-2024.html> | 8.8 |

---

## 覆盖状态与补齐计划

1. **DNSSEC / DoH / DoT**：当前 `8.1/1.8.22`、`8.2/8.2.x` 仅提及 DNS 基础安全，需补充协议细节。
2. **RPKI / BGPsec / ROV**：`8.1/1.8.22` 已提及 RPKI，需扩展为独立小节。
3. **IPsec / IKEv2**：`8.8` 安全专题可新增 VPN/隧道协议分析。
4. **MPLS / SRv6 / EVPN**：`8.3` 形式化结构可新增路由抽象模型。
5. **VXLAN / Geneve / CNI**：`8.8` 可新增数据中心网络虚拟化专题。
6. **[3GPP](https://www.3gpp.org/specifications) / ETSI MEC**：`8.8` 未来网络专题可补充 5G/边缘架构来源。

---

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-05 | 建立高级协议与安全标准映射表 | Kimi Code CLI |
