# 网络高级协议与安全标准映射 / Advanced Protocol & Security Standards Mapping


<!-- TOC START -->

- [网络高级协议与安全标准映射 / Advanced Protocol \& Security Standards Mapping](#网络高级协议与安全标准映射--advanced-protocol--security-standards-mapping)
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

1. **QUIC / HTTP/3**：已新增 `8.8/8.8.25 QUIC 协议深度分析.md`，覆盖 RFC 9000/9001/9002/9114/9204。
2. **RPKI / BGPsec / ROV**：已新增 `8.8/8.8.26 BGP 安全与 RPKI.md`，覆盖 RFC 6480/6482/6487/6811/8205。
3. **DNSSEC / DoH / DoT**：已新增 `8.8/8.8.27 DNS 安全：DNSSEC、DoH 与 DoT.md`，覆盖 RFC 4033/4034/4035/7858/8484。
4. **IPsec / IKEv2**：已新增 `8.8/8.8.28 IPsec 与 IKEv2：VPN 与隧道安全.md`，覆盖 RFC 4301/4302/4303/7296。
5. **MPLS / SRv6 / EVPN**：已新增 `8.8/8.8.29 MPLS、SRv6 与 EVPN：路由与流量工程.md`，覆盖 RFC 3031/3209/8402/8986/7432/8365。
6. **VXLAN / Geneve / CNI**：已新增 `8.8/8.8.30 数据中心网络虚拟化：VXLAN、Geneve 与 CNI.md`，覆盖 RFC 7348/8926 与 CNI Spec。
7. **OpenFlow / P4**：已新增 `8.8/8.8.31 可编程网络：OpenFlow 与 P4.md`，覆盖 ONF OpenFlow 1.5.1、P4-16、P4Runtime。
8. **[3GPP](https://www.3gpp.org/specifications) / IEEE 802.11be / ETSI MEC**：已新增 `8.8/8.8.32 5G 与边缘计算：3GPP、802.11be 与 ETSI MEC.md`，覆盖 TS 23.501/38.300、IEEE 802.11be-2024、ETSI MEC。
9. **WebSocket / HTTP/2**：已新增 `8.8/8.8.33 WebSocket 与 HTTP/2：全双工与多路复用.md`，覆盖 RFC 6455、RFC 9113、RFC 7541、RFC 8441、RFC 9110/9112。
10. **TCP Fast Open / BBR / MPTCP / SCTP / DCCP**：已新增 `8.8/8.8.34 传输层演进：TCP Fast Open、BBR、MPTCP、SCTP 与 DCCP.md`，覆盖 RFC 7413、RFC 8312、RFC 8684、RFC 4960、RFC 4340。
11. **MQTT v5.0 / CoAP**：已新增 `8.8/8.8.35 物联网协议：MQTT v5.0 与 CoAP.md`，覆盖 OASIS MQTT v5.0、RFC 7252、RFC 7641、RFC 7959/8132、RFC 8323。
12. **TLS 1.3 / PKI**：已新增 `8.8/8.8.36 TLS 1.3 与密码学工程：握手、证书与部署.md`，覆盖 RFC 8446、RFC 8448、RFC 6066、RFC 8879、RFC 8555、NIST SP 800-52 Rev. 2、PCI DSS 4.0、CAB Forum BR。
13. **SNMP / NetFlow / IPFIX / sFlow**：已新增 `8.8/8.8.37 网络可观测性与遥测：SNMP、NetFlow、IPFIX 与 sFlow.md`，覆盖 RFC 3411-3418、RFC 7011、RFC 5424、sFlow v5。
14. **TSN / 802.1AS / DetNet**：已新增 `8.8/8.8.38 时间敏感网络与确定性以太网：TSN、802.1AS 与 DetNet.md`，覆盖 IEEE 802.1AS-2020、IEEE 802.1Qbv/Qbu/Qca/CB/Qcc、RFC 8938/8939/9023/9055。
15. **Zero Trust / SASE / SDP**：已新增 `8.8/8.8.39 零信任架构与网络访问安全：NIST SP 800-207、SASE 与 SDP.md`，覆盖 NIST SP 800-207、NIST SP 800-63、CSA SDP Architecture Guide v2.0、RFC 6749、OpenID Connect。
16. **AIOps / 异常检测 / 智能流量工程**：已新增 `8.8/8.8.40 网络人工智能与智能运维：AIOps、异常检测与流量工程.md`，覆盖 ITIL 4、MEF 3.0、IEEE 802.1Qcc、OpenTelemetry、RFC 9234。
17. **CSA / TI / STIX / TAXII / MITRE ATT&CK**：已新增 `8.8/8.8.41 网络安全态势感知与威胁情报.md`，覆盖 NIST SP 800-150、STIX 2.1、TAXII 2.1、MITRE ATT&CK、VERIS。
18. **NTN / Starlink / 3GPP NR-NTN**：已新增 `8.8/8.8.42 卫星互联网与非地面网络：NTN、Starlink 与 3GPP NR-NTN.md`，覆盖 3GPP TR 38.811/38.821/22.822、TS 38.101-5、DVB-RCS2。
19. **Deterministic IP / SRv6+ / AP6**：已新增 `8.8/8.8.43 确定性 IP 与 SRv6+：网络切片、随流检测与 AP6.md`，覆盖 RFC 8402/8986、RFC 8938/8939/9023、RFC 9197/9484/8321/5357/8762、3GPP TS 23.501。
20. **RDMA / RoCE / DCB**：已新增 `8.8/8.8.44 高速数据中心网络：RDMA、RoCE 与 DCB.md`，覆盖 IBTA InfiniBand Architecture、IEEE 802.1Qbb/Qaz/Qau、RoCEv2 UDP 4791。
21. **SOC / SIEM / SOAR**：已新增 `8.8/8.8.45 网络安全运营中心与 SIEM：日志、告警与响应编排.md`，覆盖 NIST SP 800-61 Rev. 2、MITRE ATT&CK、Sigma、CEF、Sysmon、SOAR。
22. **IBN / YANG / Network Digital Twin**：已新增 `8.8/8.8.46 意图驱动网络与数字孪生：IBN、YANG 与网络数字孪生.md`，覆盖 RFC 6020/7950、RFC 7120 NEMO、ITU-T Y.3090、ETSI ZSM、MEF 3.0。
23. **CFN / Computing-aware Routing / 东数西算**：已新增 `8.8/8.8.47 算力网络与算网融合：CFN、算力路由与东数西算.md`，覆盖 IETF CAN/CFN drafts、ITU-T Y.2501/Y.2502、3GPP TS 22.261、中国 "东数西算" 政策框架。
24. **SD-WAN / SASE / MEF 70**：已新增 `8.8/8.8.48 软件定义广域网与安全访问服务边缘：SD-WAN 与 SASE 工程实践.md`，覆盖 MEF 70/MEF 3.0 SD-WAN、Gartner SASE、NIST SP 800-207、RFC 8986 SRv6。

---

## 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-05 | 建立高级协议与安全标准映射表 | Kimi Code CLI |
| 2026-07-05 | 补齐 QUIC / HTTP/3 深度分析专题（8.8.25）与 BGP 安全 / RPKI 专题（8.8.26） | Kimi Code CLI |
| 2026-07-05 | 补齐 DNS 安全（DNSSEC/DoH/DoT，8.8.27）与 IPsec/IKEv2 VPN 安全（8.8.28）专题 | Kimi Code CLI |
| 2026-07-05 | 补齐 MPLS/SRv6/EVPN 路由专题（8.8.29）与 VXLAN/Geneve/CNI 数据中心网络专题（8.8.30） | Kimi Code CLI |
| 2026-07-05 | 补齐可编程网络 OpenFlow/P4 专题（8.8.31）与 5G/边缘计算/Wi-Fi 7 专题（8.8.32） | Kimi Code CLI |
| 2026-07-05 | 新增 WebSocket/HTTP/2（8.8.33）、传输层演进（8.8.34）、物联网协议 MQTT/CoAP（8.8.35）、TLS 1.3/PKI（8.8.36）专题 | Kimi Code CLI |
| 2026-07-05 | 新增网络可观测性（8.8.37）、TSN/DetNet（8.8.38）、零信任/SASE/SDP（8.8.39）、AIOps（8.8.40）、态势感知与威胁情报（8.8.41）、卫星互联网/NTN（8.8.42）、确定性 IP/SRv6+（8.8.43）、RDMA/RoCE（8.8.44）专题 | Kimi Code CLI |
| 2026-07-05 | 新增 SOC/SIEM/SOAR（8.8.45）、IBN/YANG/数字孪生（8.8.46）、算力网络/东数西算（8.8.47）、SD-WAN/SASE（8.8.48）专题，更新映射表覆盖状态 | Kimi Code CLI |
