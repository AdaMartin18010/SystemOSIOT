# SystemOSIOT 国际化权威标准基线

> 版本：1.4.0
> 更新日期：2026-07-05
> 用途：定义项目各模块必须对齐的国际权威来源，作为引用、映射与审计的基线。

<!-- TOC START -->

- [SystemOSIOT 国际化权威标准基线](#systemosiot-国际化权威标准基线)
  - [1. 系统理论](#1-系统理论)
  - [2. 操作系统](#2-操作系统)
  - [3. 物联网嵌入式系统](#3-物联网嵌入式系统)
  - [4. 分布式系统](#4-分布式系统)
  - [5. 集群系统](#5-集群系统)
  - [6. P2P 系统](#6-p2p-系统)
  - [7. 容器与微服务](#7-容器与微服务)
  - [8. 网络系统](#8-网络系统)
  - [9. 形式化方法通用基准](#9-形式化方法通用基准)
  - [10. 更新策略](#10-更新策略)

<!-- TOC END -->

## 1. 系统理论

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| 国际标准 | ISO/IEC/IEEE 15288:2023 | 2023 | <https://www.iso.org/standard/81702.html> |
| 知识体系 | INCOSE Systems Engineering Handbook | 5th Ed., 2023 | <https://www.incose.org/products-and-publications/se-handbook> |
| 知识体系 | SEBoK | v2.13 (2025) | <https://sebokwiki.org/> |
| 建模语言 | OMG SysML v2 / KerML v1.0 | v2.0 (2025) | <https://www.omg.org/spec/SysML/> |
| 国际标准 | ISO/IEC/IEEE 24641:2023 | 2023 | <https://www.iso.org/standard/79111.html> |
| 国际标准 | ISO/IEC/IEEE 42010:2022 | 2022 | <https://www.iso.org/standard/77394.html> |

## 2. 操作系统

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| 国际标准 | POSIX.1 / IEEE Std 1003.1 | 2024 (Issue 8) | <https://pubs.opengroup.org/onlinepubs/9799919799/> |
| 国际标准 | Linux Standard Base (LSB) | ISO/IEC 23360-1-x:2021 | <https://webstore.iec.ch/en/publication/71478> |
| 安全标准 | Common Criteria | ISO/IEC 15408:2022 | <https://www.iso.org/standard/72891.html> |
| 形式化 OS | seL4 | SOSP 2009 | DOI: 10.1145/1629575.1629596 |
| 微内核 | Fiasco.OC / L4Re | 最新 | <https://l4re.org/> |
| 教材 | OSTEP (Remzi & Andrea Arpaci-Dusseau) | 最新在线版 | <https://pages.cs.wisc.edu/~remzi/OSTEP/> |
| 教材 | Operating Systems: Principles and Practice (Anderson & Dahlin) | 2nd Ed. | <https://www.amazon.com/Operating-Systems-Principles-Practice-2nd/dp/0985673524> |

| 知识体系 | ACM/IEEE CS2013 Operating Systems Knowledge Area | 2013 | <https://csed.acm.org/knowledge-areas-operating-systems-os-cs2013-version/> |
| 教材 | Silberschatz, Galvin & Gagne, *Operating System Concepts* | 10th Ed., 2018/2021 | <https://www.wiley.com/en-us/Silberschatz%27s+Operating+System+Concepts%2C+10th+Edition-p-9781119800361> |
| 教材 | Arpaci-Dusseau, *Operating Systems: Three Easy Pieces* (OSTEP) | v1.0, 2023 | <https://pages.cs.wisc.edu/~remzi/OSTEP/> |
| Linux 教材 | Michael Kerrisk, *The Linux Programming Interface* (TLPI) | 1st Ed., 2010 | <https://man7.org/tlpi/> |
| Linux 参考 | The Linux man-pages Project | 持续更新 | <https://www.kernel.org/doc/man-pages/> |
| Linux 教材 | Robert Love, *Linux Kernel Development* | 3rd Ed. | Pearson |
| Linux 教材 | Bovet & Cesati, *Understanding the Linux Kernel* | 3rd Ed. | O'Reilly |
| 驱动教材 | Corbet, Rubini & Kroah-Hartman, *Linux Device Drivers* (LDD3) | 3rd Ed. | <https://static.lwn.net/images/pdf/LDD3/ch00.pdf> |
| 架构教材 | Hennessy & Patterson, *Computer Architecture: A Quantitative Approach* | 6th Ed. | Morgan Kaufmann |
| Linux 源码文档 | Linux Kernel Documentation | 最新 | <https://docs.kernel.org/> |
| 安全关键 | IEC 61508: Functional Safety of E/E/PE Systems | 2010 (Ed. 2) | <https://webstore.iec.ch/publication/66912> |
| 安全关键 | ISO 26262: Road Vehicles — Functional Safety | 2018 | <https://www.iso.org/standard/68383.html> |
| 安全关键 | RTCA DO-178C / EUROCAE ED-12C | 2011 | <https://www.rtca.org/product/do-178c/> |
| 课程 | MIT 6.S081 / 6.828 xv6 on RISC-V | 2024 | <https://pdos.csail.mit.edu/6.S081/> |
| 课程 | CMU 15-410 / 15-605 Operating System Design and Implementation | 2026 Spring | <https://www.cs.cmu.edu/~410/> |
| 课程 | Stanford CS140 / CS140E / Pintos | 2026 目录 | <https://web.stanford.edu/class/cs140/> |
| 课程 | UC Berkeley CS162 Operating Systems | 2025 Fall | <https://cs162.org/> |
| 知识体系 | SWEBOK v4.0 — Computing Foundations (Operating Systems) | 2024 | <https://www.computer.org/education/bodies-of-knowledge/software-engineering> |
| 国际标准 | POSIX.1-2024 §11 / §18 | Terminal I/O / Asynchronous I/O | <https://pubs.opengroup.org/onlinepubs/9799919799/> |
| 总线标准 | USB 2.0 / 3.2 / USB4 | 最新 | <https://www.usb.org/documents> |
| 总线标准 | PCI Express Base Specification | 6.0 / 7.0 | <https://pcisig.com/specifications> |
| 总线标准 | NXP I²C-bus Specification | UM10204 Rev. 7 | <https://www.nxp.com/docs/en/user-guide/UM10204.pdf> |
| 总线标准 | Motorola SPI Block Guide | V04.01 | NXP/Freescale |
| 总线标准 | ISO 11898 (CAN) | 2015/2020/2021 | <https://www.iso.org/standard/63648.html> |
| 总线标准 | Bosch CAN Specification 2.0 | 2.0 | <https://www.bosch-semiconductors.com/us/ip-modules/can-protocol/can-2-0.html> |
| 固件/启动 | ACPI Specification | 6.5+ | <https://uefi.org/specifications> |
| 固件/启动 | UEFI Specification | 2.10+ | <https://uefi.org/specifications> |
| 中断控制器 | ARM Generic Interrupt Controller (GIC) | 最新 | <https://developer.arm.com/documentation> |
| 中断控制器 | RISC-V PLIC / ACLINT | 最新 | <https://riscv.org/technical/specifications/> |
| 架构手册 | Intel 64 and IA-32 Architectures Software Developer's Manual | Vol. 3A | <https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html> |

## 3. 物联网嵌入式系统

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| 国际标准 | ISO/IEC 30141 | 2024 (Edition 2) | <https://www.iso.org/standard/88800.html> |
| 安全标准 | IEC 62443-2-1 | 2024 | <https://webstore.iec.ch/en/publication/62883> |
| 安全指南 | NIST SP 800-213 / 800-213A | 2024 | <https://csrc.nist.gov/publications/detail/sp/800/213/final> |
| 协议 | MQTT | v5.0 (OASIS) | <https://docs.oasis-open.org/mqtt/mqtt/v5.0/mqtt-v5.0.html> |
| 协议 | CoAP | RFC 7252/8323 | <https://doi.org/10.17487/RFC7252> |
| 协议 | LwM2M | 1.2 | <https://omaspecworks.org/> |
| 标准 | Matter / Thread | 1.4 / 1.4 | <https://csa-iot.org/all-solutions/matter/> |
| RTOS | FreeRTOS Documentation | 最新 | <https://www.freertos.org/Documentation/RTOS-book> |
| RTOS | Zephyr Project Documentation | 最新 | <https://docs.zephyrproject.org/> |
| RTOS | RTEMS Documentation | 最新 | <https://docs.rtems.org/> |
| 实时理论 | Liu & Layland, "Scheduling Algorithms for Multiprogramming in a Hard-Real-Time Environment" | JACM 1973 | DOI: 10.1145/321738.321743 |
| 实时教材 | Hard Real-Time Computing Systems (Buttazzo) | 4th Ed. | Springer |
| 总线标准 | NXP I²C-bus Specification (UM10204) | Rev. 7, 2021 | <https://www.nxp.com/docs/en/user-guide/UM10204.pdf> |
| 总线标准 | Motorola SPI Block Guide | V04.01 (S12SPIV4/D) | NXP/Freescale |
| 总线标准 | ISO 11898 (CAN) | 2015/2020/2021 | <https://www.iso.org/standard/63648.html> |
| 总线标准 | Bosch CAN Specification 2.0 | 2.0 | <https://www.bosch-semiconductors.com/us/ip-modules/can-protocol/can-2-0.html> |
| 总线标准 | PCI Express Base Specification | 6.0/7.0 | <https://pcisig.com/specifications> |
| 总线标准 | USB 2.0/3.2/4 Specifications | 最新 | <https://www.usb.org/documents> |
| 架构手册 | Intel 64 and IA-32 Architectures Software Developer's Manual | Vol. 3A | <https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html> |
| 架构手册 | ARM Architecture Reference Manual / GIC | 最新 | <https://developer.arm.com/documentation> |
| 架构手册 | RISC-V Privileged Spec / PLIC | 最新 | <https://riscv.org/technical/specifications/> |

## 4. 分布式系统

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| 定理 | CAP Theorem (Brewer) | PODC 2000 | DOI: 10.1145/343477.343502 |
| 定理 | CAP Theorem (Gilbert & Lynch) | SIGACT News 2002 | DOI: 10.1145/564585.564601 |
| 定理 | FLP Impossibility | JACM 1985 | DOI: 10.1145/3149.214121 |
| 算法 | Paxos (Lamport) | TOCS 1998 / 2001 | DOI: 10.1145/279227.279229 |
| 算法 | Raft (Ongaro & Ousterhout) | USENIX ATC 2014 | <https://www.usenix.org/conference/atc14/technical-sessions/presentation/ongaro> |
| 算法 | PBFT (Castro & Liskov) | OSDI 1999 | DOI: 10.1145/319155.319168 |
| 一致性 | Linearizability (Herlihy & Wing) | TOPLAS 1990 | DOI: 10.1145/78969.78972 |
| 权衡 | PACELC (Abadi) | 2010 | <https://doi.org/10.1145/1835698.1835701> |
| 教材 | Designing Data-Intensive Applications | 2017 | <https://dataintensive.net/> |

## 5. 集群系统

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| 标准 | MPI Standard | 4.1 (2023) | <https://www.mpi-forum.org/docs/mpi-4.1/mpi41-report.pdf> |
| 软件 | Slurm Workload Manager | 24.11 / 25.05 | <https://slurm.schedmd.com/> |
| 基准 | TOP500 / Green500 | 2025-06 | <https://top500.org/> |
| 能耗 | Energy Aware Runtime (EAR) | v7.0 | <https://www.ear.energy/> |

## 6. P2P 系统

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| 协议 | BitTorrent / BEP 52 | v2 | <http://bittorrent.org/beps/bep_0052.html> |
| 算法 | Chord (Stoica et al.) | SIGCOMM 2001 | DOI: 10.1145/383059.383071 |
| 算法 | Kademlia (Maymounkov & Mazieres) | IPTPS 2002 | DOI: 10.1007/3-540-45748-8_5 |
| 协议栈 | libp2p / IPFS | 持续更新 | <https://docs.libp2p.io/> |
| 论文 | Bitcoin Whitepaper (Nakamoto) | 2008 | <https://bitcoin.org/bitcoin.pdf> |
| 算法 | HotStuff (Yin et al.) | 2019 | <https://doi.org/10.1145/3293611.3331591> |

## 7. 容器与微服务

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| 标准 | OCI Runtime Spec | v1.3.0 | <https://github.com/opencontainers/runtime-spec/releases/tag/v1.3.0> |
| 标准 | OCI Image Spec | v1.1.0 | <https://github.com/opencontainers/image-spec/releases/tag/v1.1.0> |
| 标准 | OCI Distribution Spec | v1.1.0 | <https://github.com/opencontainers/distribution-spec/releases/tag/v1.1.0> |
| 编排 | Kubernetes | v1.33 (2025) | <https://v1-33.docs.kubernetes.io/> |
| 接口 | CNI Spec | v1.1.0 | <https://www.cni.dev/docs/spec/> |
| 接口 | CSI / CRI | 最新 | <https://kubernetes.io/docs/concepts/> |
| RPC | gRPC | v1.71.0 | <https://github.com/grpc/grpc/releases/tag/v1.71.0> |
| 事件 | CloudEvents | v1.0.2 | <https://github.com/cloudevents/spec/blob/v1.0.2/cloudevevents/spec.md> |
| 接口 | SMI | v0.7+ | <https://smi-spec.io/> |
| 安全 | NIST SP 800-190 | Container Security Guide | <https://csrc.nist.gov/publications/detail/sp/800/190/final> |
| 安全 | CIS Docker Benchmark | v1.6+ | <https://www.cisecurity.org/benchmark/docker> |
| 安全 | CIS Kubernetes Benchmark | v1.9+ | <https://www.cisecurity.org/benchmark/kubernetes> |
| 构建 | Dockerfile reference | 最新 | <https://docs.docker.com/reference/dockerfile/> |
| Linux | cgroups v2 | 最新 | <https://docs.kernel.org/admin-guide/cgroup-v2.html> |
| Linux | Namespaces | 最新 | <https://docs.kernel.org/userspace-api/namespaces.html> |
| Linux | eBPF / BPF | 最新 | <https://docs.kernel.org/bpf/> |
| 网络 | IEEE 802.1Q VLAN | IEEE 802.1Q-2024 | <https://standards.ieee.org/standard/802.1Q-2024.html> |
| 硬件 | PCI-SIG SR-IOV | 最新 | <https://pcisig.com/specifications> |

## 8. 网络系统

| 类型 | 名称 | 版本/年份 | 链接/DOI |
|---|---|---|---|
| RFC | Internet Protocol (IPv4) | RFC 791 | <https://datatracker.ietf.org/doc/html/rfc791> |
| RFC | Transmission Control Protocol (TCP) | RFC 793 | <https://datatracker.ietf.org/doc/html/rfc793> |
| RFC | User Datagram Protocol (UDP) | RFC 768 | <https://datatracker.ietf.org/doc/html/rfc768> |
| RFC | Internet Control Message Protocol (ICMP) | RFC 792 | <https://datatracker.ietf.org/doc/html/rfc792> |
| RFC | Address Resolution Protocol (ARP) | RFC 826 | <https://datatracker.ietf.org/doc/html/rfc826> |
| RFC | Internet Protocol, Version 6 (IPv6) | RFC 8200 | <https://datatracker.ietf.org/doc/html/rfc8200> |
| RFC | TCP/IP Host Requirements | RFC 1122/1123 | <https://datatracker.ietf.org/doc/html/rfc1122> |
| RFC | TCP Congestion Control | RFC 5681 | <https://datatracker.ietf.org/doc/html/rfc5681> |
| RFC | HTTP Semantics / HTTP/1.1 / HTTP/3 | RFC 9110/9112/9114 | <https://datatracker.ietf.org/doc/html/rfc9110> |
| RFC | TLS 1.3 | RFC 8446 | <https://datatracker.ietf.org/doc/html/rfc8446> |
| RFC | DNS Concepts / Implementation | RFC 1034/1035 | <https://datatracker.ietf.org/doc/html/rfc1034> |
| RFC | QUIC | RFC 9000/9001/9002/9114 | DOI: 10.17487/RFC9000 |
| RFC | BGP | RFC 4271 及扩展 | DOI: 10.17487/RFC4271 |
| RFC | OSPF | RFC 2328/5340 | DOI: 10.17487/RFC2328 |
| 标准 | IEEE 802.3 Ethernet | IEEE 802.3-2022 | <https://standards.ieee.org/standard/802.3-2022.html> |
| 标准 | IEEE 802.1Q VLAN | IEEE 802.1Q-2024 | <https://standards.ieee.org/standard/802.1Q-2024.html> |
| 标准 | IEEE 802.11 | IEEE 802.11-2024 | <https://standards.ieee.org/standard/802.11-2024.html> |
| 协议 | OpenFlow | 1.5.1 | <https://opennetworking.org/software-defined-standards/> |
| 语言 | P4 / P4Runtime | P4-16 / v1.4.1 | <https://p4.org/> |
| 标准 | 3GPP 5G-Advanced | Release 18 | <https://www.3gpp.org/specifications> |
| 框架 | NIST SP 800-207 | Zero Trust Architecture | <https://csrc.nist.gov/publications/detail/sp/800/207/final> |
| 框架 | NIST Cybersecurity Framework | CSF 2.0 | <https://www.nist.gov/cyberframework> |
| 框架 | NIST AI Risk Management Framework | AI RMF 1.0 | <https://www.nist.gov/itl/ai-risk-management-framework> |
| 法规 | EU AI Act | 2024 | <https://eur-lex.europa.eu/legal-content/EN/TXT/?uri=CELEX:32024R1689> |
| Linux 网络文档 | netdev subsystem | 最新 | <https://docs.kernel.org/process/maintainer-netdev.html> |
| eBPF/XDP 文档 | Linux BPF / XDP | 最新 | <https://docs.kernel.org/bpf/>, <https://docs.kernel.org/networking/xdp.html> |
| 流量控制 | Linux tc / Traffic Control | 最新 | <https://docs.kernel.org/networking/sched/> |
| 教材 | TCP/IP Illustrated, Vol. 1 (Stevens) | 2nd Ed. | Addison-Wesley |
| 教材 | Linux Kernel Networking (Rami Rosen) | 最新 | Apress |
| RFC | DNSSEC | RFC 4033/4034/4035 | <https://datatracker.ietf.org/doc/html/rfc4033> |
| RFC | DNS over HTTPS (DoH) | RFC 8484 | <https://datatracker.ietf.org/doc/html/rfc8484> |
| RFC | DNS over TLS (DoT) | RFC 7858 | <https://datatracker.ietf.org/doc/html/rfc7858> |
| RFC | WebSocket | RFC 6455 | <https://datatracker.ietf.org/doc/html/rfc6455> |
| RFC | HTTP/2 | RFC 7540/7541/9113 | <https://datatracker.ietf.org/doc/html/rfc9113> |
| RFC | IPsec Architecture | RFC 4301 | <https://datatracker.ietf.org/doc/html/rfc4301> |
| RFC | IKEv2 | RFC 7296 | <https://datatracker.ietf.org/doc/html/rfc7296> |
| RFC | BGPsec | RFC 8205 | <https://datatracker.ietf.org/doc/html/rfc8205> |
| RFC | RPKI / ROA | RFC 6480/6482/6487 | <https://datatracker.ietf.org/doc/html/rfc6480> |
| RFC | Route Origin Validation (ROV) | RFC 6811 | <https://datatracker.ietf.org/doc/html/rfc6811> |
| RFC | MPLS | RFC 3031 | <https://datatracker.ietf.org/doc/html/rfc3031> |
| RFC | SRv6 | RFC 8402/8986 | <https://datatracker.ietf.org/doc/html/rfc8402> |
| RFC | TCP Fast Open | RFC 7413 | <https://datatracker.ietf.org/doc/html/rfc7413> |
| RFC | BBR Congestion Control / CUBIC | RFC 8312 | <https://datatracker.ietf.org/doc/html/rfc8312> |
| RFC | Multipath TCP (MPTCP) | RFC 8684 | <https://datatracker.ietf.org/doc/html/rfc8684> |
| RFC | SCTP | RFC 4960 | <https://datatracker.ietf.org/doc/html/rfc4960> |
| RFC | DCCP | RFC 4340 | <https://datatracker.ietf.org/doc/html/rfc4340> |
| RFC | DTLS 1.3 | RFC 9147 | <https://datatracker.ietf.org/doc/html/rfc9147> |
| 标准 | MQTT v5.0 | OASIS | <https://docs.oasis-open.org/mqtt/mqtt/v5.0/mqtt-v5.0.html> |
| 标准 | CoAP | RFC 7252 | <https://datatracker.ietf.org/doc/html/rfc7252> |
| 论文 | io_uring (Jens Axboe) | 2020 | <https://kernel.dk/io_uring.pdf> |
| 标准 | IEEE 802.1AS | gPTP / TSN, 2020 | <https://standards.ieee.org/standard/802.1AS-2020.html> |
| 标准 | IEEE 802.1Qbv / Qbu / Qca | TSN shaping / preemption / PSFP | <https://standards.ieee.org/standard/802.1Q-2024.html> |
| RFC | DetNet | RFC 8938/8939/9023/9055 | <https://datatracker.ietf.org/doc/html/rfc8938> |
| RFC | SNMPv3 | RFC 3411-3418 | <https://datatracker.ietf.org/doc/html/rfc3411> |
| RFC | IPFIX | RFC 7011 | <https://datatracker.ietf.org/doc/html/rfc7011> |
| 协议 | sFlow | v5 | <https://sflow.org/sflow_version_5.txt> |
| RFC | syslog | RFC 5424 | <https://datatracker.ietf.org/doc/html/rfc5424> |
| 框架 | NIST SP 800-63 | Digital Identity Guidelines | <https://pages.nist.gov/800-63/> |
| 框架 | CSA SDP Architecture | v2.0 | <https://cloudsecurityalliance.org/artifacts/software-defined-perimeter-zero-trust-specification-v2/> |
| 框架 | MITRE ATT&CK | Enterprise / Mobile, 2025 | <https://attack.mitre.org/> |
| 框架 | STIX / TAXII | OASIS v2.1 / v2.1 | <https://oasis-open.github.io/cti-documentation/> |
| 工具 | MISP | 最新 | <https://www.misp-project.org/> |
| 框架 | NIST SP 800-150 | Cyber Threat Information Sharing | <https://csrc.nist.gov/publications/detail/sp/800/150/final> |
| 框架 | VERIS | 最新 | <https://veriscommunity.net/> |
| 标准 | 3GPP NR-NTN | TR 38.811/38.821/22.822 | <https://www.3gpp.org/specifications> |
| 标准 | ITU-R Satellite | S.1645 / S.1857 | <https://www.itu.int/rec/R-REC-S.1645> |
| 标准 | DVB-RCS2 | ETSI EN 301 545-2 | <https://www.etsi.org/deliver/etsi_en/301500_301599/30154502/> |
| IETF draft | SRv6 SRH Compression | draft-ietf-spring-srv6-srh-compression | <https://datatracker.ietf.org/doc/draft-ietf-spring-srv6-srh-compression/> |
| RFC | IPPM / TwAMP / STAMP | RFC 9197 / 8321 | <https://datatracker.ietf.org/doc/html/rfc9197> |
| 标准 | ITU-T Deterministic Networking | Y.3800 series | <https://www.itu.int/rec/T-REC-Y.3800> |
| 标准 | InfiniBand Architecture | IBTA, 最新 | <https://www.infinibandta.org/specs> |
| 标准 | RoCEv2 | IBTA RDMA over Converged Ethernet v2 | <https://www.infinibandta.org/specs> |
| 标准 | IEEE Data Center Bridging | 802.1Qbb / 802.1Qaz / 802.1Qau | <https://standards.ieee.org/standard/802.1Q-2024.html> |
| 框架 | Gartner AIOps | Market Guide | <https://www.gartner.com/en/documents/aiops-market-guide> |
| 框架 | ITIL 4 | IT Service Management | <https://www.axelos.com/certifications/itil-service-management> |
| 标准 | MEF 3.0 | Service Framework | <https://www.mef.net/resources/technical-specifications/> |
| RFC | BGP FlowSpec v2 | RFC 9234 | <https://datatracker.ietf.org/doc/html/rfc9234> |
| 框架 | NIST SP 800-61 Rev. 2 | Computer Security Incident Handling | <https://csrc.nist.gov/publications/detail/sp/800/61/rev-2/final> |
| 框架 | Sigma Generic Log Rule Format | 最新 | <https://github.com/SigmaHQ/sigma> |
| 框架 | CEF (ArcSight Common Event Format) | 最新 | <https://www.microfocus.com/documentation/arcsight/arcsight-smartconnectors-8.3/cef-implementation-standard/> |
| 框架 | SOAR (Security Orchestration, Automation and Response) | 概念/实践 | Gartner / NIST SP 800-61 语境 |
| 建模语言 | YANG | RFC 6020 / RFC 7950 | <https://datatracker.ietf.org/doc/html/rfc6020> |
| RFC | NEMO (Network Mobility) | RFC 7120 | <https://datatracker.ietf.org/doc/html/rfc7120> |
| 标准 | ITU-T Digital Twin Network | Y.3090 series | <https://www.itu.int/rec/T-REC-Y.3090> |
| 框架 | ETSI ZSM (Zero-touch Network and Service Management) | 最新 | <https://www.etsi.org/technologies/zero-touch-network-service-management> |
| IETF draft | Computing-Aware Networking (CAN) / CFN | draft-ietf-can-scheduling | <https://datatracker.ietf.org/doc/draft-ietf-can-scheduling/> |
| 标准 | ITU-T Computing and Network Convergence | Y.2501 / Y.2502 | <https://www.itu.int/rec/T-REC-Y.2501> |
| 标准 | 3GPP 5G Service Requirements | TS 22.261 | <https://www.3gpp.org/specifications> |
| 标准 | MEF 70 | SD-WAN Service Attributes | <https://www.mef.net/resources/technical-specifications/> |
| 标准 | MEF 3.0 SD-WAN | Certification / Service Framework | <https://www.mef.net/resources/technical-specifications/> |

## 9. 形式化方法通用基准

| 类别 | 权威资料 | 链接/DOI |
|---|---|---|
| 形式语义 | Winskel, *The Formal Semantics of Programming Languages* | MIT Press, 1993 |
| 形式语义 | Nielson & Nielson, *Semantics with Applications* | Springer, 2007 |
| SOS | Plotkin, *A Structural Approach to Operational Semantics* | DOI: 10.1016/j.jlap.2004.05.001 |
| 类型论 | Pierce, *Types and Programming Languages* | <https://www.cis.upenn.edu/~bcpierce/tapl/> |
| Coq 教材 | Pierce et al., *Software Foundations* | <https://softwarefoundations.cis.upenn.edu/> |
| Isabelle 教材 | Nipkow & Klein, *Concrete Semantics* | <http://concrete-semantics.org/> |
| Lean 教材 | Avigad et al., *Theorem Proving in Lean 4* | <https://leanprover.github.io/theorem_proving_in_lean4/> |
| 模型检验 | Baier & Katoen, *Principles of Model Checking* | MIT Press, 2008 |
| TLA+ | Lamport, *Specifying Systems* | <https://lamport.azurewebsites.net/tla/book.html> |
| 霍尔逻辑 | Hoare, *An Axiomatic Basis for Computer Programming* | DOI: 10.1145/363235.363259 |
| 分离逻辑 | Reynolds, *Separation Logic* | DOI: 10.1109/LICS.2002.1029817 |
| 并发 | Herlihy & Wing, *Linearizability* | DOI: 10.1145/78969.78972 |

## 10. 更新策略

- 每季度检索 ISO/IEC/IEEE/3GPP/IETF 官方站点，更新本基线。
- 新增模块或子主题前，必须先在本基线中确认权威来源。
