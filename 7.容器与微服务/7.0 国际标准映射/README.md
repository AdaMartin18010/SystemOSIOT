# 7.0 容器与微服务 — 国际标准映射

> **目录说明 / Directory Note**：本目录为容器与微服务主题的国际权威标准（OCI、Kubernetes、CNI/CRI/CSI 等）与项目章节对齐的正式映射目录。原 `7.0 国际化标准/` 中的历史参考文档（术语、格式与引用规范、多语言支持）已合并至本目录，统一归档管理。
> This directory is the canonical standard-to-project mapping directory for the container and microservices topic (OCI, Kubernetes, CNI/CRI/CSI, etc.). Historical reference documents from the former `7.0 国际化标准/` directory (terminology, formatting and citation standards, multilingual support) have been merged here for unified archiving.

<!-- TOC START -->

- [7.0 容器与微服务 — 国际标准映射](#70-容器与微服务--国际标准映射)
  - [1. 主要对标标准](#1-主要对标标准)
  - [2. 详细映射子文档](#2-详细映射子文档)
  - [3. 标准条款映射表](#3-标准条款映射表)
  - [4. 覆盖缺口与补齐计划](#4-覆盖缺口与补齐计划)
  - [5. 权威来源链接](#5-权威来源链接)
  - [6. 形式化工件链接](#6-形式化工件链接)
  - [7. 维护记录](#7-维护记录)
  - [8. 已合并的历史参考文档](#8-已合并的历史参考文档)

<!-- TOC END -->

## 1. 主要对标标准

| 标准/规范 | 版本 | 官方链接/DOI | 对应项目章节 |
|---|---|---|---|
| OCI Runtime Spec | v1.3.0 | <https://github.com/opencontainers/runtime-spec/releases/tag/v1.3.0> | 7.1, 7.3, 7.6 |
| OCI Image Spec | v1.1.0 | <https://github.com/opencontainers/image-spec/releases/tag/v1.1.0> | 7.1, 7.3 |
| OCI Distribution Spec | v1.1.0 | <https://github.com/opencontainers/distribution-spec/releases/tag/v1.1.0> | 7.1, 7.3 |
| Kubernetes | v1.33 (Octarine) | <https://v1-33.docs.kubernetes.io/> | 7.1, 7.3, 7.6, 7.7 |
| CNI Spec | v1.1.0 | <https://www.cni.dev/docs/spec/> | 7.1, 7.3, 7.6 |
| CRI (Container Runtime Interface) | Kubernetes API v1 | <https://kubernetes.io/docs/concepts/architecture/cri/> | 7.1, 7.3, 7.6 |
| CSI (Container Storage Interface) | v1.11+ | <https://github.com/container-storage-interface/spec> | 7.1, 7.3 |
| gRPC | v1.71.0 | <https://github.com/grpc/grpc/releases/tag/v1.71.0> | 7.1, 7.3, 7.6 |
| CloudEvents | v1.0.2 | <https://github.com/cloudevents/spec/blob/v1.0.2/cloudevents/spec.md> | 7.1, 7.5, 7.6 |
| SMI (Service Mesh Interface) | v0.7+ | <https://smi-spec.io/> | 7.1, 7.3 |
| Dockerfile reference | Latest | <https://docs.docker.com/reference/dockerfile/> | 7.1 |
| NIST SP 800-190 | 2017 | <https://csrc.nist.gov/publications/detail/sp/800-190/final> | 7.2, 7.6 |
| CIS Docker Benchmark | v1.6.0+ | <https://www.cisecurity.org/benchmark/docker> | 7.2 |
| CIS Kubernetes Benchmark | v1.9.0+ | <https://www.cisecurity.org/benchmark/kubernetes> | 7.2 |
| IEEE 802.1Q | 2023 | <https://standards.ieee.org/standard/802.1Q-2023.html> | 7.1, 7.3 |
| PCI-SIG SR-IOV | 1.1+ | <https://pcisig.com/specifications> | 7.1, 7.7 |
| Linux cgroups v2 | Kernel 5.x+ | <https://docs.kernel.org/admin-guide/cgroup-v2.html> | 7.1, 7.3, 7.7 |
| Linux Namespaces | Kernel mainline | <https://man7.org/linux/man-pages/man7/namespaces.7.html> | 7.1, 7.3 |
| eBPF Documentation | Latest | <https://docs.ebpf.io/> | 7.1, 7.7 |
| Dapr | v1.15+ | <https://docs.dapr.io/> | 7.1, 7.3 |

## 2. 详细映射子文档

| 子文档 | 内容 |
|---|---|
| [7.0.1 OCI 开放容器倡议规范映射](7.0.1%20OCI-Specs.md) | OCI Runtime / Image / Distribution Spec v1.3/v1.1 条款级映射 |
| [7.0.2 Kubernetes v1.33 映射](7.0.2%20Kubernetes-v1.33.md) | K8s v1.33 API、组件、调度、新特性映射 |
| [7.0.3 CNI / CRI / CSI 接口映射](7.0.3%20CNI-CRI-CSI.md) | 容器网络、运行时、存储接口规范映射 |

## 3. 标准条款映射表

| 标准/来源 | 核心内容 | 项目覆盖章节 | 证据文件 | 覆盖状态 |
|---|---|---|---|---|
| OCI Runtime v1.3.0 | config.json, lifecycle hooks, namespaces, cgroups, capabilities, seccomp | 7.1, 7.3 | [7.0.1 OCI-Specs.md](7.0.1%20OCI-Specs.md) | 部分覆盖 |
| OCI Image v1.1.0 | Manifest, Index, Config, Layers, annotations, referrers | 7.1, 7.3 | [7.0.1 OCI-Specs.md](7.0.1%20OCI-Specs.md) | 部分覆盖 |
| OCI Distribution v1.1.0 | Push/Pull API, referrers, chunked upload | 7.1 | [7.0.1 OCI-Specs.md](7.0.1%20OCI-Specs.md) | 未覆盖 |
| K8s v1.33 API | Pod, Deployment, Service, Gateway API, Sidecar, DRA | 7.1, 7.7 | [7.0.2 Kubernetes-v1.33.md](7.0.2%20Kubernetes-v1.33.md) | 需升级版本 |
| CNI Spec v1.1.0 | ADD/DEL/CHECK, IPAM, network namespace | 7.1, 7.3 | [7.0.3 CNI-CRI-CSI.md](7.0.3%20CNI-CRI-CSI.md) | 部分覆盖 |
| CRI | RuntimeService / ImageService gRPC, PodSandbox lifecycle | 7.1, 7.3 | [7.0.3 CNI-CRI-CSI.md](7.0.3%20CNI-CRI-CSI.md) | 部分覆盖 |
| CSI | Identity / Controller / Node RPC, volume lifecycle | 7.1, 7.3 | [7.0.3 CNI-CRI-CSI.md](7.0.3%20CNI-CRI-CSI.md) | 部分覆盖 |
| CloudEvents v1.0.2 | event format, transport bindings, attributes | 7.1, 7.5 | — | 未覆盖 |
| SMI v0.7+ | TrafficSplit, TrafficPolicy, TrafficMetrics | 7.1, 7.3 | — | 未覆盖 |
| Dockerfile reference | Build instructions, multi-stage, cache | 7.1 | — | 部分覆盖 |
| NIST SP 800-190 | Container security, image, registry, orchestrator risks | 7.2, 7.6 | — | 未覆盖 |
| CIS Docker Benchmark | Host OS, Docker daemon, access control, logging | 7.2 | — | 未覆盖 |
| CIS Kubernetes Benchmark | API server, etcd, worker node, policies | 7.2 | — | 未覆盖 |
| IEEE 802.1Q | VLAN tagging, QoS, bridge filtering | 7.1, 7.3 | — | 未覆盖 |
| PCI-SIG SR-IOV | VF/PF, network device virtualization | 7.1, 7.7 | — | 未覆盖 |
| Linux cgroups v2 | unified hierarchy, controllers, delegation | 7.1, 7.3, 7.7 | — | 部分覆盖 |
| Linux namespaces | pid/net/ipc/mnt/uts/user/cgroup/time | 7.1, 7.3 | — | 部分覆盖 |
| eBPF docs | probes, maps, verifier, networking/security/observability | 7.1, 7.7 | — | 未覆盖 |

## 4. 覆盖缺口与补齐计划

1. **清理过度递归**：已删除/合并 8 层以上嵌套文件，执行最大深度 ≤ 5 规则。
2. **版本升级**：将 Kubernetes 内容升级到 v1.33，补充 Gateway API、Sidecar Containers、Resource Claims、DRA。
3. **OCI 条款级映射**：已建立 Runtime/Image/Distribution 与 runc/containerd/CRI-O 的对应，需在 `7.1 知识梳理` 中补充镜像仓库、供应链安全、Linux 安全机制细节。
4. **服务网格标准化**：增加 SMI、Istio、Linkerd、Cilium Service Mesh 对比。
5. **安全与合规**：补充 NIST SP 800-190、CIS Docker/Kubernetes Benchmark 到 `7.2 批判性分析`。
6. **网络与硬件虚拟化**：补充 IEEE 802.1Q VLAN/QoS、PCI-SIG SR-IOV 与 CNI 高性能网络方案映射。
7. **底层内核机制**：补充 Linux cgroups v2、namespaces、eBPF 与容器运行时隔离/可观测性映射。
8. **事件与 API 协议**：补充 CloudEvents v1.0.2 与 gRPC 在服务间通信中的语义映射。
9. **TLA+ 规范**：为 K8s Deployment 滚动更新、Pod 生命周期、CSI volume 状态机建立可运行模型（Phase 2）。
10. **重复目录治理**：`7.0 国际化标准/` 已合并到 `7.0 国际标准映射/`，相关历史参考文档见[已合并的历史参考文档](#8-已合并的历史参考文档)小节；新增标准映射请继续统一归入 `7.0 国际标准映射/`。

## 5. 权威来源链接

| 标准/来源 | 官方链接 |
|---|---|
| OCI Runtime Spec v1.3.0 | <https://github.com/opencontainers/runtime-spec/releases/tag/v1.3.0> |
| OCI Image Spec v1.1.0 | <https://github.com/opencontainers/image-spec/releases/tag/v1.1.0> |
| OCI Distribution Spec v1.1.0 | <https://github.com/opencontainers/distribution-spec/releases/tag/v1.1.0> |
| Kubernetes v1.33 | <https://v1-33.docs.kubernetes.io/> |
| CNI Spec v1.1.0 | <https://www.cni.dev/docs/spec/> |
| CRI | <https://kubernetes.io/docs/concepts/architecture/cri/> |
| CSI | <https://github.com/container-storage-interface/spec> |
| gRPC | <https://github.com/grpc/grpc/releases/tag/v1.71.0> |
| CloudEvents v1.0.2 | <https://github.com/cloudevents/spec/blob/v1.0.2/cloudevents/spec.md> |
| SMI | <https://smi-spec.io/> |
| Dockerfile reference | <https://docs.docker.com/reference/dockerfile/> |
| NIST SP 800-190 | <https://csrc.nist.gov/publications/detail/sp/800/190/final> |
| CIS Benchmarks | <https://www.cisecurity.org/cis-benchmarks> |
| IEEE 802.1Q | <https://standards.ieee.org/standard/802.1Q-2023.html> |
| PCI-SIG SR-IOV | <https://pcisig.com/specifications> |
| Linux cgroups v2 | <https://docs.kernel.org/admin-guide/cgroup-v2.html> |
| Linux Namespaces | <https://man7.org/linux/man-pages/man7/namespaces.7.html> |
| eBPF docs | <https://docs.ebpf.io/> |

## 6. 形式化工件链接

| 工件 | 路径 | 说明 |
|---|---|---|
| Kubernetes TLA+ 规范 | `tools/tla-specifications/Kubernetes.tla` + `Kubernetes.cfg` | Pod 生命周期与 Deployment 滚动更新 |

## 7. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建映射骨架 | Kimi Code CLI |
| 2026-07-02 | 补充 OCI/K8s/CNI-CRI-CSI 详细映射 | Kimi Code CLI |
| 2026-07-05 | 补齐 Dockerfile、NIST/CIS、IEEE 802.1Q、SR-IOV、cgroups v2、namespaces、eBPF、CloudEvents、SMI 等全量映射表；新增覆盖缺口与权威来源链接；标注重复目录说明 | Kimi Code CLI |
| 2026-07-05 | 合并 `7.0 国际化标准/` 到 `7.0 国际标准映射/`，统一归档历史参考文档 | Kimi Code CLI |

## 8. 已合并的历史参考文档

以下文件原位于 `7.0 国际化标准/`，现已统一迁移至 `7.0 国际标准映射/` 归档保留：

| 文件 | 说明 |
|---|---|
| [7.0.1 术语标准化对照表.md](7.0.1%20术语标准化对照表.md) | 术语标准化中英对照表 |
| [7.0.2 文档格式标准.md](7.0.2%20文档格式标准.md) | 文档撰写与排版格式规范 |
| [7.0.3 引用规范标准.md](7.0.3%20引用规范标准.md) | 参考文献与外部来源引用规范 |
| [7.0.4 多语言支持.md](7.0.4%20多语言支持.md) | 多语言内容组织与翻译规范 |
