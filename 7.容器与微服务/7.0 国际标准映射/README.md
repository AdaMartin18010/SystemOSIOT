# 7.0 容器与微服务 — 国际标准映射

## 1. 主要对标标准

| 标准/规范 | 版本 | 官方链接/DOI | 对应项目章节 |
|---|---|---|---|
| OCI Runtime Spec | v1.3.0 | https://github.com/opencontainers/runtime-spec/releases/tag/v1.3.0 | 7.1, 7.3, 7.6 |
| OCI Image Spec | v1.1.0 | https://github.com/opencontainers/image-spec/releases/tag/v1.1.0 | 7.1, 7.3 |
| OCI Distribution Spec | v1.1.0 | https://github.com/opencontainers/distribution-spec/releases/tag/v1.1.0 | 7.1, 7.3 |
| Kubernetes | v1.33 (Octarine) | https://v1-33.docs.kubernetes.io/ | 7.1, 7.3, 7.6, 7.7 |
| CNI Spec | v1.1.0 | https://www.cni.dev/docs/spec/ | 7.1, 7.3, 7.6 |
| gRPC | v1.71.0 | https://github.com/grpc/grpc/releases/tag/v1.71.0 | 7.1, 7.3, 7.6 |
| CloudEvents | v1.0.2 | https://github.com/cloudevents/spec/blob/v1.0.2/cloudevents/spec.md | 7.1, 7.5, 7.6 |
| SMI (Service Mesh Interface) | v0.7+ | https://smi-spec.io/ | 7.1, 7.3 |
| Dapr | v1.15+ | https://docs.dapr.io/ | 7.1, 7.3 |

## 2. 详细映射子文档

| 子文档 | 内容 |
|---|---|
| [7.0.1 OCI 开放容器倡议规范映射](7.0.1%20OCI-Specs.md) | OCI Runtime / Image / Distribution Spec v1.3/v1.1 条款级映射 |
| [7.0.2 Kubernetes v1.33 映射](7.0.2%20Kubernetes-v1.33.md) | K8s v1.33 API、组件、调度、新特性映射 |
| [7.0.3 CNI / CRI / CSI 接口映射](7.0.3%20CNI-CRI-CSI.md) | 容器网络、运行时、存储接口规范映射 |

## 3. 标准条款映射表

| 标准/来源 | 核心内容 | 项目覆盖章节 | 证据文件 | 覆盖状态 |
|---|---|---|---|---|
| OCI Runtime v1.3.0 | config.json, lifecycle hooks, namespaces, cgroups | 7.1, 7.3 | 待补充 | 部分覆盖 |
| OCI Image v1.1.0 | Manifest, Index, Config, Layers, annotations | 7.1, 7.3 | 待补充 | 部分覆盖 |
| OCI Distribution v1.1.0 | Push/Pull API, referrers, chunked upload | 7.1 | 待补充 | 未覆盖 |
| K8s v1.33 API | Pod, Deployment, Service, Gateway API, Sidecar | 7.1, 7.7 | 待补充 | 需升级版本 |
| CNI Spec v1.1.0 | ADD/DEL/CHECK, IPAM, network namespace | 7.1, 7.3 | 待补充 | 部分覆盖 |
| CloudEvents v1.0.2 | event format, transport bindings | 7.1, 7.5 | 待补充 | 未覆盖 |

## 4. 覆盖缺口与补齐计划

1. **清理过度递归**：已删除/合并 8 层以上嵌套文件，执行最大深度 ≤ 5 规则。  
2. **版本升级**：将 Kubernetes 内容升级到 v1.33，补充 Gateway API、Sidecar Containers、Resource Claims。  
3. **OCI 条款级映射**：已建立 Runtime/Image/Distribution 与 runc/containerd/CRI-O 的对应，需在 `7.1 知识梳理` 中补充细节。  
4. **服务网格标准化**：增加 SMI、Istio、Linkerd、Cilium Service Mesh 对比。  
5. **TLA+ 规范**：为 K8s Deployment 滚动更新、Pod 生命周期建立可运行模型（Phase 2）。

## 5. 维护记录

| 日期 | 操作 | 维护者 |
|---|---|---|
| 2026-07-02 | 创建映射骨架 | Kimi Code CLI |
| 2026-07-02 | 补充 OCI/K8s/CNI-CRI-CSI 详细映射 | Kimi Code CLI |
