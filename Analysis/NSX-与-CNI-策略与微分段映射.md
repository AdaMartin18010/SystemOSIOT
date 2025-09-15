# NSX × CNI 策略与微分段映射分析

## 1. 背景与目标

- 背景：数据中心网络（NSX）与容器网络（CNI）在同一基础设施并存，策略需要跨层一致。
- 目标：建立从 L2-L7 的策略对象与意图映射，明确冲突解析与落地顺序，给出运行时观测与回归方法。

### 1.1 范围与边界（Scope & Non-goals）

- 定位：知识梳理与跨层语义映射；非工程实现。
- 对标：VMware NSX 官方文档、CNI/K8s NetworkPolicy 文档、IETF/IEEE 相关标准；MIT/Stanford 相关课程材料。
- 证据：文档版本与章节/链接可复核。

## 2. 对象与策略域

- NSX 对象：Segment、T1/T0、DFW Section/Rule、Group、Tag、Service、Policy。
- CNI 对象（以 K8s 为例）：Namespace、Pod、Service、NetworkPolicy、Label/Selector、Ingress/Egress 规则。

### 2.1 形式化语义（摘要）

- 端点集合：以集合与选择器（谓词）表达；策略为有序规则列表，对数据包元组进行匹配与动作映射。
- 冲突关系：阴影/覆盖/并集/交集的判定条件与消解顺序。
- 顺序与优先级：定义全序 P，保证跨层合并后规则集（NSX ∪ K8s）按 P 严格无歧义执行（E-2025-0030）。

## 3. 映射关系（摘要）

| 语义 | NSX | CNI/K8s | 备注 |
|---|---|---|---|
| 端点集合 | Group(Tag) | Label/Selector | 双向同步标签避免漂移（E-2025-0030） |
| 东西向策略 | DFW Sections | NetworkPolicy | 优先级/匹配域需统一 |
| 南北向策略 | T1/T0 + NAT/Firewall | Ingress Controller/Service | 四层/七层语义对齐（E-2025-0010） |
| 服务抽象 | Service Object | Service/EndpointSlice | 端口/协议统一定义 |
| 可观测性 | Traceflow/Trace Policy | CNI/iptables/ebpf map | 统一追踪与事件关联（E-2025-0030） |
| 证据编号 | E-2025-0030 | E-2025-0010 | 对应参考 7 |

## 4. 冲突与优先级

- 优先级：NSX DFW 通常先于容器侧数据平面；需定义“显式允许/拒绝”的一致原则，避免双重拒绝造成排错困难。
- 作用域：明确 NSX 匹配到的端点集合与 K8s Selector 的交集，防止“阴影策略”。
- 合并算法：自上而下（南北向 → 东西向 → 容器侧），为每条规则赋权重并生成不可重叠区间，冲突走最严格原则；输出可回放工件。

## 5. 运行时验证

- 场景：跨命名空间通信、入口限速、服务间零信任。
- 方法：NSX Traceflow + K8s eBPF 观测（Cilium/Hubble 或等效），生成跨层时序图与 verdict。
- 日志/事件：vCenter/NSX 事件与 K8s Audit/Controller 事件对齐统一时间线。

### 5.1 基准方法学（Benchmark Methodology）

- 指标：策略命中率、误阻断率、端到端 p95/p99、回放一致性。
- 设计：固定策略集→生成流量矩阵→事件回放→统一时间线分析。

## 6. 实施建议

1) 标签治理：统一命名规范，建立 NSX Tag ↔ K8s Label 映射与同步流水线。
2) 策略即代码：集中存储策略源，生成 NSX 与 K8s 策略工件并回放测试。
3) 回归基线：每次变更跑策略覆盖率与误阻断率，保留审计与版本签名。
4) 变更窗口：涉及南北向策略的调整需与入口网关/Ingress 同步滚动并灰度验证。

## 7. 参考与链接

- 产品文档：VMware NSX 官方文档（DFW/Group/Tag/Traceflow）（E-2025-0030）
- 标准：IETF RFC 8939/9012（与策略/路由相关，待按需精确化）（E-2025-0031）
- K8s 文档：NetworkPolicy/Endpoints/Ingress（v1.30）（E-2025-0010）
- 实践：Cilium/Calico 关于策略与 eBPF 数据路径的实现说明（版本待补）（E-2025-0032）
