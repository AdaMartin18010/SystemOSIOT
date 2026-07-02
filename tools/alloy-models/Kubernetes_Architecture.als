/*
 * SystemOSIOT Alloy Architecture Consistency Example
 * 目标：验证 Kubernetes 容器编排架构的基本一致性约束。
 * 内容：Pod、Node、Container、Service 之间的关系与约束。
 * 工具：Alloy Analyzer（https://alloytools.org/）。
 */

module Kubernetes_Architecture

// 抽象签名
abstract sig Resource {}

sig Node extends Resource {
    runs : set Pod
}

sig Pod extends Resource {
    contains : set Container,
    scheduledOn : lone Node,
    exposedBy : lone Service
}

sig Container extends Resource {
    image : one Image
}

sig Image {}

sig Service extends Resource {
    targets : set Pod
}

// 约束 1：Pod 必须调度到某个 Node 上
fact PodScheduled {
    all p : Pod | one p.scheduledOn
}

// 约束 2：Pod 调度的 Node 必须是运行该 Pod 的 Node
fact SchedulingConsistency {
    all p : Pod, n : Node |
        p.scheduledOn = n iff n in p.~runs
}

// 约束 3：每个 Pod 至少包含一个 Container
fact PodHasContainer {
    all p : Pod | some p.contains
}

// 约束 4：Service 只能 targeting 它暴露的 Pod
fact ServiceTargetsConsistency {
    all s : Service, p : Pod |
        p in s.targets iff s in p.exposedBy
}

// 约束 4a：每个 Service 至少 target 一个 Pod
fact ServiceMustHaveTarget {
    all s : Service | some s.targets
}

// 约束 5：同一个 Node 上的 Pod 共享该 Node 资源，但容器镜像可以不同
fact ImageIndependence {
    all p1, p2 : Pod |
        (p1 != p2 and p1.scheduledOn = p2.scheduledOn)
            implies (p1.contains.image != p2.contains.image)
}

// 断言：不存在两个不同 Pod 运行在同一 Node 上但使用完全相同镜像集
assert NoDuplicatePodImagesOnSameNode {
    no disj p1, p2 : Pod |
        p1.scheduledOn = p2.scheduledOn
        and p1.contains.image = p2.contains.image
}

// 断言：每个 Service 至少 target 一个 Pod
assert ServiceHasTarget {
    all s : Service | some s.targets
}

// 运行检查
check NoDuplicatePodImagesOnSameNode for 5
check ServiceHasTarget for 5

// 示例场景：2 个 Node，3 个 Pod，2 个 Service
pred ShowExample {
    #Node = 2
    #Pod = 3
    #Service = 2
    #Container >= 3
}

run ShowExample for 10
