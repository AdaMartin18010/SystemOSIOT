; SystemOSIOT SMT-LIB / Z3 Container Resource Allocation v2
; 目标：验证多节点容器资源分配约束（含反亲和性与装箱）的可满足性。
; 内容：将 Kubernetes Pod 的 CPU/内存 requests/limits、节点容量、
;       反亲和性、bin-packing 目标建模为线性整数约束，使用 Z3 求解。
; 工具：Z3 (https://github.com/Z3Prover/z3)

(set-logic QF_LIA)

; ---------------- 常量：节点容量 ----------------
; 3 个节点的 CPU（核）与内存（GB）容量
(declare-fun node0_cpu () Int)
(declare-fun node0_mem () Int)
(declare-fun node1_cpu () Int)
(declare-fun node1_mem () Int)
(declare-fun node2_cpu () Int)
(declare-fun node2_mem () Int)

(assert (= node0_cpu 4))
(assert (= node0_mem 16))
(assert (= node1_cpu 8))
(assert (= node1_mem 32))
(assert (= node2_cpu 4))
(assert (= node2_mem 16))

; ---------------- Pod 资源请求与限制 ----------------
; Pod p0..p4 的 CPU/内存请求（固定常量）
; p0: 1 CPU, 4 GB
; p1: 2 CPU, 8 GB
; p2: 1 CPU, 4 GB
; p3: 2 CPU, 8 GB
; p4: 1 CPU, 4 GB

; Pod CPU/内存限制（必须大于等于请求）
(declare-fun p0_cpu_lim () Int)
(declare-fun p0_mem_lim () Int)
(declare-fun p1_cpu_lim () Int)
(declare-fun p1_mem_lim () Int)
(declare-fun p2_cpu_lim () Int)
(declare-fun p2_mem_lim () Int)
(declare-fun p3_cpu_lim () Int)
(declare-fun p3_mem_lim () Int)
(declare-fun p4_cpu_lim () Int)
(declare-fun p4_mem_lim () Int)

(assert (>= p0_cpu_lim 1))
(assert (>= p0_mem_lim 4))
(assert (>= p1_cpu_lim 2))
(assert (>= p1_mem_lim 8))
(assert (>= p2_cpu_lim 1))
(assert (>= p2_mem_lim 4))
(assert (>= p3_cpu_lim 2))
(assert (>= p3_mem_lim 8))
(assert (>= p4_cpu_lim 1))
(assert (>= p4_mem_lim 4))

; 为演示固定限制值
(assert (= p0_cpu_lim 2))
(assert (= p0_mem_lim 8))
(assert (= p1_cpu_lim 4))
(assert (= p1_mem_lim 16))
(assert (= p2_cpu_lim 2))
(assert (= p2_mem_lim 8))
(assert (= p3_cpu_lim 4))
(assert (= p3_mem_lim 16))
(assert (= p4_cpu_lim 2))
(assert (= p4_mem_lim 8))

; ---------------- 决策变量：Pod 放置 ----------------
; place_pX_nY = 1 表示 Pod pX 放在节点 Y 上
(declare-fun place_p0_n0 () Int)
(declare-fun place_p0_n1 () Int)
(declare-fun place_p0_n2 () Int)
(declare-fun place_p1_n0 () Int)
(declare-fun place_p1_n1 () Int)
(declare-fun place_p1_n2 () Int)
(declare-fun place_p2_n0 () Int)
(declare-fun place_p2_n1 () Int)
(declare-fun place_p2_n2 () Int)
(declare-fun place_p3_n0 () Int)
(declare-fun place_p3_n1 () Int)
(declare-fun place_p3_n2 () Int)
(declare-fun place_p4_n0 () Int)
(declare-fun place_p4_n1 () Int)
(declare-fun place_p4_n2 () Int)

; 每个 Pod 只能放置在一个节点上
(assert (= (+ place_p0_n0 place_p0_n1 place_p0_n2) 1))
(assert (= (+ place_p1_n0 place_p1_n1 place_p1_n2) 1))
(assert (= (+ place_p2_n0 place_p2_n1 place_p2_n2) 1))
(assert (= (+ place_p3_n0 place_p3_n1 place_p3_n2) 1))
(assert (= (+ place_p4_n0 place_p4_n1 place_p4_n2) 1))

; 决策变量二元约束
(assert (and (>= place_p0_n0 0) (<= place_p0_n0 1)))
(assert (and (>= place_p0_n1 0) (<= place_p0_n1 1)))
(assert (and (>= place_p0_n2 0) (<= place_p0_n2 1)))
(assert (and (>= place_p1_n0 0) (<= place_p1_n0 1)))
(assert (and (>= place_p1_n1 0) (<= place_p1_n1 1)))
(assert (and (>= place_p1_n2 0) (<= place_p1_n2 1)))
(assert (and (>= place_p2_n0 0) (<= place_p2_n0 1)))
(assert (and (>= place_p2_n1 0) (<= place_p2_n1 1)))
(assert (and (>= place_p2_n2 0) (<= place_p2_n2 1)))
(assert (and (>= place_p3_n0 0) (<= place_p3_n0 1)))
(assert (and (>= place_p3_n1 0) (<= place_p3_n1 1)))
(assert (and (>= place_p3_n2 0) (<= place_p3_n2 1)))
(assert (and (>= place_p4_n0 0) (<= place_p4_n0 1)))
(assert (and (>= place_p4_n1 0) (<= place_p4_n1 1)))
(assert (and (>= place_p4_n2 0) (<= place_p4_n2 1)))

; ---------------- 节点容量约束 ----------------
; 节点 0 CPU/内存
(assert (<= (+ (* place_p0_n0 1)
               (* place_p1_n0 2)
               (* place_p2_n0 1)
               (* place_p3_n0 2)
               (* place_p4_n0 1))
            node0_cpu))
(assert (<= (+ (* place_p0_n0 4)
               (* place_p1_n0 8)
               (* place_p2_n0 4)
               (* place_p3_n0 8)
               (* place_p4_n0 4))
            node0_mem))

; 节点 1 CPU/内存
(assert (<= (+ (* place_p0_n1 1)
               (* place_p1_n1 2)
               (* place_p2_n1 1)
               (* place_p3_n1 2)
               (* place_p4_n1 1))
            node1_cpu))
(assert (<= (+ (* place_p0_n1 4)
               (* place_p1_n1 8)
               (* place_p2_n1 4)
               (* place_p3_n1 8)
               (* place_p4_n1 4))
            node1_mem))

; 节点 2 CPU/内存
(assert (<= (+ (* place_p0_n2 1)
               (* place_p1_n2 2)
               (* place_p2_n2 1)
               (* place_p3_n2 2)
               (* place_p4_n2 1))
            node2_cpu))
(assert (<= (+ (* place_p0_n2 4)
               (* place_p1_n2 8)
               (* place_p2_n2 4)
               (* place_p3_n2 8)
               (* place_p4_n2 4))
            node2_mem))

; ---------------- 反亲和性约束 ----------------
; p0 与 p1 不能在同一节点上（硬约束）
(assert (not (and (= place_p0_n0 1) (= place_p1_n0 1))))
(assert (not (and (= place_p0_n1 1) (= place_p1_n1 1))))
(assert (not (and (= place_p0_n2 1) (= place_p1_n2 1))))

; p2 与 p3 不能在同一节点上（硬约束）
(assert (not (and (= place_p2_n0 1) (= place_p3_n0 1))))
(assert (not (and (= place_p2_n1 1) (= place_p3_n1 1))))
(assert (not (and (= place_p2_n2 1) (= place_p3_n2 1))))

; ---------------- Bin-Packing：最大化资源利用率 ----------------
; 目标：放置所有 5 个 Pod，同时使节点 0 与节点 2 的 CPU 使用尽可能均衡
; 引入辅助变量表示节点负载差异
(declare-fun load_diff () Int)
(assert (= load_diff (- (+ (* place_p0_n0 1)
                            (* place_p1_n0 2)
                            (* place_p2_n0 1)
                            (* place_p3_n0 2)
                            (* place_p4_n0 1))
                         (+ (* place_p0_n2 1)
                            (* place_p1_n2 2)
                            (* place_p2_n2 1)
                            (* place_p3_n2 2)
                            (* place_p4_n2 1)))))

; 约束差异不超过 2 核，体现 bin-packing 均衡目标
(assert (<= load_diff 2))
(assert (>= load_diff -2))

; ---------------- 求解 ----------------
(check-sat)
(get-model)

(exit)
