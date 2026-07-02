; SystemOSIOT SMT-LIB / Z3 Constraint Solving Example
; 目标：验证容器资源分配约束的可满足性。
; 内容：将 Kubernetes Pod 资源请求建模为线性约束，使用 Z3 求解。
; 工具：Z3 (https://github.com/Z3Prover/z3)

(set-logic QF_NIA)

; 节点 CPU 容量
(declare-fun node_cpu () Int)
(assert (= node_cpu 8))

; 节点内存容量（GB）
(declare-fun node_mem () Int)
(assert (= node_mem 32))

; Pod p1 资源请求
(declare-fun p1_cpu () Int)
(declare-fun p1_mem () Int)
(assert (= p1_cpu 2))
(assert (= p1_mem 4))

; Pod p2 资源请求
(declare-fun p2_cpu () Int)
(declare-fun p2_mem () Int)
(assert (= p2_cpu 3))
(assert (= p2_mem 8))

; Pod p3 资源请求
(declare-fun p3_cpu () Int)
(declare-fun p3_mem () Int)
(assert (= p3_cpu 2))
(assert (= p3_mem 4))

; 决策变量：每个 Pod 是否调度到该节点
(declare-fun place_p1 () Int)
(declare-fun place_p2 () Int)
(declare-fun place_p3 () Int)

; place_x = 1 表示调度到该节点，0 表示不调度
(assert (and (>= place_p1 0) (<= place_p1 1)))
(assert (and (>= place_p2 0) (<= place_p2 1)))
(assert (and (>= place_p3 0) (<= place_p3 1)))

; CPU 容量约束
(assert (<= (+ (* place_p1 p1_cpu)
                (* place_p2 p2_cpu)
                (* place_p3 p3_cpu))
            node_cpu))

; 内存容量约束
(assert (<= (+ (* place_p1 p1_mem)
                (* place_p2 p2_mem)
                (* place_p3 p3_mem))
            node_mem))

; 目标：最大化放置的 Pod 数量（通过检查不同组合的可满足性）
; 尝试放置所有 3 个 Pod
(assert (= (+ place_p1 place_p2 place_p3) 3))

(check-sat)
(get-model)

; 退出
(exit)
