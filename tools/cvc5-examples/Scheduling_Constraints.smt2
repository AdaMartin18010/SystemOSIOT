; SystemOSIOT CVC5 / SMT-LIB Example
; 目标：验证实时任务调度约束的可满足性。
; 内容：将两个周期性任务分配到不重叠的时间槽。
; 工具：CVC5 (https://cvc5.github.io/)

(set-logic QF_LIA)
(set-option :produce-models true)

(declare-fun slot_t1 () Int)
(declare-fun slot_t2 () Int)

; 时间槽范围 0..3
(assert (and (>= slot_t1 0) (<= slot_t1 3)))
(assert (and (>= slot_t2 0) (<= slot_t2 3)))

; 两个任务不能占用同一时间槽
(assert (not (= slot_t1 slot_t2)))

; 任务 t1 必须在 t2 之前（优先级约束）
(assert (< slot_t1 slot_t2))

(check-sat)
(get-model)
(exit)
