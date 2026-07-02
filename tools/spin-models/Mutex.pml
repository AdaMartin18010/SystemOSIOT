/*
 * SystemOSIOT SPIN / Promela Example
 * 目标：验证两进程互斥协议的安全性与活性。
 * 模型：基于 turn 变量的简单互斥。
 */

mtype = { idle, waiting, critical };

mtype p1_state = idle;
mtype p2_state = idle;
byte turn = 1;

active proctype P1() {
    do
    :: p1_state == idle -> p1_state = waiting;
    :: p1_state == waiting && turn == 1 -> p1_state = critical;
    :: p1_state == critical -> p1_state = idle; turn = 2;
    od
}

active proctype P2() {
    do
    :: p2_state == idle -> p2_state = waiting;
    :: p2_state == waiting && turn == 2 -> p2_state = critical;
    :: p2_state == critical -> p2_state = idle; turn = 1;
    od
}

// 安全性质：不能同时进入临界区
ltl safety { [] !(p1_state == critical && p2_state == critical) }

// 活性性质：等待中的进程最终能进入临界区
ltl liveness1 { [] (p1_state == waiting -> <> (p1_state == critical)) }
ltl liveness2 { [] (p2_state == waiting -> <> (p2_state == critical)) }
