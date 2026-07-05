---------------------------- MODULE OS_SchedulerFairness ----------------------------
(*
 * Scheduler Fairness Model
 * Model: A round-robin scheduler serving a set of tasks.
 * Each task gets a time slice; after its slice it returns to ready.
 * Property: every ready task eventually gets to run.
 *
 * Author: SystemOSIOT
 * Source: OSTEP Ch. 7~9, POSIX.1-2024 SCHED_RR
 *)

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS TaskSet, TimeSlice

VARIABLES ready_queue, running, ticks_remaining

TypeOK ==
    /\ ready_queue \subseteq TaskSet
    /\ running \in TaskSet \cup {"None"}
    /\ ticks_remaining \in 0..TimeSlice

(* All tasks start ready, none running *)
Init ==
    /\ ready_queue = TaskSet
    /\ running = "None"
    /\ ticks_remaining = 0

(* Dispatch one ready task if no task is running *)
Dispatch ==
    /\ running = "None"
    /\ ready_queue /= {}
    /\ \E t \in ready_queue :
        /\ running' = t
        /\ ready_queue' = ready_queue \ {t}
        /\ ticks_remaining' = TimeSlice

(* Running task consumes one tick *)
Tick ==
    /\ running /= "None"
    /\ ticks_remaining > 0
    /\ ticks_remaining' = ticks_remaining - 1
    /\ UNCHANGED <<ready_queue, running>>

(* Running task's slice expires; it goes back to ready *)
Expire ==
    /\ running /= "None"
    /\ ticks_remaining = 0
    /\ ready_queue' = ready_queue \cup {running}
    /\ running' = "None"
    /\ ticks_remaining' = 0

(* Running task voluntarily yields CPU *)
Yield ==
    /\ running /= "None"
    /\ ticks_remaining > 0
    /\ ready_queue' = ready_queue \cup {running}
    /\ running' = "None"
    /\ ticks_remaining' = 0

Next ==
    Dispatch \/ Tick \/ Expire \/ Yield

Spec ==
    /\ Init
    /\ [][Next]_<<ready_queue, running, ticks_remaining>>
    /\ SF_<<ready_queue, running, ticks_remaining>>(Dispatch)
    /\ SF_<<ready_queue, running, ticks_remaining>>(Expire)
    /\ SF_<<ready_queue, running, ticks_remaining>>(Yield)

(* Invariants *)
NoDuplicateRunning ==
    running = "None" \/ ~running \in ready_queue

(* Fairness: every task that is in the ready queue eventually runs *)
Fairness ==
    \A t \in TaskSet :
        (t \in ready_queue) ~> (running = t)

=====================================================================================
