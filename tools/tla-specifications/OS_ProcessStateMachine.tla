--------------------------- MODULE OS_ProcessStateMachine ---------------------------
(*
 * Operating System Process State Machine
 * Model: A simplified process lifecycle with five states:
 *   New, Ready, Running, Waiting, Terminated
 *
 * Properties to check:
 *   - Type correctness
 *   - No deadlock (every non-terminated process can eventually progress)
 *   - Liveness: every process eventually reaches Terminated
 *
 * Author: SystemOSIOT
 * Source: POSIX.1-2024 process lifecycle, Silberschatz Operating System Concepts 10e
 *)

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Processes

VARIABLES state

States == {"New", "Ready", "Running", "Waiting", "Terminated"}

TypeOK ==
    state \in [Processes -> States]

(* Initial state: all processes start as New *)
Init ==
    state = [p \in Processes |-> "New"]

(* A New process is admitted to Ready *)
Admit(p) ==
    /\ state[p] = "New"
    /\ state' = [state EXCEPT ![p] = "Ready"]

(* The scheduler dispatches a Ready process to Running *)
Dispatch(p) ==
    /\ state[p] = "Ready"
    /\ ~\E q \in Processes : state[q] = "Running"
    /\ state' = [state EXCEPT ![p] = "Running"]

(* A Running process requests I/O or a resource and moves to Waiting *)
Wait(p) ==
    /\ state[p] = "Running"
    /\ state' = [state EXCEPT ![p] = "Waiting"]

(* A Waiting process's event occurs and it returns to Ready *)
Wakeup(p) ==
    /\ state[p] = "Waiting"
    /\ state' = [state EXCEPT ![p] = "Ready"]

(* A Running process completes execution *)
Terminate(p) ==
    /\ state[p] = "Running"
    /\ state' = [state EXCEPT ![p] = "Terminated"]

(* A Running process is preempted back to Ready (time slice expires) *)
Preempt(p) ==
    /\ state[p] = "Running"
    /\ state' = [state EXCEPT ![p] = "Ready"]

Next ==
    \E p \in Processes :
        Admit(p) \/ Dispatch(p) \/ Wait(p) \/ Wakeup(p) \/ Terminate(p) \/ Preempt(p)

Spec ==
    /\ Init
    /\ [][Next]_state
    /\ WF_state(Next)
    /\ WF_state(\E p \in Processes : Dispatch(p))
    /\ WF_state(\E p \in Processes : Terminate(p))
    /\ WF_state(\E p \in Processes : Wakeup(p))

(* Invariants *)
AtMostOneRunning ==
    Cardinality({p \in Processes : state[p] = "Running"}) <= 1

(* Liveness properties *)
ReadyEventuallyRuns ==
    \A p \in Processes : (state[p] = "Ready") ~> (state[p] = "Running")

RunningEventuallyTerminates ==
    \A p \in Processes : (state[p] = "Running") ~> (state[p] = "Terminated")

===================================================================================
