-------------------------- MODULE FreeRTOS_TaskScheduler --------------------------
(*
 * FreeRTOS Priority-Preemptive Scheduler Model
 * Model: A set of fixed-priority tasks. The highest-priority ready task
 * always runs. Equal-priority tasks run in round-robin with time slicing.
 *
 * Properties:
 *   - Highest priority ready task is always running
 *   - No deadlock
 *   - Highest-priority ready task is dispatched immediately
 *
 * Author: SystemOSIOT
 * Source: FreeRTOS Documentation, Mastering the FreeRTOS Kernel
 *)

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Tasks, Priorities, TimeSlice

TaskPriority == [t \in Tasks |->
    CASE t = "t1" -> 3
      [] t = "t2" -> 2
      [] OTHER    -> 1]

VARIABLES task_state, running, ticks_remaining

States == {"Ready", "Running", "Blocked"}

TypeOK ==
    /\ task_state \in [Tasks -> States]
    /\ running \in Tasks \cup {"None"}
    /\ ticks_remaining \in 0..TimeSlice

(* Initially all tasks are ready, highest priority task runs *)
Init ==
    /\ task_state = [t \in Tasks |-> "Ready"]
    /\ running = CHOOSE t \in Tasks :
                  \A u \in Tasks : TaskPriority[t] >= TaskPriority[u]
    /\ ticks_remaining = TimeSlice

(* Return the highest-priority ready task; if tie, choose deterministically *)
HighestReady ==
    CHOOSE t \in {t \in Tasks : task_state[t] = "Ready"} :
        \A u \in {u \in Tasks : task_state[u] = "Ready"} :
            TaskPriority[t] >= TaskPriority[u]

(* A running task blocks (waits for event); immediately dispatch next ready task *)
Block(t) ==
    /\ running = t
    /\ task_state' = [task_state EXCEPT ![t] = "Blocked"]
    /\ LET ready_set == {u \in Tasks : task_state'[u] = "Ready"}
       IN IF ready_set = {}
          THEN /\ running' = "None"
               /\ ticks_remaining' = 0
          ELSE /\ running' = CHOOSE r \in ready_set :
                                \A u \in ready_set : TaskPriority[r] >= TaskPriority[u]
               /\ ticks_remaining' = TimeSlice

(* Dispatch: when no task is running, pick the highest-priority ready task *)
Dispatch ==
    /\ running = "None"
    /\ \E t \in Tasks : task_state[t] = "Ready"
    /\ running' = HighestReady
    /\ ticks_remaining' = TimeSlice
    /\ UNCHANGED task_state

(* A blocked task becomes ready; may preempt current running task *)
Ready(t) ==
    /\ task_state[t] = "Blocked"
    /\ task_state' = [task_state EXCEPT ![t] = "Ready"]
    /\ LET new_ready == HighestReady' IN
       IF running = "None" 
          THEN running' = new_ready
          ELSE IF TaskPriority[t] > TaskPriority[running]
                  THEN running' = t
                  ELSE running' = running
    /\ ticks_remaining' = IF running' = t THEN TimeSlice ELSE ticks_remaining

(* Running task consumes one tick; on slice expiry, equal-priority round-robin *)
Tick ==
    /\ running /= "None"
    /\ ticks_remaining > 0
    /\ ticks_remaining' = ticks_remaining - 1
    /\ UNCHANGED <<task_state, running>>

(* Time slice expires: current task returns to ready, next equal priority task runs *)
SliceExpire ==
    /\ running /= "None"
    /\ ticks_remaining = 0
    /\ task_state' = [task_state EXCEPT ![running] = "Ready"]
    /\ running' = HighestReady'
    /\ ticks_remaining' = TimeSlice

Next ==
    (\E t \in Tasks : Block(t) \/ Ready(t)) \/ Dispatch \/ Tick \/ SliceExpire

Spec ==
    /\ Init
    /\ [][Next]_<<task_state, running, ticks_remaining>>
    /\ WF_<<task_state, running, ticks_remaining>>(Next)

(* Invariants *)
RunningIsReady ==
    running = "None" \/ task_state[running] = "Ready"

HighestPriorityRunning ==
    running = "None"
    \/ ~\E t \in Tasks :
        task_state[t] = "Ready" /\ TaskPriority[t] > TaskPriority[running]

(* Highest-priority ready task is always dispatched immediately *)
HighestPriorityTaskRuns ==
    \A t \in Tasks :
        ((task_state[t] = "Ready") /\
         ~\E u \in Tasks : (task_state[u] = "Ready") /\ (TaskPriority[u] > TaskPriority[t]))
        => (running = t)

(* Liveness: every blocked task eventually becomes ready *)
NoPermanentBlock ==
    \A t \in Tasks :
        (task_state[t] = "Blocked") ~> (task_state[t] = "Ready")

====================================================================================
