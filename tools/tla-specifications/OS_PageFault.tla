----------------------------- MODULE OS_PageFault -----------------------------
(*
 * Demand Paging State Machine
 * Model: A single page access sequence showing the transition from
 *   virtual page not present -> page fault -> page allocation -> page present.
 *
 * Properties:
 *   - Type correctness
 *   - No deadlock
 *   - Liveness: every requested page eventually becomes present
 *
 * Author: SystemOSIOT
 * Source: OSTEP Ch. 20~22, Linux Kernel mm/memory.c
 *)

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Pages, MaxFrames

VARIABLES present, referenced, dirty, frames_used

TypeOK ==
    /\ present \in [Pages -> BOOLEAN]
    /\ referenced \in [Pages -> BOOLEAN]
    /\ dirty \in [Pages -> BOOLEAN]
    /\ frames_used \in 0..MaxFrames

Init ==
    /\ present = [p \in Pages |-> FALSE]
    /\ referenced = [p \in Pages |-> FALSE]
    /\ dirty = [p \in Pages |-> FALSE]
    /\ frames_used = 0

(* A process accesses a page that is not present -> page fault *)
AccessNotPresent(p) ==
    /\ ~present[p]
    /\ frames_used < MaxFrames
    /\ present' = [present EXCEPT ![p] = TRUE]
    /\ referenced' = [referenced EXCEPT ![p] = TRUE]
    /\ dirty' = dirty
    /\ frames_used' = frames_used + 1

(* A process writes a present page -> set dirty *)
WritePresent(p) ==
    /\ present[p]
    /\ dirty' = [dirty EXCEPT ![p] = TRUE]
    /\ referenced' = [referenced EXCEPT ![p] = TRUE]
    /\ present' = present
    /\ frames_used' = frames_used

(* A present page is evicted (simplified: only if not dirty) *)
Evict(p) ==
    /\ present[p]
    /\ ~dirty[p]
    /\ present' = [present EXCEPT ![p] = FALSE]
    /\ referenced' = [referenced EXCEPT ![p] = FALSE]
    /\ dirty' = dirty
    /\ frames_used' = frames_used - 1

Next ==
    \E p \in Pages :
        AccessNotPresent(p) \/ WritePresent(p) \/ Evict(p)

Spec ==
    /\ Init
    /\ [][Next]_<<present, referenced, dirty, frames_used>>
    /\ WF_<<present, referenced, dirty, frames_used>>(Next)

(* Invariants *)
FramesNotExceeded ==
    frames_used <= MaxFrames

PresentImpliesFrame ==
    frames_used >= Cardinality({p \in Pages : present[p]})

(* Liveness: every page can eventually be present *)
AllPagesCanBePresent ==
    \A p \in Pages : <>(present[p] = TRUE)

================================================================================
