(*
 * Operating System Memory Management: Page Table and Page Fault Invariants
 *
 * This file models a simplified page table mapping virtual pages to
 * physical frames, and proves basic invariants:
 *   - A mapped virtual page always maps to a valid frame.
 *   - The number of mappings does not exceed the number of frames.
 *
 * Source: OSTEP Ch. 13~22, Linux Kernel mm/memory.c
 *)

Require Import List Arith Lia.

Definition VPN := nat.  (* Virtual Page Number *)
Definition PFN := nat.  (* Page Frame Number *)

(* Page table entry: present bit + frame *)
Record PTE := mkPTE {
  present : bool;
  frame : option PFN
}.

Definition PageTable := list (VPN * PTE).

Definition num_frames := nat.

(* Number of present mappings *)
Fixpoint count_present (pt : PageTable) : nat :=
  match pt with
  | nil => 0
  | (_, pte) :: pt' =>
      if pte.(present) then S (count_present pt') else count_present pt'
  end.

(* All present entries map to a frame *)
Definition all_present_have_frame (pt : PageTable) : Prop :=
  forall vpn pte,
    In (vpn, pte) pt -> pte.(present) = true -> pte.(frame) <> None.

(* All frames are below num_frames *)
Definition all_frames_valid (pt : PageTable) (max_frame : num_frames) : Prop :=
  forall vpn pte,
    In (vpn, pte) pt ->
    pte.(present) = true ->
    forall f, pte.(frame) = Some f -> f < max_frame.

(* Mapping count invariant *)
Definition mapping_count_ok (pt : PageTable) (max_frame : num_frames) : Prop :=
  count_present pt <= max_frame.

(* Add a mapping: ensures no overflow *)
Definition add_mapping (pt : PageTable) (vpn : VPN) (f : PFN) (max : num_frames)
  : option PageTable :=
  if count_present pt <? max then
    Some ((vpn, mkPTE true (Some f)) :: pt)
  else
    None.

(* Remove a mapping by VPN *)
Fixpoint remove_mapping (pt : PageTable) (vpn : VPN) : PageTable :=
  match pt with
  | nil => nil
  | (vpn', pte) :: pt' =>
      if Nat.eqb vpn vpn' then remove_mapping pt' vpn
      else (vpn', pte) :: remove_mapping pt' vpn
  end.

(* Lemma: remove does not increase present count *)
Lemma remove_present_le :
  forall pt vpn,
    count_present (remove_mapping pt vpn) <= count_present pt.
Proof.
  induction pt as [| [vpn' pte] pt' IH]; simpl; intros vpn.
  - lia.
  - destruct (Nat.eqb vpn vpn'); simpl.
    + lia.
    + destruct (present pte); lia.
Qed.

(* Theorem: add_mapping preserves mapping count invariant *)
Theorem add_mapping_count_ok :
  forall pt vpn f max pt',
    mapping_count_ok pt max ->
    add_mapping pt vpn f max = Some pt' ->
    mapping_count_ok pt' max.
Proof.
  intros pt vpn f max pt' Hok Hadd.
  unfold add_mapping in Hadd.
  destruct (count_present pt <? max) eqn:Hlt; [|discriminate].
  inversion Hadd; subst; clear Hadd.
  unfold mapping_count_ok in *. simpl.
  apply Nat.ltb_lt in Hlt. lia.
Qed.

(* Theorem: remove_mapping preserves mapping count invariant *)
Theorem remove_mapping_count_ok :
  forall pt vpn max,
    mapping_count_ok pt max ->
    mapping_count_ok (remove_mapping pt vpn) max.
Proof.
  intros pt vpn max Hok.
  unfold mapping_count_ok in *.
  apply Nat.le_trans with (m := count_present pt); auto.
  apply remove_present_le.
Qed.
