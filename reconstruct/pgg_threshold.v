(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From pgg_reconstruct Require Import pgg_assignment pgg_deck_pairing pgg_sum_mod.

(******************************************************************************)
(*                                                                            *)
(*       (k,T)-Ramp Threshold Theorem for PGG                                *)
(*                                                                            *)
(* This file combines the assignment graph, deck pairing, and collusion       *)
(* bound into the (k,T)-ramp threshold theorem for PGG.                      *)
(*                                                                            *)
(* Section 1: Ramp scheme configuration                                       *)
(*   RampConfig == record bundling T players, N card positions, assignment,  *)
(*                 and the total number of encoded bits                       *)
(*                                                                            *)
(* Section 2: Ramp threshold theorem                                          *)
(*   ramp_threshold == for any coalition C:                                   *)
(*     (1) recoverable bits = |covered_edges C|                              *)
(*     (2) monotonicity: C <= C' implies covered_edges C <= covered_edges C' *)
(*     (3) full coalition recovers all edges                                  *)
(*                                                                            *)
(* Section 3: Corollaries for specific graph families                         *)
(*   cycle_ramp_loss  == losing a party from the cycle loses secure edges    *)
(*   complete_ramp_max == full coalition on the complete graph recovers all  *)
(*                                                                            *)
(* Section 4: Combined security-reconstruction statement                      *)
(*   ramp_security_reconstruction == the covered and secure edges partition   *)
(*                        the assignment graph, the covered count fixes the   *)
(*                        recoverable bits, coverage is monotone in the       *)
(*                        coalition, and a singleton coalition covers nothing *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope nat_scope.

(* ========================================================================= *)
(* Section 1: Ramp Scheme Configuration                                      *)
(* ========================================================================= *)

Record RampConfig := mkRamp {
  rc_T' : nat ;                    (* T = rc_T'.+1 parties *)
  rc_N' : nat ;                    (* N = rc_N'.+1 card positions *)
  rc_ag : AssignmentGraph rc_T'.+1 ;  (* assignment graph *)
  rc_num_bits : nat ;              (* total number of encoded bits = |edges|/2 *)
}.

(** The party-index bound T = (rc_T' rc).+1 of a RampConfig: the carrier
    'I_T over which the ramp theorems below quantify coalitions. *)
Definition rc_T (rc : RampConfig) : nat := (rc_T' rc).+1.
(** The bound N = (rc_N' rc).+1 on the number of card positions of a
    RampConfig: the count the ramp scheme's assignment graph encodes
    over. *)
Definition rc_N (rc : RampConfig) : nat := (rc_N' rc).+1.

(* ========================================================================= *)
(* Section 2: Ramp Threshold Theorem                                         *)
(* ========================================================================= *)

Section ramp_threshold.

Variable T' : nat.
Let T := T'.+1.

Variable ag : AssignmentGraph T.

(** The main ramp threshold theorem: three-part characterization of
    coalition power in terms of edge coverage. *)
Theorem ramp_threshold :
  forall (C : {set 'I_T}),
  (* Part 1: recoverable bits are exactly the covered directed edges (halved) *)
  recoverable_bits ag C = #|covered_edges ag C| %/ 2 /\
  (* Part 2: monotonicity -- larger coalitions recover more *)
  (forall C' : {set 'I_T}, C \subset C' ->
    covered_edges ag C \subset covered_edges ag C') /\
  (* Part 3: full coalition recovers everything *)
  (C = setT -> covered_edges ag C = ag_edges ag).
Proof.
move=> C; split; [| split].
- (* Part 1: by definition of recoverable_bits *)
  by [].
- (* Part 2: monotonicity from covered_mono *)
  move=> C' Hsub.
  exact: covered_mono.
- (* Part 3: full coalition from covered_full *)
  exact: covered_full.
Qed.

(** Derived: the number of recoverable bits is monotone in coalition size. *)
Corollary recoverable_mono (C C' : {set 'I_T}) :
  C \subset C' ->
  (recoverable_bits ag C <= recoverable_bits ag C')%N.
Proof.
move=> Hsub.
rewrite /recoverable_bits.
apply: leq_div2r.
apply: subset_leq_card.
exact: covered_mono.
Qed.

(** A singleton coalition recovers nothing. *)
Corollary singleton_no_info (C : {set 'I_T}) :
  #|C| = 1 -> recoverable_bits ag C = 0.
Proof.
move=> HC1.
rewrite /recoverable_bits (@secure_singleton _ ag _ HC1).
by rewrite cards0.
Qed.

(** The empty coalition recovers nothing. *)
Corollary empty_no_info :
  recoverable_bits ag set0 = 0.
Proof.
by rewrite /recoverable_bits covered_edges0 cards0.
Qed.

(** Secure edges and covered edges partition the edge set. *)
Lemma ramp_partition (C : {set 'I_T}) :
  covered_edges ag C :|: secure_edges ag C = ag_edges ag.
Proof. exact: covered_secure_partition. Qed.

(** Secure edges decrease as coalition grows. *)
Lemma secure_antimono (C C' : {set 'I_T}) :
  C \subset C' ->
  secure_edges ag C' \subset secure_edges ag C.
Proof.
move=> Hsub; rewrite /secure_edges.
apply: setDS.
exact: covered_mono.
Qed.

End ramp_threshold.

(* ========================================================================= *)
(* Section 3: Corollaries for Specific Graphs                                *)
(* ========================================================================= *)

Section cycle_ramp.

Variable T' : nat.
Hypothesis T'_gt1 : (1 < T')%N.

Let ag := cycle_graph (ltnW T'_gt1).

(** In the cycle graph, losing any party from the full coalition
    leaves at least some edges uncovered (secure). *)
Lemma cycle_ramp_loss (C : {set 'I_T'.+1}) :
  C \proper setT ->
  secure_edges ag C != set0.
Proof.
move=> Hproper.
have /properP [_ [i _ Hi]] := Hproper.
apply/set0Pn.
set e := (i, inZp (i + 1) : 'I_T'.+1).
exists e.
have He : e \in ag_edges ag.
  rewrite /ag /=.
  change (e \in cycle_edge_set T').
  rewrite /cycle_edge_set in_set /e /=.
  by rewrite eqxx.
have Hne : e \notin covered_edges ag C.
  apply/negP.
  rewrite /covered_edges inE => /andP [_ /andP [Hi2 _]].
  by rewrite Hi2 in Hi.
by rewrite /secure_edges inE He Hne.
Qed.

(** The full coalition on the cycle recovers all edges. *)
Lemma cycle_full_recovery :
  covered_edges ag setT = ag_edges ag.
Proof. exact: covered_full. Qed.

End cycle_ramp.

Section complete_ramp.

Variable T' : nat.

Let ag := complete_graph T'.

(** On the complete graph, the full coalition recovers the maximum
    number of bits: every pair of distinct parties contributes. *)
Lemma complete_ramp_max :
  recoverable_bits ag setT = #|ag_edges ag| %/ 2.
Proof.
rewrite /recoverable_bits.
by rewrite (covered_full ag (erefl setT)).
Qed.

End complete_ramp.

(* ========================================================================= *)
(* Section 4: Combined Security-Reconstruction Statement                     *)
(* ========================================================================= *)

(** This section packages, for a fixed coalition C, the ramp-threshold facts
    of Section 2 together with the covered/secure partition: every edge is
    either covered by C or secure against it, and a secure edge always has
    at least one endpoint outside C (secure_edge_witness below). What this
    section does not formalize is the information-theoretic half of the
    ramp scheme's security claim: bounding the coalition's view of a secure
    edge's component by an entropy term derived from the collusion bound via
    the data-processing inequality remains open. *)

Section secure_reconstruction.

Variable T' : nat.
Let T := T'.+1.

Variable ag : AssignmentGraph T.
Variable C : {set 'I_T}.

(** For each secure edge, at least one endpoint is not in C. *)
Lemma secure_edge_witness (e : 'I_T * 'I_T) :
  e \in secure_edges ag C ->
  (e.1 \notin C) || (e.2 \notin C).
Proof.
rewrite /secure_edges /covered_edges !inE.
by case: (e \in ag_edges ag) => //=; case: (e.1 \in C) => //=;
   case: (e.2 \in C).
Qed.

(* TODO: edge security. For e in secure_edges ag C, bound the coalition's
   var_dist on e's component by epsilon, via collusion_bound_k (Section 6
   of pgg_collusion_bound) transported along DPI. *)

(** ramp_security_reconstruction bundles four facts about coalition C's
    reconstruction power on ag: the covered and secure edges partition
    ag's edge set; the recoverable-bit count equals half the covered-edge
    count; covered edges grow monotonically as C grows; and a singleton
    coalition covers no edges. It repackages Section 2's ramp threshold
    together with the covered/secure partition into one statement. It
    proves no bound on the coalition's view of the secure edges; the
    epsilon-style security half of the ramp scheme's claim is not
    formalized here. *)

Theorem ramp_security_reconstruction :
  (* Every edge is either recoverable or secure *)
  covered_edges ag C :|: secure_edges ag C = ag_edges ag /\
  (* Recoverable count *)
  recoverable_bits ag C = #|covered_edges ag C| %/ 2 /\
  (* Monotonicity *)
  (forall C' : {set 'I_T}, C \subset C' ->
    covered_edges ag C \subset covered_edges ag C') /\
  (* Singleton security *)
  (#|C| = 1 -> covered_edges ag C = set0).
Proof.
split; [| split; [| split]].
- exact: covered_secure_partition.
- by [].
- move=> C' Hsub; exact: covered_mono.
- exact: secure_singleton.
Qed.

End secure_reconstruction.

(* ========================================================================= *)
(* Section 5: Numeric Ramp Parameters                                        *)
(* ========================================================================= *)

(** Convenience section: given a RampConfig, extract the threshold
    parameters and instantiate the main theorems. *)

Section ramp_config_theorems.

Variable rc : RampConfig.

Let T := rc_T rc.
Let ag := rc_ag rc.

(** ramp_threshold restated for rc's own assignment graph: recoverable bits
    equal half the covered-edge count, covered edges grow monotonically with
    the coalition, and the full coalition recovers every edge. This is the
    form of the threshold theorem quoted by files that hold a RampConfig
    rather than a bare AssignmentGraph. *)
Theorem ramp_config_threshold (C : {set 'I_T}) :
  recoverable_bits ag C = #|covered_edges ag C| %/ 2 /\
  (forall C' : {set 'I_T}, C \subset C' ->
    covered_edges ag C \subset covered_edges ag C') /\
  (C = setT -> covered_edges ag C = ag_edges ag).
Proof. exact: ramp_threshold. Qed.

(** recoverable_mono restated over rc: growing the coalition from C to C'
    never decreases the recoverable-bit count. *)
Theorem ramp_config_mono (C C' : {set 'I_T}) :
  C \subset C' ->
  (recoverable_bits ag C <= recoverable_bits ag C')%N.
Proof. exact: recoverable_mono. Qed.

End ramp_config_theorems.

Check ramp_threshold.
Check ramp_security_reconstruction.
Check ramp_config_threshold.
Check cycle_ramp_loss.
Check complete_ramp_max.
