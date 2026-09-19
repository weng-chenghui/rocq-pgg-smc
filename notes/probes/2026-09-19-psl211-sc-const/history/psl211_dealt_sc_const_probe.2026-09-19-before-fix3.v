(* Probe, 2026-09-19. Not a production file.                                 *)
(*****************************************************************************)
(* psl211_dealt_sc_const_probe: the constancy field under the dealer-dealt   *)
(*                              run parameters                              *)
(*                                                                          *)
(* Under the dealt parameters the run argument is the chirality bit and the  *)
(* deck is the scheme's own encoder. Seats 0, 1 and 2 reading cards 0, 1 and  *)
(* 6 is a reading no cut produces at one chirality and exactly one cut        *)
(* produces at the other, so the group-uniform cut is read differently at the *)
(* two secrets and the constancy field of a spectral certificate fails there  *)
(* as well.                                                                  *)
(*                                                                          *)
(* The counting is the one of notes/probes/2026-09-15-psl211-planb/           *)
(* probe_p2_codeview.v, whose psl211_codeview_neq3 compares the two           *)
(* chiralities' multiplicity vectors over the 660 tabulated cuts and whose    *)
(* printed witness is the numeral 18, the digits (0, 1, 6) and the            *)
(* multiplicities (0, 1). That lemma stops at the raw nat tables. What is     *)
(* added here is the passage from the count to the record's own field, which  *)
(* is the fiber cardinality bridge of instances/psl211/psl211_models.v read   *)
(* at the encoder deck instead of at a dealt deck description.                *)
(*                                                                          *)
(* The encoder deck of a chirality is NOT the deck the all-decks dealer lays  *)
(* at psl211_perdeck_deal: block line zero of either chirality's table is     *)
(* [0;1;2;3;4;10] and [0;1;2;3;4;11], while the encoder puts its heart codes  *)
(* on the representative rows [2;3;5;7;8;9] and [0;1;3;7;10;11]. The all-decks*)
(* refutation therefore does not transport, and the count is redone here.     *)
(*****************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import design_privacy.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_exec.
From pgg_smc Require Import psl211_endpoints psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_blocks psl211_closure.
From psl211_sc_const_probe Require Import psl211_sc_const_probe.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Local Notation seatT :=
  ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1).
Local Notation cardT :=
  ('I_(pgg_N' (mp_M (instance_profile psl211_algebra))).+1).
Local Notation cutT := (pgg_gT psl211_M).
Local Notation viewT := ({ffun seatT -> cardT}).

(*****************************************************************************)
(*     The encoder deck as a raw table                                      *)
(*****************************************************************************)

(** psl211_dealt_decktbl b — the encoder deck of chirality b as a twelve-entry
    position-to-code table: the heart codes 0 to 5 ascend along the
    representative row of the system b names and the club codes 6 to 11
    ascend along its complement. Only raw nat data is counted below, the
    ordinal enumeration going through an opaque decision that does not
    reduce. *)
Definition psl211_dealt_decktbl (b : bool) : seq nat :=
  if b then [:: 6; 7; 0; 1; 8; 2; 9; 3; 4; 5; 10; 11]
       else [:: 0; 1; 6; 2; 7; 8; 9; 3; 10; 11; 4; 5].

(** psl211_dealt_decktblE — the card the encoder deals to a position is that
    table's entry at the position. *)
Lemma psl211_dealt_decktblE (b : bool) (i : 'I_12) :
  val (tnth (psl211_orbit_encode b) i)
  = nth 0 (psl211_dealt_decktbl b) (val i).
Proof.
rewrite /psl211_orbit_encode tnth_mktuple.
by case: b; case: i => -[|[|[|[|[|[|[|[|[|[|[|[|?]]]]]]]]]]]] ?.
Qed.

(** psl211_dealt_decktbl_mod — every entry of that table is below twelve, so
    reading it modulo twelve changes nothing. *)
Lemma psl211_dealt_decktbl_mod (b : bool) (k : nat) :
  nth 0 (psl211_dealt_decktbl b) k %% 12 = nth 0 (psl211_dealt_decktbl b) k.
Proof.
by case: b; case: k => [|[|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]] //=;
   rewrite nth_nil.
Qed.

(*****************************************************************************)
(*     The separating reading, and its fiber of cuts                        *)
(*****************************************************************************)

(** psl211_dealt_view — the reading that gives cards 0, 1 and 6 to seats 0, 1
    and 2, and card 0 to every seat outside the coalition. The first numeral
    at which the two chiralities' reading multiplicities differ. *)
Definition psl211_dealt_view : viewT :=
  [ffun i => psl211_code12 (nth 0 [:: 0; 1; 6] (val i))].

(** psl211_dealt_test sq t — the coalition's reading of the deck sq under the
    cut whose table is t matches psl211_dealt_view, tested on raw codes. *)
Definition psl211_dealt_test (sq t : seq nat) : bool :=
  [&& nth 0 sq (nth 0 t 0) %% 12 == 0,
      nth 0 sq (nth 0 t 1) %% 12 == 1 &
      nth 0 sq (nth 0 t 2) %% 12 == 6].

(** psl211_dealt_testE — the raw test decides the reading, so the fiber over
    psl211_dealt_view is counted by a boolean on nat lists. *)
Lemma psl211_dealt_testE (sq t : seq nat) :
  (psl211_perdeck_raw_view sq t == psl211_dealt_view) = psl211_dealt_test sq t.
Proof.
rewrite /psl211_dealt_test; apply/idP/idP.
- move/eqP/ffunP => H; apply/and3P; split; apply/eqP.
  + by move: (H (psl211_code12 0)) => /(congr1 val); rewrite !ffunE /=.
  + by move: (H (psl211_code12 1)) => /(congr1 val); rewrite !ffunE /=.
  + by move: (H (psl211_code12 2)) => /(congr1 val); rewrite !ffunE /=.
- case/and3P => H0 H1 H2; apply/eqP/ffunP => i.
  rewrite !ffunE; apply/val_inj.
  case: i => [] [|[|[|k]]] Hk //=.
  + by rewrite (eqP H0).
  + by rewrite (eqP H1).
  + by rewrite (eqP H2).
  + by rewrite nth_default.
Qed.

(** psl211_dealt_raw_count b — how many of the 660 cuts carry the encoder deck
    of chirality b to psl211_dealt_view. *)
Definition psl211_dealt_raw_count (b : bool) : nat :=
  count (psl211_dealt_test (psl211_dealt_decktbl b))
    (unzip1 psl211_elem_table).

(** psl211_dealt_raw_countE — that count is zero at one chirality and one at
    the other. This is the count comparison of the Plan B probe read at one
    numeral instead of over the whole multiplicity vector. *)
Lemma psl211_dealt_raw_countE :
  psl211_dealt_raw_count true = 0 /\ psl211_dealt_raw_count false = 1.
Proof. by split; vm_compute. Qed.

(** psl211_dealt_static_obsE — seat i's entry of the framework's static
    coalition reading under the dealt parameters is the card the encoder deck
    of the run argument puts at the cut image of seat i. The dealt analogue of
    psl211_alldecks_static_obsE. *)
Lemma psl211_dealt_static_obsE (C : {set seatT})
    (b : ex_inputT psl211_dealt_params) (g : cutT) (i : seatT) :
  @static_coalition_obs psl211_algebra psl211_dealt_params C b g i
  = if i \in C
    then tnth (psl211_orbit_encode b) (@pgg_rho psl211_M g i)
    else ord0.
Proof.
rewrite static_coalition_obsE.
by case: ifP => // _; rewrite /= tnth_ord_tuple.
Qed.

(** psl211_dealt_raw_viewE — the raw reading is the framework's reading. *)
Lemma psl211_dealt_raw_viewE (b : bool) (g : cutT) :
  psl211_perdeck_raw_view (psl211_dealt_decktbl b) (psl211_ptbl g)
  = @static_coalition_obs psl211_algebra psl211_dealt_params
      psl211_perdeck_coalition b g.
Proof.
apply/ffunP => i.
rewrite /psl211_perdeck_raw_view ffunE psl211_dealt_static_obsE.
(* in_set and not inE: inE would rewrite the seq membership on the left
   instead of the set membership on the right *)
rewrite /psl211_perdeck_coalition in_set.
case Hi: (val i \in [:: 0; 1; 2]) => //.
rewrite psl211_perdeck_ptbl_nth; apply/val_inj.
by rewrite psl211_dealt_decktblE /= psl211_dealt_decktbl_mod.
Qed.

(* Past this point no proof needs the body of the closure table or of the
   count, and every step that names both chiralities must not be left to a
   tactic that searches for a match. *)
Local Opaque psl211_elem_table.

(** psl211_dealt_fiber b — the cuts of the group carrying the encoder deck of
    chirality b to psl211_dealt_view. *)
Definition psl211_dealt_fiber (b : bool) : {set cutT} :=
  [set g in pgg_G psl211_M |
     @static_coalition_obs psl211_algebra psl211_dealt_params
       psl211_perdeck_coalition b g == psl211_dealt_view].

(** psl211_dealt_fiberE — that fiber has the raw count as its cardinality. *)
Lemma psl211_dealt_fiberE (b : bool) :
  #|psl211_dealt_fiber b| = psl211_dealt_raw_count b.
Proof.
rewrite /psl211_dealt_fiber /psl211_dealt_raw_count.
transitivity
  (count (fun g => @static_coalition_obs psl211_algebra psl211_dealt_params
      psl211_perdeck_coalition b g == psl211_dealt_view)
    (enum (pgg_G psl211_M))).
  rewrite cardE /enum_mem size_filter count_filter.
  by apply: eq_count => g; rewrite !inE andbC.
transitivity
  (count (psl211_dealt_test (psl211_dealt_decktbl b))
    [seq psl211_ptbl g | g <- enum (pgg_G psl211_M)]).
  rewrite count_map; apply: eq_count => g.
  by rewrite -psl211_dealt_raw_viewE psl211_dealt_testE.
rewrite -!size_filter; apply: perm_size.
exact: (perm_filter _ psl211_perdeck_ptbl_enum).
Qed.

(* psl211_dealt_raw_count is sealed for the rest of the file: nothing below
   needs its body, psl211_dealt_raw_countE supplies both values, and leaving
   it transparent lets a unifier that falls back to conversion evaluate the
   count over the 660 tabulated cuts. *)
Local Opaque psl211_dealt_raw_count.

(** psl211_dealt_massE b — at the encoder deck of chirality b the law of what
    the coalition reads gives psl211_dealt_view the mass of its fiber of cuts
    over the order of the shuffle group. *)
Lemma psl211_dealt_massE (R : realType) (b : bool) :
  (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
       psl211_perdeck_coalition b) ((`U psl211_G_pos) : R.-fdist cutT))
     psl211_dealt_view
  = (#|pgg_G psl211_M|%:R)^-1 *+ #|psl211_dealt_fiber b| :> R.
Proof. by rewrite /psl211_dealt_fiber uniform_fdistmap_pointE. Qed.

(*****************************************************************************)
(*     The constancy field fails under the dealt parameters                 *)
(*****************************************************************************)

(** psl211_dealt_sc_const_false — under the dealer-dealt run parameters the
    constancy field is false at the uniform law on the shuffle group, so no
    spectral certificate over these parameters can take that law as its
    ideal cut, while a certificate at some other ideal stays open. The
    dealt run argument is the chirality and nothing else, so
    here the constancy field is exactly constancy in the secret, and it fails
    because the encoder decks of the two chiralities give one reading of three
    seats different masses. That is a fact about the group and the design:
    PSL(2,11) is 2-transitive and not 3-transitive, where PGL(2,7) certifies
    the same field through pgl27_word_view_const. The statement rules out one
    named ideal and no certificate, this tree carrying no dealt-mode sample
    adapter through which a certificate's ideal could be pinned to it. *)
Lemma psl211_dealt_sc_const_false (R : realType) :
  ~ sc_const_prop psl211_dealt_params ((`U psl211_G_pos) : R.-fdist cutT).
Proof.
move=> Hconst.
have Heq := Hconst psl211_perdeck_coalition psl211_perdeck_coalition_below_k
  true false.
(* each mass is pinned to its value in a goal naming one chirality only, and
   the two are brought together in term mode *)
have [Ht Hf] := psl211_dealt_raw_countE.
have H0 : #|psl211_dealt_fiber true| = 0 :=
  etrans (psl211_dealt_fiberE true) Ht.
have H1 : #|psl211_dealt_fiber false| = 1 :=
  etrans (psl211_dealt_fiberE false) Hf.
have Lt : (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
    psl211_perdeck_coalition true) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_dealt_view = 0 :> R.
  by rewrite psl211_dealt_massE H0 mulr0n.
have Lf : (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
    psl211_perdeck_coalition false) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_dealt_view = (#|pgg_G psl211_M|%:R)^-1 :> R.
  by rewrite psl211_dealt_massE H1 mulr1n.
have Hz : (0 : R) = (#|pgg_G psl211_M|%:R)^-1 :=
  etrans (esym Lt)
    (etrans (congr1 (fun q : R.-fdist viewT => q psl211_dealt_view) Heq) Lf).
have : (#|pgg_G psl211_M|%:R)^-1 == 0 :> R by rewrite -Hz.
rewrite invr_eq0 pnatr_eq0 => /eqP Hcard.
by move: psl211_G_pos; rewrite Hcard.
Qed.

Print Assumptions psl211_dealt_raw_countE.
Print Assumptions psl211_dealt_sc_const_false.
