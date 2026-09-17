(* PROBE Q4 (task P0, plan 2026-09-18-pgl27-encoding-parameter).
   The executed trace at an arbitrary deck function enc : bool -> 8.-tuple 'I_8,
   parallel to pgl27_player_trace / pgl27_coalition_trace of pgl27_trace.v.
   Question: does the seat-trace equality and the coalition-trace-is-view
   equality need any premise on enc (deck validity in particular)? *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg boolp reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
Require Import pgg_interface.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment pgg_run.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_reconstruct Require Import covering_scheme pgg_sharing_framework.
From pgg_reconstruct Require Import transitivity_privacy.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_scheme pgl27_profile.
From pgg_smc Require Import pgl27_run pgl27_secrecy pgl27_trace.
From pgg_smc Require Import pgg_trace_secrecy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section q4_trace_enc.
Variable R : realType.
Variable enc : bool -> 8.-tuple 'I_8.

(* Seat i's executed-trace content over the joint secret-and-cut sampler,
   dealing the deck enc s of the sampled secret s. *)
Definition enc_player_trace (i : 'I_8) : {RV (pgl27P R) -> 'I_8} :=
  fun u =>
    content_of
      (nth [::] (run_interp pgl27_fuel (pgl27_procs_deck (enc u.1) u.2)).2
           (2 + i)).

(* Seat i's trace is the card the deck enc u.1 puts at the cut-permuted
   position of seat i.  No premise on enc. *)
Lemma enc_player_trace_E (i : 'I_8) :
  enc_player_trace i
  = (fun u => tnth (enc u.1) (@pgg_rho pgl27_M u.2 i)).
Proof.
apply: boolp.funext => u; rewrite /enc_player_trace pgl27_procs_deck_abs.
case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi.
- rewrite (pgl27_abs_p0 (tnth (enc u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p1 (tnth (enc u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p2 (tnth (enc u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p3 (tnth (enc u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p4 (tnth (enc u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p5 (tnth (enc u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p6 (tnth (enc u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
- rewrite (pgl27_abs_p7 (tnth (enc u.1)) u.2) tnth_ord_tuple.
  by congr (tnth (enc u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
Qed.

(* The full seat trace is the index marker and the singleton hand holding
   that one card.  No premise on enc. *)
Lemma enc_player_trace_full (i : 'I_8) (u : bool * pgg_gT pgl27_M) :
  nth [::] (run_interp pgl27_fuel (pgl27_procs_deck (enc u.1) u.2)).2 (2 + i)
  = [:: PGG_idx 0; PGG_hand [:: enc_player_trace i u]].
Proof.
rewrite pgl27_procs_deck_abs enc_player_trace_E.
case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi.
- have -> : (@Ordinal 8 0 Hi) = (@Ordinal 8 0 isT) by apply: val_inj.
  by rewrite (pgl27_full_p0 (tnth (enc u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 1 Hi) = (@Ordinal 8 1 isT) by apply: val_inj.
  by rewrite (pgl27_full_p1 (tnth (enc u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 2 Hi) = (@Ordinal 8 2 isT) by apply: val_inj.
  by rewrite (pgl27_full_p2 (tnth (enc u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 3 Hi) = (@Ordinal 8 3 isT) by apply: val_inj.
  by rewrite (pgl27_full_p3 (tnth (enc u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 4 Hi) = (@Ordinal 8 4 isT) by apply: val_inj.
  by rewrite (pgl27_full_p4 (tnth (enc u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 5 Hi) = (@Ordinal 8 5 isT) by apply: val_inj.
  by rewrite (pgl27_full_p5 (tnth (enc u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 6 Hi) = (@Ordinal 8 6 isT) by apply: val_inj.
  by rewrite (pgl27_full_p6 (tnth (enc u.1)) u.2) tnth_ord_tuple.
- have -> : (@Ordinal 8 7 Hi) = (@Ordinal 8 7 isT) by apply: val_inj.
  by rewrite (pgl27_full_p7 (tnth (enc u.1)) u.2) tnth_ord_tuple.
Qed.

(* The coalition's joint executed trace: the card each member sees, ord0
   outside. *)
Definition enc_coalition_trace (C : {set 'I_8}) :
    {RV (pgl27P R) -> {ffun 'I_8 -> 'I_8}} :=
  fun u => [ffun i => if i \in C then enc_player_trace i u else ord0].

(* The coalition's joint executed trace is the generic coalition view at the
   deck function enc.  No premise on enc. *)
Lemma enc_coalition_trace_E (C : {set 'I_8}) :
  enc_coalition_trace C
  = coalition_view (@pgg_rho pgl27_M) (fdist_uniform card_bool) pgl27_G_pos
      enc C.
Proof.
apply: boolp.funext => u; apply/ffunP => i.
rewrite /enc_coalition_trace /coalition_view !ffunE.
case: ifP => // _.
by rewrite (enc_player_trace_E i).
Qed.

(* At enc = orbit_encode the two definitions are the source ones on the nose,
   so the generic file supersedes rather than duplicates pgl27_trace.v. *)

(* Deck validity is needed only from here on: privacy at three positions. *)
Lemma enc_coalition_trace_secrecy (C : {set 'I_8}) :
  (forall s, uniq (enc s)) -> (#|C| <= 3)%N ->
  `H( dealt_secret (G := pgg_G pgl27_M) (fdist_uniform card_bool) pgl27_G_pos
      | enc_coalition_trace C )
  = `H `p_ (dealt_secret (G := pgg_G pgl27_M) (fdist_uniform card_bool)
              pgl27_G_pos).
Proof.
move=> Huniq HC.
apply: (trace_secrecy_of_view
          (view := coalition_view (@pgg_rho pgl27_M) (fdist_uniform card_bool)
                     pgl27_G_pos enc C)
          (trace_of := id) (view_of := id)).
- by rewrite enc_coalition_trace_E.
- by [].
- exact: (@ttrans_view_indep_gen (pgg_N' pgl27_M) (pgg_gT pgl27_M)
           (pgg_G pgl27_M) (@pgg_rho pgl27_M) 3 pgl27_3transitive R
           (fdist_uniform card_bool) pgl27_G_pos enc C HC Huniq).
Qed.

End q4_trace_enc.

(* The r7 specialisation is the source statement. *)
Lemma q4_r7_player (R : realType) (i : 'I_8) :
  enc_player_trace R orbit_encode i
  = (fun u => tnth (orbit_encode u.1) (@pgg_rho pgl27_M u.2 i)).
Proof. exact: enc_player_trace_E. Qed.

Lemma q4_r7_agrees_with_source (R : realType) (i : 'I_8) :
  enc_player_trace R orbit_encode i = pgl27_player_trace R i.
Proof. by rewrite enc_player_trace_E pgl27_player_trace_E. Qed.

Print Assumptions enc_player_trace_E.
Print Assumptions enc_coalition_trace_E.
Print Assumptions enc_coalition_trace_secrecy.
