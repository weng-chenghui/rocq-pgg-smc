(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5x5 executed-trace secrecy (product instance of the executed-trace        *)
(* bridge). Two independent additive 5-of-5 piles are dealt over a product     *)
(* sampler P1 `x P2 with the identity cut; one player holds a single 'Z_5      *)
(* share of one pile, embedded into the run's 'I_10 dealt-value type. That     *)
(* player's executed trace, projected to its pile share, is fed through        *)
(* trace_secrecy_of_view with the embed/proj codec to obtain single-player     *)
(* trace secrecy against the joint product secret.                             *)
(******************************************************************************)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg boolp reals zmodp matrix.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
Require Import pgg_interface.
From pgg_smc Require Import pgg_s5x5 s5x5_profile rigidity_s5x5_instance.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment pgg_run.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_reconstruct Require Import covering_scheme pgg_sharing_framework product_threshold.
From pgg_smc Require Import pgg_leakage_witness pgg_randomized_sharing.
From pgg_smc Require Import pgg_canonical_sharing pgg_sharing_mechanism.
From pgg_smc Require Import pgg_leakage_product pgg_trace_secrecy.
From pgg_smc Require Import s5x5_run s5x5_secrecy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

(** embed_p1 — the codec embedding of a pile-1 share into the run's dealt
    value: 'Z_5 share s becomes the 'I_10 value at the same index, s < 5. It
    is the encoding half of the pile-1 leg of the trace-secrecy codec,
    inverted on the left by proj_pile (cancel_p1). *)
Definition embed_p1 (s : 'Z_5) : 'I_10 := inord (val s).

(** embed_p2 — the codec embedding of a pile-2 share into the run's dealt
    value: 'Z_5 share s becomes the 'I_10 value s + 5, landing in the upper
    five positions. It is the encoding half of the pile-2 leg of the
    trace-secrecy codec, inverted on the left by proj_pile (cancel_p2). *)
Definition embed_p2 (s : 'Z_5) : 'I_10 := inord (5 + val s).

(** proj_pile — the codec's single decoding map: recover a pile share from an
    'I_10 dealt value by reducing mod five. The same map decodes both piles,
    so it is the [view_of] argument trace_secrecy_of_view needs to run once
    per player regardless of which half of the ten-position layout that
    player's dealt value came from. *)
Definition proj_pile (c : 'I_10) : 'Z_5 := inord (val c %% 5).

(** cancel_p1 — proj_pile is a left inverse of embed_p1: decoding recovers the
    pile-1 share that was embedded. This is the codec-inversion premise
    trace_secrecy_of_view requires to bound pile-1 players' trace leakage. *)
Lemma cancel_p1 : cancel embed_p1 proj_pile.
Proof.
move=> s; rewrite /proj_pile.
have Hs5 : (val s < 5)%N by exact: ltn_ord.
have Hs10 : (val s < 10)%N by apply: (ltn_trans Hs5).
rewrite (_ : \val (embed_p1 s) = \val s); last exact: (inordK Hs10).
by rewrite modn_small // inord_val.
Qed.

(** cancel_p2 — proj_pile is a left inverse of embed_p2: decoding recovers the
    pile-2 share that was embedded. This is the codec-inversion premise
    trace_secrecy_of_view requires to bound pile-2 players' trace leakage. *)
Lemma cancel_p2 : cancel embed_p2 proj_pile.
Proof.
move=> s; rewrite /proj_pile.
have Hs5 : (val s < 5)%N by exact: ltn_ord.
have Hs10 : (5 + val s < 10)%N by rewrite -[10]/(5+5) ltn_add2l.
rewrite (_ : \val (embed_p2 s) = 5 + \val s); last exact: (inordK Hs10).
by rewrite modnDl modn_small // inord_val.
Qed.

(** content_of — the informative coordinate of a player's executed trace: the
    head of the first dealt hand, defaulting to ord0 on an empty trace. This
    turns the trace, a sequence over the non-finite [pgg_data N.+1], into the
    finType-valued content random variable the entropy bound is stated over. *)
Definition content_of (N : nat) (tr : seq (pgg_data N.+1)) : 'I_N.+1 :=
  if tr is _ :: PGG_hand (x :: _) :: _ then x else ord0.

(** s5x5_rho1_index — at the identity cut and the canonical ord_tuple starting
    layout, the group-action readout at index i returns i unchanged. Every
    per-player content lemma below (s5x5_abs_p0 .. s5x5_abs_p9) rewrites
    through this identity before vm_compute closes the run skeleton. *)
Lemma s5x5_rho1_index (i : 'I_10) : @pgg_rho s5x5_M 1%g (tnth (pi_starts s5x5_PI) i) = i.
Proof. by rewrite morph1 perm1 tnth_ord_tuple. Qed.

Section abstract_leaf.
Variable g : 'I_10 -> 'I_10.

(** s5x5_aprocs_abs — the twelve session-typed processes of one S_5 x S_5 run:
    a dealer (content readout g, identity cut, empty input prologue), a
    verifier, and the ten players. The content function g is left abstract so
    vm_compute reduces the run skeleton without unfolding the dealt share
    value, which is what lets the per-player content lemmas below close by
    plain computation. *)
Definition s5x5_aprocs_abs :=
  erase_aprocs
  [:: mk_aproc (dealer_with_input_encoding s5x5_PI
                  (fun _ => g) [:: (1%g : pgg_gT s5x5_M)] [::] s5x5_players 0)
    , mk_aproc (exchange_verifier s5x5_PI s5x5_players)
    & player_aprocs s5x5_PI s5x5_players].

(* The ten player traces are stated per concrete player index so that both the
   process-list ordinal and the readout index share the canonical isT proof,
   which lets vm_compute close each case by reflexivity (a symbolic ordinal
   proof would leave a dead tnth_default branch mismatch). *)
(** s5x5_abs_p0 — player 0's executed-trace content is the readout g at index 0. *)
Lemma s5x5_abs_p0 :
  content_of (nth [::] (run_interp 300 s5x5_aprocs_abs).2 (2 + 0)) = g (@Ordinal 10 0 isT).
Proof. rewrite /s5x5_aprocs_abs -[in RHS](s5x5_rho1_index (@Ordinal 10 0 isT)); vm_compute; reflexivity. Qed.

(** s5x5_abs_p1 — player 1's executed-trace content is the readout g at index 1. *)
Lemma s5x5_abs_p1 :
  content_of (nth [::] (run_interp 300 s5x5_aprocs_abs).2 (2 + 1)) = g (@Ordinal 10 1 isT).
Proof. rewrite /s5x5_aprocs_abs -[in RHS](s5x5_rho1_index (@Ordinal 10 1 isT)); vm_compute; reflexivity. Qed.

(** s5x5_abs_p2 — player 2's executed-trace content is the readout g at index 2. *)
Lemma s5x5_abs_p2 :
  content_of (nth [::] (run_interp 300 s5x5_aprocs_abs).2 (2 + 2)) = g (@Ordinal 10 2 isT).
Proof. rewrite /s5x5_aprocs_abs -[in RHS](s5x5_rho1_index (@Ordinal 10 2 isT)); vm_compute; reflexivity. Qed.

(** s5x5_abs_p3 — player 3's executed-trace content is the readout g at index 3. *)
Lemma s5x5_abs_p3 :
  content_of (nth [::] (run_interp 300 s5x5_aprocs_abs).2 (2 + 3)) = g (@Ordinal 10 3 isT).
Proof. rewrite /s5x5_aprocs_abs -[in RHS](s5x5_rho1_index (@Ordinal 10 3 isT)); vm_compute; reflexivity. Qed.

(** s5x5_abs_p4 — player 4's executed-trace content is the readout g at index 4. *)
Lemma s5x5_abs_p4 :
  content_of (nth [::] (run_interp 300 s5x5_aprocs_abs).2 (2 + 4)) = g (@Ordinal 10 4 isT).
Proof. rewrite /s5x5_aprocs_abs -[in RHS](s5x5_rho1_index (@Ordinal 10 4 isT)); vm_compute; reflexivity. Qed.

(** s5x5_abs_p5 — player 5's executed-trace content is the readout g at index 5. *)
Lemma s5x5_abs_p5 :
  content_of (nth [::] (run_interp 300 s5x5_aprocs_abs).2 (2 + 5)) = g (@Ordinal 10 5 isT).
Proof. rewrite /s5x5_aprocs_abs -[in RHS](s5x5_rho1_index (@Ordinal 10 5 isT)); vm_compute; reflexivity. Qed.

(** s5x5_abs_p6 — player 6's executed-trace content is the readout g at index 6. *)
Lemma s5x5_abs_p6 :
  content_of (nth [::] (run_interp 300 s5x5_aprocs_abs).2 (2 + 6)) = g (@Ordinal 10 6 isT).
Proof. rewrite /s5x5_aprocs_abs -[in RHS](s5x5_rho1_index (@Ordinal 10 6 isT)); vm_compute; reflexivity. Qed.

(** s5x5_abs_p7 — player 7's executed-trace content is the readout g at index 7. *)
Lemma s5x5_abs_p7 :
  content_of (nth [::] (run_interp 300 s5x5_aprocs_abs).2 (2 + 7)) = g (@Ordinal 10 7 isT).
Proof. rewrite /s5x5_aprocs_abs -[in RHS](s5x5_rho1_index (@Ordinal 10 7 isT)); vm_compute; reflexivity. Qed.

(** s5x5_abs_p8 — player 8's executed-trace content is the readout g at index 8. *)
Lemma s5x5_abs_p8 :
  content_of (nth [::] (run_interp 300 s5x5_aprocs_abs).2 (2 + 8)) = g (@Ordinal 10 8 isT).
Proof. rewrite /s5x5_aprocs_abs -[in RHS](s5x5_rho1_index (@Ordinal 10 8 isT)); vm_compute; reflexivity. Qed.

(** s5x5_abs_p9 — player 9's executed-trace content is the readout g at index 9. *)
Lemma s5x5_abs_p9 :
  content_of (nth [::] (run_interp 300 s5x5_aprocs_abs).2 (2 + 9)) = g (@Ordinal 10 9 isT).
Proof. rewrite /s5x5_aprocs_abs -[in RHS](s5x5_rho1_index (@Ordinal 10 9 isT)); vm_compute; reflexivity. Qed.

End abstract_leaf.

Section s5x5_trace_sec.
Variable R : realType.

(** rs1 — the concrete uniform iid 5-of-5 additive sharing scheme instantiated
    for pile 1. *)
Definition rs1 := @unif_randomized_sharing R 3 4.

(** rs2 — the concrete uniform iid 5-of-5 additive sharing scheme instantiated
    for pile 2. *)
Definition rs2 := @unif_randomized_sharing R 3 4.

(** s5x5_rlayout — the dealt layout at product tape uv: position i < 5 carries
    embed_p1 of pile-1 share i, position i >= 5 carries embed_p2 of pile-2
    share i - 5. This is the ten-position dealt-value tuple s5x5_rprocs feeds
    into the run. *)
Definition s5x5_rlayout (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type) : 10.-tuple 'I_10 :=
  [tuple if (i < 5)%N then embed_p1 (rsh_share rs1 (inord i) uv.1)
         else embed_p2 (rsh_share rs2 (inord (i - 5)) uv.2) | i < 10].

(** Pone — the uniform iid sampler distribution over one 'rV['Z_5]_5 pile tape,
    the fdist underlying one pile's share random variables. *)
Let Pone : R.-fdist 'rV['Z_5]_5 :=
  fdist_uniform (pgg_canonical_sharing.card_ZN_subproof 3) `^ 5.

(** Pprod — the product sampler distribution over the two independent pile
    tapes, Pone `x Pone. Every random variable in this section, the joint
    secret and every player's executed trace, is a random variable over
    Pprod. *)
Definition Pprod : R.-fdist ('rV['Z_5]_5 * 'rV['Z_5]_5)%type := Pone `x Pone.

(** s5x5_rprocs — the randomized S_5 x S_5 run at product tape uv: the
    abstract run skeleton s5x5_aprocs_abs fed the tape-dependent embedded
    share-tuple readout, identity cut. *)
Definition s5x5_rprocs (uv : ('rV['Z_5]_5 * 'rV['Z_5]_5)%type) :=
  s5x5_aprocs_abs (tnth (s5x5_rlayout uv)).

(** s5x5_player_trace — player j's executed-trace content, lifted over the
    product sampler tape via the run_interp projection at process index 2+j.
    This is the single-player content random variable s5x5_trace_secrecy
    bounds the leakage of. *)
Definition s5x5_player_trace (j : 'I_10) : {RV Pprod -> 'I_10} :=
  fun uv => content_of (nth [::] (run_interp 300 (s5x5_rprocs uv)).2 (2 + j)).

(** s5x5_player_trace_layout — the lifted player trace equals the dealt
    layout entry at player j: content_of factors through s5x5_rlayout
    regardless of which pile j sits in. The per-pile specializations below,
    s5x5_player_trace_p1_E and s5x5_player_trace_p2_E, read off embed_p1 or
    embed_p2 from this single equality. *)
Lemma s5x5_player_trace_layout (j : 'I_10) :
  s5x5_player_trace j = (fun uv => tnth (s5x5_rlayout uv) j).
Proof.
apply: boolp.funext => uv; rewrite /s5x5_player_trace /s5x5_rprocs.
case: j => -[|[|[|[|[|[|[|[|[|[|//]]]]]]]]]] Hj.
- rewrite (s5x5_abs_p0 (tnth (s5x5_rlayout uv))); congr (tnth _ _); exact: val_inj.
- rewrite (s5x5_abs_p1 (tnth (s5x5_rlayout uv))); congr (tnth _ _); exact: val_inj.
- rewrite (s5x5_abs_p2 (tnth (s5x5_rlayout uv))); congr (tnth _ _); exact: val_inj.
- rewrite (s5x5_abs_p3 (tnth (s5x5_rlayout uv))); congr (tnth _ _); exact: val_inj.
- rewrite (s5x5_abs_p4 (tnth (s5x5_rlayout uv))); congr (tnth _ _); exact: val_inj.
- rewrite (s5x5_abs_p5 (tnth (s5x5_rlayout uv))); congr (tnth _ _); exact: val_inj.
- rewrite (s5x5_abs_p6 (tnth (s5x5_rlayout uv))); congr (tnth _ _); exact: val_inj.
- rewrite (s5x5_abs_p7 (tnth (s5x5_rlayout uv))); congr (tnth _ _); exact: val_inj.
- rewrite (s5x5_abs_p8 (tnth (s5x5_rlayout uv))); congr (tnth _ _); exact: val_inj.
- rewrite (s5x5_abs_p9 (tnth (s5x5_rlayout uv))); congr (tnth _ _); exact: val_inj.
Qed.

(** s5x5_player_trace_p1_E — for a lower-half player j (val j < 5) the lifted
    trace is embed_p1 composed with that player's pile-1 share. This supplies
    the [view] equality trace_secrecy_of_view needs to bound pile-1 players'
    trace leakage in s5x5_trace_secrecy. *)
Lemma s5x5_player_trace_p1_E (j : 'I_10) (Hj : (val j < 5)%N) :
  s5x5_player_trace j = embed_p1 `o (fun uv => rsh_share rs1 (inord (val j) : 'I_5) uv.1).
Proof.
rewrite s5x5_player_trace_layout; apply: boolp.funext => uv.
by rewrite tnth_mktuple Hj /comp_RV /=.
Qed.

(** s5x5_player_trace_p2_E — for an upper-half player j (~~ (val j < 5)) the
    lifted trace is embed_p2 composed with that player's pile-2 share. This
    supplies the [view] equality trace_secrecy_of_view needs to bound pile-2
    players' trace leakage in s5x5_trace_secrecy. *)
Lemma s5x5_player_trace_p2_E (j : 'I_10) (Hj : ~~ (val j < 5)%N) :
  s5x5_player_trace j = embed_p2 `o (fun uv => rsh_share rs2 (inord (val j - 5) : 'I_5) uv.2).
Proof.
rewrite s5x5_player_trace_layout; apply: boolp.funext => uv.
by rewrite tnth_mktuple (negbTE Hj) /comp_RV /=.
Qed.

(** JointSecret — the joint product secret: the pair of the two piles'
    secrets, as a random variable over the product tape Pprod. This is the
    secret s5x5_trace_secrecy shows a single corrupted player's trace leaves
    at full entropy. *)
Definition JointSecret : {RV Pprod -> ('Z_5 * 'Z_5)%type} :=
  fun uv => (rsh_secret rs1 uv.1, rsh_secret rs2 uv.2).

(** s5x5_share_indep_p1 — a single pile-1 share is independent of the joint
    product secret, so the product coalition's view reduces to one first-pile
    share. This is the independence premise trace_secrecy_of_view needs for
    pile-1 players in s5x5_trace_secrecy, obtained from the product leakage
    witness leakage_product so the two piles' independence proofs stay
    separate. *)
Lemma s5x5_share_indep_p1 (j' : 'I_5) :
  Pprod |= (fun uv => rsh_share rs1 j' uv.1) _|_ JointSecret.
Proof.
have HC1 : (#|[set j']| < 5)%N by rewrite cards1.
have HC2 : (#|[set (ord0 : 'I_5)]| < 5)%N by rewrite cards1.
pose lw := leakage_product (additive_leakage rs1 HC1) (additive_leakage rs2 HC2).
pose f := (fun vv : lw_viewT lw => vv.1 j').
have Hshare : (fun uv => rsh_share rs1 j' uv.1) = f `o lw_view lw.
  apply: boolp.funext => uv; rewrite /comp_RV /f /=.
  by rewrite /rsh_view ffunE in_set1 eqxx.
have Hsec : JointSecret = lw_secret lw by [].
rewrite Hshare Hsec.
apply: inde_RV_comp; exact: lw_indep lw.
Qed.

(** s5x5_share_indep_p2 — a single pile-2 share is independent of the joint
    product secret, so the product coalition's view reduces to one
    second-pile share. This is the independence premise trace_secrecy_of_view
    needs for pile-2 players in s5x5_trace_secrecy, obtained the same way as
    s5x5_share_indep_p1 with the piles' roles in leakage_product swapped. *)
Lemma s5x5_share_indep_p2 (j' : 'I_5) :
  Pprod |= (fun uv => rsh_share rs2 j' uv.2) _|_ JointSecret.
Proof.
have HC1 : (#|[set (ord0 : 'I_5)]| < 5)%N by rewrite cards1.
have HC2 : (#|[set j']| < 5)%N by rewrite cards1.
pose lw := leakage_product (additive_leakage rs1 HC1) (additive_leakage rs2 HC2).
pose f := (fun vv : lw_viewT lw => vv.2 j').
have Hshare : (fun uv => rsh_share rs2 j' uv.2) = f `o lw_view lw.
  apply: boolp.funext => uv; rewrite /comp_RV /f /=.
  by rewrite /rsh_view ffunE in_set1 eqxx.
have Hsec : JointSecret = lw_secret lw by [].
rewrite Hshare Hsec.
apply: inde_RV_comp; exact: lw_indep lw.
Qed.

(** s5x5_trace_secrecy — a single corrupted player's executed S_5 x S_5 trace
    leaves the joint product secret ('Z_5 * 'Z_5, one component per pile) at
    full conditional entropy: `H( JointSecret | s5x5_player_trace j ) equals
    `H `p_ JointSecret for every player j, in either pile. The bound is
    unconditional; no cryptographic hardness assumption enters it. It is
    obtained by instantiating trace_secrecy_of_view once per pile, with
    embed_p1/proj_pile (resp. embed_p2/proj_pile) as the codec and
    s5x5_share_indep_p1 (resp. s5x5_share_indep_p2) as the independence
    premise, so it is the two-pile analogue of the single-pile S_5 instance's
    executed-trace secrecy bound. *)
Lemma s5x5_trace_secrecy (j : 'I_10) :
  `H( JointSecret | s5x5_player_trace j ) = `H `p_ JointSecret.
Proof.
case: (ltnP (val j) 5) => Hj.
- apply: (trace_secrecy_of_view (view := (fun uv => rsh_share rs1 (inord (val j) : 'I_5) uv.1))
            (trace_of := embed_p1) (view_of := proj_pile)).
  + exact: s5x5_player_trace_p1_E j Hj.
  + exact: cancel_p1.
  + exact: s5x5_share_indep_p1.
- have Hj5 : ~~ (val j < 5)%N by rewrite -leqNgt.
  apply: (trace_secrecy_of_view (view := (fun uv => rsh_share rs2 (inord (val j - 5) : 'I_5) uv.2))
            (trace_of := embed_p2) (view_of := proj_pile)).
  + exact: s5x5_player_trace_p2_E j Hj5.
  + exact: cancel_p2.
  + exact: s5x5_share_indep_p2.
Qed.

End s5x5_trace_sec.
