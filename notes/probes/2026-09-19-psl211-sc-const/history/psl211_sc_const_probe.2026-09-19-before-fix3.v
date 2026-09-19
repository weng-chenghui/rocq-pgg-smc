(* Probe, 2026-09-19. Not a production file.                                 *)
(*****************************************************************************)
(* psl211_sc_const_probe: the spectral certificate's constancy field at the  *)
(*                        twelve-card chirality instance, under the all-decks*)
(*                        run parameters and the group-uniform ideal cut     *)
(*                                                                           *)
(* The SpectralCert record of manifest/pgg_tableau.v carries a field sc_const*)
(* asking that a coalition below the privacy threshold read the ideal cut the*)
(* same way whatever the run argument. This file restates that field as a    *)
(* standalone proposition, checks the restatement against the record, and    *)
(* decides it at PSL(2,11) under the all-decks parameters, the ideal taken   *)
(* to be the uniform law on the shuffle group: it is false, at every real    *)
(* field, and the three seats 0, 1 and 2 at the deck description             *)
(* psl211_perdeck_deal witness it.                                           *)
(*                                                                           *)
(* Under the all-decks parameters the run argument is a whole deck           *)
(* description, whose first coordinate is the chirality and whose other three*)
(* are public, so the field asks for constancy of the reading in the block   *)
(* line and in the two labellings as well as in the chirality. It already    *)
(* fails between two deck descriptions of one chirality, so its failure does *)
(* not need the secret to move. A change of secret is always also a change of*)
(* the laid deck here, the chirality selecting the table the block line      *)
(* indexes. What three seats read about the chirality under the all-decks law*)
(* is psl211_alldecks_static_indep, which says they read nothing, and this   *)
(* refutation of the field states no leakage.                                *)
(*                                                                           *)
(* The counting bridges are those of instances/psl211/psl211_models.v.       *)
(* What is added here is the discharge of the threshold premise for those    *)
(* three seats, the transport of the framework's seat reader to the          *)
(* instance's, and a second count, at a reading and a deck description that  *)
(* file does not name.                                                       *)
(*****************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba.
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

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Import Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(** seatT — a seat of the instance's starting interface, the index a coalition
    is a set of. *)
Local Notation seatT :=
  ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1).

(** cardT — a card of the twelve-card deck, the value a seat reads. *)
Local Notation cardT :=
  ('I_(pgg_N' (mp_M (instance_profile psl211_algebra))).+1).

(** cutT — a cut, an element of the ambient permutation group the shuffle
    group sits inside. *)
Local Notation cutT := (pgg_gT psl211_M).

(** viewT — a reading, the card a coalition's seats see at each seat. *)
Local Notation viewT := ({ffun seatT -> cardT}).

(*****************************************************************************)
(*     The constancy field as a standalone proposition                       *)
(*****************************************************************************)

(** sc_const_prop E ideal — a coalition of fewer than profile_k seats reads
    the law ideal on cuts the same way whatever the run argument. This is
    what a spectral certificate asserts about its idealized cut, and the
    certificate's variation-distance field is what transfers that assertion
    from the ideal to the real cut. The run argument carries the secret, so
    the field is at least constancy in the secret; where the run argument
    carries public data as well, as it does under the all-decks parameters,
    the field asks for constancy in that public data too and is stronger
    than the privacy the instance claims. *)
Definition sc_const_prop (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A)
    (ideal : R.-fdist (pgg_gT (mp_M (instance_profile A)))) : Prop :=
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    forall x x' : ex_inputT E,
      fdistmap (@static_coalition_obs A E C x) ideal
      = fdistmap (@static_coalition_obs A E C x') ideal.

(** sc_const_prop_field — sc_const_prop is the fifth field of
    SpectralCert read at the certificate's own ideal, so refuting the
    proposition at a law refutes every certificate whose ideal cut is
    that law. *)
Lemma sc_const_prop_field (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : SpectralCert sa) : sc_const_prop E (sc_ideal cert).
Proof. exact: sc_const cert. Qed.

(*****************************************************************************)
(*     The three seats are below the privacy threshold                       *)
(*****************************************************************************)

(** psl211_perdeck_coalition_le3 — the coalition witnessing the refutation
    has at most three seats, so it is one of the coalitions the instance's
    privacy claim covers and not an oversized one. *)
(* The bound is read off a three-point superset and never off an enumeration
   of the twelve seats, the ordinal enumeration going through an opaque
   decision that does not reduce. *)
Lemma psl211_perdeck_coalition_le3 : (#|psl211_perdeck_coalition| <= 3)%N.
Proof.
have Hsub : psl211_perdeck_coalition \subset
    ((psl211_code12 0 : seatT) |: ((psl211_code12 1 : seatT) |:
       [set (psl211_code12 2 : seatT)])).
  apply/subsetP => i.
  rewrite /psl211_perdeck_coalition in_set !inE -!val_eqE.
  by case: i => [] [|[|[|k]]] Hk.
apply: leq_trans (subset_leq_card Hsub) _.
rewrite cardsU1 cardsU1 cards1.
by case: (_ \notin _); case: (_ \notin _).
Qed.

(** psl211_perdeck_coalition_below_k — those three seats meet the threshold
    premise of both security arms, the derived profile declaring six. A
    refutation of a field quantified over coalitions below the threshold has
    to discharge this premise, and it is the only nontrivial premise the
    counterexample owes. *)
Lemma psl211_perdeck_coalition_below_k :
  (#|psl211_perdeck_coalition| < profile_k (instance_profile psl211_algebra))%N.
Proof. by apply: leq_ltn_trans psl211_perdeck_coalition_le3 _. Qed.

(*****************************************************************************)
(*     The constancy field fails at the group-uniform ideal                  *)
(*****************************************************************************)

(** psl211_alldecks_sc_const_false — under the all-decks run parameters
    the uniform law on the shuffle group is the ideal cut of no spectral
    certificate: seats 0, 1 and 2 read that law differently at the two
    chiralities of the deck description psl211_perdeck_deal. The run
    argument of this mode is a whole deck description, whose first
    coordinate is the chirality and whose other three are public, and
    the field quantifies over every pair of them, so it fails at a pair
    of one chirality too, psl211_samechir_law_neq. A change of secret is
    always also a change of the laid deck here, the chirality selecting
    the table the block line indexes. Three seats learn nothing about
    the chirality under the all-decks law, which is
    psl211_alldecks_static_indep, and this refutation states no
    leakage. *)
(* psl211_samechir_law_neq refutes the field's own equation at one pair of
   run arguments of chirality true, at the reading that gives cards 3, 2 and
   4 to the three seats. How wide that failure is remains measured and not
   proved: at chirality true the L1 gap of the two reading multiplicity
   vectors is 600 of 660 cuts between block line 0 and block line 1, against
   360 of 660 between the two chiralities at block line 0. Those numbers are
   a vm_compute diagnostic of audit-soundness/audit_diag.v, recorded in
   audit-soundness/audit_diag.log.txt, and not Rocq theorems. *)
Lemma psl211_alldecks_sc_const_false (R : realType) :
  ~ sc_const_prop psl211_alldecks_params
      ((`U psl211_G_pos) : R.-fdist cutT).
Proof.
move=> Hconst.
have Heq := Hconst psl211_perdeck_coalition psl211_perdeck_coalition_below_k
  (true, psl211_perdeck_deal) (false, psl211_perdeck_deal).
(* the reader is moved by one congr1 under fdistmap and never by a rewrite:
   the two sides differ only in the chirality bool, and a rewrite there has to
   search a goal holding both deck tables *)
have Et : @static_coalition_obs psl211_algebra psl211_alldecks_params
     psl211_perdeck_coalition (true, psl211_perdeck_deal)
   = (fun g => psl211_alldecks_view psl211_perdeck_coalition
        (true, psl211_perdeck_deal) g)
  := psl211_alldecks_static_obs_funE _ _.
have Ef : @static_coalition_obs psl211_algebra psl211_alldecks_params
     psl211_perdeck_coalition (false, psl211_perdeck_deal)
   = (fun g => psl211_alldecks_view psl211_perdeck_coalition
        (false, psl211_perdeck_deal) g)
  := psl211_alldecks_static_obs_funE _ _.
move/negP: (psl211_perdeck_law_neq R); apply; apply/eqP.
exact: (etrans
  (esym (congr1 (fun f => fdistmap f ((`U psl211_G_pos) : R.-fdist cutT)) Et))
  (etrans Heq
    (congr1 (fun f => fdistmap f ((`U psl211_G_pos) : R.-fdist cutT)) Ef))).
Qed.

(*****************************************************************************)
(*     The mutation: the empty coalition reads every ideal constantly        *)
(*****************************************************************************)

(** psl211_alldecks_static_obs_set0 — a coalition with no seats reads every
    cut as the constant map to card zero. The framework's reader returns card
    zero outside the coalition, so at the empty coalition it carries no deck
    information at all. *)
Lemma psl211_alldecks_static_obs_set0 (x : ex_inputT psl211_alldecks_params) :
  @static_coalition_obs psl211_algebra psl211_alldecks_params set0 x
  = (fun _ : cutT => [ffun _ : seatT => (ord0 : cardT)]).
Proof.
apply: boolp.funext => g; apply/ffunP => i.
by rewrite psl211_alldecks_static_obsE in_set0 ffunE.
Qed.

(** psl211_alldecks_sc_const_set0 — at the empty coalition the constancy
    statement holds, for every law on cuts. A refutation of the field at
    these parameters therefore has to spend a nonempty coalition: the field
    is not false for the trivial reason that its quantifier over coalitions
    admits a reading no law can make constant. *)
Lemma psl211_alldecks_sc_const_set0 (R : realType)
    (ideal : R.-fdist cutT) (x x' : ex_inputT psl211_alldecks_params) :
  fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params set0 x)
    ideal
  = fdistmap
      (@static_coalition_obs psl211_algebra psl211_alldecks_params set0 x')
      ideal.
Proof.
by rewrite (psl211_alldecks_static_obs_set0 x)
  (psl211_alldecks_static_obs_set0 x').
Qed.

(*****************************************************************************)
(*     Two deck descriptions of one chirality                                *)
(*****************************************************************************)

(** psl211_samechir_deal — block line one, both labellings the identity. It
    differs from psl211_perdeck_deal in the block line alone, a public
    coordinate of the run argument that carries no secret. *)
Definition psl211_samechir_deal : psl211_deal :=
  (@Ordinal 132 1 isT, 1%g, 1%g).

(** psl211_samechir_view — the reading that gives cards 3, 2 and 4 to
    seats 0, 1 and 2, and card 0 to every seat outside the coalition. The
    deck laid at (true, psl211_perdeck_deal) reaches it under exactly one
    cut and the deck laid at (true, psl211_samechir_deal) under none. *)
(* Measured once and not proved: at the deck description
   (true, psl211_perdeck_deal) the 660 cuts give these three seats 660
   distinct readings. That is a vm_compute diagnostic of
   audit-soundness/audit_diag.v, line 62, recorded in
   audit-soundness/audit_diag.log.txt, and not a Rocq theorem. *)
Definition psl211_samechir_view : viewT :=
  [ffun i => psl211_code12 (nth 0 [:: 3; 2; 4] (val i))].

(** psl211_samechir_test sq t — the coalition's reading of the deck sq under
    the cut whose table is t matches psl211_samechir_view, tested on raw
    codes. *)
Definition psl211_samechir_test (sq t : seq nat) : bool :=
  [&& nth 0 sq (nth 0 t 0) %% 12 == 3,
      nth 0 sq (nth 0 t 1) %% 12 == 2 &
      nth 0 sq (nth 0 t 2) %% 12 == 4].

(** psl211_samechir_testE — the raw test decides the reading, so the fiber
    over psl211_samechir_view is counted by a boolean on nat lists. *)
Lemma psl211_samechir_testE (sq t : seq nat) :
  (psl211_perdeck_raw_view sq t == psl211_samechir_view)
  = psl211_samechir_test sq t.
Proof.
rewrite /psl211_samechir_test; apply/idP/idP.
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

(** psl211_alldecks_raw_viewE — the raw reading is the framework's reading, at
    every deck description. This is psl211_perdeck_raw_viewE of
    psl211_models.v with the deck description left free instead of fixed to
    psl211_perdeck_deal. *)
Lemma psl211_alldecks_raw_viewE (x : psl211_inputT) (g : cutT) :
  psl211_perdeck_raw_view (psl211_alldecks_seq x) (psl211_ptbl g)
  = psl211_alldecks_view psl211_perdeck_coalition x g.
Proof.
apply/ffunP => i.
(* in_set and not inE: inE would rewrite the seq membership on the left
   instead of the set membership on the right *)
rewrite /psl211_perdeck_raw_view /psl211_alldecks_view !ffunE.
rewrite /psl211_perdeck_coalition in_set.
case Hi: (val i \in [:: 0; 1; 2]) => //.
rewrite /psl211_alldecks_layout tnth_mktuple.
by rewrite psl211_perdeck_ptbl_nth.
Qed.

(** psl211_samechir_seq — the deck psl211_samechir_deal names at chirality
    true, as raw codes by position. *)
Definition psl211_samechir_seq : seq nat :=
  let H := psl211_alldecks_row (true, psl211_samechir_deal) in
  let K := psl211_alldecks_corow (true, psl211_samechir_deal) in
  [seq (if p \in H then index p H else 6 + index p K) | p <- iota 0 12].

(** psl211_samechir_row_size — block one of the chirality's table has six
    positions. *)
Lemma psl211_samechir_row_size :
  size (psl211_alldecks_row (true, psl211_samechir_deal)) = 6.
Proof. by vm_compute. Qed.

(** psl211_samechir_corow_size — its complement has the other six. *)
Lemma psl211_samechir_corow_size :
  size (psl211_alldecks_corow (true, psl211_samechir_deal)) = 6.
Proof. by vm_compute. Qed.

(** psl211_samechir_seqE — that raw list is the deck the all-decks dealer lays
    for this deck description. *)
Lemma psl211_samechir_seqE :
  psl211_alldecks_seq (true, psl211_samechir_deal) = psl211_samechir_seq.
Proof.
have Hrow := psl211_samechir_row_size.
have Hcorow := psl211_samechir_corow_size.
rewrite /psl211_samechir_deal in Hrow Hcorow.
rewrite /psl211_alldecks_seq /psl211_samechir_seq /psl211_samechir_deal.
apply/eq_in_map => p Hp.
case: ifP => Hin.
  rewrite perm1; apply: inordK.
  by rewrite -[X in (_ < X)%N]Hrow index_mem Hin.
rewrite perm1; apply/eqP; rewrite eqn_add2l; apply/eqP.
apply: inordK.
rewrite -[X in (_ < X)%N]Hcorow index_mem /psl211_alldecks_corow mem_filter.
by rewrite Hin Hp.
Qed.

(** psl211_samechir_raw_count sq — how many of the 660 cuts carry the deck sq
    to psl211_samechir_view. *)
Definition psl211_samechir_raw_count (sq : seq nat) : nat :=
  count (psl211_samechir_test sq) (unzip1 psl211_elem_table).

(** psl211_samechir_raw_countE — that count is one at the deck of
    psl211_perdeck_deal and zero at the deck of psl211_samechir_deal, both at
    chirality true. The two run arguments carry the same secret. *)
Lemma psl211_samechir_raw_countE :
  psl211_samechir_raw_count (psl211_perdeck_seq true) = 1 /\
  psl211_samechir_raw_count psl211_samechir_seq = 0.
Proof. by split; vm_compute. Qed.

(* Past this point no proof needs the body of the laid deck, of the closure
   table or of the count, and every step naming two deck descriptions must not
   be left to a tactic that searches for a match. *)
Local Opaque psl211_alldecks_view psl211_elem_table.

(** psl211_samechir_fiber x — the cuts of the group carrying the deck of the
    deck description x to psl211_samechir_view. *)
Definition psl211_samechir_fiber (x : psl211_inputT) : {set cutT} :=
  [set g in pgg_G psl211_M |
     psl211_alldecks_view psl211_perdeck_coalition x g
       == psl211_samechir_view].

(** psl211_samechir_fiberE — that fiber has the raw count of the laid deck as
    its cardinality. *)
Lemma psl211_samechir_fiberE (x : psl211_inputT) :
  #|psl211_samechir_fiber x|
  = psl211_samechir_raw_count (psl211_alldecks_seq x).
Proof.
rewrite /psl211_samechir_fiber /psl211_samechir_raw_count.
transitivity
  (count (fun g => psl211_alldecks_view psl211_perdeck_coalition x g
      == psl211_samechir_view) (enum (pgg_G psl211_M))).
  rewrite cardE /enum_mem size_filter count_filter.
  by apply: eq_count => g; rewrite !inE andbC.
transitivity
  (count (psl211_samechir_test (psl211_alldecks_seq x))
    [seq psl211_ptbl g | g <- enum (pgg_G psl211_M)]).
  rewrite count_map; apply: eq_count => g.
  by rewrite -psl211_alldecks_raw_viewE psl211_samechir_testE.
rewrite -!size_filter; apply: perm_size.
exact: (perm_filter _ psl211_perdeck_ptbl_enum).
Qed.

(* psl211_samechir_raw_count is sealed for the rest of the file: nothing below
   needs its body and psl211_samechir_raw_countE supplies both values. *)
Local Opaque psl211_samechir_raw_count.

(** psl211_samechir_massE x — at the deck description x the law of what the
    coalition reads gives psl211_samechir_view the mass of its fiber of cuts
    over the order of the shuffle group. *)
Lemma psl211_samechir_massE (R : realType) (x : psl211_inputT) :
  (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition x g)
     ((`U psl211_G_pos) : R.-fdist cutT)) psl211_samechir_view
  = (#|pgg_G psl211_M|%:R)^-1 *+ #|psl211_samechir_fiber x| :> R.
Proof. by rewrite /psl211_samechir_fiber uniform_fdistmap_pointE. Qed.

(** psl211_samechir_law_neq — at chirality true the deck descriptions
    psl211_perdeck_deal and psl211_samechir_deal send the group-uniform
    cut law to two different laws on what seats 0, 1 and 2 read. This is
    the equation the constancy field asserts, at a pair of run arguments
    carrying the same secret, and it is false, so the field's failure at
    the all-decks parameters does not need the chirality to move: it is
    already a failure of constancy in the public block line. *)
Lemma psl211_samechir_law_neq (R : realType) :
  fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
      psl211_perdeck_coalition (true, psl211_perdeck_deal))
    ((`U psl211_G_pos) : R.-fdist cutT)
  != fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
      psl211_perdeck_coalition (true, psl211_samechir_deal))
    ((`U psl211_G_pos) : R.-fdist cutT).
Proof.
have [H1 H0] := psl211_samechir_raw_countE.
(* each cardinality and each mass is pinned in a goal naming one deck
   description only, and the two are brought together in term mode *)
have C1 : #|psl211_samechir_fiber (true, psl211_perdeck_deal)| = 1.
  rewrite psl211_samechir_fiberE (psl211_perdeck_seqE true); exact: H1.
have C0 : #|psl211_samechir_fiber (true, psl211_samechir_deal)| = 0.
  rewrite psl211_samechir_fiberE psl211_samechir_seqE; exact: H0.
have E1 : @static_coalition_obs psl211_algebra psl211_alldecks_params
     psl211_perdeck_coalition (true, psl211_perdeck_deal)
   = (fun g => psl211_alldecks_view psl211_perdeck_coalition
        (true, psl211_perdeck_deal) g)
  := psl211_alldecks_static_obs_funE _ _.
have E0 : @static_coalition_obs psl211_algebra psl211_alldecks_params
     psl211_perdeck_coalition (true, psl211_samechir_deal)
   = (fun g => psl211_alldecks_view psl211_perdeck_coalition
        (true, psl211_samechir_deal) g)
  := psl211_alldecks_static_obs_funE _ _.
have L1 : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
    (true, psl211_perdeck_deal) g) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_samechir_view = (#|pgg_G psl211_M|%:R)^-1 :> R.
  by rewrite psl211_samechir_massE C1 mulr1n.
have L0 : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
    (true, psl211_samechir_deal) g) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_samechir_view = 0 :> R.
  by rewrite psl211_samechir_massE C0 mulr0n.
apply/negP => /eqP Heq.
have Hv := etrans
  (esym (congr1 (fun f => fdistmap f ((`U psl211_G_pos) : R.-fdist cutT)) E1))
  (etrans Heq
    (congr1 (fun f => fdistmap f ((`U psl211_G_pos) : R.-fdist cutT)) E0)).
have Hz : (#|pgg_G psl211_M|%:R)^-1 = 0 :> R :=
  etrans (esym L1)
    (etrans (congr1 (fun q : R.-fdist viewT => q psl211_samechir_view) Hv) L0).
have : (#|pgg_G psl211_M|%:R)^-1 == 0 :> R by rewrite Hz.
rewrite invr_eq0 pnatr_eq0 => /eqP Hcard.
by move: psl211_G_pos; rewrite Hcard.
Qed.

Print Assumptions psl211_alldecks_sc_const_false.
Print Assumptions psl211_alldecks_sc_const_set0.
Print Assumptions sc_const_prop_field.
Print Assumptions psl211_samechir_law_neq.
