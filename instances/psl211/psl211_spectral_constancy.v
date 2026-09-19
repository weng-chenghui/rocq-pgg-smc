(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_spectral_constancy: the input-indistinguishability                  *)
(*                            certificate's constancy field at the            *)
(*                            twelve-card chirality instance, refuted in      *)
(*                            both run modes                                  *)
(*                                                                            *)
(* An input-indistinguishability certificate of manifest/pgg_tableau.v        *)
(* carries five fields, and the fifth, ic_const, asks that a coalition of     *)
(* fewer than profile_k seats read the certificate's ideal cut the same way   *)
(* whatever the run argument. This file restates that field as a standalone   *)
(* proposition, checks the restatement against the record, and refutes it at  *)
(* PSL(2,11) in the two run modes the instance carries. The instance          *)
(* publishes its all-decks row through the exact arm, and this file is what   *)
(* the input-indistinguishability arm would cost it.                          *)
(*                                                                            *)
(* All-decks mode. The run argument is a whole deck description: one of the   *)
(* two chiralities, one of the 132 block lines of that chirality's Steiner    *)
(* system, and two labellings. Only the chirality is secret, so the field     *)
(* asks for constancy of the reading in the other three coordinates as well.  *)
(* At the group-uniform ideal the field fails between the two chiralities of  *)
(* one deal, and the equation it asserts is false again at a pair of run      *)
(* arguments of one chirality differing in the block line alone,              *)
(* psl211_blockline1_law_neq. The second failure moves no secret, so the      *)
(* field asks for constancy in data outside the secret and not for secrecy    *)
(* alone. What a coalition of at most five of the twelve seats reads about    *)
(* the chirality under the all-decks law is psl211_alldecks_static_indep of   *)
(* instances/psl211/psl211_models.v, which says it reads nothing, exactly, at *)
(* every real field, and that is the theorem the published row carries.       *)
(*                                                                            *)
(* The quantitative form fixes what an input-indistinguishability row would   *)
(* have to publish. A certificate over the all-decks model states its         *)
(* distance against the group-uniform law, its identification field pinning   *)
(* its shuffle law to the adapter's cut, so no certificate carries a shuffle  *)
(* bound epsilon strictly below 1/1320. The obligation of conclude bounds the *)
(* published number below by cert_eps cert, which is that epsilon twice, so   *)
(* every row over this model that publishes its certificate's own number      *)
(* publishes at least 1/660. psl211_alldecks_no_zero_eps_cert states the same *)
(* at epsilon zero, which is the epsilon profile_eps_psl211 of                *)
(* instances/psl211/psl211_profile.v gives this instance's single-card        *)
(* marginal bound.                                                            *)
(*                                                                            *)
(* Dealt mode. The run argument is the chirality itself, so here the field    *)
(* is exactly constancy in the secret, and it still fails: three seats see a  *)
(* reading that one chirality's encoder deck reaches under exactly one cut    *)
(* and the other reaches under none. That is a fact about the group and the   *)
(* design. PSL(2,11) is 2-transitive and not 3-transitive, where PGL(2,7)     *)
(* proves the same field through pgl27_word_view_const of                     *)
(* instances/pgl27/pgl27_rows.v, three-transitivity read as constancy for     *)
(* coalitions of fewer than four seats. The dealt statement rules out one     *)
(* named ideal and no certificate, this tree carrying no dealt-mode sample    *)
(* adapter through which a certificate's ideal could be pinned to it.         *)
(*                                                                            *)
(* Not claimed. The input-indistinguishability arm is not shown unavailable   *)
(* at this instance. What is excluded is a range of epsilon, and the range of *)
(* larger epsilon is occupied: the uniform law on the whole of {perm 'I_12}   *)
(* reads the same at every deck description, its variation distance from `U   *)
(* psl211_G_pos is 2 * (1 - 660/12!), so a certificate at that ideal exists   *)
(* with an epsilon near 2. Its cert_eps is that epsilon twice, near 4, while  *)
(* infotheo's var_dist sums the absolute differences of two laws and so never *)
(* exceeds 2, and the row such a certificate gives publishes a number no pair *)
(* of laws can exceed and bounds nothing. That occupancy is argued and not    *)
(* compiled. Its premise is compiled: every deck description lays a deck of   *)
(* twelve distinct cards, psl211_alldecks_uniq of                             *)
(* instances/psl211/psl211_alldecks.v. What is not compiled there is the      *)
(* separate step that the parametrization enumerates the valid decks once     *)
(* each. Nothing here says the word row is excluded outright:                 *)
(* psl211_alldecks_constancy_false_word584 reaches eps < 1/1320 - 2^-40, and  *)
(* no weighted-word sample adapter exists for this instance. How wide each    *)
(* failure is stays measured and not proved; the reading multiplicity         *)
(* diagnostics are recorded in notes/probes/2026-09-19-psl211-sc-const/.      *)
(*                                                                            *)
(* Names. The first two declarations are framework-level: they are stated for *)
(* any algebra and any execution parameters, and sit here rather than beside  *)
(* IndistinguishabilityCert in manifest/pgg_tableau.v. A deck description is  *)
(* a whole run argument and a deal is its three coordinates other than the    *)
(* secret. The psl211_blockline1_ prefix names block line one and the         *)
(* comparison with block line zero at one chirality, as psl211_perdeck_ of    *)
(* chiralities at one deal. In a proof script a leading C is a fiber          *)
(* cardinality, U a mass at the group-uniform law, L a mass at the ideal, E a *)
(* reader identification, T a step of an inequality chain and H every other   *)
(* named fact; a C, U, L or E suffix names the coordinate the quantity is     *)
(* taken at, t and f the chirality and j0 and j1 the block line; and a        *)
(* trailing digit is an index and never a value.                              *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   coalition_reading_constancy                                              *)
(*                           == a coalition of fewer than profile_k seats     *)
(*                              reads a law on cuts the same way at every     *)
(*                              run argument                                  *)
(*   psl211_blockline1_deal  == block line one, both labellings the identity  *)
(*                                                                            *)
(* Key results:                                                               *)
(*   indistinguishability_cert_reading_constancy                              *)
(*                           == the restatement is the record's fifth field   *)
(*   psl211_alldecks_constancy_false                                          *)
(*                           == the field is false at the group-uniform       *)
(*                              ideal under the all-decks parameters          *)
(*   psl211_blockline1_law_neq                                                *)
(*                           == two deck descriptions of one chirality send   *)
(*                              the group-uniform cut to two reading laws     *)
(*   psl211_alldecks_constancy_false_supp                                     *)
(*                           == the field is false at every ideal supported   *)
(*                              exactly on the shuffle group                  *)
(*   psl211_alldecks_constancy_false_close                                    *)
(*                           == and at every ideal within eps of the          *)
(*                              group-uniform law, once eps + eps < 1/660     *)
(*   psl211_alldecks_cert_ideal_close                                         *)
(*                           == a certificate's distance field is stated      *)
(*                              against the group-uniform law                 *)
(*   psl211_alldecks_no_small_eps_cert                                        *)
(*                           == no certificate over the all-decks model       *)
(*                              carries a shuffle bound epsilon under 1/1320  *)
(*   psl211_alldecks_no_zero_eps_cert                                         *)
(*                           == in particular none carries an epsilon of      *)
(*                              zero, the epsilon of this instance's          *)
(*                              single-card marginal bound                    *)
(*   psl211_alldecks_constancy_false_word584                                  *)
(*                           == the field is false at every ideal within eps  *)
(*                              of the 584-letter word shuffle's cut law      *)
(*   psl211_dealt_constancy_false                                             *)
(*                           == the field is false at the group-uniform       *)
(*                              ideal under the dealt parameters              *)
(*   psl211_alldecks_constancy_set0                                           *)
(*                           == the field holds at the empty coalition, for   *)
(*                              every law on cuts                             *)
(******************************************************************************)

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
From pgg_smc Require Import pgg_sample_adapter pgg_collusion_bound.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_reconstruct Require Import design_privacy algebraic_rigidity.
From pgg_smc Require Import pgg_instance.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_exec.
From pgg_smc Require Import psl211_endpoints psl211_alldecks psl211_models.
From pgg_smc Require Import psl211_blocks psl211_closure psl211_mixing.
From pgg_smc Require Import pgg_weighted_words.

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

(******************************************************************************)
(*     The constancy field as a standalone proposition                        *)
(******************************************************************************)

(** coalition_reading_constancy E ideal — a coalition of fewer than profile_k
    seats reads the law ideal on cuts the same way whatever the run argument.
    This is what an input-indistinguishability certificate asserts about its
    idealized cut, and the certificate's variation-distance field is what
    transfers that assertion from the ideal to the real cut. Where the run
    argument carries the secret, as it does in both run modes of this instance,
    the field is at least constancy in the secret; where the run argument
    carries data outside the secret as well, as it does under the all-decks
    parameters, the field asks for constancy in that data too and is stronger
    than the privacy the instance claims. *)
Definition coalition_reading_constancy (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A)
    (ideal : R.-fdist (pgg_gT (mp_M (instance_profile A)))) : Prop :=
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    forall x x' : ex_inputT E,
      fdistmap (@static_coalition_obs A E C x) ideal
      = fdistmap (@static_coalition_obs A E C x') ideal.

(** indistinguishability_cert_reading_constancy — coalition_reading_constancy
    is the fifth field of IndistinguishabilityCert read at the certificate's
    own ideal, so refuting the proposition at a law refutes every certificate
    whose ideal cut is that law. *)
Lemma indistinguishability_cert_reading_constancy (R : realType)
    (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E))
    (cert : IndistinguishabilityCert sa) :
  coalition_reading_constancy E (ic_ideal cert).
Proof. exact: ic_const cert. Qed.

(******************************************************************************)
(*     The three seats are below the privacy threshold                        *)
(******************************************************************************)

(** psl211_perdeck_coalition_le3 — the coalition witnessing the refutations
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

(******************************************************************************)
(*     The constancy field fails at the group-uniform ideal                   *)
(******************************************************************************)

(** psl211_alldecks_constancy_false — under the all-decks run parameters the
    uniform law on the shuffle group is the ideal cut of no
    input-indistinguishability certificate: seats 0, 1 and 2 read that law
    differently at the two chiralities of the deal psl211_perdeck_deal. The run
    argument of this
    mode is a whole deck description, whose first coordinate is the secret
    chirality and whose other three are not, and the field quantifies
    over every pair of them, so the equation it asserts is false at a pair
    of one chirality too, psl211_blockline1_law_neq. A change of secret is
    always also a change of the laid deck here, the chirality selecting the
    table the block line indexes. Three seats learn nothing about the
    chirality under the all-decks law, which is
    psl211_alldecks_static_indep, and this refutation states no leakage. *)
Lemma psl211_alldecks_constancy_false (R : realType) :
  ~ coalition_reading_constancy psl211_alldecks_params
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

(******************************************************************************)
(*     Two deck descriptions of one chirality                                 *)
(******************************************************************************)

(** psl211_blockline1_deal — block line one, both labellings the identity. It
    differs from psl211_perdeck_deal in the block line alone, a coordinate
    of the run argument that carries no secret. *)
Definition psl211_blockline1_deal : psl211_deal :=
  (@Ordinal 132 1 isT, 1%g, 1%g).

(** psl211_blockline1_view — the reading that gives cards 3, 2 and 4 to seats
    0, 1 and 2, and card 0 to every seat outside the coalition. The deck laid
    at (true, psl211_perdeck_deal) reaches it under exactly one cut and the
    deck laid at (true, psl211_blockline1_deal) under none. *)
Definition psl211_blockline1_view : viewT :=
  [ffun i => psl211_code12 (nth 0 [:: 3; 2; 4] (val i))].

(** psl211_blockline1_test sq t — the coalition's reading of the deck sq under
    the cut whose table is t matches psl211_blockline1_view, tested on raw
    codes. *)
Definition psl211_blockline1_test (sq t : seq nat) : bool :=
  [&& nth 0 sq (nth 0 t 0) %% 12 == 3,
      nth 0 sq (nth 0 t 1) %% 12 == 2 &
      nth 0 sq (nth 0 t 2) %% 12 == 4].

(** psl211_blockline1_testE — the raw test decides the reading, so the fiber
    over psl211_blockline1_view is counted by a boolean on nat lists. *)
Lemma psl211_blockline1_testE (sq t : seq nat) :
  (psl211_perdeck_raw_view sq t == psl211_blockline1_view)
  = psl211_blockline1_test sq t.
Proof.
rewrite /psl211_blockline1_test; apply/idP/idP.
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

(** psl211_alldecks_raw_viewE — the raw reading is the instance's reading, at
    every deck description. This is psl211_perdeck_raw_viewE of
    psl211_models.v with the deal left free instead of fixed at
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

(** psl211_blockline1_seq — the deck psl211_blockline1_deal names at chirality
    true, as raw codes by position. *)
Definition psl211_blockline1_seq : seq nat :=
  let H := psl211_alldecks_row (true, psl211_blockline1_deal) in
  let K := psl211_alldecks_corow (true, psl211_blockline1_deal) in
  [seq (if p \in H then index p H else 6 + index p K) | p <- iota 0 12].

(** psl211_blockline1_row_size — block line one of the chirality-true table
    has six positions. *)
Lemma psl211_blockline1_row_size :
  size (psl211_alldecks_row (true, psl211_blockline1_deal)) = 6.
Proof. by vm_compute. Qed.

(** psl211_blockline1_corow_size — the complement of that row has the other
    six. *)
Lemma psl211_blockline1_corow_size :
  size (psl211_alldecks_corow (true, psl211_blockline1_deal)) = 6.
Proof. by vm_compute. Qed.

(** psl211_blockline1_seqE — that raw list is the deck the all-decks dealer
    lays for this deck description. *)
Lemma psl211_blockline1_seqE :
  psl211_alldecks_seq (true, psl211_blockline1_deal) = psl211_blockline1_seq.
Proof.
have Hrow := psl211_blockline1_row_size.
have Hcorow := psl211_blockline1_corow_size.
rewrite /psl211_blockline1_deal in Hrow Hcorow.
rewrite /psl211_alldecks_seq /psl211_blockline1_seq /psl211_blockline1_deal.
apply/eq_in_map => p Hp.
case: ifP => Hin.
  rewrite perm1; apply: inordK.
  by rewrite -[X in (_ < X)%N]Hrow index_mem Hin.
rewrite perm1; apply/eqP; rewrite eqn_add2l; apply/eqP.
apply: inordK.
rewrite -[X in (_ < X)%N]Hcorow index_mem /psl211_alldecks_corow mem_filter.
by rewrite Hin Hp.
Qed.

(** psl211_blockline1_raw_count sq — how many of the 660 cuts carry the deck
    sq to psl211_blockline1_view. *)
Definition psl211_blockline1_raw_count (sq : seq nat) : nat :=
  count (psl211_blockline1_test sq) (unzip1 psl211_elem_table).

(** psl211_blockline1_raw_countE — that count is one at the deck of
    psl211_perdeck_deal and zero at the deck of psl211_blockline1_deal, both
    at chirality true. The two run arguments carry the same secret. *)
Lemma psl211_blockline1_raw_countE :
  psl211_blockline1_raw_count (psl211_perdeck_seq true) = 1 /\
  psl211_blockline1_raw_count psl211_blockline1_seq = 0.
Proof. by split; vm_compute. Qed.

(* Past this point no proof needs the body of the laid deck, of the closure
   table or of the counts, and every step naming two deck descriptions or two
   chiralities must not be left to a tactic that searches for a match.
   psl211_perdeck_raw_count is sealed here rather than at its first use: the
   two values it takes are supplied by psl211_perdeck_raw_countE, and leaving
   it transparent lets a unifier that falls back to conversion evaluate the
   count over the 660 tabulated cuts. *)
Local Opaque psl211_alldecks_view psl211_elem_table psl211_perdeck_raw_count.

(** psl211_blockline1_fiber x — the cuts of the group carrying the deck of the
    deck description x to psl211_blockline1_view. *)
Definition psl211_blockline1_fiber (x : psl211_inputT) : {set cutT} :=
  [set g in pgg_G psl211_M |
     psl211_alldecks_view psl211_perdeck_coalition x g
       == psl211_blockline1_view].

(** psl211_blockline1_fiberE — that fiber has the raw count of the laid deck
    as its cardinality. *)
Lemma psl211_blockline1_fiberE (x : psl211_inputT) :
  #|psl211_blockline1_fiber x|
  = psl211_blockline1_raw_count (psl211_alldecks_seq x).
Proof.
rewrite /psl211_blockline1_fiber /psl211_blockline1_raw_count.
transitivity
  (count (fun g => psl211_alldecks_view psl211_perdeck_coalition x g
      == psl211_blockline1_view) (enum (pgg_G psl211_M))).
  rewrite cardE /enum_mem size_filter count_filter.
  by apply: eq_count => g; rewrite !inE andbC.
transitivity
  (count (psl211_blockline1_test (psl211_alldecks_seq x))
    [seq psl211_ptbl g | g <- enum (pgg_G psl211_M)]).
  rewrite count_map; apply: eq_count => g.
  by rewrite -psl211_alldecks_raw_viewE psl211_blockline1_testE.
rewrite -!size_filter; apply: perm_size.
exact: (perm_filter _ psl211_perdeck_ptbl_enum).
Qed.

(* psl211_blockline1_raw_count is sealed for the rest of the file: nothing
   further needs its body and psl211_blockline1_raw_countE supplies both
   values. *)
Local Opaque psl211_blockline1_raw_count.

(** psl211_blockline1_massE x — at the deck description x the law of what the
    coalition reads gives psl211_blockline1_view the mass of its fiber of cuts
    over the order of the shuffle group. *)
Lemma psl211_blockline1_massE (R : realType) (x : psl211_inputT) :
  (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition x g)
     ((`U psl211_G_pos) : R.-fdist cutT)) psl211_blockline1_view
  = (#|pgg_G psl211_M|%:R)^-1 *+ #|psl211_blockline1_fiber x| :> R.
Proof. by rewrite /psl211_blockline1_fiber uniform_fdistmap_pointE. Qed.

(** psl211_blockline1_law_neq — the run arguments (true, psl211_perdeck_deal)
    and (true, psl211_blockline1_deal) send the group-uniform cut law to two
    different laws on what seats 0, 1 and 2 read. This is the equation the
    constancy field asserts, at a pair of run arguments carrying the same
    secret, and it is false, so the field's failure at the all-decks
    parameters does not need the chirality to move: it is already a failure
    of constancy in the block line. *)
Lemma psl211_blockline1_law_neq (R : realType) :
  fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
      psl211_perdeck_coalition (true, psl211_perdeck_deal))
    ((`U psl211_G_pos) : R.-fdist cutT)
  != fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
      psl211_perdeck_coalition (true, psl211_blockline1_deal))
    ((`U psl211_G_pos) : R.-fdist cutT).
Proof.
have [Hj0 Hj1] := psl211_blockline1_raw_countE.
(* each cardinality and each mass is pinned in a goal naming one deck
   description only, and the two are brought together in term mode *)
have Cj0 : #|psl211_blockline1_fiber (true, psl211_perdeck_deal)| = 1.
  rewrite psl211_blockline1_fiberE (psl211_perdeck_seqE true); exact: Hj0.
have Cj1 : #|psl211_blockline1_fiber (true, psl211_blockline1_deal)| = 0.
  rewrite psl211_blockline1_fiberE psl211_blockline1_seqE; exact: Hj1.
have Ej0 : @static_coalition_obs psl211_algebra psl211_alldecks_params
     psl211_perdeck_coalition (true, psl211_perdeck_deal)
   = (fun g => psl211_alldecks_view psl211_perdeck_coalition
        (true, psl211_perdeck_deal) g)
  := psl211_alldecks_static_obs_funE _ _.
have Ej1 : @static_coalition_obs psl211_algebra psl211_alldecks_params
     psl211_perdeck_coalition (true, psl211_blockline1_deal)
   = (fun g => psl211_alldecks_view psl211_perdeck_coalition
        (true, psl211_blockline1_deal) g)
  := psl211_alldecks_static_obs_funE _ _.
have Uj0 : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
    (true, psl211_perdeck_deal) g) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_blockline1_view = (#|pgg_G psl211_M|%:R)^-1 :> R.
  by rewrite psl211_blockline1_massE Cj0 mulr1n.
have Uj1 : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
    (true, psl211_blockline1_deal) g) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_blockline1_view = 0 :> R.
  by rewrite psl211_blockline1_massE Cj1 mulr0n.
apply/negP => /eqP Heq.
have Hv := etrans
  (esym (congr1 (fun f => fdistmap f ((`U psl211_G_pos) : R.-fdist cutT)) Ej0))
  (etrans Heq
    (congr1 (fun f => fdistmap f ((`U psl211_G_pos) : R.-fdist cutT)) Ej1)).
have Hz : (#|pgg_G psl211_M|%:R)^-1 = 0 :> R :=
  etrans (esym Uj0)
    (etrans (congr1 (fun q : R.-fdist viewT => q psl211_blockline1_view) Hv)
      Uj1).
have : (#|pgg_G psl211_M|%:R)^-1 == 0 :> R by rewrite Hz.
rewrite invr_eq0 pnatr_eq0 => /eqP Hcard.
by move: psl211_G_pos; rewrite Hcard.
Qed.

(******************************************************************************)
(*     The quantitative form                                                  *)
(******************************************************************************)

(** fdistmap_point_condE — the mass a pushed-forward law gives a value is the
    mass of that value's preimage, with the preimage written as a bigop
    condition, which is the form a support hypothesis is spent in. *)
(* Two lines from infotheo's fdistmapE, which writes the same sum with the
   preimage as a set membership; it is kept local for that reason. *)
Lemma fdistmap_point_condE (R : realType) (X T : finType) (f : X -> T)
    (p : R.-fdist X) (v : T) :
  (fdistmap f p) v = \sum_(x | f x == v) p x.
Proof.
rewrite fdistmapE big_mkcond [RHS]big_mkcond /=.
by apply: eq_bigr => x _; rewrite !inE.
Qed.

(** psl211_perdeck_ideal_lawE — a law on cuts satisfying the constancy field
    sends the two chiralities of psl211_perdeck_deal to one law on what seats
    0, 1 and 2 read. The all-decks run argument is a whole deck description,
    whose first coordinate is the secret chirality and whose other three are
    not, so the field implies this per-deck symmetry of the chirality without
    being exhausted by it. *)
(* This is the one consequence of the field whose fiber counts
   psl211_models.v already carries, which is why both quantitative
   refutations go through it. *)
Lemma psl211_perdeck_ideal_lawE (R : realType) (ideal : R.-fdist cutT) :
  coalition_reading_constancy psl211_alldecks_params ideal ->
  fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (true, psl211_perdeck_deal) g) ideal
  = fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
      (false, psl211_perdeck_deal) g) ideal.
Proof.
move=> Hconst.
have Heq := Hconst psl211_perdeck_coalition psl211_perdeck_coalition_below_k
  (true, psl211_perdeck_deal) (false, psl211_perdeck_deal).
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
exact: (etrans (esym (congr1 (fun f => fdistmap f ideal) Et))
  (etrans Heq (congr1 (fun f => fdistmap f ideal) Ef))).
Qed.

(** psl211_perdeck_fiber_true0 — no cut of the shuffle group carries the
    chirality-true deck of psl211_perdeck_deal to the reading
    psl211_perdeck_view. The false chirality reaches that reading under
    exactly one cut, so one reading already tells the two chiralities apart
    at this fixed deal, which is not the law the row is about. *)
Lemma psl211_perdeck_fiber_true0 : psl211_perdeck_fiber true = set0.
Proof.
have [Ht _] := psl211_perdeck_raw_countE.
have Ct : #|psl211_perdeck_fiber true| = 0 :=
  etrans (psl211_perdeck_fiberE true) Ht.
by apply/eqP; rewrite -cards_eq0 Ct.
Qed.

(** psl211_alldecks_constancy_false_supp — no law on cuts whose support is
    exactly the shuffle group satisfies the constancy field. The reading
    psl211_perdeck_view is reached by one cut of the group at the false
    chirality and by none at the true one, so such a law gives that reading
    positive mass at one chirality of psl211_perdeck_deal and zero at the
    other. *)
Lemma psl211_alldecks_constancy_false_supp (R : realType)
    (ideal : R.-fdist cutT) :
  (forall g : cutT, g \notin pgg_G psl211_M -> ideal g = 0) ->
  (forall g : cutT, g \in pgg_G psl211_M -> ideal g != 0) ->
  ~ coalition_reading_constancy psl211_alldecks_params ideal.
Proof.
move=> Hout Hin Hconst.
have Hlaw := psl211_perdeck_ideal_lawE Hconst.
have [_ Hf] := psl211_perdeck_raw_countE.
have Cf : #|psl211_perdeck_fiber false| = 1 :=
  etrans (psl211_perdeck_fiberE false) Hf.
have /cards1P[g0 Hset] : #|psl211_perdeck_fiber false| == 1 by rewrite Cf.
have Hg0 : g0 \in psl211_perdeck_fiber false by rewrite Hset inE.
move: Hg0; rewrite inE => /andP[Hg0G Hg0v].
(* the true mass vanishes term by term: a cut producing the reading is either
   outside the group, where the law is zero, or inside it and in the empty
   true fiber *)
have Lt : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
    (true, psl211_perdeck_deal) g) ideal) psl211_perdeck_view = 0 :> R.
  rewrite fdistmap_point_condE; apply: big1 => g Hg.
  apply: Hout; apply/negP => HgG.
  have Hmem : g \in psl211_perdeck_fiber true by rewrite inE HgG Hg.
  by move: Hmem; rewrite psl211_perdeck_fiber_true0 inE.
have Hfge : ideal g0 <= (fdistmap (fun g => psl211_alldecks_view
    psl211_perdeck_coalition (false, psl211_perdeck_deal) g) ideal)
    psl211_perdeck_view.
  (* no /= and no // here: the sum runs over the ambient permutation group,
     and a simplification descends into its enumeration *)
  rewrite fdistmap_point_condE (bigD1 g0 Hg0v).
  rewrite -{1}(addr0 (ideal g0)) lerD2l.
  by apply: sumr_ge0 => g _; exact: FDist.ge0.
move: Hfge; rewrite -Hlaw Lt => Hle.
have Hzero : ideal g0 = 0 :> R.
  by apply/eqP; rewrite Order.POrderTheory.eq_le Hle andTb; exact: FDist.ge0.
by move: (Hin g0 Hg0G); rewrite Hzero eqxx.
Qed.

(** psl211_alldecks_constancy_false_close — no law on cuts within variation
    distance epsilon of the group-uniform law satisfies the constancy field,
    once twice epsilon stays below the reciprocal of the group order. At the
    group-uniform law the two chiralities give the reading psl211_perdeck_view
    masses zero and one over the group order, and a variation distance moves
    each of those by at most epsilon. *)
Lemma psl211_alldecks_constancy_false_close (R : realType)
    (ideal : R.-fdist cutT) (eps : R) :
  var_dist ((`U psl211_G_pos) : R.-fdist cutT) ideal <= eps ->
  eps + eps < (#|pgg_G psl211_M|%:R)^-1 ->
  ~ coalition_reading_constancy psl211_alldecks_params ideal.
Proof.
move=> Hclose Heps Hconst.
have Hlaw := psl211_perdeck_ideal_lawE Hconst.
have [Ht Hf] := psl211_perdeck_raw_countE.
have Ct : #|psl211_perdeck_fiber true| = 0 :=
  etrans (psl211_perdeck_fiberE true) Ht.
have Cf : #|psl211_perdeck_fiber false| = 1 :=
  etrans (psl211_perdeck_fiberE false) Hf.
(* each chirality's uniform mass is pinned in a goal naming that chirality
   only, as psl211_perdeck_law_neq does *)
have Ut : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
    (true, psl211_perdeck_deal) g) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_perdeck_view = 0 :> R.
  by rewrite psl211_perdeck_massE Ct mulr0n.
have Uf : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
    (false, psl211_perdeck_deal) g) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_perdeck_view = (#|pgg_G psl211_M|%:R)^-1 :> R.
  by rewrite psl211_perdeck_massE Cf mulr1n.
have Hgap : forall b : bool,
    `| (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
          (b, psl211_perdeck_deal) g) ((`U psl211_G_pos) : R.-fdist cutT))
         psl211_perdeck_view
      - (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
          (b, psl211_perdeck_deal) g) ideal) psl211_perdeck_view | <= eps.
  move=> b; exact: (Order.POrderTheory.le_trans (leq_var_dist _ _ _)
    (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _) Hclose)).
have T1 : (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
    (true, psl211_perdeck_deal) g) ideal) psl211_perdeck_view <= eps.
  have H := Hgap true.
  move: H; rewrite Ut sub0r normrN ler_norml => /andP[_ Hup]; exact: Hup.
have T2 : (#|pgg_G psl211_M|%:R)^-1
    <= eps + (fdistmap (fun g => psl211_alldecks_view psl211_perdeck_coalition
         (false, psl211_perdeck_deal) g) ideal) psl211_perdeck_view.
  have H := Hgap false.
  move: H; rewrite Uf ler_norml lerBlDr => /andP[_ Hlo]; exact: Hlo.
have T3 : eps + (fdistmap (fun g => psl211_alldecks_view
    psl211_perdeck_coalition (false, psl211_perdeck_deal) g) ideal)
    psl211_perdeck_view <= eps + eps.
  by rewrite lerD2l -Hlaw; exact: T1.
have Hbad := Order.POrderTheory.le_lt_trans
  (Order.POrderTheory.le_trans T2 T3) Heps.
by move: Hbad; rewrite Order.POrderTheory.ltxx.
Qed.

(** psl211_alldecks_cert_ideal_close — an input-indistinguishability
    certificate over the all-decks model states its distance against the
    group-uniform law. The certificate's own identification field says its
    shuffle law is the
    adapter's cut, and this adapter's cut is the uniform law on the shuffle
    group, so the epsilon a certificate quotes is an epsilon against that law
    however its marginal bound record was built. *)
Lemma psl211_alldecks_cert_ideal_close (R : realType)
    (cert : IndistinguishabilityCert (psl211_alldecks_sample R)) :
  var_dist ((`U psl211_G_pos) : R.-fdist cutT) (ic_ideal cert)
  <= sw_bound_eps (ic_b cert).
Proof.
have Hd : sw_rho_dist (ic_b cert) = ((`U psl211_G_pos) : R.-fdist cutT)
  := etrans (ic_Hd cert) (psl211_alldecks_cut_distE R).
have Hc := ic_close cert.
rewrite Hd in Hc; exact: Hc.
Qed.

(** psl211_alldecks_no_small_eps_cert — no input-indistinguishability
    certificate over the all-decks run of the twelve-card chirality instance has
    its shuffle bound epsilon added to itself strictly below the reciprocal
    1/660 of the group order, so every such certificate has an epsilon of at
    least 1/1320, the value 1/1320 itself not excluded. A row publishes
    odflt (cert_eps cert) (c R) at its own reprice coordinate c, and cert_eps
    cert is the shuffle bound epsilon twice, so a row over this model that
    publishes its certificate's own number publishes at least 1/660. The
    obligation of conclude bounds the published number below by cert_eps
    cert, so no row over this model publishes less. This fixes from below what
    the input-indistinguishability arm can publish at this model. It says
    neither that the arm is unavailable here nor anything about what a coalition
    of at most five seats reads. *)
(* Argued and not compiled: the proposition a row carries is
   IndistinguishabilityPropAt cert c, a variation distance bounded above by c,
   so an obligation weakened from an equality to cert_eps cert <= odflt
   (cert_eps cert) (c R) could only let a row publish a number no smaller than
   cert_eps. *)
(* The excluded range of epsilon is bounded above. The header records why the
   larger range is occupied and that the occupancy is argued and not
   compiled. *)
Theorem psl211_alldecks_no_small_eps_cert (R : realType)
    (cert : IndistinguishabilityCert (psl211_alldecks_sample R)) :
  sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert)
    < (#|pgg_G psl211_M|%:R)^-1 -> False.
Proof.
move=> Heps.
apply: (@psl211_alldecks_constancy_false_close R (ic_ideal cert)
  (sw_bound_eps (ic_b cert)) (psl211_alldecks_cert_ideal_close cert) Heps).
exact: indistinguishability_cert_reading_constancy cert.
Qed.

(** psl211_alldecks_no_zero_eps_cert — in particular no
    input-indistinguishability certificate over the all-decks model has a
    shuffle bound epsilon of zero, which is the epsilon profile_eps_psl211 of
    instances/psl211/psl211_profile.v
    gives this instance's single-card marginal bound. A certificate must
    hold its ideal cut within its own epsilon of the group-uniform law, and
    the group-uniform law is not a cut these three seats read constantly, so
    the sharper the shuffle bound the less room the certificate has. *)
Corollary psl211_alldecks_no_zero_eps_cert (R : realType)
    (cert : IndistinguishabilityCert (psl211_alldecks_sample R)) :
  sw_bound_eps (ic_b cert) = 0 -> False.
Proof.
move=> Heps.
have Hlt : sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert)
    < (#|pgg_G psl211_M|%:R)^-1.
  by rewrite Heps addr0 invr_gt0 ltr0n; exact: psl211_G_pos.
(* cert is an implicit argument of the theorem, occurring in the type of its
   hypothesis, so the certificate is supplied at the @ form *)
exact: (@psl211_alldecks_no_small_eps_cert R cert Hlt).
Qed.

(******************************************************************************)
(*     The word model, which this tree carries no sample adapter for          *)
(******************************************************************************)

(** psl211_alldecks_constancy_false_word — take a cut law W within d of the
    group-uniform law, and a law on cuts within eps of W. That law does not
    satisfy the constancy field, as long as twice the sum of d and eps stays
    below the reciprocal of the group order. The first distance is the price
    of replacing the exact shuffle by one a dealer can perform, the second is
    a certificate's own distance field, and a row over any cut law but the
    group-uniform one pays both. *)
Lemma psl211_alldecks_constancy_false_word (R : realType)
    (W ideal : R.-fdist cutT) (d eps : R) :
  var_dist ((`U psl211_G_pos) : R.-fdist cutT) W <= d ->
  var_dist W ideal <= eps ->
  (d + eps) + (d + eps) < (#|pgg_G psl211_M|%:R)^-1 ->
  ~ coalition_reading_constancy psl211_alldecks_params ideal.
Proof.
move=> HW Hi Hlt.
have Hclose : var_dist ((`U psl211_G_pos) : R.-fdist cutT) ideal <= d + eps.
  apply: (Order.POrderTheory.le_trans (var_dist_triangle _ W _)).
  exact: lerD HW Hi.
exact: (@psl211_alldecks_constancy_false_close R ideal (d + eps) Hclose Hlt).
Qed.

(** psl211_alldecks_constancy_false_word584 — the cut law of the 584-letter
    word shuffle leaves the constancy field false at every ideal within eps of
    it, once twice the sum of eps and 2^-40 stays below the reciprocal of the
    group order. The dealer performs a finite word and not an exact uniform
    draw, and the 2^-40 is the whole information-theoretic price of that
    replacement, while the eps is a certificate's own distance field. It is
    stated on the cut law rather than on a certificate because no
    weighted-word SampleAdapter exists in this tree, so there is no adapter
    whose cut is this law and no ic_Hd through which a certificate's ideal
    could be held near it. *)
Lemma psl211_alldecks_constancy_false_word584 (R : realType)
    (ideal : R.-fdist cutT) (eps : R) :
  var_dist (@rho_from_words_weighted R 10 2 584 psl211_moves (psl211_Wuni R))
    ideal <= eps ->
  (2%:R^-40 + eps) + (2%:R^-40 + eps) < (#|pgg_G psl211_M|%:R)^-1 ->
  ~ coalition_reading_constancy psl211_alldecks_params ideal.
Proof.
move=> Hi Hlt.
(* psl211_word_mixing states the distance with the word law on the left, and
   the two-step lemma reads it from the group-uniform law outward *)
have HW : var_dist ((`U psl211_G_pos) : R.-fdist cutT)
    (@rho_from_words_weighted R 10 2 584 psl211_moves (psl211_Wuni R))
  <= 2%:R^-40.
  by rewrite symmetric_var_dist; exact: psl211_word_mixing.
exact: (psl211_alldecks_constancy_false_word HW Hi Hlt).
Qed.

(******************************************************************************)
(*     The dealer-dealt mode, where the run argument is the secret            *)
(******************************************************************************)

(** psl211_dealt_decktbl b — the encoder deck of chirality b as a twelve-entry
    position-to-code table: the heart codes 0 to 5 ascend along the
    representative row of the system b names and the club codes 6 to 11 ascend
    along its complement. *)
(* Only raw nat data is counted from here on, the ordinal enumeration going
   through an opaque decision that does not reduce. *)
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

(** psl211_dealt_view — the reading that gives cards 0, 1 and 6 to seats 0, 1
    and 2, and card 0 to every seat outside the coalition. The encoder decks
    of the two chiralities reach it under different numbers of cuts, which is
    what refutes the constancy field in the dealt mode. *)
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
    the other. *)
(* vm_compute reads the closure table's body whatever the conversion oracle
   has been told, so this sentence is unaffected by the Local Opaque the
   block-line section leaves standing. *)
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

(* psl211_dealt_raw_count is sealed for the rest of the file: nothing further
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

(** psl211_dealt_constancy_false — under the dealer-dealt run parameters the
    constancy field is false at the uniform law on the shuffle group, so no
    input-indistinguishability certificate over these parameters can take that
    law as its ideal cut, while a certificate at some other ideal stays open.
    The dealt run
    argument is the chirality and nothing else, so here the constancy field is
    exactly constancy in the secret, and it fails because the encoder decks of
    the two chiralities give one reading of three seats different masses. That
    is a fact about the group and the design: PSL(2,11) is 2-transitive and
    not 3-transitive, where PGL(2,7) proves the same field through
    pgl27_word_view_const. The statement rules out one named ideal and no
    certificate, this tree carrying no dealt-mode sample adapter through which
    a certificate's ideal could be pinned to it. *)
Lemma psl211_dealt_constancy_false (R : realType) :
  ~ coalition_reading_constancy psl211_dealt_params
      ((`U psl211_G_pos) : R.-fdist cutT).
Proof.
move=> Hconst.
have Heq := Hconst psl211_perdeck_coalition psl211_perdeck_coalition_below_k
  true false.
(* each mass is pinned to its value in a goal naming one chirality only, and
   the two are brought together in term mode *)
have [Ht Hf] := psl211_dealt_raw_countE.
have Ct : #|psl211_dealt_fiber true| = 0 :=
  etrans (psl211_dealt_fiberE true) Ht.
have Cf : #|psl211_dealt_fiber false| = 1 :=
  etrans (psl211_dealt_fiberE false) Hf.
have Ut : (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
    psl211_perdeck_coalition true) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_dealt_view = 0 :> R.
  by rewrite psl211_dealt_massE Ct mulr0n.
have Uf : (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
    psl211_perdeck_coalition false) ((`U psl211_G_pos) : R.-fdist cutT))
    psl211_dealt_view = (#|pgg_G psl211_M|%:R)^-1 :> R.
  by rewrite psl211_dealt_massE Cf mulr1n.
have Hz : (0 : R) = (#|pgg_G psl211_M|%:R)^-1 :=
  etrans (esym Ut)
    (etrans (congr1 (fun q : R.-fdist viewT => q psl211_dealt_view) Heq) Uf).
have : (#|pgg_G psl211_M|%:R)^-1 == 0 :> R by rewrite -Hz.
rewrite invr_eq0 pnatr_eq0 => /eqP Hcard.
by move: psl211_G_pos; rewrite Hcard.
Qed.

(******************************************************************************)
(*     The empty coalition, where the field holds                             *)
(******************************************************************************)

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

(** psl211_alldecks_constancy_set0 — at the empty coalition the constancy
    statement holds, for every law on cuts. A refutation of the field at these
    parameters therefore has to spend a nonempty coalition: the field is not
    false for the trivial reason that its quantifier over coalitions admits a
    reading no law can make constant. *)
Lemma psl211_alldecks_constancy_set0 (R : realType)
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
