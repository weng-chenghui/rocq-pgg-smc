# Plan: word-shuffle statistical privacy for the PGL(2,7) instance

Date: 2026-08-08
Spec: `20260808-120000-word-shuffle-statistical-privacy-spec.md`
Status: ready to execute. Every proof below compiled at exit 0 in
`scratchpad/probes-r3/pgl27_word_privacy_candidate.v` (238 lines), axiom-clean.
Re-audit 2026-08-08: independent recompile of the identical source, exit 0,
`pgl27_word_run_recovers` closed under the global context, the other six
results exactly the boolp trio. Findings F1-F4 folded into Tasks 4, 5, 7 and
the verification and gate paragraphs below.

## What lands

Six new results closing the gap between the paper's perfect-privacy half and its
mixing half.

| Result | Statement | Bound |
|---|---|---|
| `pgl27_word_run_recovers` | executed endpoints decode to the dealt secret, for every 200-letter word | exact, probability one |
| `pgl27_view_law_classes` | at most three positions see the same uniform-shuffle law from either orbit class | equality |
| `pgl27_view_law_const` | the same, quantified over both secrets | equality |
| `pgl27_word_view_indist` | two secrets give coalition-view laws this close under the word shuffle | `2^-39` |
| `pgl27_word_trace_indist` | the same for the executed coalition trace | `2^-39` |
| `pgl27_view_mixing` | the joint law is this close to the ideal independent execution, at any Boolean prior | `2^-40` |

## Decisions, all settled

| Question | Decision | Reason |
|---|---|---|
| One file or split correctness out | **One file**, `pgg-smc/instances/pgl27/pgl27_word_privacy.v` | The consolidated unit compiles at exit 0 and was verified twice. Splitting adds a file and a `_CoqProject` line for no measured benefit; the import cost is already paid. |
| `_CoqProject` position | Line 256, immediately after `pgl27_mixing.v` | Needs both `pgl27_secrecy` (`:252`) and `pgl27_mixing` (`:255`). |
| Retire `pgl27_view_indep`? | **No, do not touch `pgl27_secrecy.v`** | It is consumed by `pgl27_trace.v` and cited by name in the paper's source-index tables. Retiring it churns a landed file and the paper for no gain. `pgl27_view_indep_gen` records the general form in the new file. |
| Helper shape | Named base plus corollary | The bare `forall s s'` form reads as a possible tautology. The base visibly equates two different decks. |
| `Let` or `Definition` for the two views | **`Definition`** | A section-level `Let` is discharged and expanded at section close, so the exported statement would lose the names. |
| Marginals in `pgl27_view_mixing` | Explicit `fdistmap`, not `` `p_ `` | `` `p_ `` resolves its phantom to `pgl27P R`, the uniform prior. At a generic prior it typechecks, prints identically, and states the wrong thing. |
| Commit granularity | One commit for the Rocq file, then one per paper edit | The file is verified verbatim as a unit; splitting it into six commits would ship five states nobody compiled. |

## Task 1: land the Rocq file

Create `pgg-smc/instances/pgl27/pgl27_word_privacy.v` with exactly the content
below, and insert `pgg-smc/instances/pgl27/pgl27_word_privacy.v` at line 256 of
`_CoqProject`.

```coq
(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_word_privacy: coalition privacy of the eight-card orbit scheme under *)
(* the two-hundred-letter word shuffle                                        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_word_run_recovers == decoding the executed endpoints returns the   *)
(*     dealt secret, for every two-hundred-letter generator word              *)
(*   pgl27_view_law_classes == at most three positions see the same law of    *)
(*     the uniformly shuffled deal in both orbit classes                      *)
(*   pgl27_word_view_indist == two secrets give coalition-view laws within    *)
(*     2^-39 in variation distance under the word shuffle                     *)
(*   pgl27_word_trace_indist == the same for the executed coalition trace     *)
(*   pgl27_view_mixing == the joint view-and-secret law under the word        *)
(*     shuffle is within 2^-40 of the product of its exact-shuffle marginals, *)
(*     for every Boolean prior                                                *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop div prime.
From mathcomp Require Import primitive_action.
From mathcomp Require Import order ssralg ssrnum boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_interface pgg_collusion_bound.
From pgg_smc Require Import pgg_weighted_words.
From pgg_smc Require Import pgl27_group pgl27_orbit pgl27_profile pgl27_scheme.
From pgg_smc Require Import card_exchange_pismc pgg_input_commitment pgg_run.
From pgg_reconstruct Require Import covering_scheme pgg_sharing_framework.
From pgg_reconstruct Require Import transitivity_privacy.
From pgg_smc Require Import pgl27_run pgl27_secrecy pgl27_trace pgl27_mixing.
Require Import smc_interpreter pismc smc_session_types.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

Notation pgl27_Msym := (Gen_PGGTypes pgl27_sym_sigmas).

(** pgl27_word_run_recovers — the executed endpoints of a run whose shuffle is
    the product of a two-hundred-letter generator word decode to the dealt
    secret.
    @main correctness: correctness under the word shuffle is exact and holds
    at probability one. *)
Corollary pgl27_word_run_recovers (s : bool) (w : 200.-tuple 'I_5) :
  ts_recon orbit_scheme
    (tcast (pgl27_endpoints_size s (@word_eval pgl27_Msym 200 w))
       (in_tuple (endpoints_of_trace
          (nth [::] (run_interp pgl27_fuel
             (pgl27_procs s (@word_eval pgl27_Msym 200 w))).2 1))))
  = s.
Proof.
apply: pgl27_run_recovers; exact: pgl27_mixing.word_eval_in_G.
Qed.

Section pgl27_word_privacy.
Variable R : realType.

(** rho_word — the law of the product of two hundred independent uniform
    letters of the symmetrized five-letter generator alphabet.
    @intent: the realistic word shuffle law on PGL(2,7). *)
Definition rho_word : R.-fdist (pgg_gT pgl27_M) :=
  @rho_from_words_weighted R 6 4 200 pgl27_sym_sigmas (Wuni R).

(** pgl27P_gen — the joint law of a secret drawn from secretP and an
    independent uniform PGL(2,7) shuffle.
    @intent: the exact-shuffle sample space at an arbitrary Boolean prior. *)
Definition pgl27P_gen (secretP : R.-fdist bool)
    : R.-fdist (bool * pgg_gT pgl27_M)%type := secretP `x (`U pgl27_G_pos).

(** pgl27P_word_gen — the joint law of a secret drawn from secretP and an
    independent word shuffle.
    @intent: the word-shuffle sample space at an arbitrary Boolean prior. *)
Definition pgl27P_word_gen (secretP : R.-fdist bool)
    : R.-fdist (bool * pgg_gT pgl27_M)%type := secretP `x rho_word.

(** pgl27_equianharmonic_view — the coalition's observation at shuffle g when
    the dealt deck is the equianharmonic representative orbit_encode true.
    @intent: the equianharmonic branch of the coalition observable. *)
Definition pgl27_equianharmonic_view (C : {set 'I_8}) (g : pgg_gT pgl27_M)
    : {ffun 'I_8 -> 'I_8} := pgl27_view R C (true, g).

(** pgl27_harmonic_view — the coalition's observation at shuffle g when the
    dealt deck is the harmonic representative orbit_encode false.
    @intent: the harmonic branch of the coalition observable. *)
Definition pgl27_harmonic_view (C : {set 'I_8}) (g : pgg_gT pgl27_M)
    : {ffun 'I_8 -> 'I_8} := pgl27_view R C (false, g).

(** pgl27_view_law_classes — under the uniform PGL(2,7) shuffle, a coalition
    of at most three positions sees the same law whether the dealt deck is the
    equianharmonic representative or the harmonic one.
    @composes: pgl27_view_law_const *)
Lemma pgl27_view_law_classes (C : {set 'I_8}) : (#|C| <= 3)%N ->
  fdistmap (pgl27_equianharmonic_view C)
    (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
  = fdistmap (pgl27_harmonic_view C)
    (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M)).
Proof.
move=> HC.
pose k := size (enum C).
pose p : k.-tuple 'I_8 := in_tuple (enum C).
have Hk : (k <= 3)%N by rewrite /k -cardE.
have Hp : p \in dtuple_on k [set: 'I_8].
  by rewrite inE; apply/andP;
     split; [exact: enum_uniq | apply/subsetP => x _; rewrite inE].
have Hdt : (0 < #|dtuple_on k [set: 'I_8]|)%N by apply/card_gt0P; exists p.
pose maskf := fun r : k.-tuple 'I_8 =>
  [ffun i : 'I_8 => nth ord0 (val r) (index i (enum C))].
have Hone : forall b : bool,
    fdistmap (fun g : pgg_gT pgl27_M => pgl27_view R C (b, g))
      (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
    = fdistmap maskf (`U Hdt : R.-fdist (k.-tuple 'I_8)).
  move=> b.
  have Hcomp : (fun g : pgg_gT pgl27_M => pgl27_view R C (b, g))
      = maskf \o (fun g : pgg_gT pgl27_M =>
          [tuple tnth (orbit_encode b) (@pgg_rho pgl27_M g (tnth p l)) | l < k]).
    apply: boolp.funext => g; apply/ffunP => i.
    rewrite /= /maskf ffunE /pgl27_view ffunE.
    case Hi: (i \in C).
      have Hmem : i \in enum C by rewrite mem_enum Hi.
      have Hj : (index i (enum C) < k)%N by rewrite /k index_mem.
      rewrite -(tnth_nth ord0 _ (Ordinal Hj)) tnth_mktuple.
      have -> : tnth p (Ordinal Hj) = i by rewrite (tnth_nth i) nth_index.
      by [].
    have Hni : i \notin enum C by rewrite mem_enum Hi.
    have Hidx : index i (enum C) = k.
      apply/eqP; rewrite eqn_leq; apply/andP.
      by split; [rewrite /k; exact: index_size | rewrite /k leqNgt index_mem].
    by rewrite Hidx nth_default // size_tuple.
  rewrite Hcomp -fdistmap_comp.
  by rewrite (@ktuple_encode_uniform (pgg_N' pgl27_M) (pgg_gT pgl27_M)
    (pgg_G pgl27_M) (@pgg_rho pgl27_M) 3 pgl27_3transitive R pgl27_G_pos
    orbit_encode k p b Hdt Hk (orbit_encode_deck b) Hp).
by rewrite /pgl27_equianharmonic_view /pgl27_harmonic_view
  (Hone true) (Hone false).
Qed.

(** pgl27_view_law_const — under the uniform PGL(2,7) shuffle the law of the
    view of a coalition of at most three positions does not depend on the
    dealt secret.
    @composes: pgl27_word_view_indist *)
Corollary pgl27_view_law_const (C : {set 'I_8}) (s s' : bool) : (#|C| <= 3)%N ->
  fdistmap (fun g : pgg_gT pgl27_M => pgl27_view R C (s, g))
    (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
  = fdistmap (fun g : pgg_gT pgl27_M => pgl27_view R C (s', g))
    (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M)).
Proof.
by move=> HC; case: s; case: s'; rewrite ?(pgl27_view_law_classes HC).
Qed.

(* Two halves of 2^-40 make 2^-39.  The mulr_natl and mulr_natr routes fail
   here because the ring numeral 2 is itself a natmul and the rewrite fires
   inside it, yielding (2 * 1) ^- 40. *)
Let pow2_split : (2%:R : R)^-40 + 2%:R^-40 = 2%:R^-39.
Proof. by rewrite [RHS]splitr exprSr invfM. Qed.

(** pgl27_word_view_indist — under the two-hundred-letter word shuffle the
    coalition-view laws of two secrets are within 2^-39 in variation distance,
    for every coalition of at most three positions.
    @main security: statistical coalition privacy under the realistic
    shuffle. *)
Theorem pgl27_word_view_indist (C : {set 'I_8}) (s s' : bool) :
  (#|C| <= 3)%N ->
  var_dist (fdistmap (fun g => pgl27_view R C (s, g)) rho_word)
           (fdistmap (fun g => pgl27_view R C (s', g)) rho_word)
  <= 2%:R^-39.
Proof.
move=> HC.
apply: (Order.POrderTheory.le_trans (var_dist_triangle _
  (fdistmap (fun g => pgl27_view R C (s, g)) (`U pgl27_G_pos)) _)).
rewrite -pow2_split; apply: lerD.
- apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
  exact: pgl27_word_mixing.
- rewrite (pgl27_view_law_const (C:=C) s s' HC) symmetric_var_dist.
  apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
  exact: pgl27_word_mixing.
Qed.

(** pgl27_word_trace_indist — under the two-hundred-letter word shuffle the
    executed coalition traces of two secrets are within 2^-39 in variation
    distance, for every coalition of at most three positions.
    @main security: the coalition-view bound transported to the executed
    interpreter trace. *)
Theorem pgl27_word_trace_indist (C : {set 'I_8}) (s s' : bool) :
  (#|C| <= 3)%N ->
  var_dist (fdistmap (fun g => pgl27_coalition_trace R C (s, g)) rho_word)
           (fdistmap (fun g => pgl27_coalition_trace R C (s', g)) rho_word)
  <= 2%:R^-39.
Proof.
by rewrite (pgl27_coalition_trace_E R C); exact: pgl27_word_view_indist.
Qed.

(** pgl27_view_indep_gen — at every Boolean prior, a coalition of at most
    three positions has a view of the uniformly shuffled dealt arrangement
    independent of the orbit secret.
    @composes: pgl27_view_mixing *)
Lemma pgl27_view_indep_gen (secretP : R.-fdist bool) (C : {set 'I_8}) :
  (#|C| <= 3)%N -> pgl27P_gen secretP |= pgl27_view R C _|_ pgl27_secret R.
Proof.
move=> HC.
exact: (@ttrans_view_indep_gen (pgg_N' pgl27_M) (pgg_gT pgl27_M) (pgg_G pgl27_M)
  (@pgg_rho pgl27_M) 3 pgl27_3transitive R secretP pgl27_G_pos
  orbit_encode C HC orbit_encode_deck).
Qed.

(** pgl27_view_mixing — at every Boolean prior, the joint view-and-secret law
    under the two-hundred-letter word shuffle is within 2^-40 of the product
    of the two exact-shuffle marginals.
    @main bound: proximity of the word-shuffle joint law to the ideal
    independent execution. *)
Theorem pgl27_view_mixing (secretP : R.-fdist bool) (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  var_dist (fdistmap (fun u => (pgl27_view R C u, pgl27_secret R u))
                     (pgl27P_word_gen secretP))
           ((fdistmap (pgl27_view R C) (pgl27P_gen secretP))
              `x (fdistmap (pgl27_secret R) (pgl27P_gen secretP)))
  <= 2%:R^-40.
Proof.
move=> HC; rewrite -(inde_dist_of_RV2 (pgl27_view_indep_gen secretP HC)).
apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
exact: (pgl27_joint_mixing secretP).
Qed.

End pgl27_word_privacy.
```

**Verification before commit.** Compile the file. Then `Print Assumptions` on
all seven results (the six of the table plus `pgl27_view_indep_gen`):
`pgl27_word_run_recovers` must print "Closed under the global context", the
other six the boolp trio and nothing more (F3: the previous count "five" was
wrong). Then compile the whole project once to confirm the new `_CoqProject`
entry breaks nothing.

**Gate.** The commit stages a `.v` file, so the two-stage audit runs. Every
declaration above already carries its H-series role tag. All twelve new
top-level names plus the `Let pow2_split` have at most four underscore
components, return zero grep hits repo-wide, and pass I001 (F4: the previous
count "seven" was a stale carry-over from the round-two spec). H002 resolves `@composes`
targets by `git grep`, and the chain
`pgl27_view_law_classes` to `pgl27_view_law_const` to `pgl27_word_view_indist`
only resolves once the file is staged, so run the gate on the staged file rather
than pre-checking.

## Task 2: paper, security-model section

Add the observation assumption. The dealer performs 200 physical moves and the
model exposes only their product. This is structurally forced, since
`exchange_dealer`'s `W : seq gT` is a list of alternative cuts rather than a
composition, and the formal witness is `pgl27_dealer_run`'s singleton `[:: w0]`.
Say that the exact model makes the same assumption.

## Task 3: paper, correctness is law-independent

State once that correctness holds for every group element and therefore under
both shuffle laws at probability one, so only privacy carries an epsilon. Cite
`pgl27_word_run_recovers`.

## Task 4: paper, delete the now-false negative claims

F1: a sentence-level sweep found five loci in this task's remit, not two. Line
numbers drift because `main.tex` is dirty in the working tree; match on the
quoted text, not on line numbers.

1. Mixing section: the two "stops before" sentences plus the follow-on "Such
   results require a separate argument that transports distributional
   proximity through the coalition view and the interpreter." Replace with the
   two new theorems and their `2^-39` bound.
2. Introduction: "The current formalization stops at distributional
   proximity.It does not transport the bound through the protocol interpreter
   to approximate view or trace privacy." Both sentences are now false.
   Replace with the transported `2^-39` claim. This locus was missed by the
   original line-based sweep because the sentence wraps across lines.
3. Introduction roadmap: "Section~\ref{sec:conclusion} states the remaining
   bridge and other future directions." The bridge is landed. Point the
   sentence at what the conclusion now lists.
4. Conclusion: "The formalization does not yet turn these distributional
   bounds into approximate coalition-view or trace privacy." Delete.
5. Conclusion: rewrite the "separate two-model security result" sentence to
   name what actually remains, which is the entropy form and the all-decks
   dealer.

The abstract locus is in Task 7 and the Figure 1 locus is in Task 5.

## Task 5: paper, Figure 1

Extend the lower path from "endpoint and product-law transfers" to coalition
view and executed trace. The caption's "remains future work" clause goes.
F1: the figure's introducing sentence "It does not reach an approximate
security statement." is also now false. Replace it with the statement that the
lower path reaches approximate coalition-view and executed-trace privacy at
`2^-39`.

## Task 6: paper, scope sentence

One sentence: the word-shuffle privacy results cover the fixed-representative
dealer only. The all-decks and shuffle-free dealers live on different sample
spaces that `pgl27_joint_mixing` cannot reach at its `bool * gT` type.

## Task 7: paper, terminology

Rename the two models to uniform-shuffle and word-shuffle, and change the
instance's own results from "exact privacy" to "perfect privacy". F2: the
related-work section says "perfect security" for den Boer, not "perfect
privacy"; the rename adopts the standard term for the property rather than
matching an existing phrase, and the den Boer sentence stays unchanged. Add
`2^-39` to the abstract. F1: the abstract's "It does not establish approximate
coalition-view or executed-trace privacy." is now false. Replace it with the
`2^-39` coalition-view and executed-trace claim.

## Not in this plan

- Entropy form `|H(S | V_C) - H(S)| <= eps`. Needs a quantitative modulus for
  `H_2` near one half; `lib/binary_entropy_function.v:142` has only qualitative
  `continuous_H2`.
- All-decks and shuffle-free dealers under the word law. Needs a new mixing
  statement at `alldecksP` and `uniform_deckP`.
- Channel duality for pgl27's ten processes. Only the 2-player test
  configuration is proven.
- Retiring `pgl27_view_indep` in favour of `pgl27_view_indep_gen`.

## Addendum 2026-08-08, post-execution

User standard: the paper says "distribution", never "law", for probability
distributions. Applied across `main.tex` in commit 0df36a4 (46 word
occurrences plus the `product-law` and `group-law` compounds; `word-law X`
compounds became `word-shuffle X`; the two Figure 1 node labels were
re-wrapped). The unused `\wordlaw` macro became `\worddist` (a16d564). Rocq
identifiers such as `pgl27_view_law_classes` are out of scope for this
standard.
