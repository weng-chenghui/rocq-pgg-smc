# Landing of the refutations design (2026-09-21)

Branch `feat/tableau-extensions-probe`, on top of `a29635b`. Working tree
edits only, no git command that writes. Spec:
`notes/20260921-refutations-probe-design.md`, section "Results of the probe
and of the audit; landing plan". Audit: `audit.md` in this directory.

## The flow

How the all-decks Sampled program becomes a published obstruction, and what
the two corollaries derive from it. One step per line, the accumulated value
in the trailing comment.

```
start  psl211_exact_sampled : Tableau Sampled          // run correctness /\ link lemma; no number
law    sa_cut_dist (psl211_alldecks_sample R) = `U psl211_G_pos
                                by psl211_alldecks_cut_distE       // the model's own cut law is fixed
mass   reading at (true , psl211_perdeck_deal) = 0
                                by psl211_perdeck_static_mass_true // 0
mass   reading at (false, psl211_perdeck_deal) = 1/|G|
                                by psl211_perdeck_static_mass_false// 1/660
gap    |0 - 1/|G|| <= var_dist(read_true, read_false)
                                by leq_var_dist                    // >= 1/660 at one point of the reading space
core   psl211_alldecks_perdeck_reading_ge                          // >= 1/660, certificate-free
lift   exists C x x', #|C| < k /\ 1/660 <= var_dist ...
                                by psl211_perdeck_coalition_below_k// InputDistinguishabilityPropAt sa 1/660
pay    psl211_alldecks_obstruction  := InputDistinguishabilityObstruction 1/660
                                                                   // the kind at every field and index
pay    psl211_alldecks_obstruction_pf                              // its proof there
publ   s |> publish Obstruction o by pf BaselineClassicalOnly
                                                                   // PublishedObstruction; path
                                                                   // (observed, AnalysisBridged,
                                                                   //  exact_family, NegativeTransfer,
                                                                   //  BaselineClassicalOnly)
read   obstruction_of ... R tt                                     // 1/660, back off the value
-- outside the program, two consequences of the same fact --
cor1   indistinguishability_number_ge_of_input_distinguishability
         + psl211_alldecks_input_distinguishability                // every published number >= 1/660
cor2   indistinguishability_prop_of_ideal_close (eps -> eps+eps)
         then cor1                                                 // no cert with ideal within eps of the
                                                                   // model's own cut law, for eps+eps < 1/660
nonvac pgl27_word_published39's reader                             // the proposition is FALSE above 2^-39
                                                                   // at the PGL(2,7) word model
```

**Monad verdict.** No new monad. The terminal is the fourth handover out of
the existing parameterised bind `tableau_bind`, indexed by completion level:
`publish_obstruction` leaves the level indexing where the three existing
terminals leave it, and the accumulated proposition is unchanged from
`StackProp Sampled`. The two corollaries and the non-vacuity lemma are
post-processing outside the flow: they consume the published number and
preserve no per-step invariant.

**Interface of every existing result used.**

| existing result | role | interface it enters through |
|---|---|---|
| `psl211_exact_sampled` | first object of the flow | the named `Tableau Sampled` value |
| `psl211_alldecks_cut_distE` | observation change, no cost | rewrite in the core's proof |
| `psl211_perdeck_raw_countE`, `psl211_perdeck_fiberE`, `psl211_perdeck_massE`, `psl211_alldecks_static_obs_funE` | step justification of the two masses | term-mode `etrans`/`congr1`, never a rewrite |
| `leq_var_dist` (infotheo) | terminal evaluation of the core | `eq_ind` at the computed absolute difference |
| `psl211_perdeck_coalition_below_k` | step justification of the lift | first conjunct of the existential |
| `ic_const`, `var_dist_fdistmap`, `var_dist_triangle`, `symmetric_var_dist` | step justification of the general tail lemma | inside `indistinguishability_prop_of_ideal_close` |
| `indistinguishability_tail` | untouched; its general form now sits beside it | none (pure addition) |
| `psl211_alldecks_no_small_eps_cert` | companion exclusion on the other coordinate | named in the landed comment, not edited |
| `view_indistinguishability_of pgl27_word_published39` | terminal evaluation of the non-vacuity lemma | the published word program's own reader |

## Files edited, and what was added

Every deleted line in the whole diff is a comment line (checked with
`git diff -U0 | grep '^-'` filtered on `-(*`), so the landing is a pure
addition in code.

### `manifest/pgg_tableau.v` (+362 lines, compile 12.5 s)

Beside `indistinguishability_tail`:

```coq
Lemma indistinguishability_prop_of_ideal_close (R : realType)
    (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E))
    (cert : IndistinguishabilityCert sa) (eps : R) :
  var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps ->
  IndistinguishabilityPropAt cert (eps + eps).
Arguments indistinguishability_prop_of_ideal_close {R A E sa} cert eps.
```

New section "An obstruction a program publishes at its model", after "Handing
a program over below AnalysisBridged":

```coq
Definition InputDistinguishabilityPropAt (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (c : R) : Prop :=
  exists (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1})
         (x x' : ex_inputT E),
    (#|C| < profile_k (instance_profile A))%N /\
    c <= var_dist (fdistmap (static_coalition_obs C x) (sa_cut_dist sa))
                  (fdistmap (static_coalition_obs C x') (sa_cut_dist sa)).
Arguments InputDistinguishabilityPropAt {R A E} sa c.

Lemma input_distinguishability_prop_le (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (c c' : R) :
  c' <= c ->
  InputDistinguishabilityPropAt sa c -> InputDistinguishabilityPropAt sa c'.

Lemma indistinguishability_number_ge_of_input_distinguishability
    (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E))
    (cert : IndistinguishabilityCert sa) (c c' : R) :
  InputDistinguishabilityPropAt sa c ->
  IndistinguishabilityPropAt cert c' -> c <= c'.

Lemma no_indistinguishability_cert_ideal_close_of_input_distinguishability
    (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A)
    (sa : SampleAdapter R (instance_exec E)) (c eps : R) :
  InputDistinguishabilityPropAt sa c -> eps + eps < c ->
  forall cert : IndistinguishabilityCert sa,
    var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps -> False.

Variant ObstructionKind (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) : Type :=
  | InputDistinguishabilityObstruction of R.

Definition ObstructionProp ... (o : ObstructionKind sa) : Prop :=
  match o with
  | InputDistinguishabilityObstruction c => InputDistinguishabilityPropAt sa c
  end.

Definition ObstructionPayload (q : StackAt Sampled) : Type :=
  forall (R : realType) (idx : amf_index (sp_f q) R),
    ObstructionKind (amf_sample (sp_f q) R idx).

Definition ObstructionPayloadProp (q : StackAt Sampled)
    (o : ObstructionPayload q) : Prop :=
  forall (R : realType) (idx : amf_index (sp_f q) R), ObstructionProp (o R idx).

Definition PublishObstructionPayload (q : StackAt Sampled) : Type :=
  { o : ObstructionPayload q & ObstructionPayloadProp o }.

Definition mk_obstruction (q : StackAt Sampled) (o : ObstructionPayload q)
    (H : ObstructionPayloadProp o) : PublishObstructionPayload q := existT _ o H.

Record PublishedObstruction := MkPublishedObstruction {
  published_obstruction_at   : StackAt Sampled ;
  published_obstruction_path : AnalysisPath ;
  published_obstruction_kind : ObstructionPayload published_obstruction_at ;
  published_obstruction_thm  : StackProp Sampled published_obstruction_at ;
  published_obstruction_pf   : ObstructionPayloadProp
                                 published_obstruction_kind }.

Definition publish_obstruction (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (p : PublishObstructionPayload q)
    : PublishedObstruction :=
  @MkPublishedObstruction q
    (@MkAnalysisPath (sp_obs q) AnalysisBridged (sp_f q) NegativeTransfer a)
    (projT1 p) pf (projT2 p).
```

plus the six coordinate equations `publish_obstruction_completionE`
(`= AnalysisBridged`), `_transferE` (`= NegativeTransfer`), `_modelE`
(`= sp_f q`), `_observedE` (`= sp_obs q`), `_assumptionsE` (`= a`) and
`_kindE` (`= o`), each `Proof. exact: erefl. Qed.`, and the three readers
`obstruction_of`, `run_correct_of_obstruction`,
`view_identification_of_obstruction`. `Arguments ... : clear implicits` on the
three record projections whose type unfolds to a quantified statement, on
`mk_obstruction`, on `publish_obstruction` and on the three readers.

Header: one new paragraph after the paragraph on the two terminals below the
bridge, thirteen new `Definitions:` entries and eleven new `Key results:`
entries. No existing header line changed.

### `manifest/pgg_tableau_syntax.v` (+22/-7 lines, compile 4.0 s)

```coq
Notation "s |> 'publish' 'Obstruction' o 'by' pf a" :=
  (s ;;; publish_obstruction a of (mk_obstruction (tableau_at s) o pf))
  (at level 90, left associativity, o at level 0, pf at level 0,
   a at level 0).
```

The keyword paragraph's last two sentences were rewritten (header prose, the
one rewrite the brief allows) to record `Obstruction` as a third token of the
`publish` position. **Measurement, 2026-09-21**, in
`landing_draft_keyword.v`, whose Require lines are `ssreflect` and the surface
alone: `Definition obstruction_binder_check (Obstruction : nat) : nat :=
Obstruction.` and `Definition Obstruction : nat := 0.` both compile, and
`Check Obstruction.` prints `Obstruction : nat`. The reserved count stays
nineteen.

### `instances/psl211/psl211_reading_constancy.v` (+183 lines, compile 21.6 s)

New section "How far apart the two chiralities of one deal are read", placed
immediately after `psl211_alldecks_no_zero_eps_cert` and before the word-model
section.

```coq
Lemma psl211_perdeck_static_mass_true (R : realType) :
  (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
       psl211_perdeck_coalition (true, psl211_perdeck_deal))
     ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view = 0 :> R.

Lemma psl211_perdeck_static_mass_false (R : realType) :
  (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
       psl211_perdeck_coalition (false, psl211_perdeck_deal))
     ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view
  = (#|pgg_G psl211_M|%:R)^-1 :> R.

Theorem psl211_alldecks_perdeck_reading_ge (R : realType) :
  (#|pgg_G psl211_M|%:R)^-1 <=
  var_dist
    (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
         psl211_perdeck_coalition (true, psl211_perdeck_deal))
       (sa_cut_dist (psl211_alldecks_sample R)))
    (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
         psl211_perdeck_coalition (false, psl211_perdeck_deal))
       (sa_cut_dist (psl211_alldecks_sample R))).

Theorem psl211_alldecks_input_distinguishability (R : realType) :
  InputDistinguishabilityPropAt (psl211_alldecks_sample R)
    ((#|pgg_G psl211_M|%:R)^-1).

Corollary psl211_alldecks_indistinguishability_number_ge (R : realType)
    (cert : IndistinguishabilityCert (psl211_alldecks_sample R)) (c : R) :
  IndistinguishabilityPropAt cert c -> (#|pgg_G psl211_M|%:R)^-1 <= c.
```

The two mass proofs and the two mass substitutions inside the core are the
probe's term-mode forms verbatim (`etrans`/`congr1`/`eq_ind`); the recorded
228 s cost of the rewrite form is kept as a source comment. Header: one new
paragraph and five new `Key results:` entries.

### `instances/psl211/tableau/psl211_tableau_analysis_bridged.v` (+143/-4, compile 4.5 s)

One Require line added (`From pgg_smc Require Import psl211_reading_constancy.`;
`Require Import` is not transitive and the core is declared there), then:

```coq
Definition psl211_alldecks_obstruction
  : ObstructionPayload (tableau_at psl211_exact_sampled) :=
  fun (R : realType) (idx : unit) =>
    @InputDistinguishabilityObstruction R psl211_algebra
      psl211_alldecks_params (amf_sample psl211_exact_family R idx)
      ((#|pgg_G psl211_M|%:R)^-1).

Definition psl211_alldecks_obstruction_pf
  : ObstructionPayloadProp psl211_alldecks_obstruction :=
  fun (R : realType) (_ : unit) => psl211_alldecks_input_distinguishability R.

Definition psl211_alldecks_obstruction_published : PublishedObstruction :=
  psl211_exact_sampled
    |> publish Obstruction psl211_alldecks_obstruction
       by psl211_alldecks_obstruction_pf BaselineClassicalOnly.

Lemma psl211_alldecks_obstruction_published_pathE :
  published_obstruction_path psl211_alldecks_obstruction_published
  = @MkAnalysisPath PSL211Analysis.observed AnalysisBridged
      PSL211Analysis.exact_family NegativeTransfer BaselineClassicalOnly.
Proof. exact: erefl. Qed.

Lemma psl211_alldecks_obstruction_published_path_observedE :
  ap_observed
    (published_obstruction_path psl211_alldecks_obstruction_published)
  = ap_observed psl211_alldecks_path.
Proof. exact: erefl. Qed.

Lemma psl211_alldecks_obstruction_published_path_transfer_neq :
  ap_transfer
    (published_obstruction_path psl211_alldecks_obstruction_published)
  <> ap_transfer psl211_alldecks_path.
Proof. by []. Qed.

Theorem psl211_alldecks_published_input_distinguishability (R : realType) :
  InputDistinguishabilityPropAt (amf_sample psl211_exact_family R tt)
    ((#|pgg_G psl211_M|%:R)^-1).
Proof. exact: (obstruction_of psl211_alldecks_obstruction_published R tt). Qed.
```

The statement comment at `psl211_alldecks_obstruction_published` carries the
four points of the audit's section "What the landed comment must say about the
manifest", names `psl211_alldecks_no_small_eps_cert` and states how the two
relate, gives the quantifier reason (audit D5) for the absence of conflict
with `psl211_alldecks_published`, and says that `var_dist` is the sum of
absolute differences, twice the literature's total variation, so a
distinguisher's advantage at those two run arguments is at least 1/1320.
Header: the "No input-indistinguishability program is published" paragraph
gained three sentences, plus three `Definitions:` and four `Key results:`
entries.

### `instances/psl211/tableau/psl211_tableau_checks.v` (+35/-6, compile 4.1 s)

A fourth recorded-boundary section with two rejections, each compiled once
without `Fail` in its own probe file
(`landing_draft_reader_secrecy_nofail.v`, `landing_draft_reader_property_nofail.v`;
messages kept as `landing_draft_reader_secrecy.msg` and
`landing_draft_reader_property.msg` in this directory):

```
Fail Check (view_secrecy_of r).          (* r : PublishedObstruction *)
Fail Check (security_property_of r).
```

Message of the first, verbatim:

```
File "./notes/probes/2026-09-21-refutations/landing_draft_reader_secrecy_nofail.v",
line 21, characters 23-24:
Error:
In environment
r : PublishedObstruction
The term "r" has type "PublishedObstruction"
while it is expected to have type "PublishedAt ?c".
```

Message of the second is the same three lines, at
`line 21, characters 28-29`. Per audit D6 the landed comment states the type
fact as the claim and cites the two terms as the two spellings checked. The
header's "Three boundaries are recorded" became "Four".

### `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` (+32, compile 6.9 s)

```coq
Theorem pgl27_word_input_distinguishability_false (R : realType)
    (secretP : R.-fdist bool) (c : R) :
  2%:R^-39 < c ->
  InputDistinguishabilityPropAt (amf_sample pgl27_word_family R secretP) c ->
  False.
```

proved from `view_indistinguishability_of pgl27_word_published39 R secretP`
ascribed at `IndistinguishabilityPropAt (pgl27_word_cert secretP) (2%:R^-39)`,
then the framework's number bound. One new `Key results:` entry.

## Verification

`notes/probes/2026-09-21-refutations/landing_fidelity.v`, production Requires
only, compile 45.8 s: every landed declaration is `Check`ed at its full
statement (the two definitional unfoldings, `InputDistinguishabilityPropAt`
and `ObstructionProp` at the one constructor, by `erefl`), the surface rule is
checked to expand to the bind it claims, and five `Print Assumptions` are run.

All five print exactly:

```
Axioms:
propositional_extensionality
functional_extensionality_dep
constructive_indefinite_description
```

for `psl211_alldecks_perdeck_reading_ge`,
`psl211_alldecks_indistinguishability_number_ge`,
`psl211_alldecks_obstruction_published`,
`psl211_alldecks_published_input_distinguishability` and
`pgl27_word_input_distinguishability_false`.

Line width: no line above 80 bytes in any edited file except the three
pre-existing `Notation` lines of `pgg_tableau_syntax.v` (347, 385, 416).

### Drafts compiled before any production file was touched

| draft | what it held | compile |
|---|---|---|
| `landing_draft_framework.v` | the whole framework text | 12 s |
| `landing_draft_psl211.v` | the constancy-file text, plus the D4 `Check` | 20 s |
| `landing_draft_syntax.v` | the surface rule, with the other two publish rules beside it | 4 s |
| `landing_draft_keyword.v` | the `Obstruction` keyword measurement | 2 s |
| `landing_draft_tableau.v` | the psl211 program and the PGL(2,7) lemma | 45.7 s |

D4's first step, run in `landing_draft_psl211.v` and passing:

```coq
Check (fun R : realType =>
  erefl : psl211_alldecks_sample R = amf_sample psl211_exact_family R tt).
```

### Unedited production files recompiled (all green, in this order)

`manifest/pgg_tableau.v` (edited) 12.5 s, `manifest/pgg_tableau_syntax.v`
(edited) 4.0 s, `instances/psl211/psl211_reading_constancy.v` (edited) 21.6 s,
then unedited `instances/psl211/tableau/psl211_tableau_algebraic.v` 3.7 s,
`psl211_tableau_executable.v` 3.6 s, `psl211_tableau_observed.v` 4.6 s,
`psl211_tableau_sampled.v` 3.6 s, then the edited
`psl211_tableau_analysis_bridged.v` 4.5 s and `psl211_tableau_checks.v` 4.1 s;
then unedited `instances/pgl27/tableau/pgl27_tableau_algebraic.v` 3.6 s,
`pgl27_tableau_executable.v` 3.5 s, `pgl27_tableau_observed.v` 3.7 s,
`pgl27_tableau_sampled.v` 3.6 s, then the edited
`pgl27_tableau_analysis_bridged.v` 6.9 s. One Rocq process at a time,
always through the `rocq1` wrapper. `make` was never run. No file of the
frozen `psl211_endpoints` closure was compiled or edited;
`manifest/pgg_analysis_manifest.v` was not edited. The rest of the reverse
closure of `manifest/pgg_tableau.v` is left to the main session.

## Departures from the plan, with reasons

1. **The number bound sits inside the new section, not literally beside
   `psl211_alldecks_no_small_eps_cert`.** The audit's placement table asks for
   the core "appended" and the number bound "beside
   `psl211_alldecks_no_small_eps_cert`". The number bound depends on the core
   and the core depends on the two mass lemmas, so the four cannot be split
   across that theorem without moving it. The whole block was inserted
   immediately after `psl211_alldecks_no_zero_eps_cert`, which is the end of
   the certificate-exclusion section and three declarations below
   `psl211_alldecks_no_small_eps_cert`; it is still a pure addition and the
   word-model section follows it unchanged.
2. **A Require line was added to
   `instances/psl211/tableau/psl211_tableau_analysis_bridged.v`.** The plan
   did not mention it. `psl211_reading_constancy` is required by
   `psl211_tableau_executable` but `Require Import` is not transitive, so
   `psl211_alldecks_input_distinguishability` was not in scope.
3. **The PGL(2,7) lemma's proof ascribes the reader's type.** Written as
   `indistinguishability_number_ge_of_input_distinguishability Hd
   (view_indistinguishability_of pgl27_word_published39 R secretP)` the
   application left the certificate argument unresolved, and the error was
   `The term "Hge" has type "IndistinguishabilityCert (...) -> c <= odflt ..."
   while it is expected to have type "is_true (c <= ?z)"`. Naming the reader's
   proposition first, at `IndistinguishabilityPropAt (pgl27_word_cert secretP)
   (2%:R^-39)`, fixes the certificate and reduces `odflt _ (pgl27_bound39 R)`
   to the constant, which also puts the number in the proof text. This was the
   only failed attempt in the landing.
4. **`var_dist_xx` and `pgl27_word_cert_ideal_uniform` were not landed.** The
   audit's placement table notes that with the law anchored the PGL(2,7)
   non-vacuity statement changes shape and needs no `var_dist d d = 0`; under
   decision 2's certificate-free proposition it needs neither lemma. Both names
   stay free.
5. **`ObstructionPropOf` and `RefutePayload` are landed as
   `ObstructionPayloadProp` and `PublishObstructionPayload`**, per the audit's
   name table given the terminal's rename to `publish_obstruction`.
6. **No `Print Assumptions` line is landed in production.** Audit D14. The
   evidence lives in `landing_fidelity.v` and in the path's
   `BaselineClassicalOnly`.

## What is left

The main session's step 5: recompile the reverse closure of
`manifest/pgg_tableau.v` (`pgg_tableau_security_property_relations`,
`pgg_tableau_reading`, `pgg_tableau_marginal_bounds`, the s5 and kim2025
tableau directories, `psl211_colour_reading`, `pgg_analysis_client` and the
rest), one combined audit, a fix pass, and the commit.
