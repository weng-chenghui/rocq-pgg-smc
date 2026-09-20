# Refutations: a program that publishes an obstruction (spec for a probe, 2026-09-21)

Tracker step 4.2. Parent: `notes/20260919-tableau-three-extensions-probe-design.md`,
section "What this batch leaves, by phase", group "Refutations and other
dealers". The owner is away; the design decisions below are the main
session's, each with its reason, and can be overturned.

## The problem

The tree proves negative facts about models, and the Tableau can say none of
them. `TransferStatus` has a constructor for them, `NegativeTransfer` ("a
theorem transporting an obstruction to the path's observer",
`manifest/pgg_analysis_status.v`), and no path and no program uses it.

- Already at a program's model and at the coalition's static reading:
  `psl211_alldecks_constancy_false` and `psl211_alldecks_constancy_false_close`
  (`instances/psl211/psl211_reading_constancy.v`): at the PSL(2,11) all-decks
  execution the constancy of a coalition's reading in the run argument fails
  under the group-uniform cut law, and under every ideal within `eps` of it
  when `eps + eps` is below the reciprocal of the group order. Constancy is the
  field `ic_const` of an input-indistinguishability certificate, so these
  theorems say that a whole class of certificates over that execution does not
  exist; nothing states that consequence.
- At a dealer model and at no sample adapter:
  `psl211_fixed_deal_view_dep`, `psl211_dealer_view_indep_of_deck_unsat`,
  `psl211_perdeck_law_neq` (`instances/psl211/psl211_models.v`).
- Positive theorems under other dealer laws, with no model family:
  `pgl27_view_indep_alldecks`, `pgl27_view_indep_deck`,
  `pgl27_view_indep_deck_prior` (`instances/pgl27/pgl27_secrecy.v`).

Why it matters: a reader of the manifest sees which security property each
program certifies and cannot see which properties are REFUTED at a model. At
PSL(2,11) the all-decks program certifies exact independence; that an
input-indistinguishability certificate with a near-uniform ideal cannot exist
there is the reason the instance publishes no such program, and today that
reason is a comment.

## What the phases say (placement)

Tracker step 4.3 decided that a terminal hands over exactly the proposition of
its level, and that a status naming a theorem may be published only from a
level whose proposition contains that theorem. A refutation is a theorem about
a model and the coalition's reading, so it lives where such theorems live,
above `Sampled`. It is NOT security evidence: the three constructors of
`SecurityEvidence` are security properties a program certifies, and an
obstruction certifies none. So:

- no fourth constructor of `SecurityEvidence`, and `StackAt AnalysisBridged` is
  unchanged (every program keeps its type);
- a record beside the published records, `PublishedObstruction`, holding a
  program's data at `Sampled`, its path (level `AnalysisBridged` in the
  manifest's own sense: a theorem about the model's distribution and the
  observer; transfer status `NegativeTransfer`, fixed by the terminal), and
  the obstruction's proposition with its proof;
- the obstruction proposition is not free-form: it is one of a small, named
  family of propositions about the model, each the NEGATION of something a
  security property's evidence would need. First and only member in this
  batch: `NoIndistinguishabilityCertNear sa eps` := no
  `IndistinguishabilityCert sa` has its ideal within `eps` of the group-uniform
  law (stated with `var_dist`, the sum of absolute differences);
- a terminal `refute` from `Tableau Sampled` with the obstruction as payload.

Rejected: publishing `NegativeTransfer` from `publish_sampled` (4.3 refused it:
the Sampled proposition contains no obstruction); a free `Prop` payload (that is
`restate`, and a reader could not tell what kind of fact was published).

## Scope of this batch

In: the framework record, proposition and terminal; the PSL(2,11) all-decks
obstruction derived from `psl211_alldecks_constancy_false_close`; its program;
whether the manifest gains a twelfth path for it (ledger row N6 decides, the
landing does not touch the manifest unless N6 says the path is honest).

Out, with what each needs: the three dealer-model theorems need a model family
and a link lemma each (the size of landings 3 and 4 of 2026-09-20); the three
PGL(2,7) theorems under other dealers are positive and need model families of
their own (they are exact-independence programs, not refutations). They are
recorded in the tracker as separate units.

## Pinned carrier

`R : realType`, `A : PGGAlgebraic`, `E : ExecutionParams A`,
`sa : SampleAdapter R (instance_exec E)`; instance: `psl211_alldecks_params` and
the all-decks model family of `instances/psl211/tableau/psl211_tableau_sampled.v`.

## Claim ledger

| id | Claim | Passing means |
|---|---|---|
| N1 | `NoIndistinguishabilityCertNear sa U eps : Prop := forall cert : IndistinguishabilityCert sa, var_dist U (ic_ideal cert) <= eps -> False` typechecks at the pinned carrier, `U` a law on the cut group | `Definition`; monotone in `eps` downward (`Qed`) |
| N2 | General lemma: `~ coalition_reading_constancy E ideal` for every ideal within `eps` of `U` gives `NoIndistinguishabilityCertNear sa U eps` (the certificate's `ic_const` is that constancy at `ic_ideal cert`) | `Qed`; check that `ic_const`'s statement and `coalition_reading_constancy` are the same proposition (conversion, or a one-line bridge), and say which |
| N3 | At PSL(2,11): with `eps + eps < (#|G|)^-1`, `NoIndistinguishabilityCertNear (all-decks sample) (group-uniform) eps`, from `psl211_alldecks_constancy_false_close` | `Qed`; the adapter is the all-decks family's own; `Print Assumptions` |
| N4 | Non-vacuity both ways: (a) the class refuted is inhabited at OTHER models (at PGL(2,7) `pgl27_word_cert`'s ideal IS within its epsilon of the uniform law, so the proposition is false there: compile `~ NoIndistinguishabilityCertNear` at the PGL(2,7) word model for a suitable eps); (b) at PSL(2,11) the statement does not refute certificates with a far ideal: say so, and that the constancy theorem bounds how far | (a) `Qed`; (b) a sentence backed by the hypothesis `eps + eps < 1/|G|` |
| N5 | `PublishedObstruction` record, terminal `refute`, path equations by conversion (`ap_completion = AnalysisBridged`, `ap_transfer = NegativeTransfer`, model slot the program's family); a reader `obstruction_of`; no security reader applies (type mismatch, message read) | compiled; messages quoted |
| N6 | Is a manifest path at `NegativeTransfer` for this obstruction HONEST by the manifest's own header (read its definition of the level and of the status, and its duty paragraphs)? If yes, the path's five coordinates and its prose table entry are drafted in the probe (not landed by the probe). If no, the program is published without a manifest twin and the landing says why | a reasoned answer with the header quoted |
| N7 | Surface: `s |> refute P by pf` or a form the measured keyword rule allows without reserving a keyword; the existing rules still parse | measured as `manifest/pgg_tableau_syntax.v`'s header demands |
| N8 | The PSL(2,11) program: the all-decks Sampled value `|> refute ...`; its reader gives N3's statement | compiled; `Print Assumptions` equal to N3's |

## Soundness invariants

- Pure additions; no existing declaration changes; `SecurityEvidence` keeps
  three constructors.
- A `PublishedObstruction` certifies no security property and refutes only the
  class its proposition names; the all-decks program's exact-independence
  evidence is untouched by it, and the comments say that the two facts are
  about one model and do not conflict.
- A refutation of certificates near the uniform ideal is not a refutation of
  input indistinguishability itself: the proposition
  `IndistinguishabilityPropAt` might still hold at some number; what is refuted
  is a route to proving it. The statement comments say so. If the probe can
  ALSO refute the proposition at a number (from `psl211_perdeck_law_neq`-style
  facts at the all-decks model), that is a stronger second member of the
  family: ledger row N9, optional.
- `var_dist` is the sum of absolute differences, twice the literature's total
  variation.

## Procedure

Probe directory `notes/probes/2026-09-21-refutations/`: `n_framework.v`,
`n_psl211.v`, `n_pgl27_nonvacuity.v`, `n_syntax.v`, message files, `LEDGER.md`.
Two audits before a landing plan. Landing homes, if GO: `manifest/pgg_tableau.v`
(record, terminal, reader) or a new leaf file above it if the framework file
should not grow (the audits decide), `manifest/pgg_tableau_syntax.v`,
`instances/psl211/tableau/psl211_tableau_analysis_bridged.v`.

## Results of the probe and of the audit; landing plan (2026-09-21)

Probe: `notes/probes/2026-09-21-refutations/` (`LEDGER.md`), all rows compiled,
the six main files recompiled from source by the main session. Audit (soundness,
names, placement in one report): `audit.md` there, GO for a plan with four
things settled first (D1 to D5); its compiled restatements A1 to A10 are in the
scratch file it names and are reused by the landing. The owner is away; the
decisions are the main session's.

### What changed in the claims

1. **The obstruction is a fact about the model, with no certificate in it.** The
   probe's N3 and N9 both quantify over a certificate; N9's certificate is used
   by neither side of its implication, so it is vacuous exactly when the
   certificate type is empty, and inhabitation at this model is argued and not
   compiled (D2). Both follow from one certificate-free core (audit A4): under
   the all-decks model's own cut law, one coalition of three seats reads the two
   chiralities of one deal at least the reciprocal of the group order apart, in
   the sum of absolute differences. The ledger's sentence that N3 and N9 are
   independent is false: N9 gives N3 (D3).
2. **The proposition the framework names is input DISTINGUISHABILITY:**
   `InputDistinguishabilityPropAt sa c := exists C x x', #|C| < profile_k /\
   c <= var_dist (reading of C at x under the cut law) (reading at x')`. It is
   the quantitative negation of the input-indistinguishability proposition, is
   certificate-free and non-vacuous by construction, and gives both corollaries
   at framework level: every number at which the input-indistinguishability
   proposition holds is at least `c`; and no input-indistinguishability
   certificate has its ideal within `eps` of the MODEL'S OWN cut law when
   `eps + eps < c` (the law is anchored: no free law argument, D1). The second
   uses the general form of the tail lemma, landed beside
   `indistinguishability_tail` as a pure addition (audit A8):
   closeness of the ideal at `eps` gives the proposition at `eps + eps`.
3. **`ObstructionKind` has one member, `InputDistinguishabilityObstruction c`.** A
   closed variant and not a free proposition: a reader of a published
   obstruction must be able to tell what kind of fact it is. A second member is
   a later pure addition.
4. **The terminal belongs to the publish family:** `publish_obstruction`, surface
   `s |> publish Obstruction o by pf a` (the obstruction where the other rules
   write the transfer status, the assumption status last, D11, D27).
   `Obstruction` follows a literal; the keyword measurement is re-run and the
   syntax header's sentence about the publish position gains the token.
5. **No manifest path in this batch.** The path the terminal builds is honest
   on all five coordinates (the manifest's own definition of the level admits a
   limitation theorem about the same distribution and the same observer; the
   status is defined as a theorem transporting an obstruction to the path's
   observer). The manifest's closed capability vocabulary has no label for a
   limitation, and extending it is the owner's call. The landed comment at the
   published program says exactly the four points of the audit's section "What
   the landed comment must say about the manifest"; the owner's reminder lists
   the decision.
6. **Non-vacuity at another model:** at the PGL(2,7) word model the proposition
   is FALSE at every `c` above 2^-39, from
   `pgl27_word_view_indistinguishability` (or the published word program's
   reader). This replaces the probe's N4(a) and needs no `var_dist d d = 0`.
7. **The existing theorem `psl211_alldecks_no_small_eps_cert` is named in the
   landed comment and its relation stated** (it is the anchored corollary at the
   certificate's own marginal bound); it is not edited (D4). The non-conflict
   with the exact-independence program is explained by the quantifier (the deal
   is drawn in one, two run arguments are fixed in the other), not by counting
   coordinates (D5).
8. All other findings (D6 to D26) are accepted with the audit's replacements;
   names as the audit's table, adapted to decision 2's proposition
   (`InputDistinguishabilityPropAt`, `input_distinguishability_prop_le` for
   monotonicity downward in `c`, `indistinguishability_prop_of_ideal_close`,
   `indistinguishability_number_ge_of_input_distinguishability`,
   `no_indistinguishability_cert_ideal_close_of_input_distinguishability`,
   `psl211_alldecks_perdeck_reading_ge`, `psl211_alldecks_input_distinguishability`,
   `psl211_alldecks_indistinguishability_number_ge`,
   `psl211_alldecks_obstruction_published` with `_pathE`,
   `pgl27_word_input_distinguishability_false`), each checked free at the
   landing.

### Placement (the audit's table)

Framework record, kind, payload, terminal, six path equations, reader, the
proposition and its two corollaries, the general tail lemma:
`manifest/pgg_tableau.v`, a new section after "Handing a program over below
AnalysisBridged". Surface rule and payload builder: `manifest/pgg_tableau_syntax.v`.
The core and the two mass lemmas (term-mode proofs kept: the rewrite form costs
228 s), the distinguishability statement and the number bound:
`instances/psl211/psl211_reading_constancy.v`, appended. The payload, the
published program and its path equation:
`instances/psl211/tableau/psl211_tableau_analysis_bridged.v`. Two recorded
rejections of security readers: `instances/psl211/tableau/psl211_tableau_checks.v`.
The PGL(2,7) non-vacuity lemma:
`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v`.

### Order of work (after the landing of tracker 4.1 and 4.4 is committed)

1. Probe directory: the redesigned shapes compiled first
   (`landing_draft_framework.v`, `landing_draft_psl211.v`,
   `landing_draft_pgl27.v`, the keyword re-measurement, message files for every
   landed `Fail`). Land only what compiled.
2. `manifest/pgg_tableau.v`, `manifest/pgg_tableau_syntax.v`; compile.
3. `instances/psl211/psl211_reading_constancy.v`, the psl211 phase files, the
   PGL(2,7) file; compile in dependency order.
4. `landing_fidelity.v` (production only), `Print Assumptions` of the core, the
   number bound and the published program: the three classical axioms.
5. Main session: closure, fidelity, one combined audit, fix pass, commit.
