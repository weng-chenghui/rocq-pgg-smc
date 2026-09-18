# Soundness audit of the sc_const probe, round 1

Independent adversarial audit, 2026-09-19, branch `feat/kim-spectral-probe`.
Audited: `psl211_sc_const_probe.v`, `psl211_sc_const_bound_probe.v`,
`psl211_dealt_sc_const_probe.v`, `psl211_deck_diag.v`, `STATUS.md`. No file of
the repository was edited. Scratch work lives outside the repository at
`scratchpad/psl_audit/` and consists of `audit_word.v`, `audit_diag.v`,
`revdeps.py`, `drive.py`.

**Verdict: NO-GO** for "the probe's statements are true and its English says no
more than they prove".

Every compiled statement I checked is true and correctly typed, and the passage
from the record field to the standalone proposition is definitional in both
directions. The refusal is about the English. Three sentences, one of them a
comment on the headline theorem and one of them the STATUS answer line, assert
that the spectral arm is unavailable at this instance. What is proved is that
the arm is unavailable *at a usable epsilon*. The distinction is not a quibble:
the probe's own Q2 row records an ideal cut that satisfies the constancy field,
so the stronger reading is contradicted inside the probe itself.

A second, larger interpretive gap: the constancy field at the all-decks
parameters fails between two run arguments carrying the **same** secret, by a
larger margin than between the two chiralities. The probe never says this, and
the counterexample it chose makes the failure read as a statement about the
secret, which it is not.

## Findings

| ID | Severity | Claim | Evidence | Recommended change |
|---|---|---|---|---|
| S1 | BLOCKING | `psl211_alldecks_no_spectral_cert`'s comment says the exact arm "is the only arm the model can close". The theorem excludes only certificates with `sw_bound_eps + sw_bound_eps < 1/660`. | `psl211_sc_const_bound_probe.v:283-284` against the theorem at `:285-288`. The unexcluded region is inhabited: `AUDIT-SOUNDNESS-2.md` row 18 argues that the uniform law on the whole of `{perm 'I_12}` satisfies `sc_const`, and its distance from `` `U psl211_G_pos `` is `2*(1 - 660/12!)`, so a certificate at that ideal exists with `sw_bound_eps` near 2. | Replace with "no spectral certificate over this model carries an epsilon below `1/1320`, so the arm can be closed only at a number it is useless to publish". |
| S2 | BLOCKING | `STATUS.md:7-8` answers "no, at the all-decks model, and not for a reason that a different ideal cut can repair". | The same row-18 ideal is a different ideal cut and it does satisfy the field. `STATUS.md:110` itself names that ideal as not excluded, so the document contradicts its own answer line. | Answer line becomes "no, at any epsilon a row could publish". |
| S3 | BLOCKING | The probe reads the all-decks failure as a chirality failure throughout. It is not: the field already fails between two deck descriptions of one chirality, and by a larger margin. | Measured in `scratchpad/psl_audit/audit_diag.v`, `vm_compute` over `psl211_elem_table` and `psl211_alldecks_row`. At block index 0 with identity labellings the L1 gap of the two chiralities' reading multiplicity vectors is 360 of 660 cuts. Between block 0 and block 1 at chirality `true` it is 600 of 660. | Say that the field at the all-decks parameters is deck-constancy, not secret-constancy, and that it fails on a same-secret pair. See Q6. |
| S4 | SHOULD-FIX | `STATUS.md:9` says the field "fails at every ideal supported on the shuffle group". `psl211_alldecks_sc_const_false_supp` needs the ideal to vanish off the group **and** to be nonzero at every element of it. | `psl211_sc_const_bound_probe.v:162-166`. An ideal supported on a proper subset of the group is not covered. | "at every ideal whose support is exactly the shuffle group". |
| S5 | SHOULD-FIX | `STATUS.md:109-110` says "Not excluded: an ideal at variation distance `1/660` or more". The excluded region is `var_dist < 1/1320`. | With `var_dist U ideal = t` the lemma applies at `eps := t` and needs `2t < 1/660`. The abstract at `STATUS.md:10` gets this right and says `1/(2*660)`. | Make the Q3 sentence read `1/1320`, matching the abstract. |
| S6 | SHOULD-FIX | `STATUS.md:193` says both clauses of `psl211_rows.v:40-45` are out of date. Only the second is. | The first clause, the dealt-mode failure at three seats at the group-uniform ideal, is true and is now proved at the field type rather than at the raw count. That is a strengthening, not a correction. | Say the second clause is false and the first is now carried at the field type. |
| S7 | NOTE | `psl211_dealt_sc_const_false` has no certificate-level consequence, because there is no dealt-mode sample adapter in the tree. | `grep MkSampleAdapter instances/psl211/` returns only `psl211_alldecks_sample` at `psl211_models.v:223`. Without an adapter there is no `sc_Hd` to pin a dealt certificate's ideal to `` `U psl211_G_pos ``. | STATUS Q4 should say the dealt result rules out one named ideal and no certificate. |
| S8 | NOTE | The probe proves `#\|psl211_perdeck_coalition\| <= 3` and its prose calls it "the three seats". The cardinal is never proved to be 3. | `psl211_sc_const_probe.v:100-111`. | Harmless. The refutation needs only the upper bound, and the set is visibly a three-element set. |
| S9 | NOTE | The generic `fdist_uniform_close_supp` is proved and then not used. | `psl211_sc_const_bound_probe.v:85-95`, no occurrence downstream. | Keep only if a later statement needs it. The Q2 row already explains why it does not compose here. |
| S10 | NOTE | `psl211_deck_diag.v` carries its output in a comment and produces no `.vo`, so nothing checks that the recorded numbers are the ones the file prints. | Recomputed independently in `audit_diag.v`. All six recorded values match exactly. | None. The record is accurate. |

## Q1. Field fidelity

`sc_const_prop` is the `sc_const` field of `SpectralCert`
(`manifest/pgg_tableau.v:137-142`) with the same coalition quantifier, the same
threshold premise `(#|C| < profile_k (instance_profile A))%N`, the same
`static_coalition_obs` at the same explicit `A` and `E`, the same
`ex_inputT E` quantifier over the two run arguments, and the same carrier
`R.-fdist (pgg_gT (mp_M (instance_profile A)))` for the ideal. The one
difference is that `sc_const_prop` takes the ideal as an argument where the
field reads it off `sc_ideal`, which is what makes it usable against a
hypothetical certificate.

`sc_const_prop_field` is proved by `exact: sc_const cert`. That is enough for
the direction the refutations need, field implies proposition, and because
`exact:` with no further application forces the two types to be convertible it
is in fact an identification and not a one-way implication. I checked the other
direction independently rather than inferring it: `audit_word.v` defines
`audit_mk`, which hands a `sc_const_prop E ideal` to `@MkSpectralCert` in the
`sc_const` slot, and it elaborates. So a proposition and a field are
interchangeable at this type, and a refutation of the proposition is a
refutation of any certificate carrying that ideal. `Set Implicit Arguments` is
on in both files and the argument positions agree.

## Q2. The carrier

`pgg_gT psl211_M` is the ambient `{perm 'I_12}` and `pgg_G psl211_M` is the
660-element subgroup. The probe's correction is right and its statements match
their comments. `psl211_alldecks_sc_const_false_supp` assumes the ideal
vanishes off `pgg_G psl211_M` and is nonzero on all of it, and its comment says
exactly that. `psl211_alldecks_sc_const_false_close` assumes distance to
`` `U psl211_G_pos ``, the group-uniform law, and its comment says so.
`fdist_uniform_close_supp` is stated at `fdist_uniform HT` on an arbitrary
`finType`, which is the ambient uniform law when read at the cut carrier, and
the probe's Q3 row correctly explains that it does not compose with the support
argument, because closeness to the group-uniform law does not force support
inside the group.

Row 18 of `AUDIT-SOUNDNESS-2.md` is represented accurately. Its own arithmetic
uses the half-L1 convention and says the distance is "essentially 1". Under
infotheo's full-L1 `var_dist` that distance is `2*(1 - 660/12!)`, essentially 2,
and the probe gets the convention right everywhere I checked, including the
`1/1320` threshold. What S4 asks for is only that the STATUS prose carry the
second support hypothesis.

One thing the comments do not exclude and should say they do not exclude: the
ambient uniform law is not merely outside the reach of these three lemmas, it
is a positive counterexample to the strong reading. See S1 and S2.

## Q3. Scope of the headline

What is proved, exactly. `psl211_alldecks_no_spectral_cert` says: for every
`cert : SpectralCert (psl211_alldecks_sample R)`, if
`sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert) < (#|pgg_G psl211_M|%:R)^-1`
then `False`. The chain is `sc_Hd` plus `psl211_alldecks_cut_distE` to identify
the bound's law with `` `U psl211_G_pos ``, then `sc_close` to place the ideal
within `sw_bound_eps` of it, then `psl211_alldecks_sc_const_false_close`. The
sample is `psl211_alldecks_sample`, whose cut law is the group-uniform law, and
which already carries the exact arm through `psl211_exact_family` and
`psl211_alldecks_static_indep`. So the headline is about the model that does not
need a spectral arm.

The word row. There is no `psl211` sample adapter whose cut is a weighted word
law. `psl211_word_mixing` (`instances/psl211/psl211_mixing.v:545-548`) states
`var_dist (@rho_from_words_weighted R 10 2 584 psl211_moves psl211_Wuni) (`U psl211_G_pos) <= 2%:R^-40`,
on the carrier `{perm 'I_12}`, which is the cut carrier. `psl211_joint_mixing`
(`instances/psl211/psl211_mixing.v:592-599`) tensors that with an independent
binary secret prior at no cost. Both are stated inside a section fixing `R`.
A word adapter would have `sa_cut_dist = rho_from_words_weighted ...`, and a
certificate over it would carry `sc_Hd` to that law, not to the group-uniform
law, so `psl211_alldecks_cert_ideal_close` does not apply and
`psl211_alldecks_no_spectral_cert` says nothing about it.

Does `psl211_alldecks_sc_const_false_close` already cover the word case by a
triangle inequality? It does, modulo one missing library fact. infotheo's
`variation_dist.v` has `symmetric_var_dist`, `pos_var_dist`, `def_var_dist` and
`leq_var_dist`, and no triangle inequality. I proved it and the corollary in
`scratchpad/psl_audit/audit_word.v`, both `Qed`, both reporting exactly the
three boolp axioms:

    Lemma audit_var_dist_tri (R : realType) (T : finType) (P Q S : R.-fdist T) :
      var_dist P S <= var_dist P Q + var_dist Q S.

    Lemma audit_sc_const_false_word (R : realType) (W ideal : R.-fdist cutT)
        (d eps : R) :
      var_dist ((`U psl211_G_pos) : R.-fdist cutT) W <= d ->
      var_dist W ideal <= eps ->
      (d + eps) + (d + eps) < (#|pgg_G psl211_M|%:R)^-1 ->
      ~ sc_const_prop psl211_alldecks_params ideal.

Instantiated at `d := 2^-40` from `psl211_word_mixing`, this rules out a word
row's certificate whenever `eps < 1/1320 - 2^-40`. The routine unproved step is
the adapter itself, which nobody has built, plus the one-line derivation of
`var_dist (sa_cut_dist sa) ideal <= eps` from that adapter's `sc_Hd` and
`sc_close`. Neither is mathematics, both are construction.

What is NOT excluded. A certificate publishing `cert_eps = 2*eps` of order
`1/660` or larger. That is correct as the brief states it, with the arithmetic
correction of S5: the exclusion runs up to `eps < 1/1320`, so `cert_eps` is
unconstrained from `1/660` upward, against infotheo's L1 ceiling of 2. And the
unexcluded interval is not merely unvisited, it is occupied, by the ambient
uniform ideal of row 18 at `eps` near 2.

Is there an easy argument closing the interval? Not a short compiled one, but
the interval is much smaller than the probe's threshold suggests, and I measured
by how much. Under `` `U psl211_G_pos `` the 660 cuts give 660 **distinct**
readings at seats 0, 1 and 2, so each pushforward law is uniform on 660 atoms of
mass `1/660`. The probe's argument spends one atom and therefore cannot beat
`1/1320` no matter which pair it picks. The whole L1 gap between the two
chiralities' pushforwards at `psl211_perdeck_deal` is `360/660 = 6/11`, and
between two deck descriptions of one chirality it is `600/660 = 10/11`. Since
`sc_const` forces the two pushforwards of the ideal to be equal, and each of
them is within `eps` of its group-uniform counterpart, any certificate must
satisfy `2*eps >= 10/11`, that is `eps >= 5/11` and `cert_eps >= 10/11`. So the
true floor is about 600 times the proved one and sits at half the L1 ceiling.
Turning that into a theorem needs the mass of a 300-reading event rather than of
one reading, which is a fiber count over an explicit reading predicate, a
landing-sized job rather than a short lemma. I did not attempt it. The
measurement is a `vm_compute` diagnostic and not a Rocq theorem, and it is
cross-checked: my `audit_deck` reproduces `psl211_perdeck_seq` at both
chiralities, and the 0-and-1 fiber counts of `psl211_perdeck_raw_countE` are
consistent with all 660 readings being distinct.

## Q4. The counterexample

The threshold premise is discharged for the right set.
`psl211_perdeck_coalition` is `[set i : seatT | val i \in [:: 0; 1; 2]]`,
`psl211_perdeck_coalition_le3` bounds its cardinal by 3 through a three-point
superset and `cardsU1`, and `psl211_perdeck_coalition_below_k` closes
`3 < profile_k (instance_profile psl211_algebra)` by conversion, the derived
threshold being 6 by `profile_k_psl211_algebra`. `seatT` is spelled through the
derived profile in the probe exactly as in `psl211_models.v`, so the coalition
the field quantifies over and the coalition the counting lemmas name are the
same set.

The run-argument pair is legitimate. `ex_inputT psl211_alldecks_params` is
`bool * ('I_132 * {perm 'I_6} * {perm 'I_6})` by `erefl`, checked in
`audit_word.v`, a raw product carrier with no validity predicate anywhere near
the field. Both `(true, psl211_perdeck_deal)` and `(false, psl211_perdeck_deal)`
inhabit it, and validity of a deck description does not depend on the chirality
because there is no notion of validity at this type at all. The chirality enters
only through `psl211_alldecks_row`, which reads a different Steiner table at
each chirality, so one deck description names two different decks. That is the
whole mechanism, and `psl211_deck_diag.v` records it.

The refutation compares across chiralities only. It also fails within one
chirality, and worse. At chirality `true`, block index 0 against block index 1
with identity labellings, the L1 gap of the multiplicity vectors is 600 of 660,
against 360 of 660 across the chiralities at block 0. So the field is false at
these parameters for a reason with nothing to do with the secret. What that
means for the interpretation is in Q6. It does not invalidate anything the probe
proves. It changes what the result is a result about.

## Q5. Dealt mode

`psl211_dealt_sc_const_false` is at the field type:
`~ sc_const_prop psl211_dealt_params ((`U psl211_G_pos) : R.-fdist cutT)`, with
`sc_const_prop` tied to `sc_const` by Q1. `ex_inputT psl211_dealt_params` is
`pga_secretT psl211_algebra`, which is `bool`, because `psl211_dealt_params` is
`dealt_secret_params psl211_algebra psl211_fuel`
(`protocol/pgg_instance.v:398-401`). So under the dealt parameters the field's
two run arguments are the two secrets and nothing else, and the refutation
instantiates them at `true` and `false`.

The `vm_compute` in `psl211_dealt_raw_countE` is a computation over plain `nat`
tables. `psl211_dealt_raw_count b` is
`count (psl211_dealt_test (psl211_dealt_decktbl b)) (unzip1 psl211_elem_table)`,
where `psl211_dealt_decktbl` is a literal twelve-entry `seq nat`,
`psl211_dealt_test` is a conjunction of three `nth`-and-`%% 12` equalities on
`nat`, and `psl211_elem_table : seq (seq nat * seq nat)` is the breadth-first
closure of `instances/psl211/psl211_closure.v:170-171`. The table is left as an
application rather than stored, so `vm_compute` re-runs the search, which is why
the sentence costs 6.9 s. Nothing opaque, nothing extracted, no axiom:
`Print Assumptions psl211_dealt_raw_countE` reports `Closed under the global
context`. The bridge from that count to the field is
`psl211_dealt_fiberE`, `psl211_dealt_massE` and `uniform_fdistmap_pointE`, the
same route `psl211_models.v` uses for the all-decks count, with
`psl211_dealt_raw_viewE` supplying the raw-to-framework identification.

The deck claim of `psl211_deck_diag.v` is true and I recomputed every line of
its recorded output in `audit_diag.v`, with identical results:
`psl211_alldecks_row (true, psl211_perdeck_deal) = [:: 0;1;2;3;4;10]`,
`(false, ...) = [:: 0;1;2;3;4;11]`, `psl211_rep_list true = [:: 2;3;5;7;8;9]`,
`psl211_rep_list false = [:: 0;1;3;7;10;11]`,
`psl211_perdeck_seq true = [:: 0;1;2;3;4;6;7;8;9;10;5;11]` and
`psl211_perdeck_seq false = [:: 0;1;2;3;4;6;7;8;9;10;11;5]`. The encoder deals
its heart codes on the representative row, and that row is not block index 0 of
either table, so the all-decks refutation genuinely does not transport and the
count had to be redone. I also checked `psl211_dealt_decktbl` by hand against
`psl211_rep_list`: at `true`, positions `2,3,5,7,8,9` carry codes `0..5` and the
complement carries `6..11` in ascending order, and the table
`[:: 6;7;0;1;8;2;9;3;4;5;10;11]` has exactly that shape. The `false` table
matches `[:: 0;1;3;7;10;11]` the same way. `psl211_dealt_decktblE` proves this
against `psl211_orbit_encode` by twelve-way case analysis, so the hand check is
redundant and agrees.

The one thing the dealt result does not have is a certificate-level
consequence. See S7.

## Q6. Interpretation

The reading in the brief is close but not quite right, and the correction
matters for the paper.

The exact arm at PSL(2,11) holds for the average over deck descriptions.
`psl211_alldecks_view_indep` and `psl211_alldecks_static_indep` give, for every
coalition of at most five of the twelve seats, independence of the coalition's
reading from the chirality under the all-decks law. That is exact, at every real
field, and it is an average over the `2 * 132 * 720 * 720` deck descriptions and
the 660 cuts. At the same time `psl211_perdeck_law_neq` shows that fixing one
deck description destroys it. Both are true and there is no tension: an average
of laws can be secret-independent while each conditional law is not.

The spectral arm's constancy field is a per-run-argument statement, so it lands
on the conditional laws and fails. That much of the brief is right. What the
brief and the probe both understate is which per-run-argument statement. Under
the all-decks parameters the run argument is the whole deck description, of
which the secret is one of four coordinates. The field therefore asks for
constancy in the block line and in the two labellings as well, and my
measurement shows it already fails on a same-secret pair at a larger margin than
on the cross-secret pair the probe chose. So at the all-decks parameters the
obstruction is a property of how `SpectralCert` is stated. The field demands
deck-constancy where a mixed-law privacy argument needs only secret-constancy
after averaging, and no instance whose public run argument determines the deck
can satisfy it.

Under the dealt parameters the picture is different, and this is where the
domain fact lives. There `ex_inputT` is `bool`, so the field *is* exactly
secret-constancy, and it still fails. Compare PGL(2,7), which certifies the
spectral arm through `pgl27_word_view_const` (`instances/pgl27/pgl27_rows.v`),
proved from `pgl27_view_law_const`, which is three-transitivity of PGL(2,7) read
as a privacy statement for coalitions below four. PSL(2,11) is 2-transitive and
not 3-transitive, so three seats see a reading, cards 0, 1 and 6 at seats 0, 1
and 2, that one chirality's encoder deck reaches under exactly one cut and the
other reaches under none. That is a property of the group and the design, not of
the record.

So the honest answer is that both explanations are correct, for the two modes:

- Dealt mode: the obstruction is PSL(2,11) itself. The field asks only for
  secret-constancy and the group is not transitive enough on triples to deliver
  it.
- All-decks mode: the obstruction is the shape of the field. It asks for
  constancy in a public coordinate the instance never claimed anything about,
  and the exact arm, which asks only about the secret, is closed.

The thing a paper must not do is read the all-decks refutation as leakage.
Three seats learn nothing about the chirality under the all-decks law. That is
`psl211_alldecks_static_indep`, proved, at every real field, for coalitions of
at most five.

An honest sentence: "At PSL(2,11) the all-decks dealer's privacy is exact and
is an average over deck descriptions, so the exact arm closes. The spectral
arm does not, because its certificate asks that a coalition read the ideal cut
the same way at every run argument, and at this instance the run argument is
the public deck description, which the reading depends on even at a fixed
secret. Under the dealer-dealt parameters, where the run argument is the secret
alone, the same field fails for a different and sharper reason: PSL(2,11) is
2-transitive and not 3-transitive, so three seats separate the two chiralities
of the encoder deck."

## Q7. The `psl211_rows.v` header

Lines 40-45 currently read:

> Not claimed. There is no spectral arm for this dealer: a certificate's
> constancy field asks that a coalition's reading of the ideal cut not vary
> with the run argument, which fails at three seats under the dealt mode at the
> group-uniform ideal, and under the all-decks dealer it is a different
> statement nobody has measured.

The last clause is now false. The all-decks statement has been measured and is
false at the group-uniform ideal, at every ideal whose support is exactly the
shuffle group, and at every ideal within `1/1320` of the group-uniform law, and
no certificate over `psl211_alldecks_sample` carries an epsilon below `1/1320`.
The earlier clause is not out of date, contrary to `STATUS.md:193`. It was true
and is now carried at the record's own field type rather than at the raw count.

A landing should replace the whole passage with something of this shape, with
the numbers stated and the scope stated:

> Not claimed. The spectral arm is not available to this dealer at any number a
> row could publish. A certificate's constancy field asks that a coalition below
> the threshold read the ideal cut the same way at every run argument. Under the
> dealer-dealt parameters, where the run argument is the secret, it fails at
> three seats at the group-uniform ideal. Under the all-decks parameters, where
> the run argument is the deck description, it fails at the group-uniform ideal,
> at every ideal supported exactly on the shuffle group and at every ideal
> within `1/1320` of the group-uniform law, so a certificate over this model
> must quote an epsilon of at least `1/1320` against a shuffle whose single-card
> marginal error is zero. It fails at two deck descriptions of one chirality as
> well, so the field is stronger than the secret-independence this row claims
> and its failure is not leakage.

## Q8. Homes

I recomputed the reverse-dependency closures from `.Makefile.rocq.d` with
`scratchpad/psl_audit/revdeps.py`, which expands line continuations, keeps only
`.vo` nodes and takes the transitive closure of the reversed edge set.

| file | reverse-dependants | `psl211_endpoints.vo` in closure |
|---|---|---|
| `security/pgg_collusion_bound.v` | 105 | **yes** |
| `reconstruct/design_privacy.v` | 11 | no |
| `instances/psl211/psl211_models.v` | 9 | no |
| `instances/psl211/psl211_rows.v` | 0 | no |

The `pgg_collusion_bound.v` proposal violates the rule. Its closure contains
`instances/psl211/psl211_endpoints.vo`, which is the 900 s and 17 GB file, and
also the whole of `pgl27`, `kim2025`, `s5`, the manifest layer and the legacy
tree. The sibling probe's count of 105 is confirmed exactly. Landing
`var_dist_point_le` and `fdist_uniform_close_supp` there costs a near-total
rebuild.

Compliant homes. `reconstruct/design_privacy.v` is compliant as the rule is
stated, with 11 reverse-dependants and no `psl211_endpoints` among them, and it
is already the probe's choice for `fdistmap_point_condE`. `psl211_models.v` is
cheaper still at 9 and is already the probe's choice for the instance lemmas.
Both would need a new `From infotheo Require Import variation_dist`, which
neither has today. My recommendation: put all three generic lemmas in
`reconstruct/design_privacy.v`, since the two `var_dist` facts are about
infotheo and not about this instance, and accept the two extra rebuilt files
over `psl211_models.v`. If the rebuild of `psl211_analysis.v` and
`psl211_secrecy.v` turns out to be expensive, `psl211_models.v` is the fallback
and nothing is lost but generality.

The rest of the Q6 table is compliant. `psl211_rows.v` has zero
reverse-dependants and is the right place for the manifest-typed statements,
for the reason the probe gives: `psl211_models.v` deliberately imports nothing
from the manifest layer and `SpectralCert` lives there. Anything landing in
`psl211_rows.v` should also carry the `sc_const_prop` restatement itself, which
today lives only in the probe.

## What a paper may and may not say

- May say: at PSL(2,11) under the all-decks dealer, a coalition of at most five
  of the twelve seats reads nothing about the chirality, exactly, at every real
  field. That is `psl211_alldecks_static_indep`, and it is the row that is
  published.
- May say: no spectral certificate over that model carries a shuffle bound below
  `1/1320`, so the spectral arm cannot publish a number worth publishing there,
  while the exact arm closes with no number at all. That is
  `psl211_alldecks_no_spectral_cert`, stated at its own hypothesis.
- May say: under the dealer-dealt parameters, where the run argument is the
  secret itself, the constancy field fails at three seats at the group-uniform
  ideal, and the reason is that PSL(2,11) is 2-transitive and not 3-transitive,
  which is the contrast with PGL(2,7)'s certified spectral row.
- May not say: that no spectral certificate exists at this instance. The probe
  excludes a range of epsilon, and its own Q2 row names an ideal outside that
  range which satisfies the field.
- May not say: that the failure of the constancy field is leakage, or that three
  seats learn the chirality. Under the all-decks law they do not, and the field
  fails on two deck descriptions of one chirality as well.
- May not say: that the word row is excluded. No weighted-word adapter exists
  for PSL(2,11), and the corollary that would exclude one, proved in this audit
  as `audit_sc_const_false_word`, still only reaches `eps < 1/1320 - 2^-40`.

## Scratch record

- `scratchpad/psl_audit/audit_word.v`, rc 0, 12.5 s. Field fidelity in both
  directions, the `ex_inputT` carrier check, the variation-distance triangle
  inequality, the word-row corollary. Both lemmas `Qed` with exactly the three
  boolp axioms.
- `scratchpad/psl_audit/audit_diag.v`, rc 0, 12.0 s. The six recorded values of
  `psl211_deck_diag.v`, all matching. 660 distinct readings at one deck. L1 gap
  360 across chiralities at one deck description, 600 between two deck
  descriptions of one chirality.
- `scratchpad/psl_audit/revdeps.py`. Reverse-dependency closures from
  `.Makefile.rocq.d`.
