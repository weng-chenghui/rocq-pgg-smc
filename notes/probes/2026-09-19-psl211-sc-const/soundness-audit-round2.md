# Soundness and statement-comment audit of the sc_const probe, round 2

Independent adversarial audit, 2026-09-19, branch `feat/kim-spectral-probe`,
after the fix pass. Audited: `psl211_sc_const_probe.v`,
`psl211_sc_const_bound_probe.v`, `psl211_dealt_sc_const_probe.v`,
`psl211_deck_diag.v`, `STATUS.md`, each against the sources it names and
against `history/`. No file of the repository was edited except this one.
Scratch work lives outside the repository at `scratchpad/psl_audit2/`
(`revdeps2.py`, written for this pass). No Rocq process was started: the
axiom and compile evidence is read off the fix pass's own verification logs in
`scratchpad/psl_verify/`, which were produced from copies of the sources.

**Verdict: NO-GO** for "the probe's statements are true and its English says
no more than they prove".

Every compiled statement I checked is true, correctly typed and carries only
the three boolp axioms. The two new lemmas of the fix pass are sound, and so
is the same-chirality result the round 1 audit asked for. The refusal is
again about the English, and it is small: one statement comment names the
wrong field of `SpectralCert`, and three sentences deny something the probe
itself proves, namely that the constancy field also fails when the chirality
moves. Both are one-clause fixes. Round 1's ten findings are otherwise
disposed of correctly, and the home proposals now satisfy the project rule,
which I recomputed from the dependency file with my own script.

## 1. Disposition of round 1

| round 1 | severity then | state now | evidence |
|---|---|---|---|
| S1 "the only arm the model can close" | BLOCKING | **resolved** | The sentence is gone. `history/psl211_sc_const_bound_probe.2026-09-19-before-fix.v:283` still carries it; the current comment at `psl211_sc_const_bound_probe.v:292-298` states the numeric exclusion only, and the source comment at `:299-305` records that the unexcluded range is occupied and labels that "Argued and not compiled". |
| S2 STATUS contradicting itself on repair | BLOCKING | **resolved** | `STATUS.md:10` now answers "no at any number a row could publish", and `:21-22`, `:139-147` say the range above is occupied and that a different ideal cut does repair the field. Consistent with `:88-91`. See SF8 for a remaining scope gap in "any number". |
| S3 all-decks failure is not about the secret | BLOCKING | **applied, then over-rotated** | Q8 exists and is sound (section 2a). But the fix pass's new wording now denies that the field fails in the chirality, which the same file proves. See B2. |
| S4 dropped support hypothesis | SHOULD-FIX | **resolved in STATUS, survives in the file** | `STATUS.md:16-19` and `:99-103` carry both hypotheses. The statement comment at `psl211_sc_const_bound_probe.v:173-174` still paraphrases them as "any law that sees the group at all". See SF1. |
| S5 1/660 versus 1/1320 | SHOULD-FIX | **resolved** | `STATUS.md:139` now reads "variation distance `1/1320` or more", matching `:134-137` and the abstract. |
| S6 `psl211_rows.v:40-45`, which clause is stale | SHOULD-FIX | **resolved** | `STATUS.md:399-406` says only the last clause is out of date, that the first is a strengthening, and that the opening sentence overstates. |
| S7 no certificate-level consequence in dealt mode | NOTE | **resolved** | `STATUS.md:168-172` and the statement comment at `psl211_dealt_sc_const_probe.v:240-242` both say the dealt result rules out one named ideal and no certificate. |
| S8 cardinal 3 never proved | NOTE | no action, correct | The refutation needs `<= 3` only. |
| S9 `fdist_uniform_close_supp` unused | NOTE | kept, justified | `STATUS.md:520-523`. The lemma's own comment does not say it is unused here; see N3. |
| S10 `psl211_deck_diag.v` records its own output | NOTE | no action, correct | Values re-verified in round 1 and unchanged; the file is byte-identical to `history/`. |

## 2. The new mathematics

### 2a. `psl211_samechir_law_neq`

**At the record field's carrier: yes.** `SpectralCert`'s fifth field
(`manifest/pgg_tableau.v:138-142`) asserts
`fdistmap (static_coalition_obs C x) sc_ideal = fdistmap (static_coalition_obs C x') sc_ideal`.
`psl211_sc_const_probe.v:389-395` is the `!=` of exactly that equation, at
`C := psl211_perdeck_coalition`, `ideal := (`U psl211_G_pos) : R.-fdist cutT`,
`x := (true, psl211_perdeck_deal)`, `x' := (true, psl211_samechir_deal)`, with
the same `@static_coalition_obs psl211_algebra psl211_alldecks_params`, the
same `fdistmap`, and the laws compared at `R.-fdist viewT`. Nothing is
restated at a raw count.

**Below the threshold: yes.** `psl211_perdeck_coalition` is the three seats 0,
1 and 2 (`psl211_models.v:792-793`); `psl211_perdeck_coalition_le3` bounds its
cardinal by 3 and `profile_k (instance_profile psl211_algebra) = 6` by
`profile_k_psl211_algebra` (`instances/psl211/psl211_exec.v:132-134`), so
`psl211_perdeck_coalition_below_k` holds. The lemma itself carries no
threshold premise, which is correct for a statement of the field's equation,
and the premise is discharged in the same file.

**The `vm_compute` runs over plain `nat` tables: yes.**
`psl211_samechir_raw_count sq = count (psl211_samechir_test sq) (unzip1 psl211_elem_table)`.
`psl211_samechir_test` is three `nth`-and-`%% 12` equalities on `seq nat`;
`psl211_elem_table : seq (seq nat * seq nat)` is the breadth-first closure of
`psl211_closure.v`, left as an application, which is why the sentence costs
5.1 s. The two arguments reduced are `psl211_perdeck_seq true` and
`psl211_samechir_seq`, both built from `psl211_alldecks_row` (an `nth` into a
literal `seq (seq nat)`, selected by `psl211_class_tbl true = psl211_mirror_tbl`),
`psl211_alldecks_corow` (a `filter` over `iota 0 12`) and `index`. No
`inord`, no `{ffun _ -> _}`, no `{set _}` and no `{perm _}` occurs in the
reduced term. `psl211_alldecks_seq`, which does apply the two labelling
permutations through `inord`, is never computed: it is tied to the raw list
symbolically by `psl211_samechir_seqE` and `psl211_perdeck_seqE`.

**The comment's reading is right, with one clause to repair.** It is correct
that the constancy field fails with the secret held fixed, and that the
all-decks refutation therefore states no leakage: three seats read nothing
about the chirality under the all-decks law, which is
`psl211_alldecks_static_indep` (`psl211_models.v:503`, from
`psl211_alldecks_view_indep` at `#|C| <= 5`). What the comment must not say is
that the failure is "not of constancy in the chirality": the same file proves
that failure at `psl211_perdeck_deal`, through `psl211_perdeck_law_neq`
(`psl211_models.v:1037-1043`). See B2.

**`(true, psl211_samechir_deal)` is a legitimate element of `ex_inputT`.**
`ex_inputT psl211_alldecks_params` is `psl211_inputT`, the Notation
`bool * ('I_132 * {perm 'I_6} * {perm 'I_6})` (`psl211_alldecks.v:105` and
`:110`), verified by `erefl` in round 1. `@Ordinal 132 1 isT` typechecks because
`1 < 132` reduces to `true`, and `1%g` is the identity of `{perm 'I_6}`.

What the raw product means for the interpretation: the carrier has no
validity predicate anywhere near the field, so the field quantifies over every
tuple, and a refutation may use any of them. Whether a tuple lays a *valid*
deck is a separate question the field never asks. `psl211_alldecks_seq x` is a
bijection of the twelve positions exactly when the indexed block line holds
six distinct positions, and that the parametrization `(j, ph, pc) |-> deck`
enumerates the valid decks of a chirality once each is checked numerically and
not in Rocq (`instances/psl211/psl211_rows.v:48-53`). So the field's
quantifier does reach descriptions nobody has proved lay a deck. The pair this
probe uses does not depend on that: both members lay genuine decks, namely
`[:: 0;1;2;3;4;6;7;8;9;10;5;11]` at `psl211_perdeck_deal` and
`[:: 0;1;2;3;6;4;7;8;5;9;10;11]` at `psl211_samechir_deal`, each a permutation
of `0..11` (`audit-soundness/audit_diag.log.txt:47` and `:53`, the second tied
to `psl211_alldecks_seq` by `psl211_samechir_seqE`). The refutation is therefore
not an artifact of a degenerate description, and a landing may say so.

### 2b. The word lemmas

`psl211_alldecks_sc_const_false_word` (`:348-360`) takes `var_dist (`U psl211_G_pos) W <= d`,
`var_dist W ideal <= eps` and `(d + eps) + (d + eps) < (#|pgg_G psl211_M|%:R)^-1`,
and concludes `~ sc_const_prop psl211_alldecks_params ideal`. The proof is
`var_dist_triangle` (`security/pgg_collusion_bound.v:43-45`, statement
`var_dist P M <= var_dist P Q + var_dist Q M`, exactly what is needed and
already imported at `:41`) then `lerD` then
`psl211_alldecks_sc_const_false_close`. Sound.

`psl211_alldecks_sc_const_false_word584` (`:371-386`) instantiates `d` at
`2%:R^-40` through `symmetric_var_dist` (infotheo
`probability/variation_dist.v:36`) applied to `psl211_word_mixing`
(`instances/psl211/psl211_mixing.v:545-548`), whose statement puts the word
law on the left. The carrier matches:
`@rho_from_words_weighted R 10 2 584 psl211_moves (psl211_Wuni R)` on
`{perm 'I_12}`, which is `cutT`. `2%:R^-40` is `(2^40)^-1`. Sound.

The comment says exactly what is proved: on the cut law, with the closeness of
a would-be certificate as the second hypothesis, and stated there rather than
on a certificate "because no weighted-word SampleAdapter exists in this tree,
so there is no sc_Hd pinning a certificate's ideal to this law". That is
correct: the only adapter in `instances/psl211/` is `psl211_alldecks_sample`.
The currencies are labelled, the `2^-40` as the information-theoretic price of
the finite word and the `eps` as the certificate's own distance field. One
wording item, N6.

## 3. Findings

Line numbers are of the current files. Replacement comment lines are at most
80 bytes; em-dashes cost three bytes each, which the counts below respect.

### BLOCKING

**B1. `psl211_sc_const_probe.v:101-103`. `sc_const` is the fifth field of
`SpectralCert`, not the fourth.**

Current:

    (** sc_const_prop_field — the proposition above is the certificate's fourth
        field read at the certificate's own ideal. Nothing below depends on the
        spelling of the field, so a change to the record surfaces here. *)

`MkSpectralCert` (`manifest/pgg_tableau.v:133-142`) takes `sc_b`, `sc_Hd`,
`sc_ideal`, `sc_close`, `sc_const`, and the record's own comment at `:124-130`
says "Five fields". The fourth field is `sc_close`, the distance field, a
materially different claim from the one this lemma proves. The error is
pre-existing: `history/psl211_sc_const_probe.2026-09-19-before-fix.v:84` has
it too, and round 1 missed it. The same replacement also removes the two
positional pointers the fix pass flagged, "the proposition above" and "Nothing
below", and the maintenance remark, which is meta.

Replacement:

    (** sc_const_prop_field — sc_const_prop is the fifth field of
        SpectralCert read at the certificate's own ideal, so refuting the
        proposition at a law refutes every certificate whose ideal cut is
        that law. *)

**B2. Three sentences deny a failure the probe proves.** The field fails
between the two chiralities at `psl211_perdeck_deal`
(`psl211_alldecks_sc_const_false`, through `psl211_perdeck_law_neq`) and it
fails between two block lines at chirality `true` (`psl211_samechir_law_neq`).
Saying it is "not" the first is false. The true statement is that the failure
does not need the secret to move, and that at these parameters a change of
secret is always also a change of the laid deck, because the chirality selects
the table the block line indexes (`psl211_alldecks.v:117-123`).

B2a. `psl211_sc_const_probe.v:147-152`, current last sentence: "The run
argument of this mode is the public deck description, the field quantifies
over every pair of deck descriptions, and the reading depends on the deck
description already at a fixed chirality, so what fails here is constancy in a
public coordinate and not constancy in the secret." This also carries SF5.

Replacement for the whole block at `:143-152`:

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

B2b. `psl211_sc_const_probe.v:387-388`, current: "so the field's failure at
the all-decks parameters is a failure of constancy in the public block line
and not of constancy in the chirality."

Replacement for `:382-388`:

    (** psl211_samechir_law_neq — at chirality true the deck descriptions
        psl211_perdeck_deal and psl211_samechir_deal send the group-uniform
        cut law to two different laws on what seats 0, 1 and 2 read. This is
        the equation the constancy field asserts, at a pair of run arguments
        carrying the same secret, and it is false, so the field's failure at
        the all-decks parameters does not need the chirality to move: it is
        already a failure of constancy in the public block line. *)

B2c. `STATUS.md:282-284`, current: "The field already fails between two deck
descriptions of one chirality, so the refutation is not a statement about the
secret at all."

Replacement: "The field already fails between two deck descriptions of one
chirality, so its failure does not need the secret to move. No pair of run
arguments varies the secret without varying the laid deck either, because the
chirality selects the table the block line indexes."

### SHOULD-FIX

**SF1. `psl211_sc_const_bound_probe.v:170-174`.** "so any law that sees the
group at all separates the two" is weaker than the lemma's second hypothesis,
which is nonzero at *every* element of the group. This is round 1's S4
reappearing in the comment after being fixed in STATUS.

Replacement:

    (** psl211_alldecks_sc_const_false_supp — no law on cuts whose support is
        exactly the shuffle group satisfies the constancy field. The reading
        psl211_perdeck_view is reached by one cut of the group at the false
        chirality and by none at the true one, so such a law gives that
        reading positive mass at one chirality of psl211_perdeck_deal and
        zero at the other. *)

**SF2. `psl211_sc_const_bound_probe.v:160-161`.** "which is the whole of the
per-deck asymmetry" is false as a measurement: 360 of the 660 cuts separate
the two chiralities at this deck description
(`audit-soundness/audit_diag.log.txt:59`). One reading is the whole of what
the refutation spends, not the whole of the asymmetry.

Replacement for `:158-161`:

    (** psl211_perdeck_fiber_true0 — no cut of the shuffle group carries the
        chirality-true deck of psl211_perdeck_deal to the reading
        psl211_perdeck_view. The false chirality reaches that reading under
        exactly one cut, so one reading already separates the two
        chiralities at this deck description. *)

**SF3. `psl211_sc_const_probe.v:233-236`.** "Under the all-decks law the 660
cuts give these three seats 660 distinct readings at any one deck
description" is a diagnostic stated as fact and generalised from one
measurement. It was computed at `(true, psl211_perdeck_deal)` only
(`audit_diag.v:62`, output 660). It is true, by an argument nothing in the
tree carries: only the identity of PSL(2,11) fixes three of the twelve points,
so `g |-> (g 0, g 1, g 2)` is injective on the 660 cuts, and every valid deck
is a bijection. The file labels its other diagnostics (`:153-160`); this one
should be labelled or dropped.

Replacement for `:232-236`:

    (** psl211_samechir_view — the reading that gives cards 3, 2 and 4 to
        seats 0, 1 and 2, and card 0 to every seat outside the coalition. The
        deck of psl211_perdeck_deal reaches it under exactly one cut and the
        deck of psl211_samechir_deal under none. *)

**SF4. `psl211_sc_const_probe.v:26-29`, header.** "Everything mathematical is
already in instances/psl211/psl211_models.v. What is added here is the
discharge of the threshold premise for those three seats and the transport of
the framework's seat reader to the instance's, which is one congr1 and no
rewrite through the tables." Stale after the fix pass: the file now carries a
second 660-cut count, a fiber bridge at a free deck description, and a count
at a reading `psl211_models.v` does not name.

Replacement text for the paragraph, to be padded to the banner width:

    The counting bridges are those of instances/psl211/psl211_models.v.
    What is added here is the discharge of the threshold premise for those
    three seats, the transport of the framework's seat reader to the
    instance's, and a second count, at a reading and a deck description
    that file does not name.

**SF5. "the public deck description", three sites.** The run argument's first
coordinate is the secret (`psl211_alldecks.v:107-109`, "the secret is fst"),
so calling the whole run argument public says the chirality is public, which
is the opposite of what the row claims. Sites:
`psl211_sc_const_probe.v:16-17`, `psl211_sc_const_probe.v:147` (covered by
B2a), `psl211_sc_const_bound_probe.v:126-127`, `STATUS.md:277`. Write "a
whole deck description, whose first coordinate is the chirality and whose
other three are public", or "the deck description" alone where the
coordinates are not the point. The probe already gets this right at
`psl211_sc_const_probe.v:227-228` and at `:88-91`.

**SF6. `STATUS.md:63-65`.** "The twelve `Print Assumptions` of the four files
report the three boolp axioms eleven times and `Closed under the global
context` once". There are thirteen: four in `psl211_sc_const_probe.v`, seven
in `psl211_sc_const_bound_probe.v`, two in `psl211_dealt_sc_const_probe.v`,
none in `psl211_deck_diag.v`. The fix pass's own logs show twelve `Axioms:`
blocks, each listing `propositional_extensionality`,
`functional_extensionality_dep` and `constructive_indefinite_description` and
nothing else, and one `Closed under the global context`
(`scratchpad/psl_verify/*.log`). The soundness claim is unharmed; the count
is wrong, and the session summary inherited it.

Replacement: "The thirteen `Print Assumptions` of the four files report the
three boolp axioms twelve times and `Closed under the global context` once,
for `psl211_dealt_raw_countE`."

**SF7. `STATUS.md:265-270` and the Q8 row of the homes table at `:364`.**
"`psl211_perdeck_fiberE` as `psl211_samechir_fiberE`, which reads the count at
`psl211_alldecks_seq x`", and the landing instruction "generalised in place
rather than copied". `psl211_alldecks_raw_viewE` is indeed
`psl211_perdeck_raw_viewE` with the deck description free and the same proof,
so that half is accurate. `psl211_samechir_fiberE` is not: it also changes the
target reading, from `psl211_perdeck_view` to `psl211_samechir_view`, and with
it the raw test and the `testE` lemma. A landing that generalises
`psl211_perdeck_fiberE` in place must abstract the reading and its raw test as
well, for instance as one lemma taking `v : viewT`, `test : seq nat -> seq nat -> bool`
and the hypothesis `forall sq t, (psl211_perdeck_raw_view sq t == v) = test sq t`.
Say that, so the landing is not sized as a one-argument generalisation.

**SF8. `STATUS.md:10-11` and `psl211_sc_const_bound_probe.v:295-297`.** "no at
any number a row could publish", supported by "A `SpectralDecay` row publishes
`cert_eps cert`". A row carries a `Reprice`, and `PortProp`
(`manifest/pgg_tableau.v:363-369`) publishes `odflt (cert_eps cert) (c R)`, so
`cert_eps` is the number only when the row does not restate it, as the
manifest's own comment at `:342-344` says. The conclusion survives, because a
repriced number must bound `var_dist` of the two readings under the real cut,
which at the group-uniform law is at least `1/660` by
`psl211_perdeck_massE`, but that step is not compiled and not mentioned. Add
one sentence naming the reprice coordinate and saying which case is proved.

**SF9. `psl211_sc_const_bound_probe.v:128-129`.** "and the refutations take
the instance through the one consequence whose fiber counts psl211_models.v
carries" is proof strategy in a rendered statement comment. Move it to a
source comment; the statement comment keeps the fact and the position, which
the first two sentences already carry.

**SF10. `psl211_sc_const_probe.v:114-116`.** "The bound is read off a
three-point superset and never off an enumeration of the twelve seats, the
ordinal enumeration going through an opaque decision that does not reduce" is
proof strategy in a rendered statement comment, and belongs in a `(* ... *)`
comment under the statement, where the file puts its other reduction warnings.

**SF11. `STATUS.md:21-22` and `:139-147`.** The occupancy of the unexcluded
range is asserted flatly in the answer paragraph and in Q3, while `:88-91`
labels the same fact "argued and not compiled" and the source comment at
`psl211_sc_const_bound_probe.v:299-305` labels it too. A reader lands on the
answer. Carry the label at both places.

**SF12. `STATUS.md:289`.** "The same-chirality failure is proved at the field
type by the fix pass". `psl211_samechir_law_neq` is the field's *equation*
refuted at one pair of run arguments, not a `~ sc_const_prop` statement. Say
that, as `:252-254` already does correctly, or add the four-line corollary
refuting `sc_const_prop psl211_alldecks_params ((`U psl211_G_pos))` from the
same-secret pair, which would be the artifact a paper cites for this claim.

### NOTE

**N1.** `STATUS.md:70` cites `manifest/pgg_tableau.v:137-142` for the
`sc_const` field. The field is `:138-142`; `:137` is `sc_close`.

**N2.** `psl211_sc_const_probe.v:225-226`, "block index one of the
chirality's table". `psl211_samechir_deal` carries no chirality; the table is
selected by the description's first coordinate. "Block line one, both
labellings the identity" says it without the dangling possessive.

**N3.** `psl211_sc_const_bound_probe.v:93-96`, `fdist_uniform_close_supp`.
The comment does not say that the lemma is not spent at this instance, which
`STATUS.md:113-117` explains. One clause would keep a reader from looking for
its consumer.

**N4.** `psl211_dealt_sc_const_probe.v:233-242`. The causal sentence,
"PSL(2,11) is 2-transitive and not 3-transitive, where PGL(2,7) certifies the
same field through `pgl27_word_view_const`", is a domain reading and not the
file's proof, which is a count. It is sound as a reading: 3-transitivity would
make the reading law of three seats the uniform law on ordered triples of
distinct cards at every deck, hence constant in the secret, and
`pgl27_word_view_const` (`instances/pgl27/pgl27_rows.v:224-236`, at
`profile_k pgl27 = 4`) is that argument at PGL(2,7). No change needed; it is
recorded so a later pass does not read it as compiled.

**N5.** `psl211_dealt_sc_const_probe.v:233-234` opens "the uniform law on the
shuffle group is the ideal cut of no spectral certificate" and closes "rules
out one named ideal and no certificate". Both are true, the first about any
certificate over these parameters and the second about a published row, but
the pair reads as a contradiction on a first pass. Naming the two levels in
the first sentence would settle it.

**N6.** `psl211_sc_const_bound_probe.v:366-367`, "This is the statement about
the word model a paper would want a row for", is roadmap in a statement
comment. The rest of that comment is exactly right.

**N7.** `var_dist_point_le` is a duplicate of infotheo's `leq_var_dist`; see
section 5.

## 4. The comment pass, file by file

Read in full, both files, every rendered `(** ... *)` block and every source
`(* ... *)` comment. Beyond the findings above, the comments are accurate and
carry a position: `sc_const_prop` at `:83-91` states the field's domain frame
and its excess over the privacy the instance claims, which is the load-bearing
sentence of the whole probe; `psl211_perdeck_coalition_below_k` at `:130-134`
names the threshold and why the premise must be discharged;
`psl211_alldecks_sc_const_set0` at `:204-208` says why the empty coalition
does not refute the field cheaply; `psl211_alldecks_sc_const_false_close` at
`:216-221` prices the two masses and the epsilon correctly;
`psl211_alldecks_cert_ideal_close` at `:275-280` names `sc_Hd` and the
adapter's cut; `psl211_alldecks_no_spectral_cert0` at `:317-323` describes the
instance's own marginal bound correctly, whose epsilon is `0` by
`psl211_marginal_bound` (`instances/psl211/psl211_profile.v:104-105`). The
vocabulary is uniform: "constancy" for the field, "deck description" for an
element of `psl211_inputT`, "reading" for what a coalition sees. I found no
synonym drift.

Checks the brief asked for by name:

- Nothing says or implies that the spectral arm cannot be closed at all. The
  three sentences that did in round 1 are gone; `STATUS.md:21-22`, `:139-147`,
  `:439-441` and `psl211_sc_const_bound_probe.v:299-305` all say the opposite,
  and say it with the label "argued".
- Nothing reads the all-decks refutation as leakage. Every occurrence of the
  word is a denial (`psl211_sc_const_probe.v:22`, `:152`, `STATUS.md:282`,
  `:287`, `:420`, `:442`, `:459`). B2 is the reverse error, denying a failure
  rather than asserting leakage.
- 360/660, 600/660 and 10/11 are labelled as `vm_compute` diagnostics at
  `psl211_sc_const_probe.v:153-160` and `STATUS.md:291-302`. The unlabelled
  cousins are SF3, and the header's "by a wider margin" at
  `psl211_sc_const_probe.v:20-21`, which inherits its numbers from the same
  diagnostic and should say so or drop the comparative.
- The unexcluded range starts at `1/1320` in epsilon and `1/660` in the
  published number everywhere: `STATUS.md:13-14`, `:134-139`, `:428-430`,
  `psl211_sc_const_bound_probe.v:294-297`. No `1/660` in epsilon survives.

## 5. Homes

Reverse-dependency closures recomputed from `.Makefile.rocq.d` with
`scratchpad/psl_audit2/revdeps2.py`, written for this pass: line continuations
joined, `.vo` nodes only, edge from each prerequisite to each target, then the
transitive closure.

| file | reverse-dependants | `psl211_endpoints.vo` in closure |
|---|---|---|
| `security/pgg_collusion_bound.v` | 105 | **yes** |
| `reconstruct/design_privacy.v` | 11 | no |
| `instances/psl211/psl211_models.v` | 9 | no |
| `instances/psl211/psl211_rows.v` | 0 | no |
| `instances/psl211/psl211_mixing.v` | 0 | no |

Identical to `STATUS.md:324-330`, and the eleven names listed at `:340-344`
are exactly the eleven my script prints. The withdrawal of
`security/pgg_collusion_bound.v` is correct and no surviving proposal violates
the rule. `manifest/pgg_analysis_manifest.v:75` re-exports the instance
analysis files, which is why `manifest/pgg_tableau.vo` sits in the closure of
`psl211_models.vo`; that is a real edge and not a parsing artifact.

The new-file claim is correct: `_CoqProject` carries both `-R` lines and an
enumeration of 194 file names, so a new `lib/var_dist_supp.v` needs one line
in it to be built, and `lib/` holds exactly the library-extension files with
no `pgg_` prefix. `STATUS.md:346-353` cites the Kim probe's round 2 soundness
audit for this; that audit's finding G2 says it in those terms.

**The duplicate is confirmed.** infotheo's `leq_var_dist`
(`probability/variation_dist.v:51` of the installed tree) is
`` `| p x - q x | <= d(p, q) ``, which is the probe's `var_dist_point_le`
(`psl211_sc_const_bound_probe.v:85-91`) statement for statement, with the same
proof shape. `Set Implicit Arguments` is on in the infotheo file and the
finType is determined by `p`, so `leq_var_dist P Q t` is a drop-in for
`var_dist_point_le P Q t` at both call sites, `:103` and `:251`. A landing
should drop the local copy, and the probe's own source comment at `:82-84`
already says so.

## 6. Scratch record

- `scratchpad/psl_audit2/revdeps2.py`. Reverse-dependency closures, written
  independently of `audit-soundness/revdeps.py`; same five answers.
- No Rocq process was started. Axiom and compile evidence read from
  `scratchpad/psl_verify/*.log`, the fix pass's recompile from copied sources:
  twelve `Axioms:` blocks with exactly the three boolp axioms, one `Closed
  under the global context`, in `psl211_dealt_sc_const_probe.log:130`.
