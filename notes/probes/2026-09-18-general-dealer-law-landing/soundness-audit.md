# Independent soundness audit of the general dealer law landing

Date: 2026-09-18. The compiles of this audit ran across midnight into
2026-09-19 by the machine clock.

Scope: the spec `notes/20260918-general-dealer-law-landing-design.md`, the
landing probe `notes/probes/2026-09-18-general-dealer-law-landing/` (LAND), and
the four production files the copies were made from. The two earlier audits of
the mathematics, `notes/probes/2026-09-17-general-dealer-law/soundness-audit.md`
and `soundness-audit-delta.md`, are taken as given and are not redone. This
audit asks one question: if the four candidate texts are committed as the
permanent files, is every landed statement true, the statement the spec says it
is, non-vacuous, and is nothing already in the tree weakened, shadowed or
broken.

The author of this audit wrote none of the material under review.

## Machine-checked work of this audit

One Rocq process at a time, all outputs written with `-o` into the session
scratch directory, nothing under `lib/ protocol/ groups/ security/ smc/
reconstruct/ instances/ manifest/` touched, no `make` run. `ps -axo comm= |
grep -E 'rocqworker$'` was empty before and after every compile. No checksum
error and no inconsistent-assumptions error appeared at any point.

| Scratch file | Purpose | rc | Wall |
|---|---|---|---|
| `opq_a.v`, `opq_b.v` | does `Local Opaque` survive a file boundary (A6) | 0, 0 | 0 s, 0 s |
| `a2b.v` | elaborated statement of every existing declaration of `psl211_models.v`, production module against landing copy (A2) | 124 after the printing finished | 540 s |
| `a3.v` | discriminating power of the fidelity ascriptions, and an independent reproduction of them (A3) | 0 | 4 s |
| LAND `dealer_privacy.v` | independent recompile | 0 | 3 s |
| LAND `design_privacy_landing.v` | independent recompile | 0 | 4 s |
| LAND `pgl27_profile_privacy_landing.v` | independent recompile | 0 | 4 s |
| LAND `psl211_models_landing.v` | independent recompile | 0 | 29 s |
| LAND `landing_fidelity.v` | independent recompile, assumptions and ascriptions | 0 | 50 s |

`a2b.v` reached its 540 s self-kill cap while working through 62 kernel
convertibility ascriptions placed after the printing. Every print it was asked
for had already been emitted, and those prints are what settles A2. The
convertibility check that matters for the landed theorems is in `a3.v`, which
finished in 4 s.

## Findings

| ID | Severity | File:line | Claim | Evidence |
|---|---|---|---|---|
| S1 | SHOULD-FIX | `psl211_models_landing.v:1090-1095` | The statement comment on `psl211_dealer_view_indep_of_deck_unsat` ends "and the uniform deal law is the law that meets it". The definite article asserts that no other dealer law meets the mixed-law condition. Nothing in the landing proves that. Soundness invariant 4 bans a necessity claim for the uniform PSL(2,11) dealer law, and decision 8 puts the question out of scope. The feasibility delta audit raised the same class of overreach as G1 and G2. | A5 |
| S2 | SHOULD-FIX | spec:284, `pgl27_profile_privacy_landing.v:89`, `psl211_models_landing.v:129`, `:130` | The acceptance condition says "The plan then quotes the landing copies verbatim". Three `Require` lines name the probe logical path `general_dealer_law_landing`. Quoted verbatim, two permanent files would import a probe file, against soundness invariant 9. The spec never names the three substitutions. | A1, A7 |
| S3 | SHOULD-FIX | LAND `STATUS.md:66` (row L4) | "The two-way ascription against `psl211_models.psl211_alldecks_view_indep` succeeds in both forms" is false. `landing_fidelity.v` carries the `ltac:` form only, at lines 75-83. Its section 1b, lines 89-118, holds the verbatim-transcription form for the two PGL(2,7) theorems alone. The substance is sound and this audit supplied the missing form itself. | A3 |
| S4 | SHOULD-FIX | spec:266-271 | The mutation move that the spec records as decided is covered by no compile. `dealer_privacy.v` with its three mutation sections deleted has never been compiled, and neither has `landing_fidelity.v` with those sections added. The spec's own standard is that a candidate permanent text is compiled before a plan quotes it. | A10 |
| N1 | NOTE | LAND `STATUS.md:250` | "seven files under `instances/`" contradicts the list of six that follows it. Measured: six under `instances/`, two under `manifest/`, none under `reconstruct/`. The spec's own count of six is right. | A10 |
| N2 | NOTE | spec:156-157 (rows L5, L6) | As literally worded, "No sentence of the new block costs more than the same sentence costs in the feasibility probe" is falsified by LAND `STATUS.md`'s own table: 6.130 s against 6.099 s, and 6.092 s against 6.090 s. The rows need a noise tolerance. | A10 |
| N3 | NOTE | LAND `STATUS.md:318` | "Each target file's header table lists the declarations added to it" is false. Nine of the 23 PGL(2,7) additions and 21 of the 43 PSL(2,11) additions are absent from the header tables. Partial coverage is the repository's own convention, so the substance belongs to the naming audit and only the wording is a finding here. | A10 |
| N4 | NOTE | LAND `STATUS.md:175-183` | "Both are already loaded transitively through `psl211_alldecks`" misnames the route for one of the two. `psl211_alldecks.v:91` requires `psl211_blocks` and not `psl211_closure`. `psl211_closure` reaches `psl211_models.v` through `psl211_exec` and `psl211_endpoints`. The operative conclusion, no new edge and no change to the L7 closures, is correct. | A7 |
| N5 | NOTE | `psl211_models_landing.v:974-979` | The comment on `psl211_perdeck_fiber_card_neq` ends "so that symmetry is not available once a representative deck is fixed", which reads as a statement about every representative deck. What is proved is the failure at `psl211_perdeck_deal`. | A5 |
| N6 | NOTE | `psl211_models_landing.v:562`, `:752`, `:944`, `:999`, `:1203`, `:1204` | Local opacity does not survive a file boundary at this toolchain, measured in `opq_a.v` and `opq_b.v`. The closing `Local Transparent` pair is hygiene for importers and not load-bearing. The release at `:752` is load-bearing inside the file, because the raw-count chain needs the body of the reading. | A6 |
| N7 | NOTE | `reconstruct/dealer_privacy.v` (proposed) | The spec's row L1 says `Print Assumptions` covers "all eight declarations" while LAND `STATUS.md:63` says ten. Both are right for their own scope: eight landed declarations plus the two positive controls, which the pending mutation move takes out of the file. After the move the file holds exactly the eight. | A10 |
| N8 | NOTE | A9 | Everything here was compiled against `.vo` files that predate commit 1654fde. The landed statements name nothing the commit changed, but `psl211_alldecks.v` and `psl211_models.v` both sit below the two edited protocol files, so the landed block will be type-checked again when the protocol rebuild reaches them. | A9 |

No BLOCKING finding.

---

## A1. Each full copy against its production source

`diff -u` on each pair, then a count of removed and added lines and of hunks.

```
=== design_privacy ===
hunks: 2 removed lines: 15 added lines: 51
=== pgl27_profile_privacy ===
hunks: 5 removed lines: 0 added lines: 381
=== psl211_models ===
hunks: 4 removed lines: 0 added lines: 708
```

**`instances/pgl27/pgl27_profile_privacy.v` and `instances/psl211/psl211_models.v`
have zero removed lines.** Every difference is an addition. No existing
declaration, proof, comment or blank line is touched in either file. The four
PSL hunks are the header `Definitions` table, the header `Key results` table,
the import block, and the new block appended after the last production line.
The five PGL hunks are three header additions, the import line, and the new
block appended after `End pgl27_profile_privacy.`

The `%N` change is inside new material. Production `psl211_models.v` is 496
lines, the landing copy's last production line is 540, and the two patterns
`-[X in (_ < X)%N]Hrow` and `-[X in (_ < X)%N]Hcorow` are at landing lines 819
and 822, inside `psl211_perdeck_seqE`, which is itself new. Zero removed lines
already proves no production rewrite pattern was respelled.

`reconstruct/design_privacy.v` has exactly two hunks. The first replaces four
header table lines by seven, renumbering the sections because a section was
inserted. The second inserts `uniform_fdistmap_pointE` before
`uniform_fdistmap_fiberE` inside `Section fibers`, replaces the eleven proof
lines of `uniform_fdistmap_fiberE` by two, and appends
`Section full_set_fibers` with `uniform_fdistmap_fiberTE`. The fifteen removed
lines are exactly those four header lines and those eleven proof lines. Nothing
else in the file is touched.

**`uniform_fdistmap_fiberE`: statement byte-identical.** Extracted from both
files and compared as bytes:

```
production reconstruct/design_privacy.v:51
'Lemma uniform_fdistmap_fiberE (f0 f1 : X -> T) :\n  (forall v, #|[set x in A | f0 x == v]| = #|[set x in A | f1 x == v]|) ->\n  fdistmap f0 (`U HA : R.-fdist X) = fdistmap f1 (`U HA).'
landing design_privacy_landing.v:71
'Lemma uniform_fdistmap_fiberE (f0 f1 : X -> T) :\n  (forall v, #|[set x in A | f0 x == v]| = #|[set x in A | f1 x == v]|) ->\n  fdistmap f0 (`U HA : R.-fdist X) = fdistmap f1 (`U HA).'
BYTE IDENTICAL: True
COMMENT IDENTICAL: True
```

The new proof is

```coq
move=> Hfib; apply/fdist_ext => v.
by rewrite (uniform_fdistmap_pointE f0 v) (uniform_fdistmap_pointE f1 v) Hfib.
```

and `design_privacy_landing.glob`, read with the reference offsets attributed
to the enclosing declaration, confirms the route and that nothing else moved:

```
  uniform_fdistmap_pointE: used by ['uniform_fdistmap_fiberE']
  uniform_fdistmap_fiberE: used by ['colour_view_indep_fibers', 'uniform_fdistmap_fiberTE']
```

`colour_view_indep_fibers` is the existing consumer and still reaches
`uniform_fdistmap_fiberE` directly.

**No new axiom.** `landing_fidelity.v:232-233` runs `Print Assumptions` on the
production constant and on the landing constant. This audit recompiled that
file itself and paired its 97 assumption blocks with its 97 `Print Assumptions`
commands positionally:

```
Print Assumptions commands in the source: 97
assumption blocks in my recompile output  : 97
  ('constructive_indefinite_description','functional_extensionality_dep','propositional_extensionality') -> 67
  CLOSED -> 30
mentions of 'admit'/'Admitted' in the output: 0
```

No fourth axiom, no project-local constant and no `Admitted` appears anywhere in
the 97 blocks. Both copies of `uniform_fdistmap_fiberE` are in the 67, so the
new proof pulls in nothing the old one did not. Both copies of `card_fiber_sum`
and of `pair_fibers_class_sizes` are in the 30, unchanged. One small correction
to LAND `STATUS.md`: it enumerates the 30 as `psl211_deal_pos`, the raw-count
chain and the four `design_privacy.v` lemmas, which is 24. The other six are
`pgl27_dealer_embed`, `pgl27_dealer_view`, `pgl27_dealer_bad_embed`,
`psl211_dealer_assoc`, `psl211_dealer_view` and `psl211_dealer_bad_assoc`, all
of them plain definitions, so the omission is an incomplete list and not a
discrepancy.

No `Axiom`, `Parameter`, `Conjecture`, `Admitted`, `Abort`, `Time`, `Timeout`
or `Print Assumptions` occurs in any of the four candidate texts, checked by
grep over all four.

**The three probe-path `Require` lines are the one difference that is neither
an addition to the permanent content nor a documented change.** See S2.

```
pgl27_profile_privacy_landing.v:89:From general_dealer_law_landing Require Import dealer_privacy.
psl211_models_landing.v:129:From general_dealer_law_landing Require Import dealer_privacy.
psl211_models_landing.v:130:From general_dealer_law_landing Require Import design_privacy_landing.
```

Independent recompile of the four candidate texts and of `landing_fidelity.v`,
all five with `rc=0`:

```
dealer_privacy rc=0 errors=0 === rc=0 wall=3s
design_privacy_landing rc=0 errors=0 === rc=0 wall=4s
pgl27_profile_privacy_landing rc=0 errors=0 === rc=0 wall=4s
psl211_models_landing rc=0 errors=0 === rc=0 wall=29s
landing_fidelity rc=0 errors=0 === rc=0 wall=50s
```

Compiling a file that contains `Fail C` succeeds only if `C` fails, so a clean
recompile is itself the evidence that all seven mutations still fail: the four
in `dealer_privacy.v`, the two in `pgl27_profile_privacy_landing.v` and the one
in `psl211_models_landing.v`.

## A2. Do the new imports change how an existing lemma of `psl211_models.v` elaborates

The three new import commands sit at the top of the file, above every
declaration, so every existing lemma of the landing copy elaborates under them.
The file compiling is necessary and not sufficient, so the elaborated statements
were compared.

`a2b.v` requires the production module `pgg_smc.psl211_models` and the landing
module `general_dealer_law_landing.psl211_models_landing` side by side and
prints the type of all 31 existing declarations from each. The production
module is imported, the landing one only required, so the landing prints carry
the module prefix on that module's own constants and the production prints do
not. With that prefix stripped and whitespace normalised:

```
Set Printing All  psl211_alldecks_view_indep: identical after stripping the module prefix and normalising whitespace: True
Set Printing All  psl211_alldecks_static_obsE: identical after stripping the module prefix and normalising whitespace: True
default printing, all 31 declarations: production chars: 8894  landing chars: 8894
default printing, all 31 declarations: IDENTICAL: True
```

`psl211_alldecks_static_obsE` is identical even before the prefix is stripped,
byte for byte, 18538 bytes on each side, because its statement names no constant
of `psl211_models.v` itself. `psl211_alldecks_view_indep` differs on exactly two
lines, both of them the qualification of a constant of the module under test:

```
-         (psl211_alldecksP R)
+         (psl211_models_landing.psl211_alldecksP R)
-         (psl211_alldecks_secret R)
+         (psl211_models_landing.psl211_alldecks_secret R)
```

19250 bytes against 19294, a difference of 44 bytes, which is two occurrences of
the 22-character prefix.

`Set Printing All` prints every implicit argument, every coercion and every
canonical structure instance by name, so an argument that a notation or a
canonical instance had resolved differently would show. None does, on the two
headline lemmas the request named. The default-printed comparison covers the
other 29 as well and is also exact.

Conclusion: adding `Import Num.Theory` and the two `Require Import` lines
changes nothing about how any existing declaration of `psl211_models.v`
elaborates. The reason is structural and is worth recording: `Import` inside a
file is not re-exported, `psl211_blocks` and `psl211_closure` were already
loaded on every path that reaches this file, and `Num.Theory` supplies lemma
names rather than notations that could recapture an existing statement.

## A3. Statement fidelity, and whether the test could fail

`landing_fidelity.v` holds six `ltac:`-form ascriptions at lines 59-83, two per
theorem, and four verbatim-transcription ascriptions at lines 91-118 for the two
PGL(2,7) theorems. The PSL(2,11) theorem has no verbatim form there, which is
S3.

This audit reproduced the fidelity check independently and added the negative
controls the request asked for. `a3.v` compiled with `rc=0` in 4 s, which means
every `Definition` in it was accepted and every `Fail Definition` in it was
rejected.

Accepted:

- `audit_pgl27_right_bound_written`, `pgl27_view_indep_via_dealer` at the
  statement of `pgl27_view_indep` transcribed from `instances/pgl27/pgl27_secrecy.v:82`.
- `audit_decoy_pgl_control` and `audit_decoy_psl_control`, the two decoys at
  their own kernel types, which shows the `ltac:` machinery accepts what it
  should.
- `audit_psl_via_dealer_at_models_type` and `audit_psl_models_at_via_dealer_type`,
  the two-way `ltac:` ascription between `psl211_alldecks_view_indep_via_dealer`
  and `psl211_models.psl211_alldecks_view_indep`.
- `audit_psl_via_dealer_at_written_type` and `audit_psl_models_at_written_type`,
  the verbatim-transcription form for PSL(2,11) that `landing_fidelity.v` lacks,
  written out from `instances/psl211/psl211_models.v:427-430`:

```coq
  forall (R : realType)
    (C : {set ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1)}),
  (#|C| <= 5)%N ->
  psl211_alldecksP R |= (fun u => psl211_alldecks_view C u.1 u.2)
                    _|_ psl211_alldecks_secret R
```

Rejected, each inside a `Fail` that the compile accepted:

- `audit_pgl27_wrong_bound_written`, the same PGL statement with `#|C| <= 4`.
- `audit_pgl27_wrong_bound_ltac`, the same weakening through the `ltac:` form.
- `audit_pgl27_swapped_readers`, the same statement with view and secret
  exchanged.
- `audit_psl211_wrong_bound_ltac` and `audit_psl_wrong_bound_written`, the PSL
  statement with `#|C| <= 4` in each of the two forms.

So the test discriminates. A wrong coalition bound is rejected in both forms and
for both instances, and so is an exchange of the two readers, which the bound
test alone would not catch.

The three restated statements were also read side by side with their originals.
`instances/pgl27/pgl27_secrecy.v:82`, `:215` and
`instances/psl211/psl211_models.v:427` match the three `_via_dealer` statements
up to the leading `(R : realType)` that each section supplies, and the proofs of
the originals are untouched, which A1 already established from the zero removed
lines.

## A4. Routes, and soundness invariant 8

Read from the `.glob` files by attributing each reference offset to the
declaration that encloses it.

```
=== pgl27_profile_privacy_landing.glob ===
  dealer_shuffle_view_indep: used by ['pgl27_dealer_view_indep']
  dealer_shuffle_view_indep_of_deck: used by ['pgl27_view_indep_alldecks_via_dealer']
  inde_RV_fdistmap: used by ['pgl27_view_indep_via_dealer']
  ktuple_encode_uniform: used by ['pgl27_alldecks_dealer_view_law']
  fdistmap_prod_const: used by ['pgl27_dealer_view_indep']
=== psl211_models_landing.glob ===
  dealer_shuffle_view_indep: used by ['psl211_dealer_view_indep']
  inde_RV_fdistmap: used by ['psl211_alldecks_view_indep_via_dealer']
  fdistmap_prod_sectionE: used by ['psl211_dealer_mixed_lawE']
  uniform_fdistmap_pointE: used by ['psl211_perdeck_massE']
  uniform_fdistmap_fiberTE: used by ['psl211_dealer_sectionE']
  psl211_alldecks_per_cut_count: used by ['psl211_dealer_sectionE']
=== dealer_privacy.glob ===
  inde_prod_kernel_fst: used by ['dealer_shuffle_view_indep']
  fdistmap_prod_const: used by ['dealer_shuffle_view_indep_of_deck']
```

This matches the spec's flow exactly. `pgl27_view_indep_alldecks_via_dealer`
goes through the per-deck condition and through no other of the three.
`pgl27_view_indep_via_dealer` and `psl211_alldecks_view_indep_via_dealer` each
go through `inde_RV_fdistmap`, and each rests on a `_dealer_view_indep` lemma
that goes through the mixed-law condition. The proof scripts read the same way:
`pgl27_view_indep_alldecks_via_dealer` closes with
`exact: Hgen` on a `dealer_shuffle_view_indep_of_deck` instance, and the other
two close with `by apply/inde_RV_fdistmap.`

Soundness invariant 8 holds. Each of the three generic results is used by at
least one landed instance theorem, and `dealer_shuffle_view_indep_of_deck` has
exactly one user, which is the whole point of decision 2. The two supporting
generic results have users too, `fdistmap_prod_sectionE` at
`psl211_dealer_mixed_lawE` and `uniform_fdistmap_fiberTE` at
`psl211_dealer_sectionE`, and `uniform_fdistmap_pointE` at
`psl211_perdeck_massE` as well as inside the new proof of
`uniform_fdistmap_fiberE`. No landed generic declaration is unused.

## A5. The PSL(2,11) refutation block

**Statements.** Each of the six was extracted from the landing copy and from the
feasibility probe and compared as bytes:

```
psl211_perdeck_fiber_card_neq: probe=psl211_per_deck_counter.v:240 landing=:980 char_identical=True
psl211_perdeck_law_neq: probe=psl211_per_deck_law_counter.v:68 landing=:1016 char_identical=True
psl211_perdeck_no_common_law: probe=psl211_per_deck_law_counter.v:108 landing=:1056 char_identical=True
psl211_dealer_valid_forced: probe=psl211_per_deck_law_counter.v:132 landing=:1080 char_identical=True
psl211_dealer_view_indep_of_deck_unsat: probe=psl211_per_deck_law_counter.v:148 landing=:1096 char_identical=True
psl211_fixed_deal_view_dep: probe=psl211_per_deck_law_counter.v:190 landing=:1138 char_identical=True
```

Extending the same comparison to every landed declaration reproduces row L9
independently:

```
landed declarations checked: 82
  character-identical to the feasibility probe : 81
  identical after whitespace normalisation only : 0
  genuinely different                           : 1
  === uniform_fdistmap_pointE
```

The one difference is the documented binder discharge of
`uniform_fdistmap_pointE` into `Section fibers`. The count is 82 rather than 75
because it includes the seven `Fail` mutations.

**Carriers.** Character-identical source text is not by itself enough, because
the same text can name different objects. It names better ones here. The
feasibility probe wrote

```coq
Local Notation seatT := 'I_12.
Local Notation cardT := 'I_12.
```

while the landing copy uses the production file's own

```coq
Local Notation seatT := ('I_(pi_T' (mp_PI mpP)).+1).
Local Notation cardT := ('I_(pgg_N' (mp_M mpP)).+1).
Local Notation mpP := (instance_profile psl211_algebra).
```

so the six statements are stated on the production seat and card types, the
production deal type `psl211_deal` from `instances/psl211/psl211_alldecks.v:105`,
the production group through `cutT := (pgg_gT psl211_M)`, and the production
reading `psl211_alldecks_view`. The coalition is `psl211_perdeck_coalition`,
which is `[set i : seatT | val i \in [:: 0; 1; 2]]`, three seats. The elaborated
form that `a2b.v` printed for the neighbouring theorem carries the same
production index, `{set 'I_(pi_T' (pgg_monodromy_profile.mp_PI
(pgg_instance.instance_profile psl211_exec.psl211_algebra))).+1}`.

**Non-vacuity.** `psl211_perdeck_no_common_law` and
`psl211_dealer_view_indep_of_deck_unsat` are negations, so they would be cheap
if their premises were unsatisfiable. They are not. `psl211_dealer_valid_forced`
is the lemma that makes the first premise satisfiable and forces the validity
predicate to accept the witness deal, and it is proved by
`fdist_uniform_supp_neq0`, which is available exactly because the dealer law is
uniform on the whole deal type. The count itself is a positive fact,
`psl211_perdeck_raw_countE : psl211_perdeck_raw_count true = 0 /\
psl211_perdeck_raw_count false = 1`, and `psl211_fixed_deal_view_dep` uses the
non-empty fiber of the false chirality to produce the witness. `psl211_deal_pos`
supplies the inhabitant. Nothing here is vacuously true.

**Comments against invariants 4, 5 and 10.** One sentence overreaches.

At `psl211_models_landing.v:1090-1095`:

> **So of the model's two conditions only the mixed-law condition of
> dealer_shuffle_view_indep is available to this instance, and the uniform deal
> law is the law that meets it.**

The first clause is supported. The lemma quantifies over every validity
predicate compatible with `psl211_dealer_delta` and over every candidate law, so
the per-deck condition is genuinely unavailable at this instance's dealer. The
second clause is not. What is proved is that the uniform deal law meets the
mixed-law condition, by `psl211_dealer_mixed_lawE`. Nothing rules out another
dealer law meeting it. Decision 8 puts the necessity question out of scope and
soundness invariant 4 bans the claim. Weaker wording, keeping the sentence
otherwise as it stands:

> So of the model's two conditions only the mixed-law condition of
> dealer_shuffle_view_indep is available to this instance, and the uniform deal
> law meets it.

This is the same class of overreach the feasibility delta audit raised as G1 on
the earlier text of this comment. The rest of G1 and the whole of G2 were fixed.

`psl211_fixed_deal_view_dep` at `:1128-1137` is now careful and states its own
limits:

> Read together with psl211_alldecks_view_indep_via_dealer it says that for
> PSL(2,11) privacy depends on which deal law the dealer uses: the uniform one
> delivers it, and the point mass at psl211_perdeck_deal does not. What is NOT
> shown here is that a hidden uniform deal leaks: the deal is public in this
> refutation, being a point mass.

That is the wording the delta audit asked for under G2, and it discharges the
third clause of invariant 4 explicitly.

One weaker case, N5, at `:974-979`: "so that symmetry is not available once a
representative deck is fixed" reads as a statement about every representative
deck. Suggested: "so that symmetry is not available at the deck
psl211_perdeck_deal".

No landed comment claims privacy for an arbitrary dealer law. The header of
`reconstruct/dealer_privacy.v` says "two sufficient conditions on the dealer
law", and every instance comment names the condition it discharges. No landed
comment says `uniq` is necessary. The nearest is the mutation comment at
`pgl27_profile_privacy_landing.v:562-566`, which says only that omitting the
argument leaves `uniq d ->` as an arrow in the term's type, a statement about
the term and not about the mathematics. Invariant 10 holds in the comments as
well as in the proofs: `pgl27_dealer_view_indep` discharges the guard with
`=> s _` and `pgl27_view_indep_alldecks_via_dealer` with `move=> s d _ Hu`, and
no comment suggests the guard does work.

## A6. Opacity

Three `Local Opaque` commands and three `Local Transparent` commands, all inside
the new block:

```
562:Local Opaque psl211_alldecks_view.
752:Local Transparent psl211_alldecks_view.
944:Local Opaque psl211_alldecks_view psl211_elem_table.
999:Local Opaque psl211_perdeck_raw_count.
1203:Local Transparent psl211_alldecks_view psl211_elem_table.
1204:Local Transparent psl211_perdeck_raw_count.
```

**Every existing lemma is outside every sealed span.** Production
`psl211_models.v` is 496 lines, the landing copy reproduces it up to line 540,
and the first `Local Opaque` is at line 562. The block banner is at 542.

**The file ends with everything transparent again.** The file is 1204 lines and
the last two are the two `Local Transparent` commands. Each sealed constant is
released: `psl211_alldecks_view` sealed at 562 and 944, released at 752 and
1203; `psl211_elem_table` sealed at 944, released at 1203;
`psl211_perdeck_raw_count` sealed at 999, released at 1204. Counts are three and
three. None of `psl211_alldecks.v`, `psl211_closure.v` or production
`psl211_models.v` contains any `Opaque` or `Transparent` at all, so the releases
restore the default state rather than change it.

**Does the pairing matter.** Measured rather than assumed. `opq_a.v` defines
`audit_foo` and seals it with `Local Opaque`, defines `audit_bar` and seals it
with a bare `Opaque`, and leaves `audit_baz` alone. In the same file,
`Eval cbv in audit_foo` prints

```
     = audit_foo
     : nat
```

so `cbv` does respect the seal inside the file. `opq_b.v` requires that module
and evaluates all three:

```
     = 2
     : nat
     = 2
     : nat
     = 2
     : nat
```

Neither `Local Opaque` nor bare `Opaque` survives the file boundary at this
toolchain. So the closing pair at lines 1203 and 1204 is hygiene: importers
`psl211_analysis`, `psl211_rows`, the manifest files and the Tableau files see
exactly what they saw before whether or not it is there. The release at line 752
is a different matter and is load-bearing, because the raw-count chain below it
needs the body of `psl211_alldecks_view` under `vm_compute`. The comment at
`:749-751` says so.

## A7. Import graph

**`dealer_privacy.v` imports `transitivity_privacy` and nothing else of the
repository.** Its import block is

```coq
From pgg_reconstruct Require Import transitivity_privacy.
```

and its only other requires are HB, mathcomp and infotheo. `dealer_privacy.glob`
shows `inde_prod_kernel_fst` and `fdistmap_prod_const` as the only two
repository lemmas it consumes, both from `transitivity_privacy.v`.

**No cycle.** `transitivity_privacy.v` depends on `pgg_interface`,
`pgg_monodromy_profile`, `covering_scheme` and `pgg_sharing_framework`, none of
them an instance file, so nothing reachable from `dealer_privacy.v` reaches
`pgl27_profile_privacy.v` or `psl211_models.v`. The forward closure of
`psl211_closure.v` is three files, all of them already inside the forward
closure of `psl211_models.v`, so the second new import adds no node either. A
cycle check on `psl211_closure.v` against `psl211_models.v` returns false.

**Reverse-dependency closures, recomputed in Python from
`.Makefile.rocq.d`, read-only, no `make`:**

```
reconstruct/design_privacy.v: 11 importers (transitive)
    instances/kim2025/five_card_rows.v
    instances/pgl27/pgl27_rows.v
    instances/psl211/psl211_analysis.v
    instances/psl211/psl211_models.v
    instances/psl211/psl211_rows.v
    instances/psl211/psl211_secrecy.v
    instances/s5/s5_rows.v
    manifest/pgg_analysis_client.v
    manifest/pgg_analysis_manifest.v
    manifest/pgg_tableau.v
    manifest/pgg_tableau_syntax.v
instances/pgl27/pgl27_profile_privacy.v: 0 importers (transitive)
instances/psl211/psl211_models.v: 9 importers (transitive)
    instances/kim2025/five_card_rows.v
    instances/pgl27/pgl27_rows.v
    instances/psl211/psl211_analysis.v
    instances/psl211/psl211_rows.v
    instances/s5/s5_rows.v
    manifest/pgg_analysis_client.v
    manifest/pgg_analysis_manifest.v
    manifest/pgg_tableau.v
    manifest/pgg_tableau_syntax.v
UNION with edited files: 13
instances/psl211/psl211_endpoints.v in union: False
instances/psl211/psl211_profile.v in union: False
instances/psl211/psl211_exec.v in union: False
```

11, 0, 9 and 13, the numbers the spec states, and the three heavy PSL(2,11)
files are in none of them. The 900 s rebuild is not owed. The 13-file union is
the same set the probe lists, member for member.

Two caveats on the recomputation. `.Makefile.rocq.d` predates the landing, so it
carries none of the three new edges. Their effect was computed separately: the
edge into `dealer_privacy.v` gives that new file a reverse closure of ten, which
invalidates nothing at landing time because the file does not exist yet, and the
edge into `psl211_closure.v` is not new as a load, only as a name import, so no
closure changes. The second caveat is N4, on the route by which `psl211_closure`
already arrives.

**`_CoqProject` position.** Line 171 is `reconstruct/transitivity_privacy.v`,
line 172 `reconstruct/coalition_view_transport.v`, line 173
`reconstruct/design_privacy.v`, line 180
`instances/pgl27/pgl27_profile_privacy.v`, line 212
`instances/psl211/psl211_models.v`. Inserting `reconstruct/dealer_privacy.v` at
line 172 puts it after the only file it imports and before both files that
import it, with eight files in between that neither import it nor are imported
by it. That `design_privacy.v` sits at 173 and does not import
`dealer_privacy.v` leaves their relative order free, so the position is correct.
The file order in `_CoqProject` is a build order and not a dependency
declaration, and `coqdep` derives the real order from the `Require` lines, so
the insertion cannot introduce an ordering error even if it were placed
elsewhere.

## A8. Shadowing, clashes and leakage into importers

**Name scan.** The 87 identifiers introduced by the four candidate texts, which
is the 75 landed names plus seven `Fail` names plus five local notations, were
scanned as whole words across `lib protocol groups security smc reconstruct
instances manifest` and across every `.v` file of the installed libraries under
`_opam/lib/coq/user-contrib`, 1948 files.

```
=== tree hits (production .v only) ===
  viewT -> ['protocol/pgg_functionality.v', 'reconstruct/transitivity_privacy.v', 'security/pgg_leakage_witness.v', 'security/pgg_trace_secrecy.v']
installed .v scanned: 1948
  none in installed libs
```

The only hit is `viewT`, which is a `Local Notation` or a section variable in
each of those four files and in the landing copies, so it escapes none of them.
Every one of the 75 landed declaration names is absent from the tree and from
the installed `infotheo` and `mathcomp`. In particular
`uniform_fdistmap_pointE` and `uniform_fdistmap_fiberTE` occur nowhere, so
neither can shadow an identifier that any of the 11 importers of
`design_privacy.v` uses, and none of the roughly 60 new names of
`psl211_models.v` can shadow anything the 9 importers use. The reverse direction
is also clear: no importer defines a local identifier with one of these names,
because none of the names occurs in any importer at all.

**Leakage of the new imports.** `Import` inside a file is re-exported only under
`Require Export`, and there is no `Require Export` and no bare `Export` in any
of the four candidate texts or in any of the three production sources they came
from, checked by grep. So `Import Num.Theory` and the two new `Require Import`
lines are invisible to importers of `psl211_models.v`.

**Leakage of the 25 s.** The cost is compile time of `psl211_models.v` itself.
It cannot reach an importer, because an importer loads `psl211_models.vo` and
does not re-elaborate its proofs. The one thing that could reach an importer is
a larger `.vo`, and that is a disk cost rather than a correctness one. The
sealing of `psl211_perdeck_raw_count` inside the file does not travel either,
per A6, so an importer that happened to name that constant would find it
transparent, exactly as it would find any other `Definition`.

## A9. Staleness, and what a protocol rebuild could do

`git show 1654fde` changes two definitions and one comment:

- `protocol/card_exchange_pismc.v`, `exchange_verifier`: the `Init (PGG_sheet
  ep) ;` line is removed and the loop counter changes from `fun k => k.+2` to
  `S`.
- `protocol/pgg_run.v`, `endpoints_of_trace`: `rev (evens (sheets_of
  verifier_trace))` becomes `rev (sheets_of verifier_trace)`.
- `protocol/pgg_run.v`, `evens`: its comment only. The definition is unchanged
  and now has no user.

A whole-tree grep for `endpoints_of_trace`, `exchange_verifier` and `evens`
returns 15 `.v` files. Neither `instances/psl211/psl211_alldecks.v` nor
`instances/psl211/psl211_models.v` is among them, and none of the 13 files of
the L7 union is among them. So no landed statement names a changed definition,
and no landed proof rewrites with one.

The residual risk is not zero, and it is worth stating plainly rather than
dismissing. `psl211_alldecks.v` and `psl211_models.v` both sit below the two
edited protocol files in the import graph, through `protocol/pgg_execution_plug.v`
and `security/pgg_sample_adapter.v`, both of which do name
`endpoints_of_trace`. When the protocol rebuild eventually reaches them, every
file above is re-elaborated, the landed block included. What could then break is
an existing lemma of `psl211_models.v` about the execution and trace layer, and
that risk exists whether or not this landing happens. The landed block adds no
new exposure, because it names nothing from that layer: its inputs are
`psl211_alldecksP`, `psl211_alldecks_view`, `psl211_alldecks_secret`,
`psl211_alldecks_per_cut_count`, `psl211_deal`, `pgg_gT psl211_M`,
`psl211_G_pos`, `psl211_elem_table` and `psl211_ptbl`, none of which is defined
through the verifier or the trace. The honest statement is that the landing
inherits the tree's existing staleness risk and does not enlarge it, and that
nobody has yet compiled anything against a post-1654fde snapshot.

## A10. The spec

The claim ledger checks out where this audit could check it. L2, L3, L4, L7, L8,
L9 and L12 were reproduced independently and all hold, and the numbers the spec
quotes for the closures, the `_CoqProject` lines and the cited-object lines are
right. Every line number in the "Cited objects" table was verified:

```
inde_prod_kernel_fst  spec=167 actual=167  OK
fdistmap_prod_const  spec=216 actual=216  OK
ktuple_encode_uniform  spec=591 actual=591  OK
alldecksP  spec=771 actual=771  OK
uniform_fdistmap_fiberE  spec=51 actual=51  OK
pgl27_view_indep  spec=82 actual=82  OK
pgl27_view_indep_alldecks  spec=215 actual=215  OK
psl211_alldecksP  spec=138 actual=138  OK
psl211_alldecks_secret  spec=145 actual=145  OK
psl211_alldecks_view_indep  spec=427 actual=427  OK
psl211_alldecks_view  spec=678 actual=678  OK
psl211_alldecks_per_cut_count  spec=1334 actual=1334  OK
```

What is missing for a plan to be written from the spec verbatim:

1. **The three import substitutions, S2.** The spec's flow says "imports
   `dealer_privacy`" for each instance file and its acceptance condition says
   the plan quotes the copies verbatim. It never says that
   `From general_dealer_law_landing Require Import dealer_privacy.` becomes
   `From pgg_reconstruct Require Import dealer_privacy.` in two files, and that
   `From general_dealer_law_landing Require Import design_privacy_landing.` is
   deleted from the third. Without that sentence the plan would import a probe
   file from two permanent files and break soundness invariant 9. The
   consequence of the deletion was checked and is harmless: in the copy, the
   production `design_privacy` is required last and wins the ten short names it
   shares, while `uniform_fdistmap_pointE` and `uniform_fdistmap_fiberTE` are
   reached in the landing module because production has neither. After the
   landing all twelve come from one module, so no name resolution changes.

2. **The post-move `dealer_privacy.v`, S4.** The spec records the decision to
   move the four mutations and their two positive controls out of
   `reconstruct/dealer_privacy.v` and into `landing_fidelity.v`. The premise of
   the decision is right, verified by grep: six files under `instances/` and two
   under `manifest/` contain a `Fail`, and no file under `reconstruct/`,
   `lib/`, `protocol/`, `groups/`, `security/` or `smc/` does. But the file that
   results has never been compiled, and neither has the `landing_fidelity.v`
   that receives the three sections. The move deletes `Section
   dealer_kernel_mutations`, `Section carrier_transport_mutation` and `Section
   product_section_mutation` whole, which is low risk, and the header table
   survives it because it numbers only the three real sections. Still, the
   spec's own standard is that a candidate permanent text compiles before a plan
   quotes it, so one compile of each is owed. `landing_fidelity.v` already
   prints assumptions for the two positive controls at lines 154 and 155, so
   after the move those lines refer to local declarations rather than imported
   ones, which is consistent.

3. **Rows L5 and L6, N2.** As worded, "no sentence of the new block costs more
   than the same sentence costs in the feasibility probe" is refuted by the
   probe's own measurement table, where two of the four slow sentences are a few
   milliseconds slower in the landing copy. The intent is clear and the
   measurement supports it. The rows need a tolerance so that a later reader
   does not read a noise difference as a failed row.

4. **The mutation-precedent count, N1**, and **the header-table claim, N3**, are
   wording errors in LAND `STATUS.md` rather than in the spec, and the second is
   the naming audit's substance.

Nothing in the spec is vacuous. Nothing in it is stronger than the probe
supports except the two comment sentences at S1 and N5, which are in the landed
material rather than in the spec, and the ledger sentence at S3.

The soundness invariants were checked one by one and all ten hold in the
material as it stands, with the two qualifications recorded at S1 for invariant
4 and at S2 for invariant 9. Invariant 1: no axiom, assumed constant, `Admitted`
or `Abort` in any of the four texts, and no `Print Assumptions` either.
Invariant 2: every premise and conclusion in the block is an equality or a
non-equality of finite distributions, with no approximation and no computational
assumption anywhere. Invariant 3: `dealer_shuffleP` is `secretP `X (fun s =>
(delta s) `x nu)`, which fixes the order. Invariant 5: the per-deck lemma takes
`uniq d` as a premise and nothing claims it is necessary. Invariant 6: zero
removed lines in the two instance files, a byte-identical statement for
`uniform_fdistmap_fiberE`, and untouched proofs for the three restated theorems.
Invariant 7: three law equations and six reader equations, all named lemmas.
Invariant 8: A4. Invariant 10: A5.

VERDICT: GO
