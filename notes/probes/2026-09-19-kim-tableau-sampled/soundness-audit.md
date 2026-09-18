# Independent soundness audit: Kim's two five-card rows as Tableau programs

Date: 2026-09-19.
Auditor: independent session. Nothing in this audit was written by the author of
the spec or of the probe.
Spec audited: `notes/20260919-kim-tableau-sampled-design.md`.
Probe audited: `notes/probes/2026-09-19-kim-tableau-sampled/` (`STATUS.md`,
`kim_rows_probe.v`, `kim_biased_arms_probe.v`, `five_card_rows_landing.v`,
`kim_fidelity.v`).

Line references of the form `landing:NNN` are lines of
`notes/probes/2026-09-19-kim-tableau-sampled/five_card_rows_landing.v`, the text
that would be committed as `instances/kim2025/five_card_rows.v`.

## What was compiled for this audit

One Rocq process at a time. `ps -axo comm= | grep -E 'rocqworker$'` was empty
before and after each run. Flags were built from the production `_CoqProject`
(the five `-arg -w -arg <name>` pairs and every `-R`), plus
`-Q . kim_tableau_sampled_probe`. No `make`. No `.vo` under the repository
changed: every output went to the audit scratch directory.

| run | what | wall | peak RSS | result |
|---|---|---|---|---|
| 1 | `rocq compile` of `five_card_rows_landing.v` | 3.88 s | 1.70 GB | exit 0, one pre-existing `notation-incompatible-prefix` warning from the infotheo `Require` line |
| 2 | `rocq repl -q <flags> < five_card_rows_landing.v` | — | — | exit 0, the three `Fail` messages captured verbatim (B1, B4) |
| 3 | `rocq compile` of a byte-identical copy in the scratch directory | — | — | exit 0 |
| 4 | `rocq repl -q <flags> < kim_audit_check.v` (this audit's own checks) | 7.75 s | 1.96 GB | exit 0 |

No checksum error, no inconsistent-assumptions error, no `Admitted`, no `Abort`,
no new axiom.

## Findings

| id | severity | file:line | claim | evidence |
|---|---|---|---|---|
| S1 | SHOULD-FIX | landing:6-17 | The header's first paragraph is no longer true of the file. It says "every statement below is about a coalition of at most one of the five seats" and "input privacy ... is not what this row states". `five_card_row_biased_leak_bound` (landing:505) quantifies over an unrestricted `A : seq nat`, with no threshold condition, and the header's own Key results table (landing:74-76) calls it "Kim's input-privacy bound". Read together, a reader can take the leak bound for a threshold-restricted coalition statement, which is the reading the whole design is meant to prevent. Spec ledger row K11 asserts the header is true after the change. | The diff leaves lines 6-17 untouched; the new lemma's type quantifies over `A : seq nat` only. |
| S2 | SHOULD-FIX | landing:383-395, `manifest/pgg_analysis_status.v:55-59` | The biased row's comment explains the level gap by the two `certify` arms but never says that the manifest's `AnalysisBridged` and the Tableau's `AnalysisBridged` are the same constructor admitted by different criteria: the manifest's is "a theorem about that distribution and that observer", the Tableau's is one of two specific arms supplied. Without that clause a reader of the paper can conclude the manifest overclaims for this row. It does not. | `pgg_analysis_status.v:59`; `manifest/pgg_analysis_manifest.v:322-328`. |
| S3 | NOTE | landing:413-433 vs `kim_rows_probe.v:47-71` | The landed `prefixE` states three conjuncts; the probe's five-conjunct form, which pins `Ht`, `He`, `Hr` one by one, was not landed. The spec's sentence "three conjuncts pin five components" is an inference through dependent record injectivity, not the landed proposition. | I re-proved the five-conjunct form `by split` for both rows in run 4, so nothing is lost mathematically. |
| S4 | NOTE | landing:404, landing:462 | A `Fail` does not pin which error occurred. Both landed mutations would keep passing if `S5Analysis.rand_family` became unbound or `five_card_row_biased` were renamed. The level gap does not rest on the `Fail`: the declared type `Tableau Sampled` together with `five_card_row_biased_levelE` and the disjointness of two constructors of `CompletionLevel` already settle it. | Run 2 captured the two error texts; the file itself records neither. |
| S5 | NOTE | landing:472-479 | The endpoint comment says "at every seat" for a bound variable `s : 'I_5` that the statement uses as a card position. At this instance `pi_starts FiveCardKim_PI = ord_tuple 5`, so seat `i` starts at position `i` and the two readings coincide; the statement itself quantifies over positions. | Run 2 goal display: `(fc_sigma ^+ k)%g (tnth (ord_tuple 5) i)`. |
| S6 | NOTE | spec, Cited objects table | `kim_centi_witness_rhoE` is listed as a required object and is not used (STATUS finding 2 already records this). `ExactWitness`, `SpectralCert`, `SecurityPort` are cited at `manifest/pgg_tableau.v:150`; the actual lines are `:114`, `:131`, `:149`. `STATUS.md` cites `manifest/pgg_analysis_manifest.v:1785` for the repeated row's level check; the actual line is `:1787`. | Direct reads. |
| S7 | NOTE | `STATUS.md` K9 | The reported closure has one auxiliary target; the same traversal over the same file gives me three (`.required_vo`, `.required_vos`, `.v.beautified`). More importantly, "closure `.v` files: NONE" is vacuous, because `.v` files never appear as Make targets. The decisive facts, which I checked separately, are that no other module's `.vo` is in the forward closure and that no file in the tree mentions `five_card_rows`. | Recomputed in Python; whole-tree scan of 133 `.v` files gives one hit, the file's own header line. |
| S8 | NOTE | landing:40-41 | "This is the situation `instances/s5/s5_rows.v` already records for `s5_row_word`" is true of the missing arms and not of the treatment: `s5_rows.v` writes no program at all for that row, while the landing copy writes both Kim programs and stops them at `Sampled`. The Kim treatment is the stronger one. | `instances/s5/s5_rows.v:54-70`. |

No BLOCKING finding. Every landed statement is true, every landed comment is
accurate about the statement it sits above, and nothing in the landing copy
claims coalition privacy for either Kim row.

## B1. The landing copy against production

`diff -u instances/kim2025/five_card_rows.v
notes/probes/2026-09-19-kim-tableau-sampled/five_card_rows_landing.v` has six
hunks and touches nothing else:

```
@@ -1,7 +1,7 @@        title line
@@ -23,9 +23,22 @@      header prose: three removed lines, sixteen added
@@ -53,6 +66,15 @@      Definitions table: nine added lines
@@ -77,6 +99,25 @@      Key results table: nineteen added lines
@@ -97,6 +138,7 @@      one added Require Import line
@@ -325,6 +367,157 @@    the new material, before "The ideal functionality"
```

Counted: four removed content lines (the title at production `:4`, and the three
lines `:26-28` saying that neither further row is written as a program) and 197
added content lines. This matches the spec's own count.

Invariant 5 holds. The last hunk begins at production line 325, which is the
`Qed.` of `five_card_exact_view_secrecy`, and inserts before the
`The ideal functionality` banner. Everything at or above production line 324 is
byte-identical apart from the header, so `five_card_committed`,
`five_card_colour_fill`, `five_card_viewS_nth`, `five_card_static_obsE`,
`five_card_viewS_indep`, `five_card_exact_viewE`, `five_card_static_obs_indep`,
`five_card_exact_witness`, `five_card_row_uniform_tableau`,
`five_card_row_uniform_rowE` and `five_card_exact_view_secrecy` are unchanged in
statement and in proof. The functionality block after the insertion is
unchanged, including its pre-existing `Fail Definition five_card_F_or`.

The one new import is `From pgg_smc Require Import kim_input_privacy.` at
landing:141.

## B2. The two programs, the shared prefix, and what `Tableau Sampled` proves

**Type.** `five_card_row_repeated_tableau : Tableau Sampled` (landing:379) and
`five_card_row_biased_tableau : Tableau Sampled` (landing:396). Both elaborate;
run 2 prints `five_card_row_repeated_tableau is defined` and
`five_card_row_biased_tableau is defined`.

**One prefix value.** `s sample f` is notation for `s ;;; sample_step of f`
(`manifest/pgg_tableau_syntax.v:366`), which is
`tableau_bind s sample_step f = sample_step (tableau_at s) (tableau_thm s) f`
(`manifest/pgg_tableau.v:428-431`). Both definitions name `five_card_committed`
in that slot, so the prefix is literally one value before any lemma is stated.
The `prefixE` lemmas are a weaker derived record of it.

**What the `prefixE` lemmas state.** Three conjuncts: the algebra `projT1`, the
run parameters `projT1 (projT2 _)`, and
`sp_obs (tableau_at <row>) = ob_obs (tableau_at five_card_committed)`.

Does the third carry the three run facts? Yes, as terms.
`instance_observed A E Ht He Hr` is
`MkObservedExecution (instance_profile A) (instance_exec E) 0 (ex_content_obs E)
(ex_expected E) Ht He Hr` (`protocol/pgg_instance.v:366-370`), and
`oe_terminates`, `oe_endpoints`, `oe_static_recon` are the record's last three
fields (`protocol/pgg_observed_execution.v:110-135`). `sample_step` rebuilds the
stack as `existT _ (ob_Ht x) (existT _ (ob_He x) (existT _ (ob_Hr x) f))`
(`manifest/pgg_tableau.v:505-506`), so `sp_Ht`, `sp_He`, `sp_Hr` of the result
are `ob_Ht`, `ob_He`, `ob_Hr` of the prefix by conversion.

I checked that directly rather than inferring it. In run 4 both

```
Lemma audit_prefix_five_repeated :
  [/\ projT1 (...) = projT1 (...), projT1 (projT2 (...)) = projT1 (projT2 (...)),
      sp_Ht (tableau_at five_card_row_repeated_tableau)
      = ob_Ht (tableau_at five_card_committed),
      sp_He (...) = ob_He (...) & sp_Hr (...) = ob_Hr (...)].
Proof. by split. Qed.
```

and its biased twin close with `No more goals.` So the stronger five-conjunct
statement is available; the landed three-conjunct one is simply weaker as a
proposition (S3).

The alien-family mutation fires, captured verbatim in run 2:

```
The command has indeed failed with message:
The term "S5Analysis.rand_family" has type
 "AnalysisModelFamily s5_exec.s5_rand_observed"
while it is expected to have type
 "FamPayload (tableau_at five_card_committed)".
```

**`sample_step`'s own obligation.** `manifest/pgg_tableau.v:502-511`:

```coq
Definition sample_step (x : StackAt Observed) (q : StackProp Observed x)
    (f : FamPayload x) : Tableau Sampled :=
  @MkTableau Sampled (StackProp Sampled)
    (existT _ (projT1 x) (existT _ (projT1 (projT2 x))
       (existT _ (ob_Ht x) (existT _ (ob_He x) (existT _ (ob_Hr x) f)))))
    (conj q (fun R idx C =>
               @sa_coalition_viewE R (instance_profile (projT1 x))
                 (instance_exec (projT1 (projT2 x))) (amf_sample f R idx) 0
                 (ex_content_obs (projT1 (projT2 x)))
                 (fun u => ob_He x _ _) C)).
```

The proof term is a function of `x`, `q` and `f` alone. `sa_coalition_viewE`
(`security/pgg_sample_adapter.v:265`) is the generic lemma
`sa_coalition_view C = sa_static_coalition_view C`, and its endpoint hypothesis
is discharged from `ob_He x`, a field of the prefix. Kim's two families enter
only as `f`. Nothing about `kim_centi_family` or `kim_biased_family` is
consulted, and no instance fact is used that the uniform family does not also
use. The obligation is therefore discharged by exactly the same generic argument
as for the uniform family, with `f` substituted.

**What reaching `Sampled` proves, exactly.**
`StackProp Sampled q = oe_correct_prop (sp_obs q) /\ sampled_viewE_prop (sp_f q)`
(`manifest/pgg_tableau.v:396-397`). Run 4 prints the two components at the
repeated row:

```
proj1 (tableau_thm five_card_row_repeated_tableau)
     : oe_correct_prop (sp_obs (tableau_at five_card_row_repeated_tableau))
proj2 (tableau_thm five_card_row_repeated_tableau)
     : sampled_viewE_prop (sp_f (tableau_at five_card_row_repeated_tableau))
```

- `oe_correct_prop` (`manifest/pgg_tableau.v:256-271`): at every run argument and
  every cut in the group, every process reaches `Finish`, the endpoint list has
  one entry per seat, and decoding the executed endpoints returns the expected
  value. This is run correctness.
- `sampled_viewE_prop` (`manifest/pgg_tableau.v:286-295`): at every real field,
  every family index and **every** coalition `C`, the executed coalition reader
  equals `fun u => static_coalition_obs C (sa_arg u) (sa_cut u)`. This is an
  identification of two readers, not a statement about what either reveals.

A `Tableau Sampled` therefore asserts nothing about security. It says the run
computes what it is meant to compute, and that a coalition's executed reading is
its static reading. No probability is bounded, no secret appears, no threshold
appears. The security propositions live one level up, in `ExactProp` and
`SpectralPropAt` under `PortProp` (`manifest/pgg_tableau.v:302-372`), and neither
Kim row reaches them.

## B3. `modelE`: does it pin the law?

`sp_f (tableau_at five_card_row_repeated_tableau) = apr_model five_card_row_repeated`
and its biased twin close `by []` (run 2: `No more goals.` for both).

The question is whether the equation could hold while the program samples a law
other than the one the manifest's theorems are about. It cannot, and I checked
the whole chain by conversion in run 4 rather than reading it off:

```
erefl : FiveCardAnalysis.centi_family = kim_centi_family
erefl : FiveCardAnalysis.biased_family = kim_biased_family
erefl : FiveCardAnalysis.observed = five_card_observed

fun R : realType => erefl
  : amf_sample (apr_model five_card_row_repeated) R tt
  = FiveCardAnalysis.centi_sample R
fun R : realType => erefl
  : amf_sample (apr_model five_card_row_biased) R tt
  = FiveCardAnalysis.single_biased_sample (kim_centi_lt R) (kim_centi_gt R)
```

So: the manifest row's model slot, evaluated at its unique index, is the concrete
sample adapter the manifest's own bound theorems name.
`FiveCardAnalysis.centi_sample := kim_centi_repeated_sample`
(`instances/kim2025/five_card_analysis.v:210`), which is the adapter
`kim_centi_cut_distE` (`five_card_models.v:402`) and therefore
`kim_deal_centi_lt` speak about.
`FiveCardAnalysis.single_biased_sample := @kim_single_sample`
(`five_card_analysis.v:204`), whose `sa_sampleP` is Kim's input law (B6).
Both families are unit-indexed (`amf_index = fun _ => unit`,
`five_card_models.v:426-446`), so one member is the whole family and there is no
index at which the family could differ from what the theorems cover.

`modelE` is the right statement. Equality of families forces equality of every
member, hence of `sa_sampleP` and `sa_cut_dist` at every real field.

## B4. The level statements and the recorded `Fail`

`five_card_row_repeated_at_manifest_level : Tableau (apr_completion five_card_row_repeated)`
(landing:449) typechecks; run 2 prints
`five_card_row_repeated_at_manifest_level is defined`. Because `TableauAt` takes
the level as a parameter, the ascription forces
`apr_completion five_card_row_repeated` to be convertible to `Sampled`. The
manifest checks the same equation itself at
`manifest/pgg_analysis_manifest.v:1787`.

`five_card_row_biased_levelE : apr_completion five_card_row_biased = AnalysisBridged`
(landing:454) closes `by []`.

The `Fail` at landing:462, re-captured verbatim in run 2:

```
The command has indeed failed with message:
The term "five_card_row_biased_tableau" has type "Tableau Sampled"
while it is expected to have type
 "Tableau (apr_completion five_card_row_biased)".
```

This is the level mismatch and nothing else. It names both level terms, the
program's `Sampled` and the manifest's `apr_completion five_card_row_biased`, and
it is a type error, not a parse error or an unbound name. See S4 for why the gap
does not depend on the `Fail` surviving future edits.

**Is the manifest's higher level honest?** Yes. `manifest/pgg_analysis_manifest.v:322-328`:

```
(* Level justification. single_biased_sample is the sample adapter with the   *)
(* same carrier and the same argument and cut maps as uniform_sample and with *)
(* Kim's biased distribution, and single_cut_distE identifies its cut         *)
(* distribution with the biased rotation, giving Sampled.                     *)
(* colour_view_leak_bound bounds a conditional mutual information of a joint  *)
(* distribution whose middle component is the executed reader colour_view     *)
(* itself, over that same biased distribution, giving AnalysisBridged.        *)
```

The manifest's criterion for `AnalysisBridged` is stated where the level is
defined: "AnalysisBridged adds a theorem about that distribution and that
observer" (`manifest/pgg_analysis_status.v:59`), and any security, leakage,
mixing or limitation theorem satisfies it. The Tableau's criterion is narrower:
one of the two `certify` arms supplied. Both are correct under their own
definitions; the same constructor is admitted by two different criteria.

The landing copy's comments describe the manifest's justification faithfully.
They name the same theorem, `five_card_colour_view_leak_bound`, and the same
reason, that a conditional mutual information bound is not what either arm asks
for. What they omit is the sentence that keeps a reader from concluding that the
manifest overclaims (S2). Also note that the manifest's own row 4 table already
says `| bound or certificate | none; kim_leak_bound is the numeric constant of
the bridge theorem, not a shuffle certificate |` and `| missing premise | the
ideal distribution equality, as in row 3 |`, so the manifest is not hiding
anything.

## B5. `five_card_row_repeated_endpoint_lt`

Statement as landed (landing:477):

```coq
Lemma five_card_row_repeated_endpoint_lt (R : realType) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
              (sa_cut_dist (amf_sample kim_centi_family R tt)))
           (fdist_uniform (card_ord 5))
  < 2%:R ^- 40.
Proof. by rewrite kim_centi_cut_distE; exact: kim_deal_centi_lt. Qed.
```

**Is `sa_cut_dist (amf_sample kim_centi_family R tt)` the cut law the repeated row
samples?** Yes, and by conversion. Run 4:

```
fun R : realType => erefl
  : sa_cut_dist (amf_sample kim_centi_family R tt)
  = sa_cut_dist (kim_centi_repeated_sample R)
```

and `kim_centi_family`'s only member is `kim_centi_repeated_sample R`
(`five_card_models.v:443-446`), which is the adapter the program's payload names.
`kim_centi_cut_distE` (`five_card_models.v:402`) then rewrites it to
`sw_rho_dist (scb_bound (kim_security_bundle_centi R))`, the exact left-hand side
of `kim_deal_centi_lt` (`instances/kim2025/five_card_kim.v:646`). Two lemmas, not
three: `kim_centi_witness_rhoE` is not used (S6).

**What does `sigma` act on?** `sigma : {perm 'I_5}` and `s : 'I_5`, so `sigma s`
is an element of `'I_5`. Throughout this development `'I_5` in the cut's
codomain is a card position: `static_coalition_obs` reads
`tnth (den_boer_layout u.1) (pgg_rho sigma (tnth (pi_starts FiveCardKim_PI) i))`
(`instances/kim2025/five_card_rows.v:191-196`), that is, it applies the cut to a
seat's starting position and indexes the layout at the image. `fdist_uniform
(card_ord 5)` is the uniform law on the same `'I_5`. So both sides are laws on
card positions, and the statement is: the law of the image of one starting
position under the repeated cut is within `2^-40` of uniform in variation
distance. It quantifies over `s : 'I_5` and over `R : realType` and over nothing
else. It names no set of seats, no secret, no coalition, no reveal pattern.

The landed comment says exactly that. It mentions "no set of seats and no
secret" only to deny them, which serves invariant 2 rather than breaching it.
One looseness: the comment says "at every seat" for a variable the statement uses
as a position; at this instance `pi_starts FiveCardKim_PI = ord_tuple 5`, so seat
`i` starts at position `i` and the two coincide (S5).

**Mutations.** Both re-captured in run 4, from this audit's own file, not from
the probe's:

```
Fail Definition audit_endpoint_lt41 ... < 2%:R ^- 41 := ltac:(...).
  The command has indeed failed with message:
  Cannot apply lemma kim_deal_centi_lt

Fail Definition audit_endpoint_pair_lt (R : realType) (s s' : 'I_5) :
  var_dist (fdistmap (fun sigma => (sigma s, sigma s')) ...) ... := ltac:(...).
  The command has indeed failed with message:
  Cannot apply lemma kim_deal_centi_lt
```

Both fail at the `exact:` step, which means the `rewrite kim_centi_cut_distE`
succeeded in each case and the failure is the final application: `2^-41` is not
what `kim_deal_centi_lt` bounds, and a law on `'I_5 * 'I_5` is not the carrier it
is stated at. The lemma therefore says what its comment says and no more.

**Non-vacuity.** `var_dist P Q = \sum_a |P a - Q a|` is bounded by `2` for any two
laws. `2^-40 ~ 9.1e-13`. The bound is eleven orders of magnitude inside the
trivial ceiling. The inequality is strict, `<`, the same relation
`kim_deal_centi_lt` proves; nothing was weakened to `<=` and nothing was
tightened.

## B6. `five_card_row_biased_leak_bound`

### (a) Is the law Kim's input law?

Run 4, this audit's own check:

```
fun R : realType => erefl
  : sa_sampleP (amf_sample kim_biased_family R tt)
  = kim_input_dist (kim_centi_lt R) (kim_centi_gt R)
```

So the ascription of the three random variables at
`sa_sampleP (amf_sample kim_biased_family R tt)` changes nothing: it is Kim's own
joint law by conversion, and `five_card_colour_view_leak_bound` already lives on
it. The restatement consumes none of the manifest's three bridge lemmas.

I also ran the negative control the probe did not run, to check that the
ascription is not vacuous about which law it names:

```
Fail Check (fun R : realType => erefl
  : sa_sampleP (amf_sample five_card_uniform_family R tt)
  = kim_input_dist (kim_centi_lt R) (kim_centi_gt R)).

The command has indeed failed with message:
... (cannot unify "sa_sampleP (amf_sample five_card_uniform_family R tt)" and
"kim_input_dist (kim_centi_lt R) (kim_centi_gt R)").
```

The uniform family's member is a different law. The biased row's bound is
genuinely stated at the biased row's law.

### (b) Argument order of `cond_mutual_info`

infotheo, `information_theory/entropy.v:1084-1087`:

```coq
(* I(X;Y|Z) = H(X|Z) - H(X|Y,Z) 2.60 *)
Definition cond_mutual_info :=
  centropy (fdist_proj13 PQR) - centropy (fdistA PQR).
```

for `PQR : R.-fdist (A * B * C)`. `fdist_proj13` keeps the first and third
components, so the first term is `H(A | C)` and the second is `H(A | B, C)`;
`cond_mutual_info PQR = I(A ; B | C)`. The conditioning variable is the **third**
component.

The landed triple is
`[% kim_inputs, (executed colour reading), kim_secret]`, so the statement is
`I(Inputs ; executed colour reading | Secret)`. That is what
`instances/kim2025/kim_input_privacy.v:21` writes as
`I(Inputs ; View | Secret) <= kim_leak_bound eps`, and what the comment at
landing:495-504 says: "between the two committed inputs and the executed colour
reading at a list of card positions, given the conjunction the run computes".
Correct. `kim_secret` is `a && b` (`kim_input_privacy.v:68`), the conjunction the
run computes.

The reading of `A` is also correct. `five_card_exec_colour_view A` is documented
in production as "decoded ... as colours at a list of card positions A"
(`five_card_models.v:277-283`), and `ViewA A` as "the partial view at the fixed
list of card positions A" (`five_card_leakage.v:78-83`). The landed comment's
"at a list of card positions" is the file's own vocabulary, not a softening.

### (c) `kim_centi_small`

`kim_centi_small (R : realType) : 0 < 5%:R^-1 - `|1 / 100 : R|` (landing:489).

It is the right condition. `kim_input_private`'s side condition is
`Hypothesis eps_small : 0 < 5%:R^-1 - `|eps|`
(`kim_input_privacy.v:439`), which `five_card_colour_view_leak_bound` takes as a
section hypothesis (`five_card_models.v:352`). `kim_centi_spec` is a different
condition, `` `|1 / 100| < 4%:R / 5%:R `` (`five_card_kim.v:612`), the spectral
one. The landed comment says exactly this, naming `kim_input_private` and
distinguishing the fourth condition from `kim_centi_lt`, `kim_centi_gt` and
`kim_centi_spec`.

True and non-vacuous: `1/5 - 1/100 = 19/100 > 0`. The proof compiles and its
assumption closure is the classical trio.

### (d) Does any comment overclaim?

No. The comment at landing:495-504 says the statement "is a numeric ceiling on
that information and not the assertion that the information vanishes, it is about
a reading at a list of card positions and not about a coalition of seats, and it
is carried beside the program above rather than by it". It does not use
"coalition privacy", does not claim exact independence, does not use "secrecy",
and does not call the bound a certificate of the row.

The two halves of the probe's claim about positivity both hold:

- No lemma anywhere proves `kim_leak_bound (1/100) > 0`. A whole-tree scan of the
  133 `.v` files under `lib protocol groups security smc reconstruct instances
  manifest` for `kim_leak_bound` returns the definition
  (`kim_input_privacy.v:78`), two bound statements (`kim_input_privacy.v:717`,
  `five_card_models.v:364`), one `Corollary` at bias zero
  (`kim_input_privacy.v:757`), one rewriting step (`:736-737`) and six comment
  lines. No positivity statement.
- No landed comment says the bound is positive.

### Is the bound vacuous?

No, by a wide margin. `log` in infotheo is base two
(`lib/realType_ln.v:177`, `Definition log x := Log 2 x`), and
`kim_leak_bound e = 12 * log(e_const) * e^2 / (1/5 - |e|)`
(`kim_input_privacy.v:78-79`). At `e = 1/100`:

```
  12 * log_2(e) * (1/100)^2 / (1/5 - 1/100)
= 12 * 1.4426950... * 1e-4 / 0.19
= 0.0091118...   bits
```

Even with the crude enclosure `1 < log_2(e) < 1.5` the value is below
`0.0095` bits.

The trivial ceilings, in the same units:

- `log 2 = Log 2 2 = 1` bit.
- `H(Inputs) = 2` bits, the inputs being uniform on four values
  (`kim_input_privacy.v:53-60`).
- The sharpest trivial ceiling for this quantity is
  `I(Inputs ; View | Secret) <= H(Inputs | Secret) = H(Inputs) - H(Secret)`,
  because `Secret` is a function of `Inputs`. The development itself computes
  `H(Secret) = 2 - (3/4) log 3` (`five_card_leakage.v:89`), so
  `H(Inputs | Secret) = (3/4) log 3 = 1.1887...` bits.

`0.0091 < 1.1887` by a factor of about 130. The bound carries information; the
`AnalysisBridged` level the manifest gives the biased row does not rest on a
vacuous number. Nothing in the landing copy presents the number as larger or
smaller than it is, because nothing in the landing copy evaluates it at all.

## B7. K8, and whether the scope is stated honestly

I re-ran the three searches, in Python with `\b` word boundaries, since BSD
`grep -E '[[:<:]]'` matches nothing on this machine. 133 `.v` files under
`lib protocol groups security smc reconstruct instances manifest`.

**Independence at the biased law.** Lines carrying `kim_input_dist`,
`kim_single_sample` or `kim_biased_family` together with any of `_|_`,
`inde_RV`, `indep`, `independen`: **zero hits**. The exact arm's one missing
field, `ew_indep`, has no theorem behind it at this law.

**Variation distance on the cut group.** Every `var_dist` statement in the
five-card cone is in `instances/kim2025/five_card_kim.v`, and each is of the
shape `var_dist (fdistmap (fun sigma => sigma s) ...) (fdist_uniform (card_ord 5))`,
that is, a law on `'I_5` at one starting position:
`:414`, `:464`, `:575`, `:646` (`kim_deal_centi_lt`), `:661`
(`kim_one_cut_centiE`). The spectral arm's `sc_close` asks for
`var_dist (sw_rho_dist sc_b) sc_ideal <= sw_bound_eps sc_b`
(`manifest/pgg_tableau.v:137`), between two laws on the cut group
`pgg_gT (mp_M ...)`. Nothing of that shape exists for this instance.

**Constancy in the run argument.** `sc_const` (`manifest/pgg_tableau.v:138`) has
one instance of its shape in the tree, `pgl27_word_view_const`
(`instances/pgl27/pgl27_rows.v:224`), supplied there by three-transitivity of
PGL(2,7); also `pgl27_view_law_const` (`pgl27_word_privacy.v:168`). The five-card
development states nothing of that shape at any cut law.

So K8's compiled conclusion stands: neither arm can be supplied for the biased
row from theorems that exist today.

**Is the scope honest?** Yes. The header sentence (landing:35-40) reads

```
(* kind: the exact arm asks for independence of the static coalition          *)
(* observation from a secret, which the development states under the          *)
(* uniform cut and not under the biased one, and the spectral arm asks for    *)
(* a variation distance to an ideal cut on the shuffle group together with    *)
(* the constancy of a coalition's reading of that ideal, and neither of       *)
(* those is proved at this instance.                                          *)
```

"which the development states under the uniform cut and not under the biased
one" is a statement about this development, and "neither of those is proved at
this instance" is a statement about what exists here. Neither says "cannot be
proved". The biased row's own comment (landing:383-395) uses the same two
formulations. No landed comment slides from "not supplied here" to "not
provable".

The scope is in fact conservative in the useful direction. The exact arm's
`ew_indep` at the biased cut is not merely unproved: Kim's whole point is that a
biased cut leaks, so that conjunct is expected to be false. Saying "not proved"
understates rather than overstates.

## B8. Invariants 2, 3, 4, 6

Every occurrence of `privacy`, `private`, `secrec`, `secure`, `securit`,
`certif`, `independen`, `coalition` and `leak` in the new material
(landing:368-520), read in context:

| line | text | reading |
|---|---|---|
| 378 | "not about what any set of seats reads, so no security payload follows it" | denial; serves invariant 2 |
| 386-392 | "bounds a conditional mutual information ... the exact arm asks for independence ... the spectral arm asks for ... constancy of a coalition's reading of that ideal, neither of which is proved at this instance" | describes the two arms, attributes the manifest's level to the theorem; serves invariant 3 |
| 485-487 | "the smallness condition of kim_input_private ... the one Kim's input-privacy bound consumes" | names the side condition's role |
| 497-503 | "at most kim_leak_bound at bias one hundredth ... a numeric ceiling ... not the assertion that the information vanishes ... not about a coalition of seats ... carried beside the program above rather than by it" | denial of three readings; serves invariants 2 and 3 |

No line claims coalition privacy, certification by the Tableau, exact
independence, secrecy, or positivity of the bound. Invariants 2 and 3 hold.

Invariant 4: the diff touches one file. Nothing under `manifest/` changes, no
`certify` arm is added, no completion level is redefined. Invariant 6: see B2,
the prefix is one value by construction and the `prefixE` lemmas are compiled.

`git status --short -- lib protocol groups security smc reconstruct instances
manifest _CoqProject` is empty, at the start of this audit and at its end. The
landing copy is not applied.

## B9. Dependencies

Recomputed in Python from `/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/.Makefile.rocq.d`
(188546 bytes, written 2026-09-18 23:01), joining line continuations, reading each
`target...: prereq...` rule as edges from every prerequisite to every target, and
taking the forward transitive closure.

```
forward closure of instances/kim2025/five_card_rows.vo : []
  .vo of any other module in that closure              : NONE
sanity: forward closure of manifest/pgg_tableau.vo contains
  instances/kim2025/five_card_rows.vo, instances/pgl27/pgl27_rows.vo,
  instances/psl211/psl211_rows.vo, instances/s5/s5_rows.vo,
  manifest/pgg_tableau_syntax.vo, and 15 further targets
```

Confirmed independently by a whole-tree scan: `five_card_rows` occurs on exactly
one line in the 133 `.v` files, the file's own header at
`instances/kim2025/five_card_rows.v:4`. Nothing requires it. Editing it
recompiles that file alone.

The new import adds no build-graph edge:
`instances/kim2025/five_card_models.v:33` is
`From pgg_smc Require Import five_card_exec kim_input_privacy.`, and
`five_card_models` is already required by `five_card_rows.v`.

Nothing here touches `instances/psl211/psl211_endpoints.v` or any other psl211
file; no psl211 file appears in the diff, in the new imports, or in any new
statement.

## B10. The spec, read against what the probe supports

Correct and supported: the pinned carrier and all cited line numbers except S6;
the flow block; the parameterised-monad reading of the Tableau, which matches
`tableau_bind` / `tableau_start` / `tableau_left_unit`
(`manifest/pgg_tableau.v:428-456`); soundness invariants 1 and 4 to 7; the
out-of-scope list.

Corrected by the probe and already folded into the spec's "Probe results": K5 is
landed as a type ascription rather than as `five_card_row_repeated_levelE`, which
is stronger; K6 needs two lemmas and not three; K7 needs a fourth side condition
the tree did not carry.

Remaining gaps for a plan written from the landing copy verbatim:

1. The header's first paragraph (S1). This is the one item that must be settled
   before the file lands, because it is the only place in the landing copy where
   a reader can acquire the coalition reading of the biased row's bound.
2. The absence of a clause distinguishing the manifest's admission criterion for
   `AnalysisBridged` from the Tableau's (S2).
3. `kim_centi_small` sits in `five_card_rows.v` rather than in
   `five_card_kim.v` beside `kim_centi_lt`, `kim_centi_gt` and `kim_centi_spec`.
   The probe records the reason and records the move as future work. This is a
   placement question for the naming audit, not a soundness question.
4. The spec's sentence "three conjuncts pin five components" is stronger than the
   landed lemma (S3). Either land the five-conjunct form or soften the sentence.

Nothing in the spec is vacuous. Nothing in the spec is stronger than the probe
supports except the two wording items S3 and S6. Everything a plan needs is
present: the landing copy is a complete file, its one new import is named, the
placement decision is recorded with its reason, and the compile scope is one
file.

## Assumption closure

Run 4 ran `Print Assumptions` on all eleven new declarations against this
audit's own build of the landing copy.

| declaration | verdict |
|---|---|
| `five_card_row_repeated_tableau` | the three `boolp` axioms |
| `five_card_row_biased_tableau` | the three `boolp` axioms |
| `five_card_row_repeated_prefixE` | the three `boolp` axioms |
| `five_card_row_biased_prefixE` | the three `boolp` axioms |
| `five_card_row_repeated_modelE` | the three `boolp` axioms |
| `five_card_row_biased_modelE` | the three `boolp` axioms |
| `five_card_row_repeated_at_manifest_level` | the three `boolp` axioms |
| `five_card_row_biased_levelE` | `Closed under the global context` |
| `five_card_row_repeated_endpoint_lt` | the three `boolp` axioms |
| `kim_centi_small` | the three `boolp` axioms |
| `five_card_row_biased_leak_bound` | the three `boolp` axioms |

The three are `propositional_extensionality`,
`functional_extensionality_dep` and `constructive_indefinite_description`, the
repository's classical trio, which every fdist-record statement in this tree
carries. No fourth name appears anywhere in the output. This reproduces
`kim_fidelity.v`'s report exactly.

## What the paper may say about Kim's two rows, and what it may not

**May say.**

- One prefix, `five_card_committed`, and three continuations. This is a compiled
  fact, not a layout convention: the three rows are three applications of
  `sample_step` to one value, and the `prefixE` lemmas record it.
- The three rows differ in exactly one line, the probability model, and in how
  far the security mathematics then reaches.
- The uniform row reaches `AnalysisBridged` and publishes the manifest's
  `five_card_row_uniform` through the exact arm. What it certifies is coalition
  privacy below the threshold of two seats: at `#|C| < 2`, the executed
  coalition view is independent of the conjunction, carries zero mutual
  information with it, leaves its entropy unchanged, and stays independent under
  every deterministic post-processing (`five_card_exact_view_secrecy`).
- Both Kim rows stop at `Sampled`. Reaching `Sampled` proves run correctness and
  the identification of the executed coalition reader with the static one. It
  proves nothing about security, and this is the reason the rows stop there.
- Beside the repeated row: for every seat and every real field, the law of the
  image of one starting position under the seven-cut law at bias one hundredth is
  within `2^-40` of uniform in variation distance. This is an endpoint marginal.
- Beside the biased row: for every list of card positions and every real field,
  the conditional mutual information between the two committed inputs and the
  executed colour reading, given the conjunction the run computes, is at most
  `kim_leak_bound (1/100)`, about `0.0091` bits. This is input privacy under a
  biased cut, in den Boer's second sense, and it holds at every reveal pattern
  including the full one.
- The biased row's manifest level is `AnalysisBridged` while its program reaches
  `Sampled`, and both are correct: the manifest's level records that a theorem
  exists about the row's own distribution and observer, the program's level
  records that one of two specific `certify` arms was supplied. Neither arm
  accepts a conditional mutual information bound.
- Neither arm can be supplied for the biased row from theorems that exist in the
  development today. For the exact arm the one missing field is `ew_indep`; for
  the spectral arm, `sc_b`, `sc_Hd` and `sc_ideal` can be built and `sc_close`
  and `sc_const` cannot.

**May not say.**

- That the `2^-40` bound is privacy of any kind. It quantifies over one starting
  position. It names no coalition, no reveal pattern and no secret, and the
  repeated row carries no security payload.
- That the repeated row shows Kim's seven cuts make the protocol private. Mixing
  of one endpoint marginal is not indistinguishability of a coalition's view.
- That `kim_leak_bound (1/100)` is a coalition-privacy bound, or that it is
  restricted to coalitions below the threshold. It is stated at an unrestricted
  list of card positions.
- That the leak bound says the executed reading is independent of the inputs, or
  that the leakage is exactly this number. It is an upper bound, and no lemma in
  the tree proves it positive.
- That the leak bound limits what a viewer learns about the output `a && b`. It
  is conditioned on that output and bounds only what is learned about the two
  bits beyond it.
- That the biased row is certified by the Tableau, or that the manifest is wrong
  to place it at `AnalysisBridged`.
- That reaching `Sampled` is evidence of anything about security.
- That either Kim row is at the same evidential standing as the uniform row.

VERDICT: GO
