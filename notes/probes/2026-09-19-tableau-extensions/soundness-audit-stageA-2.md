# Independent soundness audit of stage A, second round

**NO-GO.** Two blocking findings, both sentences written during fix pass 1:
one comment in `t0_sampled_branch_pgl27.v` names a mechanism the compiler did
not use, and `STATUS.md` step 3 records a `Fail` the same fix pass deleted and
asserts of it the opposite of what the D8 entry says. Everything else holds.
The Tableau copy itself (`pgg_tableau.v`, `pgg_tableau_syntax.v`) is sound: the
four new general lemmas are true, the composite statement a paper's table needs
is derivable from them by rewriting, the weakened `conclude` obligation rests on
exactly the monotonicity the comments now name, no new assumed constant enters,
and neither design rule is broken. Both blocking items have a one-paragraph
replacement below.

Date 2026-09-19. Commit 83045c5 plus fix pass 1. The author of this report
wrote none of the probe and neither first-round audit.

## What was compiled

Thirty-one single-file compiles through the shared lock wrapper, flags from the
production `_CoqProject` plus `-Q <probe dir> tableau_ext_probe`, `-time` on,
return codes from Python `subprocess`. Files under
`notes/probes/2026-09-19-tableau-extensions/audit-soundness-2/`.

| file | what it measures | rc |
|---|---|---|
| `q1_composite.v` | the composite arm statement from the four general lemmas | 1, at the fourth lemma only, see N1 |
| `q2p_identifiers.v` | the seven tokens the header says stay identifiers | 0 |
| `q2n_<token>.v`, nineteen files | the nineteen the header calls keywords | 1 each, parse error |
| `q4a_cross_model.v`, `q4b_cross_model_back.v` | the two cross-model `Fail`s without `Fail` | 1 each |
| `q5a_unindexed.v`, `q5b_unindexed_bind.v` | the replaced recorded `Fail` without `Fail` | 1 each |
| `q6a_unconcluded_done.v` | `by []` on the unconcluded coordinate pair | 0, tactic 0.091 s |
| `q6b_concluded_done.v` | `by []` on the concluded pair | 124, no return in 150 s |
| `q7_prod_s5.v` | `Print Assumptions` on the production S5 row | 0 |
| `t0_sampled_branch.v` recompiled | the time of its `by split` | 0, tactic 0.001 s |

`instances/psl211/psl211_endpoints.v` was never opened and never compiled. No
`make`. No git command that changes state. Nothing edited outside
`soundness-audit-stageA-2.md` and `audit-soundness-2/`.

## Findings

| ID | class | content | evidence | replacement |
|---|---|---|---|---|
| S1 | BLOCKING | `t0_sampled_branch_pgl27.v`, above the cross-model `Fail`s: "so the sample adapter the witness is stated over and the one the branch point reached are compared where the clause is written" | the two adapters are never compared. Compiled without `Fail`: `(cannot unify "amf_index (sp_f (tableau_at pgl27_word_sampled)) R" and "unit")`, and in the other direction `... and "{fdist bool}%fdist"`. Unification stops at the index type of the family, one binder before the adapter | R1 below |
| S2 | BLOCKING | `STATUS.md` step 3: "The recorded `Fail` `pgl27_row_word39_bare` still fails ... Its reason is unchanged, the payload is not quantified over the field and the index ... The same `Fail` is kept in both surfaces (`pgl27_row_word39_bare`, `pgl27_row_word39_bare_bind`)" | no declaration whose name contains `_bare` exists in any probe file. The D8 entry of the same document says the opposite: "The `Fail` whose comment claimed to isolate the quantification no longer did so after C ... It is replaced". Step 4 repeats the dead name, and so does the D2 row `:389-394` | R2 below |
| S3 | SHOULD | `STATUS.md` verdict table, the four "Where" cells `pgg_tableau.v:607-651`, `pgl27_rows.v:382`, `pgl27_rows.v:455-465`, `:467-472`, `pgg_tableau_syntax.v:396-402` | none of the four points at the cited content in the copies after fix pass 1. C1 is at `:650-687`, the changed payload at `:419`, C3 at `:464-491`, the conclude rule at `:398-404`. `pgl27_rows.v:455-465` is the `_unindexed_bind` rejection and `:467-472` the 2^-41 section banner | R3 below |
| S4 | SHOULD | `STATUS.md` D10/D11 code site names only `notes/probes/2026-09-19-kim-spectral-arm/kim_spectral_rows_probe.v:288` and `:365` | both lines are exact, but the same two rows now also stand in the landing probe that would carry them to production, `notes/probes/2026-09-19-kim-spectral-landing/five_card_rows.v:745` and `:788`, with a recorded `Fail` at `:751-757` and a third equality payload in that directory's `pgl27_rows.v:382`. A Kim landing edits that copy, not the arm probe | R4 below |
| S5 | SHOULD | `STATUS.md` D10/D11: "makes the two published rows equal by `erefl`" | `five_card_row_repeated_spectral_tableau : PublishedRow` and `five_card_row_repeated39 : PublishedRowAt five_card_reprice39` are at different `Reprice` indices, so they are of two types and no equation between them is well formed. What becomes one term is their `published_at` coordinate | R5 below |
| S6 | SHOULD | nothing records what a new arm costs | `SecurityArm` mirrors `SecurityPort`'s constructors. Adding `IdealProximity` costs a constructor in `SecurityPort`, a constructor in `SecurityArm`, a branch in `port_arm`, a branch in `PortProp`, a branch in `RepricePayload` and a case in `port_reprice`. `STATUS.md` D1 records only the naming rule for the new tag; no file gives the reason the tag is a second variant | R6 below |
| S7 | SHOULD | `t0_sampled_branch.v`, `t0_row_uniform_atE`, `Proof. by split. Qed.`, three `published_at` equations under one `done` | it is instant here, measured 0.001 s, because no side is concluded. The sibling file records, and my `q6b` confirms, that the same tactic on a concluded side does not return in 150 s. Stage B and the Kim landing both add concluded rows to files of this shape | R7 below |
| S8 | SHOULD | `pgg_tableau.v` header: "it enters as the witness or the certificate a certify statement takes, and once more as the payload of conclude, an inequality between the number the row's own certificate proved and the number the row publishes" | for an exact port the payload is `unit`, not an inequality; `RepricePayload`'s own comment says so two hundred lines below | R8 below |
| S9 | SHOULD | `certify_exact_armE`: "The arm of a row written in the surface is therefore settled by one line of it" | the "therefore" attributes to this lemma what needs `conclude_armE` and `publish_armE` as well; `certify_spectral_armE`'s comment gets this right by saying "Together with the previous lemma" | R9 below |
| N1 | NOTE | `conclude` cannot be applied twice, and nothing says so | `q1_composite.v`: a second `conclude` is rejected, `cannot unify "BridgedProp c q0" and "StackProp AnalysisBridged q0"`. `restate` cannot follow `conclude` either, for the same reason. This is a good property and it bounds the shapes the surface can write, which is why the four `_armE` lemmas cover all of them |
| N2 | NOTE | `certify_spectral_armE`: "the two statements are the only ones that build a port" | true of the Tableau's statements, and checked: the only applications of `ExactIndependence` and `SpectralDecay` as constructors in the copy are at `:625` and `:641`, and the only two `existT` chains at `AnalysisBridged` are in the same two definitions. It is not true of the ambient logic, where a hand-written coordinate may carry a port that branches on the index. `ab_arm`'s comment carries the right hedge, "for a row written in the surface" |
| N3 | NOTE | `STATUS.md` G3 row `\|`:63`\|` (index) \| no change \|` | the row records a line that does not change and reads as a table entry with no content. The information it carries, that the index lists no level accessor, belongs in the D1 prose where it is already stated |
| N4 | NOTE | `pgg_tableau_syntax.v:393-396` and `:68-71` in the D2 and G3 tables | both start one line inside the sentence they quote: the `publish` comment begins at `:392` and the tokens sentence at `:67` |

## 1. The new lemmas

**The four general ones are true and their comments hold.** Each is an equation
between `SecurityArm` values, closed by conversion.

`certify_exact_armE` and `certify_spectral_armE` are quantified over the data,
the payload, the field and the index, so they hold at every row either
statement can build. Both are correct: `certify_exact` writes
`fun R idx => ExactIndependence (p R idx)` and `certify_spectral` writes
`fun R idx => SpectralDecay (p R idx)`, and `port_arm` reads the constructor.
`conclude_armE` and `publish_armE` are correct because `conclude` returns
`@MkTableau AnalysisBridged (BridgedProp c) q ...` with the incoming `q`, and
`publish` writes that same `q` into `published_at`.

**"The two statements are the only ones that build a port", checked by
reading.** In the copy, the constructors `ExactIndependence` and
`SpectralDecay` are applied in exactly two places, `:625` inside
`certify_exact` and `:641` inside `certify_spectral`. Every other occurrence is
a declaration (`:162`, `:163`) or a pattern in a consumer: `port_arm` (`:180`,
`:181`), `PortProp` (`:409`, `:410`), `RepricePayload` (`:662`, `:663`),
`port_reprice` (`:679`, `:680`). Producers of a `StackAt AnalysisBridged` are
the same two `existT` chains; `conclude`, `restate` and `publish` each pass the
incoming coordinate through unchanged. So within the Tableau the sentence is
true. It is a claim about the Tableau's statements and not about what a term of
the ambient logic can be, and N2 records that boundary.

**The six per-row lemmas.** All six statements match what `STATUS.md` step 5
tabulates, word for word, and each spells its index type. They are true: each
row's `certify` line writes the constructor the lemma names. Their comments say
they are the value a paper's table prints and that the general lemmas are why
that value can be read off the `certify` line, which is exactly their position.

**The exact theorem that would say "the arm of a published row is decided by
its certify line", and whether the four give it.** There is no single Rocq
statement quantifying over "every program the surface can write", because the
surface is notation and not an inductive syntax: a program is a term, and the
theorem would have to quantify over terms. What is provable, and what says the
same thing, is one statement per shape the surface admits. The surface admits a
finished row of exactly one shape, `certify` then at most one `conclude` then
`publish`, because `conclude` demands `StackProp AnalysisBridged q` and returns
`BridgedProp c q`, so it cannot be applied to its own output (N1). Three
statements therefore exhaust it, and all three are provable **from the four by
rewriting alone**, compiled in `q1_composite.v` over arbitrary `Sampled` data:

```coq
Lemma q1_row_e_armE (p : ExactPayload x) (R : realType)
    (idx : amf_index (ab_f (published_at (q1_row_e p))) R) :
  security_arm_of (q1_row_e p) R idx = ExactIndependenceArm.
Proof. by rewrite publish_armE certify_exact_armE. Qed.            (* 0.057 s *)

Lemma q1_row_e_c_armE ... :
  security_arm_of (@q1_row_e_c p c pr) R idx = ExactIndependenceArm.
Proof. by rewrite publish_armE conclude_armE certify_exact_armE. Qed.
                                                                   (* 0.066 s *)
Lemma q1_row_s_c_armE ... :
  security_arm_of (@q1_row_s_c p c pr) R idx = SpectralDecayArm.
Proof. by rewrite publish_armE conclude_armE certify_spectral_armE. Qed.
                                                                   (* 0.078 s *)
```

The fourth, with two `conclude` terminals, does not elaborate, and that is N1.
So the answer is yes, with one qualification the comments already carry: the
entailment is over rows *written in the surface*. A coordinate built by hand
may hold a port that answers one arm at one index and the other at another, and
nothing in the framework forbids it. `ab_arm`'s comment says this correctly and
`STATUS.md` D6 records that no counter-example is compilable today.

## 2. The rewritten sentences, F1 to F4 and F7 to F9

**The header of `pgg_tableau.v`.** "There are five statements" stays true.
"A row commits to one of them and claims nothing about the other, and
security_arm_of names which of the two a finished row committed to" is true.
"it leaves the data and the arms untouched and moves the real the spectral
arm's proposition mentions to any upper bound of it" is true: the obligation is
`cert_eps cert <= odflt (cert_eps cert) (c R)`, so the target is any upper
bound of the row's own bound. The one defect is S8, the conclude payload
described as an inequality without the exact port's `unit` branch.

**`SecurityArm`.** "two rows over one model and one pair of statuses are one
manifest row" is true: `publish` builds
`MkAnalysisPathRow (ab_obs q) AnalysisBridged (ab_f q) t a`, whose five
components are fixed by the model and the two statuses. F2 is closed, and the
comment now agrees with `security_arm_of`'s.

**`ab_arm`.** "The two certify statements build a port whose constructor is the
same at every field and index, so for a row written in the surface the answer
does not depend on either argument" is true and is the statement reason F4
asked for. The old function-type reason is gone.

**`port_reprice` and `RepricePayload`.** True, see section 3.

**`conclude`.** "The terminal concluding a row at a chosen number, against a
proof that the number is at least the row's accumulated bound" now agrees with
the index line. F9's first item is closed. The word "republish" is gone from
the copy.

**The keyword paragraph, derived from the rules and then measured.** I took the
thirteen `Notation` rules of the copy and marked each quoted token by what
precedes it. A token preceded by a slot is a keyword; a token preceded by
another terminal is not.

| rule | tokens after a slot | tokens after a literal |
|---|---|---|
| `A 'dealt' 'fuel' n` | dealt | fuel |
| `A 'functionality' f` | functionality | |
| `t 'encoded' 'inputs' T 'layout' L 'by' enc 'decoded_by' d 'committed_by' procs 'fuel' n` | encoded, layout, by, decoded_by, committed_by, fuel | inputs |
| `A 'supplied' 'inputs' T 'layout' L 'expecting' e 'fuel' n` | supplied, layout, expecting, fuel | inputs |
| `s 'execute' 'terminates' 'by' t 'endpoints' 'by' e 'recon' 'by' r` | execute, endpoints, recon | terminates, by, by, by |
| the same with `'vm_compute'` | execute, endpoints, recon | terminates, by, vm_compute, by, by |
| `s 'sample' f` | sample | |
| `s 'certify' 'ExactIndependence' w` | certify | ExactIndependence |
| `... w 'leaks' 'at' k 'by' H` | leaks, by | at |
| `s 'certify' 'SpectralDecay' c` | certify | SpectralDecay |
| `... 'SpectralDecay' 'at' R idx b 'tied' 'by' Hd 'ideal' u 'mixing' 'by' Hc 'invariant' 'by' Hk` | tied, ideal, mixing, invariant | at, by, by, by |
| `s \|> 'conclude' c 'by' p` | by | conclude |
| `s \|> 'publish' t a` | | publish |

The union of the first column, less `by`, is dealt, functionality, encoded,
layout, decoded_by, committed_by, fuel, supplied, expecting, execute,
endpoints, recon, sample, certify, leaks, tied, ideal, mixing, invariant:
**nineteen**, the same nineteen the paragraph lists and in the same set. The
union of the second column is inputs, terminates, by, vm_compute, at,
ExactIndependence, SpectralDecay, conclude. Every clause of the paragraph
follows:

- "Each follows a slot in some rule": true of all nineteen.
- "fuel is among them: it follows the literal dealt in the dealer-dealt rule
  and would stay an identifier for that rule alone, but it follows a slot in
  the two rules added beside it": true, the slots being `procs` and `e`.
- "The tokens inputs, terminates, publish, conclude, vm_compute,
  ExactIndependence and SpectralDecay follow a literal and stay identifiers":
  true, the literals being encoded or supplied, execute, `|>`, `|>`, by,
  certify and certify.
- "at follows a literal too, the literal leaks in one rule and SpectralDecay in
  the other": true, and `at` occurs in no third rule.
- "by follows the slot L of the encoded rule, the slot k of the leaks rule and
  the slot c of the conclude rule, so it would be a twentieth": true, and those
  are the only three slot positions `by` takes. In the two execute rules and in
  the five-clause spectral rule it follows a literal.

Measured, not only derived. `q2p_identifiers.v` binds all seven of the second
list in one file that requires the extended surface and compiles, rc 0. Each of
the nineteen, bound the same way in its own file, is
`Syntax error: [name] expected after '(' (in [closed_binder]).`, rc 1,
nineteen for nineteen. So the count is right, the two lists are right, and the
`conclude` rule costs no new keyword. F1 is closed, and closed differently from
what the first-round audit proposed: that report's own replacement said `by`
follows a slot in the execute rule, which the table above refutes.

## 3. Monotonicity

**The condition named is the condition the proof uses.** `port_reprice` closes
with

```coq
case: p => [w|cert] //= H1 H2 C x x' HC.
exact: Order.POrderTheory.le_trans (H1 C x x' HC) H2.
```

`H1` is `SpectralPropAt cert (cert_eps cert)` applied, of the form `d <= e`,
and `H2` is `e <= c`. What transitivity supplies is precisely the implication
`e <= c -> SpectralPropAt cert e -> SpectralPropAt cert c`, that is, the
proposition is weakly increasing in its number. So "the spectral arm's
proposition is monotone in its number" names the exact hypothesis, and no more
than it: nothing about the certificate, the model or the coalition is used.

**"Any future arm carrying a number owes the same" is a design obligation, not
a fact about the code, and the wording says so.** `RepricePayload` reads "an
arm whose proposition is not monotone in the number it carries owes a different
obligation here" and `port_reprice` reads "which is the condition any future
arm carrying a number owes as well". Both use *owes*, which is the right mood.
Nothing in the framework checks it: `RepricePayload` is a hand-written match
and a third branch could be written as `unit` for an arm whose proposition
mentions a number, and then `conclude` would move that number with no
obligation at all. The comments do not claim otherwise, and a reader is not
misled. No finding.

**Stage B's `IdealProximity` is monotone in the needed sense.** The spec says
the certificate carries "for each coalition below the threshold a bound on the
distance between the two joint laws of reading and secret" and that "The
proposition has the shape `pgl27_view_mixing` already has". That theorem is

```coq
Theorem pgl27_view_mixing (secretP : R.-fdist bool) (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  var_dist (fdistmap (fun u => (pgl27_view R C u, pgl27_secret R u))
                     (pgl27P_word_gen secretP))
           ((fdistmap (pgl27_view R C) (pgl27P_gen secretP))
              `x (fdistmap (pgl27_secret R) (pgl27P_gen secretP)))
  <= 2%:R^-40.
```

so the arm's proposition is `forall C, #|C| < k -> var_dist _ _ <= c`, again of
the form `d <= c` under a quantifier prefix that does not mention `c`. Weakly
increasing in `c`, and the third case of `port_reprice` closes by the same
`le_trans` with the same shape of `intro` pattern. The answer is yes. Two
things stage B still owes and stage A does not supply: a `cert_eps` analogue
for the new certificate, since `cert_eps` is defined from `SpectralCert`'s own
`sw_bound_eps` field, and a decision about whether the new arm's number and the
spectral one are ever added, since `Reprice` names one number per real field
and a row carries one port.

## 4. T0 as restated

**`t0_sampled_branch.v`.** Every sentence checks out. One named value,
`five_card_uniform_sampled : Tableau Sampled`. Two continuations, both writing
`certify ExactIndependence five_card_exact_witness`, so the same arm and the
same witness. Two pairs of statuses, `(StaticExecutedOnly,
BaselineClassicalOnly)` and `(IdealFinite, BaselineClassicalOnly)`, which are
two distinct pairs. `t0_row_uniform_atE` proves the two continuations and the
unbranched program hold one coordinate, and `t0_row_uniform_row_neq` proves the
two manifest rows differ, by `congr1 apr_transfer`. The header's "one security
claim under two pairs of statuses" is exactly what is shown. F3 is closed.

**`t0_sampled_branch_pgl27.v`, the two word-branch equations.**

`pgl27_row_word_branch_atE` says
`published_at pgl27_row_word_branch = published_at pgl27_row_word_tableau`.
The left side is the branch point continued by `certify SpectralDecay
pgl27_word_cert` and published; the right side is the unbranched program, whose
certify line is the five-clause form. The equation therefore also re-proves
`pgl27_row_word_certE` at the published coordinate. Its comment says "hold one
AnalysisBridged coordinate, so a spectral payload reduces through the name
exactly as an exact one does", which is the equation plus an inference from the
definition having elaborated at all. Nothing beyond that is claimed.

`pgl27_row_word_branch39_atE` says
`published_at pgl27_row_word_branch = published_at pgl27_row_word_branch39`,
the unconcluded continuation against the one concluded at 2^-39 first. Its
comment says "Concluding at 2^-39 leaves that coordinate alone, so the terminal
between the branch point and the manifest row moves a number and no data", and
that is all it says and all that is true: `conclude` returns the incoming `q`
and `publish` writes it. The two sides are at different `Reprice` indices, which
is fine, because `published_at` lands in `StackAt AnalysisBridged` for either.
The header index line "concluding at 2^-39 leaves that coordinate" is a
truncated sentence and reads as if a word were missing.

**The two cross-model `Fail`s, compiled without `Fail`.** Both hold. Their
reason is not the one the comment gives. See S1. Full messages:

```
q4a: pgl27_word_sampled certify ExactIndependence pgl27_exact_witness
The term "pgl27_exact_witness" has type
 "forall (R : realType) (idx : unit),
  ExactWitness (amf_sample pgl27_exact_family R idx)"
while it is expected to have type
 "ExactPayload (tableau_at pgl27_word_sampled)"
(cannot unify "amf_index (sp_f (tableau_at pgl27_word_sampled)) R" and
"unit").

q4b: pgl27_exact_sampled certify SpectralDecay pgl27_word_cert
The term "pgl27_word_cert" has type
 "forall (R : realType) (secretP : {fdist bool}%fdist),
  SpectralCert (amf_sample pgl27_word_family R secretP)"
while it is expected to have type
 "SpectralPayload (tableau_at pgl27_exact_sampled)"
(cannot unify "amf_index (sp_f (tableau_at pgl27_exact_sampled)) R" and
"{fdist bool}%fdist").
```

Unification fails on the domain of `idx`, one binder before the adapter, so the
adapters are never reached. `STATUS.md`'s "Open for stage B" paragraph states
this correctly and draws the right consequence, that stage B's ideal and actual
families over one instance will share an index type and will not be separated
this way. The file comment says the opposite of the record.

The cross-*instance* mutations of `t0_sampled_branch.v` are a different case:
`five_card_uniform_family` and `s5_rand_family` both have index `unit`, so
there the adapters are compared, and `STATUS.md`'s quoted message for that file
shows it. The sentence is right in one file and wrong in the other, because it
was copied.

## 5. The replaced recorded `Fail`

**It isolates what its comment claims.** The comment reads "A payload with the
right relation but no index binder is rejected, which is what keeps a row from
publishing a bound that holds only at the index a reader happened to pick."
Compiled without `Fail`, both forms give one error, and the two sides of it
differ in the binder alone:

```
The term "ssr_ext.eqW (pow2_split R)" has type
 "is_true (2 ^- 40 + 2 ^- 40 <= 2 ^- 39)"
while it is expected to have type
 "forall idx : amf_index (ab_f (tableau_at (pgl27_dealt sample
    pgl27_word_family certify SpectralDecay pgl27_word_cert))) R,
  match ab_port ... R idx with
  | ExactIndependence _ => unit
  | SpectralDecay cert =>
      cert_eps cert <= odflt (cert_eps cert) (pgl27_reprice39 R)
  end".
```

The relation is `<=` on both sides and the arithmetic is the right arithmetic,
so the only thing wrong with the payload is the missing `forall idx`. That is
the isolation F6 asked for, and it is what D8 claims. The surface form and the
bind form give byte-identical reasons, so the surface is not what rejects it.
The text `STATUS.md` D8 quotes matches the compiler's output. GO on this item.

## 6. The hang shape, and every file that risks it

**No other file of the probe, and no production file, closes an equation
between `published_at` of a concluded and an unconcluded row by `by []` or
`done`.** There is exactly one such equation anywhere, and it is in
`t0_sampled_branch_pgl27.v` itself, where it is closed by `exact: erefl`.

Full inventory. I walked every `.v` file in the repository for `published_at`
and read the proof of every sentence that mentions it.

| file | sentence | shape | tactic | measured |
|---|---|---|---|---|
| `t0_sampled_branch_pgl27.v` | `pgl27_row_exact_branch_atE` | two unconcluded | `exact: erefl` | 0.149 s is the file's slowest sentence, per `STATUS.md` |
| `t0_sampled_branch_pgl27.v` | `pgl27_row_exact_branch_ideal_atE` | two unconcluded | `exact: erefl` | as above |
| `t0_sampled_branch_pgl27.v` | `pgl27_row_word_branch_atE` | two unconcluded | `exact: erefl` | 0.133 s recorded; my `by []` control on the same goal is 0.091 s |
| `t0_sampled_branch_pgl27.v` | `pgl27_row_word_branch39_atE` | **concluded against unconcluded** | `exact: erefl` | 0.133 s recorded. My `q6b_concluded_done.v` puts `by []` on this goal: rc 124, **no return in 150 s** |
| `t0_sampled_branch.v` | `t0_row_uniform_atE`, three equations in one `and3` | all unconcluded | `by split` | **0.001 s**, measured by recompiling the file with `-time` |
| `pgg_tableau.v` | `publish_armE` | not a `published_at` equation; `published_at` occurs only in the type of `idx` | `by []` | file compiles in 12.7 s total |
| `pgl27_rows.v` | `pgl27_row_exact_armE`, `pgl27_row_word_armE`, `pgl27_row_word39_armE` | the same, `SecurityArm` equations | `by []` | file 6.3 s total |
| `five_card_rows.v`, `s5_rows.v`, `psl211_rows.v` | one `_armE` each, the same shape | | `by []` | 4.1 s, 4.0 s, 5.5 s total |
| `notes/probes/2026-09-19-kim-spectral-arm/audit-soundness/audit_checks.v` | `A5_same_data`, `A5_same_thm` | two `published_at` equations, both between rows with no `conclude` | `:= erefl`, a definition body and not a tactic | not timed, the file is another batch's |
| production | none | `published_at` occurs in production only in `manifest/pgg_tableau.v`, as the record field and inside the four projections, in no equation | | |
| `notes/probes/2026-09-19-kim-spectral-landing/` | none | its `pgg_tableau.v` has no such equation; its `five_card_rows.v` proves `published_row` equations only, for instance `five_card_row_biased_forms_publishedE`, `Proof. by []. Qed.` | | |

No `.v.timelog` file exists in this probe; the four that exist in the tree
belong to `notes/probes/2026-09-19-psl211-nogo-landing/`. Every number above
that is not attributed to `STATUS.md` is my own compile.

**What this means for stage B and for the Kim landing.** The discriminating
coordinate is `conclude`, not the instance and not the branch point: the same
`by []` is a tenth of a second on two unconcluded rows and does not return on a
concluded one. The Kim landing adds repriced rows and already proves
`published_row` equations across them; the moment it proves a `published_at`
equation between a repriced row and its unrepriced sibling, `by []` will hang.
`t0_sampled_branch.v` is the one file in this probe that still closes
`published_at` equations by `done`, and it is one added conjunct away from the
hang, which is S7.

## 7. STATUS.md

**Eight D2 entries verified against production, and then some.** Every quoted
sentence exists in production exactly as quoted, at exactly the cited line.

| entry | production text at that line | verdict |
|---|---|---|
| `manifest/pgg_tableau.v:28-29` | "A row commits to one of them and claims nothing about the other." | exact, spans 28 and 29 |
| `manifest/pgg_tableau.v:43-45` | "it leaves the data and the arms untouched and moves only the real the spectral arm's proposition mentions." | exact, spans 43 to 45 |
| `manifest/pgg_tableau.v:60` | `conclude               == the terminal republishing the bound` | exact |
| `manifest/pgg_tableau.v:74` | `port_reprice           == a port's proposition at a renamed bound` | exact |
| `manifest/pgg_tableau.v:614` | `\| SpectralDecay cert => cert_eps cert = odflt (cert_eps cert) (c R)` | exact |
| `manifest/pgg_tableau.v:631` | `Proof. by case: p => [w\|cert] //= H1 H2; rewrite -H2. Qed.` | exact |
| `manifest/pgg_tableau.v:722` | `Arguments view_indist_of {c} r.` | exact, and it is the last line of the file |
| `manifest/pgg_tableau_syntax.v:36` | "The publish separator is \|>." | exact |
| `instances/pgl27/pgl27_rows.v:382` | `;;; conclude pgl27_reprice39 of (fun R _ => pow2_split R)` | exact |
| `instances/pgl27/pgl27_rows.v:53-54` | the two index lines, including "republished at that name" | exact |
| `security/pgg_mixing.v:304` | "\|\|e_s - U\|\|_2^2 = 1 - 1/N <= 1 to conclude" | exact, and it is an English-word hit |
| the three one-line rows, `five_card_rows.v:348-350`, `s5_rows.v:285-287`, `psl211_rows.v:184-186` | each is the `rowE` statement, its `Proof` and the blank line after | exact |
| the six import-line citations of step 1 | `:110`, `:115`, `:116`, `:101`, `:102`, `:94`, `:152`, `:153` | all exact |

The two off-by-one starts are N4. The four stale citations are S3, and they are
citations of the **probe copies**, not of production; the production citations
are all sound. The lesson the campaign has learned twice already is visible
again: the production half of the list was built by searching and is right, the
probe half was written by hand after the files moved and is wrong.

**Does `STATUS.md` cite its own lines by number?** No. It cites `pgg_tableau.v`,
`pgg_tableau_syntax.v`, the four rows files, six production files and one
scratch path, and it refers to itself only by name and by section, as in "see
the D8 entry below" and "the probe's status note". Clean.

**The Kim consequence, against the landing probe as it stands.** The substance
is true and the address is wrong, which is S4.

True: `notes/probes/2026-09-19-kim-spectral-landing/five_card_rows.v` holds two
`conclude` terminals with equality payloads, `:745`
`;;; conclude five_card_reprice39 of (fun R _ => five_card_pow2_39_split R)`
and `:788`
`;;; conclude five_card_reprice_inv25 of (fun R _ => five_card_inv50_split R)`,
each of which needs `ssr_ext.eqW` under the weakened obligation, the same
one-token fix `pgl27_rows.v` took. Also true: the better end state exists in
that file, `kim_centi_cert_eps_lt (idx : unit) : cert_eps (kim_centi_cert R idx)
< 2%:R ^- 39` at `:670`, whose `ltW` discharges
`cert_eps cert <= odflt (cert_eps cert) (five_card_reprice39 R)` directly from
`kim_centi_cert`, making `kim_centi_cert40` at `:716` and
`kim_centi_cert40_epsE` at `:728` unnecessary. Wrong: the sentence describing
what becomes equal is not type honest (S5), and `STATUS.md` names only the arm
probe's copy of those two rows, so a landing reading the seed list would miss
the copy that is actually landing (S4).

**The axiom paragraph is true, checked independently.** `Axiom
s5_group_order_eq` is declared at `instances/s5/rigidity_s5_instance.v:179`, as
claimed. My own `q7_prod_s5.v` requires the **production** `s5_rows` and
nothing of this probe, and `Print Assumptions s5_row_rand_tableau` reports
`rigidity_s5_instance.s5_group_order_eq` together with the three boolp
constants and nothing else; `s5_row_rand_rowE` reports the same. So the fourth
constant reaches `s5_row_rand_armE` through the production S5 witness and not
through anything stage A adds, exactly as the paragraph says. The paragraph's
own note about the earlier scan, that a `\w+` pattern cannot match the dot of a
module-qualified name, is correct and is why the round-one report missed it.

## 8. The first-round findings

| ID | state |
|---|---|
| F1, keyword sentence false about `at` | **closed, and closed differently**: the paragraph now puts `at` back in the literal list with both literals named and gives `by` its own clause with the three slots. The first-round report's own proposed wording was wrong about the execute rule; the fix pass caught that and `STATUS.md` D4 records it |
| F2, `SecurityClaim`'s comment | **closed**: the qualifier "and one pair of statuses" is in, and the two comments agree |
| F3, T0 did not demonstrate two claims | **closed by restating**: header, comments, `STATUS.md` heading and D7 all now say one claim published under two pairs of statuses plus a branch point whose payload type reduces through the name, which is what the files show |
| F4, `stack_claim`'s wrong reason | **closed**: `ab_arm`'s comment gives the statement reason, and D6 records that the old function-type reason was false and that no counter-example is compilable |
| F5, C's blast radius omits the sibling probe | **closed for the arm probe, not for the landing probe**: the two lines are named and exact, the landing copy is not, which is S4 |
| F6, C degraded an isolating counter-probe | **closed by replacement**, and the replacement isolates what it claims, verified in section 5. The record of that replacement in step 3 is now self-contradictory, which is S2 |
| F7, `conclude`'s payload is a second door | **closed with one imprecision**: both sentences now name the payload, and S8 is the exact port's `unit` branch going unmentioned |
| F8, monotonicity unnamed | **closed**: both comments name it, and section 3 confirms it is the condition the proof uses |
| F9, three wording defects | **two closed, one deferred**: the `conclude` body now agrees with the index, "republished at" is gone from `RepricePayload`, and the `SpectralDecay` naming objection is recorded as an open production-naming question for the owner, with `view_indist_of` named as moving with it. That is the right disposition for a probe that edits no production file |
| F10, the pins are a table column | **closed**: the four general lemmas are in the file as named lemmas, the six per-row ones say in their comments that they record the table column, and all ten are reached by `Print Assumptions` |
| F11, an exact row at any number | **closed as recorded**: `STATUS.md` keeps it under "Known properties of the framework, no change proposed", with the scratch evidence path and the consequence that the table's number column must be read through `security_arm_of` |
| F12, a number at or above the ceiling | **closed as recorded**, with the reason a framework guard is wrong and the note that `var_dist_le2` lives only in the Kim arm probe |
| F13, further D2 seed items | **closed**: all seven are in the D10/D11 table, and the seven production citations check out |
| F14, two smaller things | **closed**: the index no longer lists `ab_arm`, since it lists no level accessor, and `assumptions_report.v` now prints five published rows as well as the lemmas, thirty-one blocks in all |

## 9. The two design rules

**Rule (1), extension by what a phase means.** No violation. Stage A adds no
statement and no phase: the arm reader is a terminal-side reader, placed where
the phase table puts the published number and the manifest row; the weakened
obligation is the terminal's, which is where the spec places the published
number; the keyword notation is surface only, and `pgl27_row_word39E` proves
the surface and the bind build one term. Nothing is removed. The header's
"There are five statements" stays true.

**Rule (2), one security claim with its whole chain per row.** No violation.
Every program in the copies certifies exactly once. The T0 files publish one
claim twice under two status pairs, and say so. `conclude` cannot be iterated
(N1), so a row cannot launder its number through a chain of terminals, which
strengthens the rule rather than straining it.

**The cost of a new arm is not recorded, which is S6.** `SecurityArm` mirrors
`SecurityPort`, and the mirroring is load bearing: `SecurityPort` is indexed by
the real field, the algebra, the run parameters and the sample adapter, and a
tag a manifest table prints must be closed in none of those, so a second
variant is the right construction and not an accident. But nothing says so, and
nothing counts the six edits a third arm costs. `STATUS.md` D1 records only how
a future constructor is to be named. Stage B is the batch that pays the bill,
so the reason and the count belong in the file before it starts.

## Replacements

**R1.** `t0_sampled_branch_pgl27.v`, the comment above `pgl27_cross_model`.
Replace the whole block with, at the file's own width and indent:

```
(** The exact model's witness does not continue the word model's branch
    point. The payload type is ExactPayload at the coordinate the name holds,
    so the clause is checked first against the index type that coordinate's
    family carries, unit against a distribution on the booleans, and the two
    sample adapters are never reached. Two models of one instance are
    separated here, and separated by their index types alone, so an ideal
    family and an actual family that share one index will need a different
    mutation. *)
```

**R2.** `STATUS.md` step 3, the paragraph beginning "The recorded `Fail`
`pgl27_row_word39_bare` still fails". Replace the paragraph and its two code
blocks with:

```
The baseline's recorded `Fail`, `pgl27_row_word39_bare` on a bare
`pow2_split`, still failed after C, but for two reasons at once instead of
one, so fix pass 1 replaced it rather than keeping it. What the copy records
is `pgl27_row_word39_unindexed` and `pgl27_row_word39_unindexed_bind`; the
payload, the message and the reason are in the D8 entry below.
```

In step 4, replace "`pgl27_row_word39_bare`, rewritten in the new surface,
still fails, and the raw spelling of the same rejection is kept beside it."
with "`pgl27_row_word39_unindexed`, in the new surface, fails, and the bind
spelling of the same rejection is kept beside it." In the D2 table, replace the
third cell of the `:389-394` row with "replaced: after C a bare `pow2_split` is
wrong twice over, so the recorded rejection becomes the indexed-payload one of
D8, in the conclude surface and in the bind form."

**R3.** `STATUS.md` verdict table, the four "Where" cells:

```
| C1 | GO | `pgg_tableau.v:650-687` |
| C2 | GO, one payload changed in the whole tree | production `instances/pgl27/pgl27_rows.v:382`, the copy `:419` |
| C3 | GO | `pgl27_rows.v:464-491` |
| G2 | GO, `conclude` costs no keyword | `pgg_tableau_syntax.v:398-404` |
```

and, in step 5, replace "(`pgl27_rows.v:580`)" with "(production `:580`, the
copy `:677`)".

**R4.** `STATUS.md`, after the "Code site" paragraph of D10 and D11, add:

```
The same two rows stand in the probe that would carry them to production,
`notes/probes/2026-09-19-kim-spectral-landing/five_card_rows.v`, at `:745` and
`:788`, with the recorded `Fail` at `:751-757` and a third equality payload in
that directory's `pgl27_rows.v:382`. A Kim landing edits that copy and not the
arm probe, so the landing's own status note owes the four sites.
```

**R5.** `STATUS.md`, in the same section, replace "and makes the two published
rows equal by `erefl`, where the equality obligation had forced two
certificates and two `AnalysisBridged` coordinates" with "and makes the two
rows' `published_at` coordinates one term by `erefl`, where the equality
obligation had forced two certificates and two coordinates. The rows themselves
are at two `Reprice` indices and so are of two types, and no equation between
them is well formed."

**R6.** `STATUS.md` D1, after the paragraph on constructor naming, add:

```
What a new arm costs, so that stage B can price it: a constructor in
`SecurityPort`, a constructor in `SecurityArm`, a branch in `port_arm`, a
branch in `PortProp`, a branch in `RepricePayload` and a case in
`port_reprice`. `SecurityArm` is a second variant and not a projection of the
first because `SecurityPort` is indexed by the real field, the algebra, the run
parameters and the sample adapter, and a tag the manifest's table prints must
be closed in none of them.
```

**R7.** `t0_sampled_branch.v`, `t0_row_uniform_atE`, replace
`Proof. by split. Qed.` with `Proof. split; exact: erefl. Qed.`
(`STATUS.md` measured that spelling at 0.145 s on the PGL(2,7) conjunction.)

**R8.** `pgg_tableau.v`, the header lines 40 to 44, padded to the file's
eighty-column box:

```
(* instance never appears as a line: it enters as the witness or the          *)
(* certificate a certify statement takes, and once more as the payload of     *)
(* conclude, which for a spectral port is an inequality between the number    *)
(* the row's own certificate proved and the number the row publishes and      *)
(* for an exact port is nothing. And of the three terminals only              *)
```

**R9.** `pgg_tableau.v`, the comment above `certify_exact_armE`:

```
(* A row built by the exact statement carries the exact arm at every real
   field and index of its family. With conclude_armE and publish_armE below it
   settles the arm of a finished row by one line of the row's text, so a
   reader needs no argument about the instance's probability model to know
   which statement the row proved. *)
```

## What this audit did not check

- The naming audit's items, except where a naming fix changed a sentence's
  truth. `naming-audit-stageA.md` was read for its verdict and its keyword
  claim, not adjudicated.
- The four instances' mathematics. `pgl27_word_mixing`, `pgl27_view_mixing`,
  `psl211_alldecks_view_indep` and the five-card witnesses were read for their
  statement shapes and not reproved.
- The compile table of step 6 and the thirty-one assumption blocks, both
  recompiled by the main session before this round. I reran one of them,
  `Print Assumptions` on the production S5 row, and it agrees.
- Whether `exact: erefl` is the fastest closing tactic for the coordinate
  equations. I measured only `by []` against the recorded `exact: erefl` times.
- The nineteen keyword measurements were taken with the probe's extended
  surface loaded. I did not repeat them against the production surface, where
  the count is the same by the same derivation and one rule fewer.
- `psl211_endpoints.v`, per the standing rule.
