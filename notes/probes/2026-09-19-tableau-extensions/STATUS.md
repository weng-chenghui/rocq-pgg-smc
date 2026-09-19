# Stage A of the Tableau extensions probe

Directory `notes/probes/2026-09-19-tableau-extensions/`, logical path
`tableau_ext_probe`. Branch `feat/tableau-extensions-probe`, nothing committed,
no permanent file edited, `instances/psl211/psl211_endpoints.v` never touched
and never compiled.

Stage A covers ledger rows T0, C1, C2, C3, K1, G1, G2, and the start of G3
and D2. The IdealProximity arm and the instance programs are later stages.

## Verdict table

| Row | Verdict | Where |
|---|---|---|
| T0 | GO, no framework change needed | `t0_sampled_branch.v` |
| C1 | GO | `pgg_tableau.v:607-651` |
| C2 | GO, one payload changed in the whole tree | `pgl27_rows.v:382` |
| C3 | GO | `pgl27_rows.v:455-465`, `:467-472` |
| G2 | GO, `conclude` costs no keyword | `pgg_tableau_syntax.v:396-402` |
| K1 | GO | `pgg_tableau.v`, four rows copies |
| G1 | GO at baseline, after C, and after K | compile table below |
| G3 | eight sentences rewritten | list below |
| D2 | list below | built by searching the tree |

## Step 1. The copies, and the baseline (G1)

Six full copies, keeping their base names:

| copy | source | import lines changed |
|---|---|---|
| `pgg_tableau.v` | `manifest/pgg_tableau.v` | none |
| `pgg_tableau_syntax.v` | `manifest/pgg_tableau_syntax.v` | `:110` split |
| `s5_rows.v` | `instances/s5/s5_rows.v` | `:115` split, `:116` |
| `pgl27_rows.v` | `instances/pgl27/pgl27_rows.v` | `:101` split, `:102` |
| `psl211_rows.v` | `instances/psl211/psl211_rows.v` | `:94` |
| `five_card_rows.v` | `instances/kim2025/five_card_rows.v` | `:152` split, `:153` |

A line naming both a production module and a Tableau module was split in two:
`From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.` became
`From pgg_smc Require Import pgg_analysis_manifest.` followed by
`From tableau_ext_probe Require Import pgg_tableau.`

Isolation, by a script over the Require lines
(`scratchpad/isolate_check.py`): the production import closure of each copy,
computed from the production `_CoqProject` graph, contains neither
`pgg_tableau` nor `pgg_tableau_syntax`.

```
pgg_tableau.v            prod-closure=29 CLEAN
pgg_tableau_syntax.v     prod-closure=25 CLEAN
s5_rows.v                prod-closure=50 CLEAN
pgl27_rows.v             prod-closure=43 CLEAN
psl211_rows.v            prod-closure=41 CLEAN
five_card_rows.v         prod-closure=52 CLEAN
VERDICT: isolated
```

The reverse-dependants of `pgg_tableau` in the tree are exactly
`pgg_tableau_syntax` and the four rows files, confirmed by a grep over
`manifest protocol instances security smc lib reconstruct groups legacy`.

Untouched copies saved under `history/` with suffix `.0-baseline`;
`history/pgg_tableau.v.1-after-C` and `history/pgg_tableau.v.2-after-K`.

## Step 2. T0, two claims from one named `Tableau Sampled` value

**GO, with nothing needed.** File `t0_sampled_branch.v`, a new file Requiring
the copies of `five_card_rows.v` and `s5_rows.v`, so that the rows copies stay
at their baseline text for the C and K measurements.

As compiled:

```coq
Definition five_card_uniform_sampled : Tableau Sampled :=
  five_card_committed
    sample five_card_uniform_family.

Definition t0_row_uniform : PublishedRow :=
  five_card_uniform_sampled
    certify ExactIndependence five_card_exact_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.

Definition t0_row_uniform_transfer : PublishedRow :=
  five_card_uniform_sampled
    certify ExactIndependence five_card_exact_witness
    |> publish IdealFinite BaselineClassicalOnly.

Lemma t0_row_uniform_rowE :
  published_row t0_row_uniform
  = published_row five_card_row_uniform_tableau.
Proof. by []. Qed.

Lemma t0_row_uniform_manifestE :
  published_row t0_row_uniform = five_card_row_uniform.
Proof. by []. Qed.

Lemma t0_row_uniform_atE :
  [/\ published_at t0_row_uniform
      = published_at five_card_row_uniform_tableau,
      published_at t0_row_uniform_transfer
      = published_at five_card_row_uniform_tableau
    & published_at t0_row_uniform = published_at t0_row_uniform_transfer].
Proof. by split. Qed.

Lemma t0_row_uniform_row_neq :
  published_row t0_row_uniform <> published_row t0_row_uniform_transfer.
Proof. by move=> H; move: (congr1 apr_transfer H). Qed.
```

**The hazard of design audit h1 did not fire.** No `Arguments ... : simpl
never`, no extra transparent definition, no type ascription on the payload.
`sp_f (tableau_at five_card_uniform_sampled)` reduces to
`five_card_uniform_family` by delta and iota alone, so
`five_card_exact_witness` unifies with
`ExactPayload (tableau_at five_card_uniform_sampled)` where the clause is
written, and `t0_row_uniform_rowE` holds by `erefl` at the first attempt.

Mutation, recorded `Fail`, first message line:

```
Fail Definition t0_cross_instance : Tableau AnalysisBridged :=
  t0_s5_sampled certify ExactIndependence five_card_exact_witness.
-> The term "five_card_exact_witness" has type
```

with `cannot unify "ExactWitness (amf_sample five_card_uniform_family R idx)"
and "ExactWitness (amf_sample (sp_f (tableau_at t0_s5_sampled)) R idx)"`. The
mirror mutation, the S5 witness on the five-card branch point, is rejected the
same way.

## Step 3. C, `conclude` at an inequality

### C1, the framework

`pgg_tableau.v`, `RepricePayload` and `port_reprice`, equality weakened to
`<=`:

```coq
Definition RepricePayload (c : Reprice) (q : StackAt AnalysisBridged) : Type :=
  forall (R : realType) (idx : amf_index (ab_f q) R),
    match ab_port q R idx with
    | ExactIndependence _ => unit
    | SpectralDecay cert => cert_eps cert <= odflt (cert_eps cert) (c R)
    end.

Lemma port_reprice (c : Reprice) (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (p : SecurityPort sa) :
  PortProp no_reprice p ->
  (match p with
   | ExactIndependence _ => unit
   | SpectralDecay cert => cert_eps cert <= odflt (cert_eps cert) (c R)
   end) ->
  PortProp c p.
Proof.
case: p => [w|cert] //= H1 H2 C x x' HC.
exact: Order.POrderTheory.le_trans (H1 C x x' HC) H2.
Qed.
```

`conclude` itself is unchanged. One name had to be qualified: bare `le_trans`
is not in scope in this file, which imports `GRing.Theory Num.Theory` and not
`Order.Theory`.

### C2, the payloads in the importers

`conclude` occurs in exactly one production file. Searched over
`manifest protocol instances security smc lib reconstruct groups legacy` for
`RepricePayload`, `port_reprice`, `cert_eps`, `Reprice`, `no_reprice` and
`conclude`: the only hits outside `manifest/pgg_tableau.v` are
`instances/pgl27/pgl27_rows.v:371`, `:382`, `:393` (and one occurrence of the
English word in a `legacy/reconstruct/ag_code.v` comment).

One payload change, in the copy of `pgl27_rows.v`:

| | text |
|---|---|
| old (`:382`) | `;;; conclude pgl27_reprice39 of (fun R _ => pow2_split R)` |
| new (`:382`) | `\|> conclude pgl27_reprice39 by (fun R _ => ssr_ext.eqW (pow2_split R))` |

`ssr_ext.eqW : x = y -> (x <= y)%O` is infotheo's, reachable under its
qualified name from this file's existing `From infotheo Require Import fdist`.
Searched first: mathcomp has no bare `x = y -> x <= y` in `Order` or
`Num.Theory` (`Search (_ = _ -> (_ <= _)%O)` returns `eq_leq` for `nat` only),
so a name was not guessed.

`pgl27_word_bridge` and the two `restate` uses are not affected: `restate`
takes a `RestatePayload` and never a `RepricePayload`.

The recorded `Fail` `pgl27_row_word39_bare` still fails, first message line:

```
The term "pow2_split" has type
```

full: `"forall R : realType, 2 ^- 40 + 2 ^- 40 = 2 ^- 39"` against
`RepricePayload pgl27_reprice39 (tableau_at (pgl27_dealt sample
pgl27_word_family certify SpectralDecay pgl27_word_cert))`. Its reason is
unchanged, the payload is not quantified over the field and the index; only
the expected type's relation symbol moved from `=` to `<=`. The same `Fail`
is kept in both surfaces (`pgl27_row_word39_bare`,
`pgl27_row_word39_bare_raw`).

### C3, a number below the proved one is refutable

```coq
Definition pgl27_reprice41 : Reprice := fun R => Some (2%:R^-41 : R).

Lemma pgl27_word_reprice41_false (R : realType) (secretP : R.-fdist bool) :
  ~~ (cert_eps (@pgl27_word_cert R secretP)
      <= odflt (cert_eps (@pgl27_word_cert R secretP)) (pgl27_reprice41 R)).
Proof.
rewrite /cert_eps /= pow2_split -Order.TotalTheory.ltNge.
rewrite ltf_pV2 ?posrE ?exprn_gt0 //.
by rewrite ltr_eXn2l ?ltr1n.
Qed.
```

and the row at that number is rejected where its terminal is written:

```
Fail Definition pgl27_row_word41 : PublishedRowAt pgl27_reprice41 := ...
-> The term "ssr_ext.eqW (pow2_split R)" has type
   "is_true (2 ^- 40 + 2 ^- 40 <= 2 ^- 39)"
   while it is expected to have type
   "... | SpectralDecay cert =>
       is_true (cert_eps cert <= odflt (cert_eps cert) (pgl27_reprice41 R))"
```

`@pgl27_word_cert R secretP` needs the `@`: `R` occurs in the type of
`secretP`, so `Set Implicit Arguments` makes it implicit and the bare
application is read as `pgl27_word_cert secretP`.

### The three comments rewritten

`RepricePayload`, `port_reprice` and `conclude` each said the terminal renames
a number. Rewritten so that each says it publishes an upper bound, and that a
row may not publish a number its certificate does not reach.

## Step 4. G2, the `conclude` notation

Added to `pgg_tableau_syntax.v`, immediately before the `publish` rule:

```coq
Notation "s |> 'conclude' c 'by' p" := (s ;;; conclude c of p)
  (at level 90, left associativity, c at level 0, p at level 0).
```

`publish` after `conclude` typechecks through the notation exactly as in the
raw form: `conclude` returns `TableauAt AnalysisBridged (BridgedProp c)`, and
`|> publish t a` binds at the same level and associates to the left, so the
row reads as one chain. `pgl27_row_word39` in the copy:

```coq
Definition pgl27_row_word39 : PublishedRowAt pgl27_reprice39 :=
  pgl27_dealt
    sample  pgl27_word_family
    certify SpectralDecay pgl27_word_cert
    |> conclude pgl27_reprice39 by (fun R _ => ssr_ext.eqW (pow2_split R))
    |> publish IdealFinite BaselineClassicalOnly.

Definition pgl27_row_word39_raw : PublishedRowAt pgl27_reprice39 :=
  pgl27_dealt
    ;;; sample_step of pgl27_word_family
    ;;; certify_spectral of pgl27_word_cert
    ;;; conclude pgl27_reprice39 of (fun R _ => ssr_ext.eqW (pow2_split R))
    ;;; publish BaselineClassicalOnly of IdealFinite.

Lemma pgl27_row_word39E : pgl27_row_word39 = pgl27_row_word39_raw.
Proof. by []. Qed.
```

`pgl27_row_word39_bare`, rewritten in the new surface, still fails, and the
raw spelling of the same rejection is kept beside it.

### The keyword measurement

Two words are written in the rule, `conclude` and `by`. Measured on
2026-09-19, in a file requiring the extended surface
(`g2_keyword_measure.v`, and `scratchpad/q_kw.v` for the negative half):

| token | position in the rule | binds as an identifier? |
|---|---|---|
| `conclude` | right after the literal `\|>` | yes |
| `by` | right after the slot `c` | no, and it did not before either |
| `sample` (control) | right after a slot, existing rule | no |

- `Check conclude.` prints `conclude : Reprice -> forall q : StackAt
  AnalysisBridged, ...`, and
  `Definition conclude_stays_bindable (conclude : nat) : nat := conclude.`
  compiles. So the rule adds **no** new global keyword, and the header's
  count of nineteen is unchanged.
- `Definition kw_sample (sample : nat) : nat := sample.` is
  `Syntax error: [name] expected after '(' (in [closed_binder])`, which is
  what a keyword costs.
- `Definition kw_by (by : nat) : nat := by.` is the same syntax error in a
  file requiring nothing but `From mathcomp Require Import ssreflect`, so
  `by` was a keyword before this surface, as `at` was. The rule therefore
  needs no alternative word, and `at ... with` and `of` were not needed.
- A parse error is raised before `Fail` can see the command, so the two
  negative measurements are recorded here and not as `Fail`s in the file.
- No existing program broke: all six copies compile, and `pgl27_row_word39E`
  says the two surfaces build one term.

## Step 5. K1, the claim a finished row carries

Added to `pgg_tableau.v`, all by `erefl` at every use:

```coq
Variant SecurityClaim := ExactViewIndependence | SpectralViewDecay.

Definition port_claim (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (p : SecurityPort sa) : SecurityClaim :=
  match p with
  | ExactIndependence _ => ExactViewIndependence
  | SpectralDecay _ => SpectralViewDecay
  end.
Arguments port_claim {R A E sa} p.

Definition stack_claim (q : StackAt AnalysisBridged) (R : realType)
    (idx : amf_index (ab_f q) R) : SecurityClaim :=
  port_claim (ab_port q R idx).
Arguments stack_claim : clear implicits.

Definition security_claim_of (c : Reprice) (r : PublishedRowAt c)
    (R : realType) (idx : amf_index (ab_f (published_at r)) R)
  : SecurityClaim :=
  stack_claim (published_at r) R idx.
Arguments security_claim_of {c} r R idx.
```

**How the reader deals with the `forall R idx`: it takes them as arguments.**
The port is a function of the field and the index, so the claim is read at the
same two arguments the port is written at. Returning a `SecurityClaim` for a
quantified port would need either a choice of field, which the arm's
uniformity exists to avoid, or a proof that the answer is constant in the
field, which is a theorem where the present shape is a definition. Both
arguments are explicit, because `Set Implicit Arguments` would otherwise make
`q` and `R` implicit (they occur in the type of `idx`).

Pins, one per published program, beside its `rowE`:

| file | pin |
|---|---|
| `pgl27_rows.v` | `security_claim_of pgl27_row_exact_tableau R idx = ExactViewIndependence` |
| `pgl27_rows.v` | `security_claim_of pgl27_row_word_tableau R idx = SpectralViewDecay` |
| `pgl27_rows.v` | `security_claim_of pgl27_row_word39 R idx = SpectralViewDecay` |
| `five_card_rows.v` | `security_claim_of five_card_row_uniform_tableau R idx = ExactViewIndependence` |
| `s5_rows.v` | `security_claim_of s5_row_rand_tableau R idx = ExactViewIndependence` |
| `psl211_rows.v` | `security_claim_of psl211_row_alldecks_tableau R idx = ExactViewIndependence` |

each written `Check (fun R idx => (erefl : ... )).`, the manifest's own pin
idiom. Isolating counter-probe, in `pgl27_rows.v`:

```
Fail Definition pgl27_word_claim_is_not_exact ... :=
  (erefl : security_claim_of pgl27_row_word_tableau R idx
           = ExactViewIndependence).
-> cannot unify "security_claim_of pgl27_row_word_tableau R idx" and
   "ExactViewIndependence"
```

The existing `Fail pgl27_word_arm_is_not_exact` (`pgl27_rows.v:580`) still
fails, unchanged.

## Step 6. G1, G3, D2

### G1, the compile table

Real return codes from a Python driver, one file at a time through the
machine-wide lock, `rocq compile -time`. Peak resident memory from
`RUSAGE_CHILDREN` of a fresh child per file.

| file | baseline | after C | after K |
|---|---|---|---|
| `pgg_tableau.v` | rc=0 13.0 s 1715 MB | rc=0 13.7 s 1715 MB | rc=0 12.7 s 1714 MB |
| `pgg_tableau_syntax.v` | rc=0 4.5 s 1644 MB | rc=0 4.9 s 1644 MB | rc=0 4.7 s 1644 MB |
| `pgl27_rows.v` | rc=0 6.2 s 1656 MB | rc=0 7.0 s 1654 MB | rc=0 6.3 s 1660 MB |
| `five_card_rows.v` | rc=0 4.2 s 1622 MB | rc=0 5.0 s 1622 MB | rc=0 4.1 s 1622 MB |
| `s5_rows.v` | rc=0 4.5 s 1613 MB | rc=0 4.5 s 1612 MB | rc=0 4.0 s 1612 MB |
| `psl211_rows.v` | rc=0 6.0 s 1730 MB | rc=0 6.0 s 1730 MB | rc=0 5.5 s 1730 MB |

Probe files added on top: `t0_sampled_branch.v` rc=0 3.9 s 1614 MB,
`g2_keyword_measure.v` rc=0 3.8 s 1601 MB, `assumptions_report.v` rc=0 8.5 s
1848 MB.

No sentence anywhere reached 5 s, at the baseline or after either change, so
the 20 s defect threshold was never approached. One run of `pgg_tableau.v`
measured 55.4 s; that is lock wait inside the wrapper, and the repeat under
an idle lock is 12.7 s.

### Print Assumptions

Every new or reproved statement, plus the three claim readers:
`port_reprice`, `port_claim`, `stack_claim`, `security_claim_of`,
`pgl27_word_reprice41_false`, `pgl27_row_word39E`, `t0_row_uniform_rowE`,
`t0_row_uniform_manifestE`, `t0_row_uniform_atE`, `t0_row_uniform_row_neq`.

All ten print the same three constants and nothing else:
`propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`. No custom axiom, no `Admitted`, no
`Abort`, no `Parameter`, no `admit`. The floor is the documented boolp trio,
which reaches every statement whose type mentions an fdist record.

### G3, the header sentences the changes made false or incomplete

Production line numbers.

`manifest/pgg_tableau.v`:

| line | current text | why it fails | rewritten as |
|---|---|---|---|
| `:28-29` | "A row commits to one of them and claims nothing about the other." | incomplete: nothing says the commitment is now readable | "...and security_claim_of names which of the two a finished row committed to." |
| `:43-45` | "it leaves the data and the arms untouched and moves only the real the spectral arm's proposition mentions." | incomplete: the real now moves only upward | "...and moves the real the spectral arm's proposition mentions to any upper bound of it." |
| `:50` | `SecurityPort == the arm an instance certifies` | incomplete as an index: three new names follow it | two lines added for `SecurityClaim` and `port_claim` |
| `:60` | `conclude == the terminal republishing the bound` | false: it publishes an upper bound, not the same number renamed | `conclude == the terminal publishing an upper bound of the accumulated bound` |
| `:63` | (index) | incomplete | `stack_claim` line added before `conclude` |
| `:68` | `view_indist_of == the same statement, spectral-arm name` | incomplete | `security_claim_of` line added after it |
| `:74` | `port_reprice == a port's proposition at a renamed bound` | false: at an upper bound | `port_reprice == a port's proposition at an upper bound of its own` |

`:17` "There are five statements." stays true: Stage A adds no statement.

`manifest/pgg_tableau_syntax.v`:

| line | current text | why it fails | rewritten as |
|---|---|---|---|
| `:36` | "The publish separator is \|>." | incomplete: `\|>` now carries two terminal rules | "The separator of the two terminal rules is \|>." |
| `:68-71` | "The tokens inputs, terminates, publish, vm_compute, ExactIndependence and SpectralDecay follow a literal and stay identifiers ... at follows a literal too and was a keyword of Rocq before this file." | incomplete twice: `conclude` belongs in that list, and `by` follows a slot in three existing rules and is named nowhere | list gains `conclude`; the last clause becomes "at and by follow a slot in some rule but were keywords of Rocq and of ssreflect before this file, measured on 2026-09-19 by binding each in a file that requires nothing but ssreflect" |

The `by` gap at `:68-71` is **pre-existing**: `by` already follows the slot
`t` in the execute rule and the slot `k` in the leaks rule, so the header was
incomplete on it before this probe. The count of nineteen keywords at `:60-64`
stays correct.

### D2, what a landing would change in the production files

Built by searching the tree, not from memory. Every hit of `conclude`,
`Reprice`, `RepricePayload`, `port_reprice`, `cert_eps`, `no_reprice`,
`word39`, `reprice39` over `manifest protocol instances security smc lib
reconstruct groups legacy`, plus every `^Fail ` in the five Tableau files.

**`manifest/pgg_tableau.v`** (reverse closure five: `pgg_tableau_syntax` and
the four rows files)

| line | current text | change |
|---|---|---|
| `:28-29` | header sentence on committing to one arm | one clause added |
| `:43-45` | header sentence on `conclude` | one clause changed |
| `:50`, `:60`, `:63`, `:68`, `:74` | Definitions and Key results index | four lines added, two rewritten |
| `:149-152` | `Variant SecurityPort ...` | `SecurityClaim` and `port_claim` added after it |
| `:241-245` | `ab_port` and its `Arguments` | `stack_claim` added after it |
| `:607-609` | comment "one numeric identity for a spectral port" | rewritten |
| `:614` | `SpectralDecay cert => cert_eps cert = odflt (cert_eps cert) (c R)` | `=` becomes `<=` |
| `:618-621` | comment "Renaming proves nothing new about the coalition" | rewritten |
| `:628` | same equality in `port_reprice`'s statement | `=` becomes `<=` |
| `:631` | `Proof. by case: p => [w\|cert] //= H1 H2; rewrite -H2. Qed.` | two-line proof by transitivity |
| `:634-637` | comment on `conclude` | rewritten |
| `:722` | end of file, after `Arguments view_indist_of {c} r.` | `security_claim_of` added |

**`manifest/pgg_tableau_syntax.v`** (reverse closure four)

| line | current text | change |
|---|---|---|
| `:36` | "The publish separator is \|>." | rewritten |
| `:68-71` | the identifier-cost sentence | rewritten |
| `:393-396` | the comment and rule of `\|> publish` | the `conclude` rule and its comment inserted before it |

**`instances/pgl27/pgl27_rows.v`**

| line | current text | change |
|---|---|---|
| `:53-54` | `pgl27_reprice39 == the name 2^-39 for the word row's bound`, `pgl27_row_word39 == the word row republished at that name` | "republished" becomes "published"; two index lines added for `pgl27_row_word39_raw` and `pgl27_word_reprice41_false` if C3 lands here |
| `:373-377` | "the identity that adds the two copies is pow2_split" | rewritten: the identity plus `eqW` |
| `:378-383` | `pgl27_row_word39`, raw form | rewritten in the `\|> conclude ... by ... \|> publish` surface; the raw spelling kept as `pgl27_row_word39_raw` with an `erefl` lemma |
| `:382` | `;;; conclude pgl27_reprice39 of (fun R _ => pow2_split R)` | `\|> conclude pgl27_reprice39 by (fun R _ => ssr_ext.eqW (pow2_split R))` |
| `:385-388` | "The reprice obligation is one identity per real field" | "one inequality per real field" |
| `:389-394` | `Fail pgl27_row_word39_bare` | rewritten in the new surface; its reason is unchanged, its message's relation symbol changes |
| `:320-330` | the two `rowE` lemmas | three claim pins added beside them |
| `:574-582` | the comment and `Fail pgl27_word_arm_is_not_exact` | still true and still failing; its comment becomes incomplete, since the difference between the arms is now also readable through `security_claim_of` |

**`instances/kim2025/five_card_rows.v`**: `:348-350`, one claim pin after
`five_card_row_uniform_rowE`.

**`instances/s5/s5_rows.v`**: `:285-287`, one claim pin after
`s5_row_rand_rowE`.

**`instances/psl211/psl211_rows.v`**: `:184-186`, one claim pin after
`psl211_row_alldecks_rowE`.

**Not changed, checked by searching**

- `manifest/pgg_analysis_manifest.v`: no hit for any reprice name and no hit
  for `pgl27_row_word39`. The manifest sits below the programs, so its
  `Check (erefl : ...)` pins and its header tables are untouched by C, by K
  and by the notation.
- `manifest/pgg_analysis_client.v`: no hit for `pgg_tableau`.
- the facade files: no alias of any reprice name.
- `instances/psl211/psl211_endpoints.v`: not in either closure; never opened.
- `legacy/reconstruct/ag_code.v:163` contains the English word "conclude" in
  a comment and is not a use.
- the recorded `Fail`s of the four rows files: eleven of the twelve are
  untouched. The twelfth, `pgl27_row_word39_bare`, keeps its reason and
  changes only the relation symbol printed in its message.

## What in the brief or the spec turned out wrong

1. The spec's ledger row C2 expects "every existing `conclude` in the five
   importer copies" to need a payload change. There is exactly one `conclude`
   in the whole tree outside the framework, and one `Fail` beside it.
2. The brief's example payload `fun R _ => eq_le (pow2_split R)` names a
   lemma that does not exist. MathComp has no bare `x = y -> x <= y`; the
   lemma that does this is infotheo's `ssr_ext.eqW`.
3. The brief's `~ (cert_eps cert <= 2^-41)` is best stated with `~~`, since
   both sides are booleans.
4. The design audit's h1 hazard, that `sp_f` might not reduce through a named
   `Tableau Sampled` value, did not fire at all.
5. `Fail` does not catch a parse error, so the negative half of a keyword
   measurement cannot be recorded as a `Fail` inside a compiling file.
