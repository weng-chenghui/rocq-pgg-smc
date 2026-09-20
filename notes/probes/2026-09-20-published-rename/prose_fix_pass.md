# Fix pass over the rulings of `prose_rulings.md`

Base `c07f6a8`, branch `feat/tableau-extensions-probe`. The comments-only pass
in the working tree was kept; only the rulings below were applied. No `make`,
no git write, nothing removed under `notes/probes/`, no frozen file opened.

## Group manifest

### M1 `manifest/pgg_analysis_manifest.v` (header, line 9)

old
```
(* twelve-card chirality instance, and records one path per analysis path.    *)
(* Each path names its protocol instance, probability model, profile,         *)
(* execution, observed-execution and sample aliases, its observers with their *)
(* carriers, its correctness theorem, its security, leakage, mixing or        *)
(* limitation theorem, its static-to-executed bridge and model-transfer       *)
(* theorem when present, the missing model-transfer premise when none is      *)
(* claimed, its exact capability, its completion level and its assumption     *)
(* status.                                                                    *)
```
new
```
(* twelve-card chirality instance, and records each analysis path as one      *)
(* typed value. Each path names its protocol instance, probability model,     *)
(* profile, execution, observed-execution and sample aliases, its observers   *)
(* with their carriers, its correctness theorem, its security, leakage,       *)
(* mixing or limitation theorem, its static-to-executed bridge and            *)
(* model-transfer theorem when present, the missing model-transfer premise    *)
(* when none is claimed, its exact capability, its completion level and its   *)
(* assumption status.                                                         *)
```
Declaration fact: `Record AnalysisPath := MkAnalysisPath {...}` at line 941 of
the same file; the header already says "Each path is also a typed value of
AnalysisPath below", so every analysis path is recorded as one typed value.

### M2 `manifest/pgg_analysis_manifest.v` (Path 10 prose)

old
```
(* status, and they carry different statements, Path 9 exact independence and *)
(* this path a bound on the distance to that independent model. The           *)
(* propositions refuted in instances/psl211/psl211_reading_constancy.v are    *)
(* instances of coalition_reading_constancy, which                            *)
```
new
```
(* status, and the programs published over them prove different statements,   *)
(* Path 9's exact independence and this path's a bound on the distance to     *)
(* that independent model. The propositions refuted in                        *)
(* instances/psl211/psl211_reading_constancy.v are instances of               *)
(* coalition_reading_constancy, which                                         *)
```
Declaration fact: the five fields of `AnalysisPath` are `ap_observed`,
`ap_completion`, `ap_model`, `ap_transfer`, `ap_assumptions` (lines 942, 944,
950, 953, 956); none is a `Prop`, so a path carries no statement and the
statement belongs to the program published over the path.

### M3 `manifest/pgg_analysis_manifest.v` (Path 5 prose)

old `(* and deal_centi_lt stay in the path for what they are: they bound the       *)`
new `(* and deal_centi_lt stay named in the path for what they are: they bound the *)`

Declaration fact: `AnalysisPath` stores no theorem (five fields above), while
the header says "Each path names ... its security, leakage, mixing or
limitation theorem"; the two names are named, not stored.

M3's second place. The ruling says "the same sentence in the docstring of
`five_card_repeated_path`". That docstring does not carry the header's
sentence; it carries a different one with the same verb. I applied the
ruling's correction (the verb `stay` becomes `stay named`) and left the
docstring's own continuation intact:

old
```
    endpoint_bound and deal_centi_lt stay in the path as endpoint marginal
    bounds: each bounds one seat's endpoint distribution and neither quantifies
    over a coalition. *)
```
new
```
    endpoint_bound and deal_centi_lt stay named in the path as endpoint
    marginal bounds: each bounds one seat's endpoint distribution and neither
    quantifies over a coalition. *)
```

### M4 `manifest/pgg_analysis_manifest.v` (Absent capabilities)

old
```
(* No path is filled with a dummy theorem, an option-valued proof, an axiom   *)
(* or a placeholder, no endpoint marginal bound is recorded as a privacy or   *)
```
new
```
(* No path names a dummy theorem, an option-valued proof, an axiom or a       *)
(* placeholder, no endpoint marginal bound is recorded as a privacy or        *)
```
Same declaration fact as M3.

### M5 `manifest/pgg_analysis_status.v` (docstring of `TransferStatus`)

old
```
   NoModelComparison carry no such theorem, and the manifest path of such a
   path names the absent premise instead. *)
```
new
```
   NoModelComparison carry no such theorem, and a path with such a status
   names the absent premise instead. *)
```
Declaration fact: `Inductive TransferStatus : Set := | NoModelComparison |
StaticExecutedOnly | IdealFinite | NegativeTransfer.` is a status carried by a
path (`ap_transfer`), so the subject is a path with that status.

### M6 `manifest/pgg_analysis_client.v` (CODE)

banner old `(*     The typed status vocabulary and the nine paths                         *)`
banner new `(*     The typed status vocabulary and the eleven paths                       *)`

added after `Check psl211_alldecks_path.`
```
Check pgl27_prior_exact_path.
Check psl211_word_path.
```
Declaration fact: `Definition pgl27_prior_exact_path : AnalysisPath` at
`pgg_analysis_manifest.v:1090` and `Definition psl211_word_path : AnalysisPath`
at `:1105`; with the nine already listed this makes eleven, which is the count
the file header states.

### M7 `manifest/pgg_tableau.v` (comment above `Variant SecurityArm`)

old
```
   forgotten. A published program's manifest path records the path the program
   ran and no theorem, so two programs over one model and one pair of statuses
   are one manifest path; the arm is where they differ, and a reader asking what
   a finished program proved about a coalition reads this and not the
   manifest. *)
```
new
```
   forgotten. A published program's manifest path records the execution, the
   level, the model family and the two statuses, and no theorem, so two programs
   over one model and one pair of statuses are one manifest path; the arm is
   where they differ, and a reader asking what a finished program proved about a
   coalition reads this and not the manifest. *)
```
Declaration fact: the five fields listed under M2.

### M8 `manifest/pgg_tableau.v:4` (banner)

old `(* Tableau: the path program of one protocol instance                         *)`
new `(* Tableau: an analysis path of one protocol instance as a program            *)`

Declaration fact: the file header's next paragraph reads "A path of the
analysis manifest is written here as a program."

### M9 `manifest/pgg_analysis_manifest.v` (CODE, the `Timeout 60 Check`)

old
```
Timeout 60 Check (fun (row : AnalysisPath)
    (fam : AnalysisModelFamily (ap_observed row)) (R : realType)
    (x : amf_index fam R) =>
  amf_sample fam R x
    : @SampleAdapter R _ (OE.oe_execution (ap_observed row))).
```
new
```
Timeout 60 Check (fun (p : AnalysisPath)
    (fam : AnalysisModelFamily (ap_observed p)) (R : realType)
    (x : amf_index fam R) =>
  amf_sample fam R x
    : @SampleAdapter R _ (OE.oe_execution (ap_observed p))).
```
Three occurrences in that one term, nothing else.

## Group psl_s5_rest

### P1 `instances/psl211/tableau/psl211_tableau_analysis_bridged.v`

old
```
    decides the equation, so the manifest's path for this path is a claim this
    equation discharges rather than a table maintained beside the program. It
    differs from psl211_alldecks_path in the model family and in the transfer
```
new
```
    decides the equation, so the manifest's path for this program is a claim
    this equation discharges rather than a table maintained beside the program.
    It differs from psl211_alldecks_path in the model family and in the transfer
```
Declaration fact: `Lemma psl211_word_proximity_published_pathE :
published_path psl211_word_proximity_published = psl211_word_path.` The claim
is about the program's published path.

### P2 `instances/s5/tableau/s5_tableau_observed.v`

old `    which is the whole of what this path publishes. *)`
new `    which is the whole of what this path records. *)`

Declaration fact: `Lemma s5_dealt_path_observedE : ob_obs (tableau_at
s5_dealt) = ap_observed s5_det_path.` The path side is the record field
`ap_observed`, which is recorded, not published.

### P3 `instances/s5/tableau/s5_tableau_sampled.v` (header)

old (first two lines of the reflowed block)
```
(* dealer-dealt run, and the manifest's path over it, s5_word_path, is        *)
(* published from a mixing theorem rather than from a program: two of the     *)
```
new
```
(* dealer-dealt run, and the manifest's path over it, s5_word_path, is        *)
(* justified by a mixing theorem and by no program: two of the five parts of  *)
```
(the rest of that paragraph, through "claim about a coalition.", was re-flowed
without any word change).
Declaration fact: no `PublishedAt` value in this development names
`s5_word_path`; the file's own paragraph gives the two missing certificate
fields, so no program publishes it.

### P4 `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:165` (banner)

old `(*     The path program                                                       *)`
new `(*     The path as a program                                                  *)`

## Group pgl27

### G1 `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` (two places)

line 56 old `(* pgl27_exact_published, under The two path programs:                        *)`
line 56 new `(* pgl27_exact_published, under The two paths as programs:                    *)`

banner old `(*     The two path programs                                                  *)`
banner new `(*     The two paths as programs                                              *)`

### G2 index entries 102, 103, 131

Kept, as ruled. They already read "the exact path as a program", "the word
path as a program" and "the word path as a program at the proximity ...".

### G3 same file, docstring of `pgl27_prior_exact_published_pathE`

old
```
    conversion decides the equation, so the manifest's path for this path is a
    claim this equation discharges rather than a table maintained beside the
```
new
```
    conversion decides the equation, so the manifest's path for this program is
    a claim this equation discharges rather than a table maintained beside the
```
Declaration fact: `Lemma pgl27_prior_exact_published_pathE : published_path
pgl27_prior_exact_published = pgl27_prior_exact_path.`

### G4 and G10 same file, docstring of `pgl27_word_proximity_published_pathE`

old
```
(** The proximity program publishes the manifest's path for the word path, as
    pgl27_word_published_pathE says of the word program. An AnalysisPath holds
    descriptive metadata and no Prop, so one manifest path carrying an input-
    indistinguishability program and a proximity program says nothing about
    either claim. *)
```
new
```
(** The proximity program publishes the manifest's word path, as
    pgl27_word_published_pathE says of the word program. An AnalysisPath holds
    descriptive metadata and no Prop, so one manifest path published by an
    input-indistinguishability program and by a proximity program says nothing
    about either claim. *)
```
Declaration fact: `Lemma pgl27_word_proximity_published_pathE :
published_path pgl27_word_proximity_published = pgl27_word_path.` and the five
non-`Prop` fields of `AnalysisPath`. The re-flow also joined the hyphenated
word that the old third line split.

### G5 same file, header

old
```
(* about either claim. The manifest carries no fourth path over this instance *)
(* and publishes none of the three by a route this development's programs do  *)
(* not take.                                                                  *)
```
new
```
(* about either claim. The manifest carries no fourth path over this          *)
(* instance, and none of the three is published by a route this development's *)
(* programs do not take.                                                      *)
```
Declaration fact: `publish` is a constructor of the program language in
`manifest/pgg_tableau.v` and returns `PublishedAt`; the manifest holds
`AnalysisPath` values only.

### G6 `instances/pgl27/pgl27_proximity.v` (header)

old `(* with no program and no published program in it.                            *)`
new `(* with no program in it, published or not.                                   *)`

### G7 same header

old
```
(* The certificate itself, the program it publishes and the statements about  *)
(* them are in instances/pgl27/tableau/, whose AnalysisBridged file requires  *)
(* this one. This file requires no tableau module, so the arrow between the   *)
```
new
```
(* The certificate itself, the program published over it and the statements   *)
(* about them are in instances/pgl27/tableau/, whose AnalysisBridged file     *)
(* requires this one. This file requires no tableau module, so the arrow      *)
```
Declaration fact: `IndistinguishabilityCert` and `IdealProximityCert` are
records of data; `publish` is applied to a program, so a certificate publishes
nothing.

### G8 `instances/pgl27/pgl27_word_privacy.v`, docstring of `pgl27_word_marginal_bound`

old
```
    group itself; 2^-40 here bounds the loss of replacing that draw by a
    finite word, and it is the number a word program's spectral arm carries. *)
```
new
```
    group itself; 2^-40 here bounds the loss of replacing that draw by a finite
    word, and it is the number a word program's input-indistinguishability arm
    carries. *)
```
CONFIRMATION asked for by G8: `pgl27_word_marginal_bound` IS the `ic_b` of
`pgl27_word_cert`. `ic_b : ShuffleMarginalBound R (instance_M A)` is the first
field of `Record IndistinguishabilityCert` (`manifest/pgg_tableau.v:197`), and
`pgl27_word_cert` is built as
`@MkIndistinguishabilityCert R pgl27_algebra pgl27_dealt_params (amf_sample
pgl27_word_family R secretP) (pgl27_word_marginal_bound R) ...`
(`pgl27_tableau_analysis_bridged.v:341-349`), whose fifth argument, the first
field, is `pgl27_word_marginal_bound R`. The certificate is consumed by
`certify InputIndistinguishability pgl27_word_cert`, so the arm carrying that
number is the input-indistinguishability arm.

### G9 `instances/pgl27/pgl27_spectral.v`, docstring of `pgl27_rayleigh_Q2`

old `    one spectral input of the PGL(2,7) program and the only place the`
new `    one spectral input of the PGL(2,7) path and the only place the`

Twin: `instances/s5/s5_mixing.v:419` already reads "This is the one spectral
input of the S_5 path", so no edit was needed there; the twins now say one
thing in one word.

## Group kim

### K1 `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` (header)

old
```
(* published program is a program, and an AnalysisPath holds descriptive      *)
(* metadata and no Prop, so two programs publishing one AnalysisPath say      *)
(* nothing about each other's claim.                                          *)
```
new
```
(* published program carries its own theorem, and an AnalysisPath holds       *)
(* descriptive metadata and no Prop, so two programs publishing one           *)
(* AnalysisPath say nothing about each other's claim.                         *)
```
Declaration fact: `Record PublishedAt (c : ConcludedBound) := MkPublished {
published_at ...; published_path : AnalysisPath ; published_thm : BridgedProp c
published_at }` (`manifest/pgg_tableau.v:932-935`): `published_thm` is a field
of the finished program, and `AnalysisPath` has no `Prop` field.

### K2 same file, index glosses

```
old (*                           == the uniform program as a program              *)
new (*                           == the uniform path as a program                 *)

old (*                           == the repeated program as a program at the      *)
    (*                              input- indistinguishability arm               *)
new (*                           == the repeated path as a program at the         *)
    (*                              input-indistinguishability arm                *)

old (*                           == the one-cut program as a program at that same *)
new (*                           == the one-cut path as a program at that same    *)

old (*                           == the one-cut program as a program at the       *)
new (*                           == the one-cut path as a program at the          *)
```
The `==` column (29) and the continuation column (32) are unchanged.

### K3 same file, five docstrings

```
old (** The repeated program's certified program publishes the manifest's path for
        that path. Conversion decides it, as it does for the uniform program. An
new (** The repeated path's certified program publishes the manifest's repeated
        path. Conversion decides it, as it does for the uniform program. An

old (** The arm the repeated program's certified program carries, at every real
        field and index: a variation distance between the readings of the cut at
        two committed pairs, and not independence of the view from the
        conjunction of the committed bits. The certify statement the program
        wrote settles which arm that is. *)
new (** The arm the repeated path's certified program carries, at every real field
        and index: a variation distance between the readings of the cut at two
        committed pairs, and not independence of the view from the conjunction of
        the committed bits. The certify statement the program wrote settles which
        arm that is. *)

old (** The arm the one-cut program's certified program carries. The two Kim
        programs publish different manifest paths, and a reader of the manifest
        alone could not tell which arm either committed to. *)
new (** The arm the one-cut path's certified program carries. The two Kim programs
        publish different manifest paths, and a reader of the manifest alone could
        not tell which arm either committed to. *)

old (** The three coordinates the repeated program's certified program
        publishes. *)
new (** The three coordinates the repeated path's certified program publishes. *)

old (** The three coordinates the one-cut program's certified program
        publishes. *)
new (** The three coordinates the one-cut path's certified program publishes. *)
```
Declaration fact: each named `..._published` value has type `PublishedAt c`,
so the certified program is the program and the repeated/one-cut noun in front
of it is the manifest's entry.
K3's sixth place, `five_card_tableau_checks.v:126`, is inside the sentence K7
rewrites whole; it is covered there and not edited twice.

### K4 same file, docstring of `five_card_biased_proximity_published_pathE`

old
```
    holds descriptive metadata and no Prop, so one manifest path carrying
    an input-indistinguishability program and a proximity program says
    nothing about either claim. *)
```
new
```
    holds descriptive metadata and no Prop, so one manifest path published
    by an input-indistinguishability program and by a proximity program
    says nothing about either claim. *)
```
Declaration fact: `Lemma five_card_biased_proximity_published_pathE :
published_path five_card_biased_proximity_published = five_card_biased_path.`

### K5 `instances/kim2025/tableau/five_card_tableau_sampled.v`

old `(* programs named here reach Sampled. Each of the two paths also carries a    *)`
new `(* programs named here reach Sampled. Each of the two paths also has a        *)`

old `    biased path also carries a program that does reach AnalysisBridged. *)`
new `    biased path also has a program that does reach AnalysisBridged. *)`

Declaration fact: a path is a record of five descriptive fields and carries
nothing; the certified programs live in
`five_card_tableau_analysis_bridged.v`.

### K6 `instances/kim2025/tableau/five_card_tableau_checks.v` (header)

old
```
(* certified program against the uniform path, which differ in two of their   *)
(* five fields.                                                               *)
```
new
```
(* certified program's path against the uniform path, which differ in two of  *)
(* their five fields.                                                         *)
```
Declaration fact: the refused equation is between `published_path
five_card_repeated_indistinguishability_published` and
`five_card_uniform_path`, so the two sides compared are both paths.

### K7 same file, the docstring above the refused equation

old
```
(** What a path equation does reject is a program written for another
    path. The repeated program's certified program publishes the seven-cut
    model at IdealFinite and the uniform path holds the uniform family at
    StaticExecutedOnly, so the two paths differ in two of their five
    fields and the equation is refused. *)
```
new
```
(** What a path equation does reject is a program written for another
    path. The repeated path, which the repeated certified program
    publishes, holds the seven-cut model at IdealFinite and the uniform
    path holds the uniform family at StaticExecutedOnly, so the two paths
    differ in two of their five fields and the equation is refused. *)
```
Declaration fact: `five_card_repeated_path` is built as `@MkAnalysisPath
FiveCardAnalysis.observed AnalysisBridged FiveCardAnalysis.centi_family
IdealFinite BaselineClassicalOnly`, so the seven-cut model at `IdealFinite` is
held by the path, and the program publishes that path.

### K8 `instances/kim2025/five_card_proximity.v` (header)

old `(* with no program and no published program in it.                            *)`
new `(* with no program in it, published or not.                                   *)`

`instances/psl211/psl211_word_proximity.v` does not carry this sentence, so
nothing was changed there.

### K9 same header

old
```
(* The certificate itself, the program it publishes and the statements about  *)
(* them are in instances/kim2025/tableau/, whose AnalysisBridged file         *)
```
new
```
(* The certificate itself, the program published over it and the statements   *)
(* about them are in instances/kim2025/tableau/, whose AnalysisBridged file   *)
```
`psl211_word_proximity.v` does not carry this sentence either.

### K10 `instances/kim2025/five_card_mixing.v` (header)

old
```
(* other. That is the conclusion the analysis manifest's two Kim paths are   *)
(* bridged by. The manifest sits below the file that certifies those paths   *)
(* and holds no theorem of its own, so the theorem it names for a path's     *)
(* level has to be a facade alias, and the facade sits above this file.       *)
```
new
```
(* other. That is the conclusion the analysis manifest's two Kim paths are    *)
(* bridged by. The manifest sits below the file whose programs publish those  *)
(* paths and holds no theorem of its own, so the theorem it names for a       *)
(* path's level has to be a facade alias, and the facade sits above this      *)
(* file.                                                                      *)
```
Declaration fact: `five_card_uniform_path`, `five_card_biased_path` and
`five_card_repeated_path` are published by the `PublishedAt` values of
`five_card_tableau_analysis_bridged.v`; the manifest certifies nothing. The
re-flow also restored the four lines to 80 bytes (they stood at 79).

### K11 layout, `five_card_tableau_analysis_bridged.v`

```
old (*                              input- indistinguishability arm               *)
new (*                              input-indistinguishability arm                *)

old (*                              input- indistinguishability arm               *)
new (*                              input-indistinguishability arm                *)

old (*                              thirty- ninth and at its own number carry one *)
new (*                              thirty-ninth and at its own number carry one  *)
```
The first of the three is the K2 entry re-flowed above.

## Step 2: the tree-wide idiom, every site changed

| file:line | old | new | ruling |
|---|---|---|---|
| `manifest/pgg_tableau.v:4` | Tableau: the path program of one protocol instance | Tableau: an analysis path of one protocol instance as a program | M8 |
| `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:56` | under The two path programs: | under The two paths as programs: | G1 |
| `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:353` | The two path programs | The two paths as programs | G1 |
| `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:165` | The path program | The path as a program | P4 |
| `five_card_tableau_analysis_bridged.v:149` | the uniform program as a program | the uniform path as a program | K2 |
| `five_card_tableau_analysis_bridged.v:155` | the repeated program as a program at the | the repeated path as a program at the | K2 |
| `five_card_tableau_analysis_bridged.v:158` | the one-cut program as a program at that same | the one-cut path as a program at that same | K2 |
| `five_card_tableau_analysis_bridged.v:176` | the one-cut program as a program at the | the one-cut path as a program at the | K2 |
| `five_card_tableau_analysis_bridged.v:681,697,710,721,734` | the repeated/one-cut program's certified program | the repeated/one-cut path's certified program | K3 |
| `five_card_tableau_checks.v:125` | The repeated program's certified program publishes | The repeated path, which the repeated certified program publishes, | K7 |

After the pass the phrases "program as a program", "programs as programs",
"program program", "path program", "path for this path", "path of such a
path", "program's program", "path as a path" and "paths as paths" occur
nowhere in the 44 changed files. Every surviving "'s certified program" reads
"path's certified program".

Doubled phrases found and NOT changed, because no ruling covers them:

- `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:49-51` (header)
  "An AnalysisPath holds descriptive metadata and no Prop, so one manifest
  path carrying an input-indistinguishability program and a proximity program
  says nothing about either claim." This is the G10/K4 sentence, but the
  rulings name only the docstring of `pgl27_word_proximity_published_pathE`.
- `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:1078`
  "The proximity program publishes the manifest's path for the biased path".
  This is the G4 sentence, but K4 rules only the clause that follows it.
- `instances/s5/tableau/s5_tableau_sampled.v:34` "What the manifest publishes
  for that path is an endpoint marginal bound ...". A manifest publishes
  nothing (cf. G5), and no ruling names this sentence.

## Step 4: hyphen splits

Within-line hyphen-plus-space pairs, all in
`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` and all
fixed under K11: "input- indistinguishability" twice (the K2 index entry and
the `..._armE` index entry) and "thirty- ninth" once. A scan of all 44 changed
files finds no other within-line pair; none exists now.

Cross-line hyphen splits found by a separate scan. Each already split at the
same point at `c07f6a8`, so none was produced by the comments-only pass, and
none is in an entry K11 names. Left unchanged, listed for the owner:

| file | lines | word |
|---|---|---|
| `five_card_tableau_analysis_bridged.v` | 172-173 | input-indistinguishability |
| `five_card_tableau_analysis_bridged.v` | 241-242 | thirty-ninth |
| `five_card_tableau_analysis_bridged.v` | 295-296 | input-indistinguishability |
| `five_card_tableau_sampled.v` | 83-84 | one-cut |
| `five_card_tableau_sampled.v` | 92-93 | one-cut |
| `pgl27_tableau_analysis_bridged.v` | 158-159 | input-indistinguishability |
| `pgl27_tableau_checks.v` | 231-232 | point-mass |
| `instances/s5/s5_mixing.v` | 4-5 | adjacent-transposition |
| `manifest/pgg_analysis_status.v` | 115-116 | distribution-to-observer |

## Step 3: the two compiles

Run one at a time through the single-process wrapper, with the flags of
`_CoqProject`, in the ruled order.

| file | rc | seconds |
|---|---|---|
| `manifest/pgg_analysis_manifest.v` | 0 | 7 |
| `manifest/pgg_analysis_client.v` | 0 | 4 |

The client's output shows the two added checks resolving,
`pgl27_prior_exact_path` and `psl211_word_path`. Other importers of the
manifest were not recompiled.

## Step 6: `check_prose.py c07f6a8`

The checker was upgraded mid-pass (it now aligns the two word streams and
reports one OTHER CHANGE per region plus a NOUN SWAP category), so the run
below is against that version. Result: 44 files changed, program 619, path
240, other changed regions 51, and no LONG, no BOX and no BARRED line.

The run prints 51 OTHER CHANGE regions, 5 NOUN SWAP lines and 2 "code tokens
differ" lines. One ruled sentence can span several adjacent regions, because
the aligner splits at each unchanged word inside it. Every line, in the
checker's order:

| file | region the checker prints | regions | id |
|---|---|---|---|
| five_card_mixing.v | below the file that certifies those rows | 1 | K10 |
| five_card_proximity.v | no published row in it | 2 | K8 |
| five_card_proximity.v | the row it publishes | 2 | K9 |
| five_card_tableau_analysis_bridged.v | A published row is a program | 1 | K1 |
| five_card_tableau_analysis_bridged.v | input- indistinguishability, index gloss | 1 | K11 with K2 |
| five_card_tableau_analysis_bridged.v | row carries the input- indistinguishability | 1 | K11 |
| five_card_tableau_analysis_bridged.v | thirty- ninth | 1 | K11 |
| five_card_tableau_analysis_bridged.v | the manifest's row for that path | 1 | K3 |
| five_card_tableau_analysis_bridged.v | one manifest row carrying ... | 2 | K4 |
| five_card_tableau_checks.v | the repeated certified row against | 1 | K6 |
| five_card_tableau_checks.v | The repeated row's certified program publishes | 2 | K7 |
| five_card_tableau_sampled.v | carries -> has, twice | 2 | K5 |
| pgl27_proximity.v | no published row in it | 2 | G6 |
| pgl27_proximity.v | the row it publishes | 2 | G7 |
| pgl27_word_privacy.v | a word row's spectral arm | 1 | G8 |
| pgl27_tableau_analysis_bridged.v | ... and publishes none of the three ... | 3 | G5 |
| pgl27_tableau_analysis_bridged.v | NOUN SWAP row -> paths, then The two row programs: | 1 + swap | G1, index line |
| pgl27_tableau_analysis_bridged.v | NOUN SWAP row -> paths, then The two row programs | 1 + swap | G1, banner |
| pgl27_tableau_analysis_bridged.v | NOUN SWAP path -> program | swap | G3 |
| pgl27_tableau_analysis_bridged.v | the manifest's row for the word path | 1 | G4 |
| pgl27_tableau_analysis_bridged.v | one manifest row carrying an input- ... | 3 | G10, with the hyphen join |
| psl211_tableau_analysis_bridged.v | The row program, banner | 1 | P4 |
| psl211_tableau_analysis_bridged.v | NOUN SWAP path -> program | swap | P1 |
| s5_tableau_observed.v | this path publishes | 1 | P2 |
| s5_tableau_sampled.v | published from a mixing theorem rather than from a program | 2 | P3 |
| pgg_analysis_client.v | code tokens differ | code | M6, the two added Check lines |
| pgg_analysis_client.v | nine rows -> eleven paths | 1 | M6 |
| pgg_analysis_manifest.v | code tokens differ | code | M9, the bound variable |
| pgg_analysis_manifest.v | records one row per analysis path | 2 | M1 |
| pgg_analysis_manifest.v | stay in the row, header | 1 | M3 |
| pgg_analysis_manifest.v | they carry different statements, Row 9 ... | 3 | M2 |
| pgg_analysis_manifest.v | No row is filled with | 1 | M4 |
| pgg_analysis_manifest.v | stay in the row, docstring | 1 | M3, second place |
| pgg_analysis_status.v | the manifest row of such a path | 3 | M5 |
| pgg_tableau.v | Tableau: the row program, banner | 1 | M8 |
| pgg_tableau.v | NOUN SWAP program -> path | swap | M8 |
| pgg_tableau.v | A row of ... as a program | 1 | M8 |
| pgg_tableau.v | records the path the row ran | 2 | M7 |

The region column sums to 51 and the swap column to 5. No line is unmapped. `left as row` is 0 everywhere except
`pgg_analysis_manifest.v`, where it is 2; both are sense 4 and predate this
pass.

## Rulings not applied, and why

- **G2.** The ruling is "keep"; the three index entries already read as ruled.
- **G9, twin half.** `instances/s5/s5_mixing.v:419` already says "the one
  spectral input of the S_5 path"; no edit was needed.
- **K3, sixth place.** `five_card_tableau_checks.v:126` sits inside the
  sentence K7 replaces whole; applying K3 there as well would have written a
  phrase K7 removes.
- **K8 and K9, second half.** `instances/psl211/psl211_word_proximity.v` has
  neither sentence in its header, so the conditional half of each ruling does
  not fire.
- **M3, second place, applied in adapted form.** The ruling's sentence is
  "endpoint_bound and deal_centi_lt stay named in the path for what they are",
  which is FALSE of the docstring of `five_card_repeated_path`: that docstring
  reads "endpoint_bound and deal_centi_lt stay in the path as endpoint
  marginal bounds: each bounds one seat's endpoint distribution and neither
  quantifies over a coalition." Writing the ruling's sentence verbatim would
  have severed the colon and dropped the two clauses after it. I applied the
  correction the ruling makes (the path names them, it does not hold them) and
  kept the docstring's own predicate.

## Other observations, changed nothing

- Two boxed lines that the comments-only pass left at 79 bytes rather than 80:
  `five_card_tableau_analysis_bridged.v:118` and
  `pgg_analysis_manifest.v:603`. Neither is a line this fix pass touched, and
  the checker does not flag them, since they keep the space before the closing
  delimiter.
- The three unruled doubled-phrase sentences listed at the end of step 2.

## Follow-up

Second round of rulings, R1 to R5, on the observations above. Comments only,
no compile. M3's adapted second place is confirmed as written.

### R1 `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` header

old
```
(* metadata and no Prop, so one manifest path carrying an                     *)
(* input-indistinguishability program and a proximity program says nothing    *)
```
new
```
(* metadata and no Prop, so one manifest path published by an                 *)
(* input-indistinguishability program and by a proximity program says nothing *)
```
The rest of the paragraph re-flowed to the same lines it already had. The
header and the docstring of `pgl27_word_proximity_published_pathE` now carry
the same sentence.

### R2 `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v`, docstring of `five_card_biased_proximity_published_pathE`

old
```
(** The proximity program publishes the manifest's path for the biased
    path, as its input-indistinguishability sibling does. An AnalysisPath
    holds descriptive metadata and no Prop, so one manifest path published
    by an input-indistinguishability program and by a proximity program
    says nothing about either claim. *)
```
new
```
(** The proximity program publishes the manifest's biased path, as its
    input-indistinguishability sibling does. An AnalysisPath holds
    descriptive metadata and no Prop, so one manifest path published by an
    input-indistinguishability program and by a proximity program says
    nothing about either claim. *)
```
Confirmed before writing: `Lemma five_card_biased_proximity_published_pathE :
published_path five_card_biased_proximity_published = five_card_biased_path.`
The path the program publishes IS `five_card_biased_path`, so "the manifest's
biased path" names it.

### R3 `instances/s5/tableau/s5_tableau_sampled.v` header

old
```
(* before any coalition is named. What the manifest publishes for that path   *)
(* is an endpoint marginal bound against the encoder-image ideal, with no     *)
(* claim about a coalition.                                                   *)
```
new
```
(* before any coalition is named. What the manifest names for that path is an *)
(* endpoint marginal bound against the encoder-image ideal, with no claim     *)
(* about a coalition.                                                         *)
```
Declaration fact: the manifest header says each path names its theorems, and
the `AnalysisPath` record has no `Prop` field, so nothing is published there.

### R4 the two boxed lines at 79 bytes

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:118`

old `(*     and, under What the proximity program states at this instance, the    *)`
new `(*     and, under What the proximity program states at this instance, the     *)`

`manifest/pgg_analysis_manifest.v:603`

old `(*                          this path is observer-level and does NOT         *)`
new `(*                          this path is observer-level and does NOT          *)`

Both are now exactly 80 bytes with the space before the closing delimiter. No
word changed, so neither shows in the checker's word comparison.

### R5

The nine cross-line hyphen splits listed in step 4 were left as they are.

### Checker after the follow-up

`check_prose.py c07f6a8`: 44 files changed, program 619, path 239, other
changed regions 55, and no LONG, no BOX and no BARRED line. Against the
previous run the region list grows by exactly four entries and loses none:

| file | region the checker prints | id |
|---|---|---|
| pgl27_tableau_analysis_bridged.v | one manifest row carrying an input-indistinguishability row | R1 |
| pgl27_tableau_analysis_bridged.v | input-indistinguishability row and a proximity row | R1 |
| five_card_tableau_analysis_bridged.v | publishes the manifest's row for the biased path, as | R2 |
| s5_tableau_sampled.v | What the manifest publishes for that path | R3 |

The `path` total drops from 240 to 239 because R2 removes the trailing "path"
that the first pass had turned from "row"; the word is gone, not re-nouned.
R4 adds nothing, as expected of a padding-only change.
