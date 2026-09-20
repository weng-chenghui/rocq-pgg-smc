# Comments-only fix pass 2: the audit rulings T1-T9 and S1-S5, S8, S11, S12

Applied over the working tree on top of `c07f6a8` (the noun pass and fix pass 1
were already in the tree and nothing of theirs was reverted). Comments only: no
code token was touched, nothing was compiled, no Rocq process was started, no
git command that writes was run, nothing under `notes/probes/` was deleted, and
no file of the forward closure of `instances/psl211/psl211_endpoints.v` was
opened for editing.

Files edited in this pass:

```
instances/kim2025/five_card_mixing.v
instances/kim2025/tableau/five_card_tableau_analysis_bridged.v
instances/kim2025/tableau/five_card_tableau_sampled.v
instances/pgl27/pgl27_profile_privacy.v
instances/pgl27/pgl27_spectral.v
instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v
instances/psl211/psl211_word_proximity.v
instances/psl211/tableau/psl211_tableau_analysis_bridged.v
instances/psl211/tableau/psl211_tableau_executable.v
instances/psl211/tableau/psl211_tableau_sampled.v
instances/s5/s5_mixing.v
instances/s5/tableau/s5_tableau_analysis_bridged.v
instances/s5/tableau/s5_tableau_executable.v
instances/s5/tableau/s5_tableau_observed.v
manifest/pgg_analysis_manifest.v
manifest/pgg_tableau.v
manifest/pgg_tableau_syntax.v
```

---

## T1. `instances/pgl27/pgl27_profile_privacy.v`, 22 sites, noun **analysis**

The file requires `pgg_interface`, `pgg_monodromy_profile`,
`pgg_sharing_framework`, `covering_scheme`, `transitivity_privacy`,
`dealer_privacy`, `pgl27_group`, `pgl27_orbit`, `pgl27_scheme`, `pgl27_profile`
and `pgl27_secrecy`, so no `Tableau`, `Published` or `AnalysisPath` value is in
scope; the two referents are the laws `pgl27P` (`pgl27_secrecy.v`) and
`pgl27P_alldecks` (`pgl27_trace.v`). Every occurrence of "the model" in the file
names the dealer model of `reconstruct/dealer_privacy.v` and was left untouched,
so "the exact analysis" and "the dealer model" stand apart in every sentence.
`==` columns and the file's continuation column of five are kept; every boxed
line is 80 bytes.

Header prose, sites 1-3:

```
old: (* The dealer route. The same two theorems are obtained a third way, from     *)
     (* the dealer model of reconstruct/dealer_privacy.v, by placing the two       *)
     (* PGL(2,7) programs in its sample space. The exact program goes through the  *)
     (* mixed-law condition, ... the all-decks program goes through the            *)
     (* per-deck condition, ...
new: (* The dealer route. The same two theorems are obtained a third way, from the *)
     (* dealer model of reconstruct/dealer_privacy.v, by placing the two PGL(2,7)  *)
     (* analyses in its sample space. The exact analysis goes through the          *)
     (* mixed-law condition, its deterministic dealer making that condition a      *)
     (* statement about a single deck; the all-decks analysis goes through the     *)
     (* per-deck condition, with validity taken to be a deck without repeated      *)
     (* cards. Both restate an existing theorem and replace no proof.              *)
```

Header index entries, sites 4-10:

| site | new line(s) |
|---|---|
| 4 | `(*   pgl27_dealer_delta      == the deterministic dealer of the               *)` + `(*     exact analysis                                                         *)` |
| 5 | `(*   pgl27_dealerP           == the exact analysis in the dealer sample space *)` |
| 6 | `(*   pgl27_alldecks_dealerP  == the all-decks analysis in that sample space   *)` |
| 7 | `(*   pgl27_dealerPE == the exact analysis's law is the dealer model's law at  *)` + `(*     the deterministic kernel                                               *)` |
| 8 | `(*   pgl27_dealer_viewE == the model's view along the embedding is the exact  *)` + `(*     analysis's view                                                        *)` |
| 9 | `(*   pgl27_dealer_secretE == and its secret is the analysis's orbit secret    *)` |
| 10 | `(*   pgl27_alldecks_dealerPE == the all-decks analysis's law is the           *)` + `(*     model's law                                                            *)` |

Docstrings, sites 11-22, with the declaration each sits on:

| site | declaration | phrase now |
|---|---|---|
| 11 | `Definition pgl27_dealer_delta` | "the deterministic dealer of the exact PGL(2,7) analysis" |
| 12 | `Definition pgl27_dealerP` | "the exact analysis's data placed in the dealer model's sample space" |
| 13 | `Definition pgl27_dealer_embed` | "a sample of the exact analysis, which carries only a secret and a shuffle" |
| 14 | `Lemma pgl27_dealerPE` | "the exact analysis's law pushed along pgl27_dealer_embed" |
| 15 | `Lemma pgl27_dealerPE` | "the analysis's two-coordinate law" |
| 16 | `Lemma pgl27_dealerPE` | "the function the analysis leaves implicit" |
| 17 | `Lemma pgl27_dealer_viewE` | "is the exact analysis's view" |
| 18 | `Lemma pgl27_dealer_secretE` | "is the exact analysis's orbit secret" |
| 19 | `Lemma pgl27_dealer_view_law` | "the deck the exact analysis lays" |
| 20 | `Lemma pgl27_view_indep_via_dealer` | "the exact analysis's own privacy statement" |
| 21 | `Lemma pgl27_view_indep_via_dealer` | "the same law in the analysis's two coordinates" |
| 22 | `Definition pgl27_alldecks_dealerP` | "the all-decks analysis's data in the dealer model's sample space" |

Declaration facts that make the new sentences true: `pgl27_dealerP` and
`pgl27_alldecks_dealerP` are `R.-fdist (bool * (deckT * shuffleT))` built by
`dealer_shuffleP` from `pgl27_dealer_delta` / `pgl27_alldecks_dealer_delta` and
`pgl27_dealer_nu`; `pgl27_dealerPE` equates `fdistmap pgl27_dealer_embed
(pgl27P R)` with `pgl27_dealerP`, so the law on the left is the exact analysis's
own law; `pgl27_dealer_viewE` and `pgl27_dealer_secretE` equate the dealer
model's view and secret, composed with the embedding, with `pgl27_view` and
`pgl27_secret`; `pgl27_view_indep_via_dealer` states `pgl27P R |= pgl27_view R C
_|_ pgl27_secret R` verbatim.

**Sentences that stay loose after the noun change** (the noun was applied
anyway, as instructed; both are inherited from the base text at `c07f6a8`,
which read "row" in the same slot):

- site 5, `pgl27_dealerP == the exact analysis in the dealer sample space`;
- site 6, `pgl27_alldecks_dealerP == the all-decks analysis in that sample
  space`.

An analysis is not a point of a sample space. The two docstrings these entries
index (sites 12 and 22) say the exact thing, "the exact analysis's **data**
placed in the dealer model's sample space", so a one-word repair of the index
entries would be to read "data" into them, which is outside this pass.

---

## T2. `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v`, docstring of `pgl27_exact_published`

```
old:     above, and the manifest path. Its last line publishes a program whose
         transfer status is StaticExecutedOnly, because the cut this model draws is
new:     above, and the manifest path. Its last line publishes a path whose transfer
         status is StaticExecutedOnly, because the cut this model draws is already
```

Declaration fact: `publish` is `@MkPublished c q (@MkAnalysisPath (ab_obs q)
AnalysisBridged (ab_f q) t a) pf`, so the transfer status `t` is `ap_transfer`,
a field of the `AnalysisPath` the line builds; `PublishedAt` has only
`published_at`, `published_path`, `published_thm`. Both siblings already read
"publishes a path whose transfer status is StaticExecutedOnly".

---

## T3. `five_card_tableau_analysis_bridged.v`, docstring of `five_card_biased_forms_pathE`

```
old:     AnalysisPath holds descriptive metadata and no Prop, so an equation
         between two published programs says nothing about either certificate,
new:     AnalysisPath holds descriptive metadata and no Prop, so an equation between
         two published paths says nothing about either certificate, and in particular
```

Declaration fact: the lemma is `published_path
five_card_biased_indistinguishability_published = published_path
five_card_biased_published_inv25`, an equation between two `AnalysisPath`
values. An equation between two `PublishedAt` values would carry
`published_thm` with it and would say something about the certificates.

---

## T4. `five_card_tableau_analysis_bridged.v`, the branch's path equation

Docstring:

```
old: (** The branch publishes the manifest's own path for the biased path. *)
new: (** The branch publishes the manifest's own biased path. *)
```

Index entry:

```
old: (*                           == the branch publishes the manifest's path for  *)
     (*                              the one-cut path                              *)
new: (*                           == the branch publishes the manifest's           *)
     (*                              one-cut path                                  *)
```

Declaration fact: `five_card_biased_branch_indistinguishability_published_pathE
: published_path five_card_biased_branch_indistinguishability_published =
five_card_biased_path`, so the path published is `five_card_biased_path` itself.

---

## T5. `instances/kim2025/five_card_mixing.v`, header

```
old: (* Those two are the base premises of the certificates the analysis manifest  *)
     (* records for Kim's one-cut and seven-cut paths. ...
new: (* Those two are the base premises of the certificates Kim's one-cut and      *)
     (* seven-cut programs carry. The constancy is exact and is quantified over    *)
     (* every coalition below the privacy threshold and over both committed pairs; *)
     (* the distance is where the two programs' published numbers come from. The   *)
     (* seven-cut law is given at the bundle's own spectral number, the one-cut    *)
     (* law at that number and at the exact one fiftieth its program publishes.    *)
```

Declaration fact: `Record AnalysisPath` has the five fields `ap_observed`,
`ap_completion`, `ap_model`, `ap_transfer`, `ap_assumptions` and no certificate
field; `kim_centi_cert` and `kim_biased_cert` are the `certify` payloads of
`five_card_repeated_indistinguishability_published` and
`five_card_biased_indistinguishability_published` in
`five_card_tableau_analysis_bridged.v`. The sibling `five_card_analysis.v:16`
already says "programs".

---

## T7. The spectral input, both twins

`instances/pgl27/pgl27_spectral.v`, docstring of `pgl27_rayleigh_Q2`:

```
old:     one spectral input of the PGL(2,7) path and the only place the
new:     one spectral input of the PGL(2,7) word analysis and the only place the
```

`instances/s5/s5_mixing.v`, docstring of `s5_rayleigh_Q2_R`:

```
old:     does to the complement.  This is the one spectral input of the S_5 path,
         and the only place the certificate tables are used.
new:     does to the complement.  This is the one spectral input of the S_5 word
         analysis, and the only place the certificate tables are used.
```

Declaration fact: `pgl27_rayleigh_Q2` bounds `v^T Q^2 v` on the sum-zero
subspace and feeds the mixing field of `pgl27_word_cert`, which
`pgl27_word_published` carries; `s5_rayleigh_Q2_R` feeds `S5Analysis`'s word
bound, and the manifest's `s5_word_path` is reached by a mixing theorem and by
no program. Neither number is a coordinate of an `AnalysisPath`, so "path" was
wrong in both; "word analysis" names the same thing in both files.

---

## T8. `five_card_tableau_sampled.v`, header

```
old: (* five_card_repeated_sampled and five_card_biased_sampled are names the      *)
     (* instance already had, and they carry the published-program suffix although *)
     (* both are Tableau Sampled values and neither is a published program. They   *)
     (* are existing names and they stay. five_card_uniform_sampled follows the    *)
     (* naming scheme, and the five programs written out from the prefix are       *)
     (* identified with these three values in                                      *)
     (* five_card_tableau_analysis_bridged.v.                                      *)
new: (* five_card_repeated_sampled, five_card_biased_sampled and                   *)
     (* five_card_uniform_sampled follow one naming scheme, and the five programs  *)
     (* written out from the prefix are identified with these three values         *)
     (* in five_card_tableau_analysis_bridged.v.                                   *)
```

**The count "five" is correct.** `five_card_tableau_analysis_bridged.v` has
exactly five `_sampledE` lemmas, and no sixth:

```
516  five_card_uniform_published_sampledE
656  five_card_repeated_indistinguishability_published_sampledE
674  five_card_biased_indistinguishability_published_sampledE
842  five_card_repeated_published39_sampledE
915  five_card_biased_published_inv25_sampledE
```

(line numbers before this pass's edits to the file). They identify one program
written from the prefix with `five_card_uniform_sampled`, two with
`five_card_repeated_sampled` and two with `five_card_biased_sampled`, which is
the "three values" the sentence names.

---

## T9. `five_card_tableau_analysis_bridged.v`, index entry of `five_card_biased_proximity_published`

```
old: (*                              proximity arm, published at one fiftieth      *)
new: (*                              proximity arm, certified at one fiftieth      *)
```

Declaration fact: `Definition five_card_biased_proximity_published : Published`
has no `conclude` line, and `Notation Published := (PublishedAt
no_concluded_bound)`, so the value publishes no number; one fiftieth is
`kim_biased_proximity_cert`'s own number.

---

## S1. `manifest/pgg_tableau_syntax.v`, the `execute` notation block

```
old:    What this statement builds is the observed execution, and publish writes it
        unchanged into the program's ap_observed. A program therefore describes the
new:    What this statement builds is the observed execution, and publish writes it
        unchanged into the path's ap_observed. A program therefore describes the run
```

Declaration fact: `ap_observed` is the first field of `Record AnalysisPath`, and
`publish` writes the observed execution into the path it builds;
`Record PublishedAt` has no `ap_observed`.

---

## S2. `manifest/pgg_tableau.v`, docstring of `Record PublishedAt`

```
old:    program reached. The manifest already publishes the descriptive path; a
new:    program reached. The manifest already records the descriptive path; a
```

Declaration fact: the manifest is a list of `Definition ..._path :
AnalysisPath` values and holds no `Prop`; `pgg_analysis_manifest.v:9` states its
own verb, "records each analysis path as one typed value". A program publishes a
path, a manifest does not.

---

## S3. `manifest/pgg_analysis_manifest.v`, docstring of `five_card_repeated_path`

```
old:     endpoint_bound and deal_centi_lt stay named in the path as endpoint
new:     endpoint_bound and deal_centi_lt are listed for this path as endpoint
```

Declaration fact: `five_card_repeated_path := @MkAnalysisPath
FiveCardAnalysis.observed AnalysisBridged FiveCardAnalysis.centi_family
IdealFinite BaselineClassicalOnly` stores no theorem, and the `AnalysisPath`
docstring twelve lines above says so ("It stores no theorem: theorems stay
facade aliases, named separately"). The two theorems are named in the Path 5
prose entry at `:403-404` and `:425-428`.

---

## S4. `instances/s5/tableau/s5_tableau_observed.v`, docstring of `s5_dealt_path_observedE`

```
old:     description of the run and the proof of run correctness for it are one term,
         which is the whole of what this path records. *)
new:     description of the run and the proof of run correctness for it are one term,
         which is the whole of what this path says about the run. *)
```

Declaration fact: `s5_det_path = @MkAnalysisPath S5Analysis.observed Observed
None NoModelComparison (AcceptsAxioms [:: AxS5GroupOrder])` also records the
level, the empty model slot and two statuses, so the identification `ob_obs
(tableau_at s5_dealt) = ap_observed s5_det_path` is not the whole of what the
path records; it is the whole of what the path says about the run.

---

## S5. `instances/psl211/psl211_word_proximity.v`, header

```
old: (* names. The certificate built on them, the row it certifies and the         *)
     (* statements about that row are at AnalysisBridged, in                       *)
     (* instances/psl211/tableau/.                                                 *)
     [fix pass 1 had made this "the program it certifies"]
new: (* names. The certificate built on them, the program certified over it and    *)
     (* the statements about that program are at AnalysisBridged,                  *)
     (* in instances/psl211/tableau/.                                              *)
```

Declaration fact: `manifest/pgg_tableau_arm_relations.v:6` states that a Tableau
program certifies one of three arms; a certificate certifies nothing. The two
sibling headers `instances/pgl27/pgl27_proximity.v:42` and
`instances/kim2025/five_card_proximity.v:37` read "the program published over
it", so the pair now agrees in shape.

---

## S8. `manifest/pgg_analysis_manifest.v`, the Path 11 entry

```
old: (* status, and the programs published over them prove different statements,   *)
     (* Path 9's exact independence and this path's a bound on the distance to     *)
     (* that independent model. The propositions refuted in                        *)
new: (* status, and the programs published over them prove different statements:   *)
     (* exact independence over Path 9, and over this path a bound on the distance *)
     (* to that independent model. The propositions refuted in                     *)
```

Declaration fact: over Path 9 `psl211_alldecks_published` proves exact
independence and over Path 11 `psl211_word_proximity_published` proves the
2^-40 bound; the two paths differ in `ap_model` (`PSL211Analysis.exact_family`
against `word_family`) and in `ap_transfer` (`StaticExecutedOnly` against
`IdealFinite`). The elliptical genitives that could be read as the paths' own
statements are gone.

---

## T6. One value, one name, in the three five-card tableau files

Decision rule applied at every site: where the noun phrase **names** the value
`five_card_repeated_indistinguishability_published` or
`five_card_biased_indistinguishability_published`, it now reads "the repeated
certified program" / "the one-cut certified program". The phrase stays bare
where the sentence sits on, or speaks of, `five_card_repeated_sampled` /
`five_card_biased_sampled`, or names the thing a terminal concludes a constant
for (`five_card_repeated_published39`, `five_card_biased_published_inv25`), or
names a fifth or sixth value (the branch, the proximity program). The phrase
"the repeated path's certified program" / "the one-cut path's certified
program" from the withdrawn ruling K3 no longer occurs anywhere in the tree.

### Changed, 18 sites, all in `five_card_tableau_analysis_bridged.v`

| line now | declaration the comment sits on | old | new |
|---|---|---|---|
| 150 | index, `kim_centi_cert` | the repeated program's certificate at its bundle's number | the repeated certified program's certificate at its bundle's number |
| 152 | index, `kim_biased_cert` | the one-cut program's certificate at its bundle's number | the one-cut certified program's certificate at its bundle's number |
| 240 | index, `kim_centi_cert_epsE` | the repeated program's number in closed form | the repeated certified program's number in closed form |
| 244 | index, `kim_biased_cert_epsE` | the one-cut program's number in closed form | the one-cut certified program's number in closed form |
| 605 | `Definition kim_centi_cert` | certificate of the repeated program | certificate of the repeated certified program |
| 623 | `Definition kim_biased_cert` | certificate of the one-cut program | certificate of the one-cut certified program |
| 626 | `Definition kim_biased_cert` | the same two terms as in the repeated program's certificate | ... as in the repeated certified program's certificate |
| 666 | `Definition five_card_biased_indistinguishability_published` | Its certificate has the shape the repeated program's has | ... the shape the repeated certified program's has |
| 675 | `Lemma five_card_biased_indistinguishability_published_sampledE` | The same for the one-cut program and the named one-cut model. | The same for the one-cut certified program and the named one-cut model. |
| 683 | `Lemma five_card_repeated_indistinguishability_published_pathE` | The repeated path's certified program publishes the manifest's repeated path. | The repeated certified program publishes the manifest's repeated path. |
| 693 | `Lemma five_card_biased_indistinguishability_published_pathE` | The same for the one-cut program and the manifest's biased path. | The same for the one-cut certified program and the manifest's biased path. |
| 700 | `Lemma five_card_repeated_indistinguishability_published_armE` | The arm the repeated path's certified program carries | The arm the repeated certified program carries |
| 713 | `Lemma five_card_biased_indistinguishability_published_armE` | The arm the one-cut path's certified program carries. | The arm the one-cut certified program carries. |
| 724 | `Lemma five_card_repeated_indistinguishability_published_path_fieldsE` | The three coordinates the repeated path's certified program publishes. | The three coordinates the repeated certified program publishes. |
| 737 | `Lemma five_card_biased_indistinguishability_published_path_fieldsE` | The three coordinates the one-cut path's certified program publishes. | The three coordinates the one-cut certified program publishes. |
| 771 | `Lemma kim_centi_cert_epsE` | The repeated program's published bound in closed form | The repeated certified program's published bound in closed form |
| 791 | `Lemma kim_biased_cert_epsE` | The one-cut program's published bound in closed form | The one-cut certified program's published bound in closed form |
| 798 | `Lemma kim_biased_cert_eps_lt2` | The one-cut program's bound is under two | The one-cut certified program's bound is under two |

Declaration facts: `five_card_repeated_indistinguishability_published` is
`five_card_committed sample kim_centi_family certify InputIndistinguishability
kim_centi_cert |> publish IdealFinite BaselineClassicalOnly`, so `kim_centi_cert`
is its certificate and `cert_eps (kim_centi_cert R idx)` its number; the one-cut
twin is the same with `kim_biased_family` and `kim_biased_cert`. The `_pathE`,
`_armE` and `_path_fieldsE` lemmas are all stated of those two values.

### Left bare, deliberately, with the declaration

`five_card_tableau_analysis_bridged.v`:

| line now | declaration / place | why it stays |
|---|---|---|
| 643 | `Definition five_card_repeated_indistinguishability_published` | "Kim's repeated program certified by the input-indistinguishability arm and published at IdealFinite" is the docstring that introduces the value; the appositive already says "certified by", and inserting the name would make the sentence say "certified program certified by the arm". The audit's own finding puts the two defining docstrings outside the rule. |
| 665 | `Definition five_card_biased_indistinguishability_published` | same, first sentence only; its second sentence was changed (line 666 above) |
| 42, 45, 51, 82 (twice), 83 | header, about `five_card_repeated_published39` and `five_card_biased_published_inv25` | names the thing a terminal concludes a constant for |
| 163, 168, 249, 252, 256, 261, 267 | index entries of the concluded values | same |
| 164, 879, 891 | `kim_biased_cert_exact` and its two lemmas | the certificate of the concluded value `five_card_biased_published_inv25` |
| 172 | index, `five_card_biased_branch_indistinguishability_published` | a different value, the branch |
| 758 | `Fact five_card_pow2_39_split` | "the constant the repeated program publishes" is 2^-39, the terminal's constant |
| 826, 842, 855, 869, 900, 917, 937, 949 | the concluded values' definitions and lemmas | all read "the concluded ... program" or name the constant |
| 959, 1146, 1211, 1225 | `kim_biased_proximity_cert` and the proximity lemmas | the proximity program, a different value |
| 130, 927 | "the two one-cut programs" | a set of two values, not a name |
| 575 | `A program built ...` | generic |

`five_card_tableau_sampled.v`: lines 77 and 80 (index of
`five_card_repeated_sampled_modelE` / `five_card_biased_sampled_modelE`) and 143
(docstring of `five_card_repeated_sampled`) all speak of the Sampled values and
stay bare. Nothing in this file was edited for T6.

`five_card_tableau_checks.v`: line 17 ("the one-cut Sampled program"), 43 and 49
("the two programs over the one-cut model") stay bare; lines 19 and 125 already
read "the repeated certified program" after ruling K6 and K7, so the K3 phrase
is not present and nothing was edited here.

---

## S11. Banners

Changed:

```
psl211_tableau_analysis_bridged.v:165
  old: (*     The path as a program                                                  *)
  new: (*     The all-decks program                                                  *)

pgl27_tableau_analysis_bridged.v:353
  old: (*     The two paths as programs                                              *)
  new: (*     The exact and the word program                                         *)

pgl27_tableau_analysis_bridged.v:56 (the header line that quotes that banner)
  old: (* pgl27_exact_published, under The two paths as programs:                    *)
  new: (* pgl27_exact_published, under The exact and the word program:               *)
```

Each is one content line, indented five spaces like every other banner of its
file, 80 bytes, with a space before the closing delimiter.

**Every "under <banner>" reference of the four files was checked against the
banners that exist.** Only `pgl27:56` had gone stale. The others all quote a
banner verbatim: kim `:91` (The uniform program), `:94` (The exact arm's four
conjuncts at this instance), `:96-97` (Kim's two programs, certified against the
uniform rotation law), `:100` ("the same banner"), `:103-104` (The same two
programs at the constants they publish), `:108` ("the same banner"), `:112-113`
(One model, two claims, two programs), `:115` ("the same banner"), `:118` (What
the proximity program states at this instance); pgl27 `:60`, `:66` ("the same
banner"), `:64` (The word program concluded at 2^-39), `:68-69` (The same
program from the named word model), `:71-72` (The ideal: the exact shuffle at
every prior), `:74` (One model, two claims, two programs). The psl211 and S_5
headers carry no such reference.

### All section banners of the four analysis-bridged files, after this pass

`five_card_tableau_analysis_bridged.v`

```
 362  The instance-side reading of a coalition
 428  The uniform family's witness
 496  The uniform program
 544  The exact arm's four conjuncts at this instance
 574  Kim's two certificates
 640  Kim's two programs, certified against the uniform rotation law
 752  The number each certificate publishes
 819  The same two programs at the constants they publish
 956  The proximity certificate, and its ideal
 995  The number
1035  One model, two claims, two programs
1121  What the proximity program states at this instance
1181  A number below the certificate's is refused
1203  Every hypothesis discharged at one concrete coalition
1222  The proximity proposition at this instance, and what implies it
```

`pgl27_tableau_analysis_bridged.v`

```
 253  The exact family's witness
 307  The word family's certificate
 353  The exact and the word program
 456  The word program concluded at 2^-39
 503  The same program from the named word model
 528  A number below the proved one
 549  The word statement, from the word program
 610  The exact statement, from the exact program
 670  The exact arm's four conjuncts at this instance
 698  Each published statement and its restatement are one statement
 733  The ideal: the exact shuffle at every prior
 813  The proximity certificate, and its ideal
 850  The number
 904  One model, two claims, two programs
 976  What the proximity program states at this instance
```

`psl211_tableau_analysis_bridged.v`

```
 140  The exact arm's witness
 165  The all-decks program
 212  The exact arm's four conjuncts at this instance
 248  The certificate, and its ideal
 309  The number
 336  The program
 399  What the program states at this instance
```

`s5_tableau_analysis_bridged.v`

```
  93  The instance-side reading of a coalition
 140  The tape model's witness
 160  The randomized program
 206  The exact arm's four conjuncts at this instance
```

Read as one family: every banner over a finished program now names the program
(`The uniform program`, `The all-decks program`, `The randomized program`, `The
program`, `The exact and the word program`, `Kim's two programs, ...`); no
banner says "as a program" any more.

---

## S12. The five re-flowed docstrings, same words, same order

```
psl211_tableau_analysis_bridged.v, docstring of psl211_alldecks_published_armE
  old:     readings. The certify statement the program wrote settles which arm that is.
           *)
  new:     readings. The certify statement the program wrote settles which arm
           that is. *)

s5_tableau_analysis_bridged.v, docstring of s5_rand_published_armE
  old:     readings. The certify statement the program wrote settles which arm that is.
           *)
  new:     readings. The certify statement the program wrote settles which arm
           that is. *)

psl211_tableau_executable.v, header
  old: (* edge of a program the surface cannot write when the two levels are two     *)
       (* files.                                                                     *)
  new: (* edge of a program the surface cannot write when the two levels are         *)
       (* two files.                                                                 *)

s5_tableau_executable.v, header
  old: (* edge of a program the surface cannot write when the two levels are two     *)
       (* files.                                                                     *)
  new: (* edge of a program the surface cannot write when the two levels are         *)
       (* two files.                                                                 *)

psl211_tableau_sampled.v, header
  old: (* instance part here and not lower. The deck description is drawn uniformly  *)
       (* in both.                                                                   *)
  new: (* instance part here and not lower. The deck description is drawn            *)
       (* uniformly in both.                                                         *)
```

No closing delimiter and no single word stands alone on a last line in any of
the five.

---

## Layout

Every line written in this pass is at most 80 bytes; every boxed line is exactly
80 bytes with a space before the closing delimiter. A scan of every new line of
every changed `.v` file against `c07f6a8` reports no line over 80 bytes and no
boxed line off 80 bytes. The `==` columns of `pgl27_profile_privacy.v` and of
the five-card index are unchanged, the continuation column is five in
`pgl27_profile_privacy.v` and thirty in the five-card index, docstring
continuations are four spaces, and no new text holds the project's barred
vocabulary, a token made of a capital letter and a digit, an abbreviation of
"indistinguishability", a history word or a metaphor word.

---

## `check_prose.py c07f6a8`

```
44 files changed; program 592, path 231; other changed regions 109
PROBLEMS
```

`PROBLEMS` is the expected verdict: the two "code tokens differ" lines and the
noun swaps set the flag. No `LONG`, no `BOX`, no `BARRED`, no `FROZEN FILE
CHANGED`. Five `NOUN SWAP` lines and two "code tokens differ" lines, the same
count as after fix pass 1:

| line | belongs to |
|---|---|
| `code tokens differ in manifest/pgg_analysis_client.v` | M6, the two added `Check` lines (fix pass 1) |
| `code tokens differ in manifest/pgg_analysis_manifest.v` | M9, the renamed bound variable (fix pass 1) |
| `NOUN SWAP pgg_tableau.v: program -> path` | M8 (fix pass 1) |
| `NOUN SWAP pgl27_tableau_analysis_bridged.v: path -> program` | G3 (fix pass 1) |
| `NOUN SWAP psl211_tableau_analysis_bridged.v: path -> program` | P1 (fix pass 1) |
| `NOUN SWAP pgl27_tableau_analysis_bridged.v: programs: -> program:` | S11, the header line at `:56` (was a swap for G1 after fix pass 1) |
| `NOUN SWAP pgl27_tableau_analysis_bridged.v: programs -> program` | S11, the banner at `:353` (was a swap for G1 after fix pass 1) |

### Regions: 109 = 55 from the earlier passes + 54 from this one

The table in `prose_fix_pass.md` sums to 51. Four regions of the earlier work
are not in that table and were present before this pass began, so the true
baseline is 55:

- `pgl27_tableau_analysis_bridged.v`, 2 regions, the K4/R1 twin sentence in the
  header at `:49-51` (the table counts the `:927-929` copy only);
- `five_card_tableau_analysis_bridged.v`, 1 region, R2, "publishes the
  manifest's biased path" at the proximity twin;
- `s5_tableau_sampled.v`, 1 region, R3, "What the manifest names for that path".

The 54 new regions, per file:

| file | new regions | id |
|---|---|---|
| `pgl27_profile_privacy.v` | 22 (0 -> 22) | T1, one per site |
| `five_card_tableau_analysis_bridged.v` | 21 (8 -> 29) | T6 18, T4 2 (docstring and index), T9 1 |
| `five_card_mixing.v` | 2 (1 -> 3) | T5 |
| `five_card_tableau_sampled.v` | 3 (2 -> 5) | T8 |
| `psl211_word_proximity.v` | 2 (0 -> 2) | S5 |
| `pgl27_spectral.v` | 1 (0 -> 1) | T7, pgl27 half |
| `s5_mixing.v` | 1 (0 -> 1) | T7, S_5 half |
| `pgg_tableau.v` | 1 (4 -> 5) | S2 |
| `pgg_analysis_manifest.v` | 1 (8 -> 9) | S8 splits M2's three regions into four |

Four of this pass's rulings produce no new region, because the checker sees them
as a legal noun swap or as a re-flow only:

- **T2** turns "publishes a program whose" back into "publishes a path whose",
  and the base word was "row", so it counts as one more `path` swap;
- **T3** turns "two published programs" into "two published paths", likewise;
- **S1** turns "the program's ap_observed" into "the path's ap_observed",
  likewise;
- **S4**, **S3** and **S11** re-use a region that fix pass 1 already opened at
  the same words, so the region count does not move;
- **S12** changes no word at all, only line breaks.

`left as row` is 0 or a sense-4 count everywhere; nothing in senses 1 to 3 is
left.

---

## Rulings not applied, and why

- **T6, two sites.** The defining docstrings at `five_card_tableau_analysis_bridged.v:643`
  and the first sentence at `:665` keep "Kim's repeated program" and "Kim's
  one-cut program". Both sentences introduce the value they sit on and continue
  "certified by the input-indistinguishability arm" / "certified by the same
  arm", so the full name would make each read "certified program certified by
  the arm". The audit's T6 finding states the same carve-out. Everything else
  that names either value was changed.
- **T6, residual for the owner.** `five_card_tableau_analysis_bridged.v:758`
  ("the constant the repeated program publishes", inside
  `Fact five_card_pow2_39_split`) and `:855` ("The repeated program concluded at
  2^-39 and the program at the bundle's ...") both sit in sentences that name
  the terminal's constant, so they stay bare by the rule, and they stand three
  lines from `:771`, which now reads "The repeated certified program's published
  bound". The two readings are correct but a reader meets both words close
  together.
- **T1, two sites.** Listed above under T1: the index entries for
  `pgl27_dealerP` and `pgl27_alldecks_dealerP` read "the exact analysis in the
  dealer sample space" and "the all-decks analysis in that sample space". The
  noun was applied as instructed; the sentences stay loose in the way the base
  text was loose.
- Nothing else was withheld. T2, T3, T4, T5, T7, T8, T9, S1, S2, S3, S4, S5, S8,
  S11 and S12 are applied in full.
