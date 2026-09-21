# Probe ledger: manifest paths for the two programs over the PSL(2,11) dealer-dealt model

Spec: `notes/20260921-manifest-paths-dealer-dealt-model-probe-design.md`.
Probe tree: `notes/probes/2026-09-21-dealt-manifest-paths/`, staged copies under
`staged/`, load path in `_CoqProject` (the two staged roots last, so a staged
copy shadows the production module of the same name), one file at a time
through `python3 compile.py SECONDS MAXMB FILE`, which calls the session lock
`$SP/rocq1`.

Production is read-only. `instances/psl211/psl211_endpoints.v` was never
compiled and no file of the frozen closure was staged.

Every row is GO. The staged chain compiles in dependency order, the fidelity
file passes all 35 statement checks and both path equations, and the reverse
closure of the landing meets no frozen file.

## 1. Row verdicts

| id | verdict | file that shows it |
|---|---|---|
| M1 the adapter, its four law lemmas and the family need nothing above the manifest | GO | `staged/instances/psl211/psl211_dealt_model.v`, rc 0, 14.9 s; its Requires stop at `pgg_analysis_status` and the instance cone |
| M2 raw theorem (a) provable below the manifest | GO | `psl211_dealt_colour_indep`, `Qed`, same file |
| M3 raw inequality (b) likewise | GO | `psl211_dealt_perdeck_reading_ge`, `Qed`, same file, term-mode `etrans` steps kept |
| M4 `AnalysisModelFamily psl211_dealt_observed` typechecks below the manifest; the link lemma stays provable at the Tableau level | GO | `psl211_dealt_family` in the new file; `psl211_dealt_sampled_viewE` unchanged in `staged/instances/psl211/tableau/psl211_tableau_dealt.v`, rc 0, 4.3 s |
| M5 no Require cycle | GO | the eleven staged files compile in the order of `_CoqProject` |
| M6 the two published paths equal the two typed manifest paths | GO | `fidelity.v`, four `Timeout 300` `erefl` checks, all inside the file's 44.9 s |
| M7 every existing statement unchanged | GO | `fidelity.v`, 35 checks of the form `Timeout 300 Check (@name : <today's statement>)` |
| M8 reverse closure holds no frozen file | GO | `closure.py` prints `frozen files met: none`, touched 7, closure 34 |
| M9 capability vocabulary suffices | GO | Path 13 uses `exact privacy`, Path 14 `input distinguishability at 1/660`; no new label |

## 2. What moved, and from where

Nothing below was restated. Every lemma listed as verbatim was copied with its
statement, its proof script and its comment unchanged; the only edits are the
`seats`/`cards` notations of `psl211_colour_reading.v` rewritten as the
`seatT`/`cardT` of `psl211_reading_constancy.v`, which expand to the same
terms, and two comment sentences that named the file a lemma used to live in.

Destination for all of them: `instances/psl211/psl211_dealt_model.v` (new).

| lemma | current file | verbatim |
|---|---|---|
| `psl211_perdeck_coalition_le3` | `psl211_reading_constancy.v` | yes |
| `psl211_perdeck_coalition_below_k` | `psl211_reading_constancy.v` | yes |
| `psl211_dealt_inputTE` | `psl211_colour_reading.v` | yes |
| `psl211_dealt_sample` | `psl211_colour_reading.v` | yes |
| `psl211_dealt_sample_lawE` | `psl211_colour_reading.v` | yes |
| `psl211_dealt_sample_argE` | `psl211_colour_reading.v` | yes |
| `psl211_dealt_sample_cutE` | `psl211_colour_reading.v` | yes |
| `psl211_dealt_sample_cut_distE` | `psl211_colour_reading.v` | yes |
| `psl211_dealt_family` | `tableau/psl211_tableau_dealt.v` | yes |
| `psl211_dealt_decktbl` | `psl211_reading_constancy.v` | yes |
| `psl211_dealt_decktblE` | `psl211_reading_constancy.v` | yes |
| `psl211_dealt_decktbl_mod` | `psl211_reading_constancy.v` | yes |
| `psl211_dealt_view` | `psl211_reading_constancy.v` | yes |
| `psl211_dealt_test` | `psl211_reading_constancy.v` | yes |
| `psl211_dealt_testE` | `psl211_reading_constancy.v` | yes |
| `psl211_dealt_raw_count` | `psl211_reading_constancy.v` | yes |
| `psl211_dealt_raw_countE` | `psl211_reading_constancy.v` | yes |
| `psl211_dealt_static_obsE` | `psl211_reading_constancy.v` | yes |
| `psl211_dealt_raw_viewE` | `psl211_reading_constancy.v` | yes |
| `psl211_dealt_fiber` | `psl211_reading_constancy.v` | yes |
| `psl211_dealt_fiberE` | `psl211_reading_constancy.v` | yes |
| `Local Opaque psl211_dealt_raw_count` | `psl211_reading_constancy.v` | yes, and a second copy stays in `psl211_reading_constancy.v` |
| `psl211_dealt_massE` | `psl211_reading_constancy.v` | yes |
| `psl211_colour_of_reading` | `psl211_colour_reading.v` | yes, notation renamed |
| `psl211_colour_of_reading_obsE` | `psl211_colour_reading.v` | yes, notation renamed |
| `psl211_colour_of_reading_collides` | `psl211_colour_reading.v` | yes, notation renamed |

Two declarations of the new file are not moves.

- `psl211_dealt_colour_viewE` is `psl211_colour_reading_funE` with
  `psl211_colour_of_reading C` where `cr_read psl211_colour_reading C` stood,
  the two being one iota step apart. Its proof is the two lines of
  `psl211_colour_readingE` under the `funext` of `psl211_colour_reading_funE`.
- the two raw theorems, section 3 below.

Three results stay above the manifest because their statements name a record
of the Tableau, and the raw theorems avoid those records.

| result | the Tableau record it names | how the raw statement avoids it |
|---|---|---|
| `psl211_colour_reading_indep` | `ReadingExactIndependence`, `CoalitionReading` | the raw theorem writes the unfolded proposition and puts `psl211_colour_of_reading C` where the reading record's `cr_read` stands; one iota step apart, so the Tableau lemma is now `exact: psl211_dealt_colour_indep` |
| `psl211_dealt_input_distinguishable` | `InputDistinguishabilityPropAt`, `coalition_endpoint_reading` | the raw theorem is the inequality at the fixed coalition and the two fixed chiralities, with no existential and no reading; the Tableau lemma supplies the existential, discharges the threshold premise from `psl211_perdeck_coalition_below_k` and closes with the raw one |
| `psl211_dealt_constancy_false` | `coalition_reading_constancy` of `psl211_reading_constancy.v` | it is needed by neither raw theorem nor the manifest, so it stays where it is and takes the fibre counts from below |

`psl211_leak_coalition_not_below_k`, `psl211_colour_reading_dep_k6`,
`psl211_dealt_perdeck_reading`, `psl211_dealt_perdeck_readingE`,
`psl211_dealt_reading_indep_false` and
`psl211_colour_indistinguishability_of_coalition_reading` also stay in
`psl211_colour_reading.v`, unchanged. The first of those could move and was
left where it is to keep the move as small as the raw theorems require.

## 3. The two raw theorems, in full

```coq
Theorem psl211_dealt_colour_indep (R : realType) (secretP : R.-fdist bool) :
  forall C : {set seatT},
    (#|C| < profile_k (instance_profile psl211_algebra))%N ->
    sa_sampleP (psl211_dealt_sample secretP)
    |= (fun u => psl211_colour_of_reading C
                   (static_coalition_obs C
                      ((psl211_dealt_sample secretP).(sa_arg) u)
                      ((psl211_dealt_sample secretP).(sa_cut) u)))
       _|_ psl211_secret secretP.
```

```coq
Theorem psl211_dealt_perdeck_reading_ge (R : realType)
    (secretP : R.-fdist bool) :
  (#|pgg_G psl211_M|%:R)^-1 <=
  var_dist
    (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
         psl211_perdeck_coalition true)
       (sa_cut_dist (psl211_dealt_sample secretP)))
    (fdistmap (@static_coalition_obs psl211_algebra psl211_dealt_params
         psl211_perdeck_coalition false)
       (sa_cut_dist (psl211_dealt_sample secretP))).
```

The second is the dealer-dealt twin of `psl211_alldecks_perdeck_reading_ge` of
`instances/psl211/psl211_alldecks_input_distinguishability.v` and is written
in that lemma's shape, so a reader comparing the two dealers compares two
statements of one form.

## 4. Facade alias names

All inside `Module PSL211Analysis` of `instances/psl211/psl211_analysis.v`. An
unprefixed alias is the all-decks dealer, an alias beginning `dealt_` the
dealer-dealt one; the file header says so and no name is shared.

| alias | target | section |
|---|---|---|
| `dealt_exec_plug` | `instance_exec psl211_dealt_params` | 2 Execution |
| `dealt_observed` | `psl211_dealt_observed` | 3 Observers |
| `dealt_prior` | `@psl211P` | 3 Observers |
| `dealt_static_view` | `@static_coalition_obs psl211_algebra psl211_dealt_params` | 3 Observers |
| `dealt_colour_of_reading` | `@psl211_colour_of_reading` | 3 Observers |
| `dealt_secret` | `@psl211_secret` | 3 Observers |
| `dealt_sample` | `@psl211_dealt_sample` | 4 Models |
| `dealt_family` | `psl211_dealt_family` | 4 Models |
| `dealt_cut_distE` | `@psl211_dealt_sample_cut_distE` | 4 Models |
| `dealt_observed_recovers` | `OE.oe_run_recovers psl211_dealt_observed` | 5 Correctness |
| `dealt_colour_indep` | `@psl211_dealt_colour_indep` | 6 Security |
| `dealt_perdeck_reading_ge` | `@psl211_dealt_perdeck_reading_ge` | 6 Security |
| `dealt_colour_transfer_status` | `StaticExecutedOnly` | 7 Transfer |
| `dealt_obstruction_transfer_status` | `NegativeTransfer` | 7 Transfer |

`psl211_analysis.v` gains two Requires, `psl211_secrecy` and
`psl211_dealt_model`, in its imported instance cone, and `variation_dist` in
its exported type vocabulary, because `dealt_perdeck_reading_ge`'s spelled
type is written in `var_dist`.

The typed paths are `psl211_dealt_colour_path` and
`psl211_dealt_obstruction_path`, in `manifest/pgg_analysis_manifest.v` beside
the twelve.

## 5. Path 13 and Path 14, draft text

The text below is what `staged/manifest/pgg_analysis_manifest.v` carries,
between Path 12 and the table of aliases carrying no capability.

```
    Path 13: twelve-card chirality instance, dealer-dealt model, colour
    observer

| field | value |
|---|---|
| protocol family and model | PSL(2,11) twelve-card chirality deck; the
                              chirality drawn from a prior on it and the
                              cut drawn uniformly over the 660 elements of
                              the group, the two independent |
| profile alias      | PSL211Analysis.profile |
| execution alias    | PSL211Analysis.dealt_exec_plug |
| observed alias     | PSL211Analysis.dealt_observed |
| sample alias       | PSL211Analysis.dealt_sample; the path's typed model
                       witness is PSL211Analysis.dealt_family, the family
                       indexed by the prior on the chirality |
| observers          | PSL211Analysis.dealt_colour_of_reading
                         : {ffun 'I_12 -> bool}, the colour of the card
                           each seat of the coalition holds;
                       PSL211Analysis.dealt_static_view
                         : {ffun 'I_12 -> 'I_12}, the card identities the
                           colour map is read off |
| distribution-to-observer bridges | PSL211Analysis.dealt_cut_distE |
| bound or certificate | none: the theorem is an independence and carries
                         no number |
| final bridge theorem | PSL211Analysis.dealt_colour_indep |
| correctness theorem  | PSL211Analysis.dealt_observed_recovers |
| model transfer       | none claimed |
| missing premise      | none: the cut this model draws is the uniform law
                         on the group already, so no idealized model is
                         compared and there is no transfer premise to
                         lack |
| completion level     | AnalysisBridged |
| transfer status      | StaticExecutedOnly |
| assumption status    | BaselineClassicalOnly |
| typed path           | psl211_dealt_colour_path |

Capabilities, one line per (theorem, distribution, observer, notion):

| theorem | distribution | observer | notion |
|---|---|---|---|
| dealt_colour_indep | the cut law of dealt_sample, which dealt_cut_distE
  names as the uniform law on the 660 elements of the shuffle group
  | dealt_colour_of_reading at a coalition of at most five of the twelve
    seats | exact privacy |
| dealt_observed_recovers | none, the statement is distribution-free
  | the executed endpoint list | correctness |

Level justification. profile gives Algebraic; dealt_exec_plug is indexed
by profile, giving Executable; dealt_observed is the ObservedExecution
over that profile and plug, giving Observed; dealt_sample is a
SampleAdapter over that plug and dealt_cut_distE identifies its cut
distribution with the uniform law on the shuffle group, giving Sampled;
dealt_colour_indep is a privacy theorem stated at that cut distribution
and at the colour observer read off that model's own coalition reader,
giving AnalysisBridged. The transfer status is StaticExecutedOnly, the
path comparing no idealized model.

Under these parameters the run argument of the execution IS the chirality,
so the secret the independence is of is the run argument itself and not a
coordinate of a drawn deck description, which is what separates this path
from Path 9 over the same instance. The capability is exact privacy at the
colour observer and at no other: at the card-identity observer
dealt_static_view the same independence is false over this model, by
psl211_dealt_reading_indep_false of
instances/psl211/psl211_colour_reading.v, and that is the theorem Path 14
below records in its distributional form. The threshold the capability is
stated below is the largest one: at the six seats of the mirror
representative independence at the colour observer already fails, by
psl211_colour_reading_dep_k6 of the same file, and six is what the derived
profile declares. The program that publishes this path is
psl211_colour_exact_published of psl211_tableau_dealt.v in
instances/psl211/tableau/.

    Path 14: twelve-card chirality instance, dealer-dealt model, input
    distinguishability

| field | value |
|---|---|
| protocol family and model | PSL(2,11) twelve-card chirality deck; the
                              chirality drawn from a prior on it and the
                              cut drawn uniformly over the 660 elements of
                              the group, the two independent |
| profile alias      | PSL211Analysis.profile |
| execution alias    | PSL211Analysis.dealt_exec_plug |
| observed alias     | PSL211Analysis.dealt_observed |
| sample alias       | PSL211Analysis.dealt_sample; the path's typed model
                       witness is PSL211Analysis.dealt_family |
| observers          | PSL211Analysis.dealt_static_view
                         : {ffun 'I_12 -> 'I_12}, the reading of the deck
                           the dealer laid, which static_coalition_obs of
                           protocol/pgg_instance.v is at this model |
| distribution-to-observer bridges | PSL211Analysis.dealt_cut_distE |
| bound or certificate | none: the program over this path publishes an
                         obstruction, which carries neither a witness nor
                         a certificate |
| final bridge theorem | PSL211Analysis.dealt_perdeck_reading_ge |
| correctness theorem  | PSL211Analysis.dealt_observed_recovers |
| model transfer       | none claimed |
| missing premise      | none: the path's theorem is a limitation. No
                         input-indistinguishability proposition holds at
                         this model at this observer at a number below
                         1/660, in the sum of absolute differences, and
                         the advantage of a distinguisher comparing the
                         two run arguments that theorem names is at least
                         1/1320. The path compares no idealized model, so
                         there is no transfer premise to lack |
| completion level     | AnalysisBridged |
| transfer status      | NegativeTransfer |
| assumption status    | BaselineClassicalOnly |
| typed path           | psl211_dealt_obstruction_path |

Capabilities, one line per (theorem, distribution, observer, notion):

| theorem | distribution | observer | notion |
|---|---|---|---|
| dealt_perdeck_reading_ge | the cut law of dealt_sample, which
  dealt_cut_distE names as the uniform law on the 660 elements of the
  shuffle group
  | dealt_static_view at psl211_perdeck_coalition, three of the twelve
    seats | input distinguishability at 1/660 |
| dealt_observed_recovers | none, the statement is distribution-free
  | the executed endpoint list | correctness |

Level justification. The first four levels are Path 13's, the two paths
naming one execution, one observed execution and one model family.
dealt_perdeck_reading_ge is a limitation theorem stated at that cut
distribution and at the coalition's own reading of the laid deck, and
AnalysisBridged admits a limitation theorem about the same distribution
and the same observer, giving AnalysisBridged. The transfer status is
NegativeTransfer, which is defined as a theorem transporting an
obstruction to the path's observer, and the theorem is that one. Path 13
records the same instance, the same execution and the same model, and this
path differs from it in the observer and in the transfer status: the two
describe different theorems about one model, Path 13 the exact
independence the colours of a coalition of at most five of the twelve
seats have of the chirality, and this path the distance between the
readings of the two chiralities at three seats' card identities. Because
the run argument is the chirality here, the two run arguments this path's
theorem compares are the two values of the secret, so the limitation is
about this model's privacy and not only about two inputs; at Path 12,
whose run argument is a deck description, the same shape of theorem says
nothing about a secret. The program that publishes this path is
psl211_dealt_obstruction_published of psl211_tableau_dealt.v in
instances/psl211/tableau/, which certifies no security property.

```

## 6. The staged set, and the landing's recompile closure

Eleven files plus the fidelity file. Everything above the staged manifest that
the chain needs is staged, because a production `.vo` compiled against the
production manifest is inconsistent with the staged one; nothing else is.

| # | staged file | changed? |
|---|---|---|
| 1 | `staged/instances/psl211/psl211_dealt_model.v` | new |
| 2 | `staged/instances/psl211/psl211_analysis.v` | yes, the fourteen aliases |
| 3 | `staged/manifest/pgg_analysis_manifest.v` | yes, two path tables, two typed paths, the checks, the counts |
| 4 | `staged/manifest/pgg_tableau.v` | no, recompiled against the staged manifest |
| 5 | `staged/manifest/pgg_tableau_syntax.v` | no, recompiled |
| 6 | `staged/manifest/pgg_tableau_reading.v` | no, recompiled |
| 7 | `staged/instances/psl211/psl211_reading_constancy.v` | yes, the moved block removed |
| 8 | `staged/instances/psl211/psl211_colour_reading.v` | yes, the moved block removed, three proofs now cite the raw results |
| 9 | `staged/instances/psl211/tableau/psl211_tableau_dealt.v` | yes, the family removed, one proof and two path equations restated |
| 10 | `staged/manifest/pgg_analysis_client.v` | yes, ten Checks and the count |
| 11 | `fidelity.v` | new, the probe's own |

The landing's reverse closure, from `closure.py` over the seven production
files the landing changes, is 34 tracked files plus the new one, and it prints
`frozen files met: none`. `pgg_tableau_marginal_bounds.v` and
`psl211_word_proximity.v` are outside it.

## 7. Timings

No file is over 120 s.

| file | seconds |
|---|---|
| `psl211_dealt_model.v` | 14.9 |
| `psl211_analysis.v` | 3.7 |
| `pgg_analysis_manifest.v` | 6.0 |
| `pgg_tableau.v` | 13.2 |
| `pgg_tableau_syntax.v` | 4.4 |
| `pgg_tableau_reading.v` | 3.7 |
| `psl211_reading_constancy.v` | 15.9 |
| `psl211_colour_reading.v` | 16.1 |
| `psl211_tableau_dealt.v` | 4.3 |
| `pgg_analysis_client.v` | 3.8 |
| `fidelity.v` | 44.9 |

## 8. Axioms

`Print Assumptions` on `psl211_dealt_colour_indep`,
`psl211_dealt_perdeck_reading_ge`, `psl211_colour_exact_published` and
`psl211_dealt_obstruction_published`, in `logs/fidelity.log`: each prints the
same three and nothing else.

```
propositional_extensionality
functional_extensionality_dep
constructive_indefinite_description
```

No `Admitted`, no `Axiom`, no `Abort` in any staged file.

## 9. Departures from the spec

1. The spec's 2.4 asks the two `_pathE` lemmas to equate the published path
   with the manifest's typed path, and M7 asks every existing statement to be
   unchanged. The two cannot both hold for those two lemmas, whose right-hand
   sides are today the `@MkAnalysisPath ...` term spelled out. The `_pathE`
   statements were changed, as 2.4 directs, and `fidelity.v` carries two
   further `erefl` checks showing the old right-hand side still holds, so the
   change is a change of spelling alone.
2. `Local Opaque psl211_dealt_raw_count` is left standing in
   `psl211_reading_constancy.v` as well as in the new file. The seal is per
   file, and `psl211_dealt_constancy_false` stays in the constancy file over a
   count whose body is now in another one.
3. The spec's 2.1 names `psl211_colour_of_reading` as the colour map to move
   "if the raw theorem needs it". It does, so it moved, together with
   `psl211_colour_of_reading_obsE` and `psl211_colour_of_reading_collides`,
   which are statements about that map alone.
4. `psl211_analysis.v` gains `variation_dist` in its exported vocabulary. The
   facade contract exports the type vocabulary an alias type is written in,
   and `var_dist` is now one of those types.
5. The file name is `psl211_dealt_model.v`, the spec's provisional one. It
   sits beside `psl211_word_model.v`, which is the same kind of file for the
   584-letter word model of the same instance, so the convention holds.

## 10. What is worth landing

All of it. The two theorems the manifest wants are provable below it with
their existing proofs, the move is 26 declarations and no restatement, the
chain has no cycle, both programs' paths are decided by conversion against the
manifest's typed paths, and the closure holds no frozen file. The dependency
the landing adds is one new file below the manifest; nothing above the
manifest gains a Require.
