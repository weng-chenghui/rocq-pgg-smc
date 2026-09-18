# What a third `certify` arm for Kim's biased row would take

Date: 2026-09-19. Status: not built. This note records the change list so the
decision can be made later with the facts in hand. It follows
[[20260919-kim-tableau-sampled-design]] and
[[20260919-dealer-law-and-kim-rows-summary]]. The file and line references
below were read on 2026-09-19. The Rocq fragments were not compiled.

## Problem

The manifest places `five_card_row_biased` at `AnalysisBridged`. Its Tableau
program, `five_card_row_biased_tableau`, stops one level lower, at `Sampled`.
The reason is that `certify` has two arms and the row's theorem fits neither.
`five_card_colour_view_leak_bound` bounds a conditional mutual information.
`ExactIndependence` asks for exact independence of a coalition's observation
from a secret. `SpectralDecay` asks for a variation distance certificate.

Today the file says this honestly. A recorded `Fail` rejects the biased program
at the manifest's level, `five_card_row_biased_levelE` states the manifest's
level, and the header explains that `AnalysisBridged` is one constructor with
two admission criteria.

The question here is what it would cost to close the gap instead, by giving
`certify` a third arm whose currency is a leakage bound. The cost has two
parts. The engineering part is small and is listed below. The semantic part is
larger, and it is why the arm was not added.

## The check for work on the DSL layer itself

- `Operation:` add one constructor to the sum type `SecurityPort` and one
  branch to every `match` on it. The invariant is that a program reaching
  `AnalysisBridged` proves exactly its own arm's proposition.
- `Monad:` unchanged. The Tableau stays a parameterised monad indexed by
  completion level before and after a statement. The new piece is one more
  `certify_*` step from `Sampled` to `AnalysisBridged`, and the laws of
  `tableau_bind` are not touched.
- `DSL:` yes. The Tableau cannot state a bound measured in conditional mutual
  information, and a third arm removes exactly that gap. Its price is semantic
  and is the last section of this note.

## 1. `manifest/pgg_tableau.v`, seven places

`SecurityPort` has two constructors (line 149). Three definitions match on it.
Each arm also has its own payload, proposition and `certify_*` step.

**(a) A new payload record**, after `SpectralCert` (line 131).

```coq
Record LeakCert (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) :=
  MkLeakCert {
    lc_inputT : finType ;
    lc_inputs : {RV (sa_sampleP sa) -> lc_inputT} ;
    lc_outT   : finType ;
    lc_out    : {RV (sa_sampleP sa) -> lc_outT} ;
    lc_eps    : R ;
    lc_bound  : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
      cond_mutual_info
        (`p_ [% lc_inputs,
                (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u)),
                lc_out])
      <= lc_eps }.
```

`lc_bound` has no threshold guard `#|C| < profile_k`. Kim's bound holds at every
reveal, the full one included. This is where its quantifier differs from the
other two arms.

**(b) The third constructor** (lines 149 to 152).

```coq
  | ExactIndependence of ExactWitness sa
  | SpectralDecay of SpectralCert sa
  | LeakageCeiling of LeakCert sa.
```

**(c) A new proposition `LeakPropAt`**, on the model of `SpectralPropAt` (line
331). It states `lc_bound` with the static observation replaced by the executed
`sa_coalition_view`, along the link lemma. The bound is a parameter `c`, so that
a row can be repriced.

**(d) A third branch of `PortProp`** (lines 363 to 369).

```coq
  | LeakageCeiling cert => LeakPropAt cert (odflt (lc_eps cert) (c R))
```

**(e) A third branch in `RepricePayload` and in `port_reprice`** (lines 610 to
630), and one more case in the proof of `port_reprice`.

```coq
    | LeakageCeiling cert => lc_eps cert = odflt (lc_eps cert) (c R)
```

**(f) `LeakPayload`, a tail lemma and `certify_leak`**, on the model of the
exact and spectral pairs at lines 515 to 601. The step has the shape of
`certify_exact`, and its last layer is
`fun R idx => LeakageCeiling (p R idx)`. The tail lemma uses `proj2 q R idx`,
the `Sampled` level's identification of the executed view with the static one.

**(g) A projection name and the header.** `view_secrecy_of` and
`view_indist_of` (lines 713 and 720) are the same `proj2` under two names. A
third name, `view_leak_of`, goes beside them. The Definitions table of the file
header and the sentence at line 22 are updated.

## 2. `manifest/pgg_tableau_syntax.v`, one or two notations

```coq
Notation "s 'certify' 'LeakageCeiling' c" := (s ;;; certify_leak of c)
  (at level 90, left associativity, c at level 0).
```

The header of that file (lines 60 to 71) records which identifiers the surface
spends as global keywords. It says that `ExactIndependence` and `SpectralDecay`
follow a literal and so stay identifiers. `LeakageCeiling` follows `certify`
and should behave the same way. That was measured on 2026-09-14 and not
inferred, so it has to be measured again: `Check LeakageCeiling.` must still
pass, and the result goes into that header paragraph.

## 3. `instances/kim2025/five_card_rows.v`, where the real work is

The program gains two lines.

```coq
Definition five_card_row_biased_tableau : PublishedRow :=
  five_card_committed
    sample  kim_biased_family
    certify LeakageCeiling five_card_biased_leak_cert
    |> publish StaticExecutedOnly BaselineClassicalOnly.
```

It also needs `five_card_row_biased_rowE`, by conversion, linking the published
row to the manifest's `five_card_row_biased`. The manifest already records that
row as `AnalysisBridged`, `StaticExecutedOnly`, `BaselineClassicalOnly`, so
conversion is expected to decide it.

Three things that landed on 2026-09-19 are removed or rewritten: the recorded
`Fail` `five_card_row_biased_at_manifest_level`, the lemma
`five_card_row_biased_levelE`, and the header passage on the two admission
criteria.

**`five_card_biased_leak_cert` needs a lemma the tree does not have.**

- The landed bound `five_card_row_biased_leak_bound` observes
  `five_card_exec_colour_view A`. For a list of card positions `A : seq nat` it
  decodes the executed endpoint at each position into a colour
  (`five_card_models.v:284`).
- The new arm observes the framework's `static_coalition_obs C`, indexed by a
  set of seats `C`, with values in `{ffun 'I_5 -> 'I_5}`.
- The existing bridge is `five_card_static_obsE` (`five_card_rows.v:234`):
  `static_coalition_obs C ... = five_card_colour_fill C (ViewS R C u)`. It
  reaches `ViewS`, the colour reading indexed by a set. The leak bound lives on
  `ViewA`, the reading indexed by a list, through `five_card_colour_viewE`.
- So two facts are missing. One relates `ViewS R C` to `ViewA R` at the list
  that enumerates `C`. The other says that a conditional mutual information
  does not grow when the observer is passed through the injective map
  `five_card_colour_fill C`. The second is a case of data processing.
  `view_mutual_info_le` in `reconstruct/transitivity_privacy.v` is of the same
  kind, and whether it applies directly has to be probed.
- This is the only uncertain part of the whole change. The estimate is one or
  two lemmas of moderate size. No probe was run, so no line count is given.

## 4. What recompiles

`pgg_tableau.v` has five importers: `pgg_tableau_syntax`, `s5_rows`,
`pgl27_rows`, `psl211_rows` and `five_card_rows`. None of the rows files
matches on the arm directly. They use the arms only through the `certify`
notations and through the projections such as `view_secrecy_of`. A new
constructor therefore gives them no non-exhaustive match.

The six files take about 40 s in total, by the times measured on 2026-09-19.
`psl211_endpoints` is not affected. `manifest/pgg_analysis_manifest.v` needs no
edit.

## 5. The real cost is semantic

The header of `five_card_rows.v` now carries a compiled and audited sentence: a
program reaches `AnalysisBridged` only through one of two arms, so the
Tableau's criterion is stricter than the manifest's. That sentence is true
because both arms are statements about what a coalition below the threshold
sees.

A third arm has three consequences.

- **That sentence stops being true.** A published row no longer means "there is
  a coalition privacy theorem". It means "there is a quantitative theorem about
  the sampled distribution and the observer", which is the manifest's
  criterion. The two criteria become one.
- **The paper's table needs a column for the arm**, so that a reader can tell
  exact rows from spectral rows from leakage ceilings. Without it Kim's biased
  row looks as finished as the PGL(2,7) row.
- **The same argument then applies to the repeated row.** Once a leakage arm is
  accepted, it is hard to say why the $2^{-40}$ endpoint bound should not get an
  `EndpointMarginal` arm, which is the option the design of 2026-09-18 rejected
  first. The difference between the two is one of degree. The leak bound is at
  least about an observer and a secret. The endpoint bound mentions no secret.

## Recommendation

Keep the present state. The gap is a compiled `Fail` beside a lemma, and the
header gives the reason. The paper can present exactly that structure: one
prefix, three continuations, two of which stop at `Sampled`, each with one
bound stated beside its program on the law the program samples.

If the arm is wanted, it is a third batch, and its first step is a probe of the
missing lemma of section 3. That lemma decides whether the batch is a day of
work or more.
