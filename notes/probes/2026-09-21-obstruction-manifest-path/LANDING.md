# Landing, 2026-09-21: a published obstruction's number is positive, and the
# manifest records the obstruction as its twelfth path

Branch `feat/tableau-extensions-probe`, base `6cd54f9`. Two owner-approved
changes landed as one.

## Change A: the proposition a kind stands for requires the number positive

`ObstructionProp` in `manifest/pgg_tableau.v` becomes

```
| InputDistinguishabilityObstruction c =>
    0 < c /\ InputDistinguishabilityPropAt sa c
```

`InputDistinguishabilityPropAt` and the three lemmas about it are untouched,
so the downward-closed family a number bound is read against keeps its old
statement, and only what a published member asserts changes.

Carried through:

- `ObstructionPayloadProp`, `mk_obstruction`, `obstruction_of`,
  `publish_obstruction` and the six path equations typecheck unchanged: all
  are parametric in the payload's proposition.
- At PSL(2,11), `psl211_alldecks_obstruction_pf` now proves the pair.
- `psl211_alldecks_published_input_distinguishability` projects the second
  conjunct.
- No reader-level lemma was added for the first conjunct: no statement in the
  tree needs it.

## Change B: Path 12

`psl211_perdeck_static_mass_true`, `psl211_perdeck_static_mass_false` and
`psl211_alldecks_perdeck_reading_ge` moved from
`instances/psl211/psl211_reading_constancy.v` to the new
`instances/psl211/psl211_alldecks_input_distinguishability.v`, statements and
term-mode proofs verbatim, with their comments. The new file requires nothing
above `psl211_models.v`: `probe_cycle.v` in this directory states them against
production's load path with no Tableau, no `pgg_analysis_manifest` and no
`pgg_analysis_status`, and compiles in 3.9 s with the three classical axioms
only.

## Decisions taken here

**The facade alias is `PSL211Analysis.perdeck_reading_ge`, not
`alldecks_reading_ge`.** The brief proposed the latter "unless the module's
conventions say otherwise". They do: the facade's own header states that it is
about the all-decks dealer, and every existing alias drops both `psl211_` and
`alldecks_` (`psl211_alldecks_observed` is `observed`,
`psl211_alldecks_sample` is `exact_sample`, `psl211_alldecks_cut_distE` is
`cut_distE`, `psl211_alldecks_static_indep` is `static_indep`). What a prefix
is kept for is the model (`exact_`, `word_`). `perdeck_` names the comparison
between the two chiralities at one deal, which is what the statement is about,
so it is the fragment the convention keeps.

**A file may be named after a constant that a file requiring it declares.**
The new file is `psl211_alldecks_input_distinguishability.v` and the theorem
`psl211_alldecks_input_distinguishability` stays in
`psl211_reading_constancy.v`, which requires that file. `probe_name_clash.v`,
`probe_name_clash_decl.v` and `probe_name_clash_use.v` reproduce the shape:
the constant resolves, and `Locate` prints `Constant …` and `Module …` on two
lines. No warning, no ambiguity.

**`psl211_alldecks_obstruction_published_path_observedE` and
`…_path_transfer_neq` are removed.** Nothing outside `notes/` cited them
(grep over tracked `.v` files). What they said is now said by the manifest's
own pins: `ap_model psl211_alldecks_obstruction_path : AnalysisModelFamily
PSL211Analysis.observed` fixes the observed execution against
`psl211_alldecks_path`'s identical pin, and the two `ap_transfer` `erefl` pins
give `NegativeTransfer` against `StaticExecutedOnly`. A comparison between two
manifest paths belongs to the manifest, not to a statement about one program.

**One declaration was added beyond the brief:
`psl211_alldecks_obstruction_gt0`.** The brief asks
`psl211_alldecks_obstruction_pf` to prove the pair, "positivity of 1/660 by a
one-line field argument", and that argument needs a home. The payload stays a
`Definition` with a transparent term body, as `psl211_exact_witness` and
`psl211_word_proximity_cert` are, so every path and kind equation over the
program stays decided by conversion; the positivity is the named lemma beside
it. Its index entry is in the file's `Key results`.

**Two manifest sentences were widened beyond the letter of the brief.** Duty
(3)'s closed vocabulary gains `input distinguishability` as asked, with a
sentence saying what the label means. The `Absent capabilities` paragraph
said "every path whose transfer status is NoModelComparison or
StaticExecutedOnly states in its missing-premise cell either the premise it
lacks or why none is absent"; `NegativeTransfer` is added to that list, and a
clause saying no limitation is recorded as a privacy or security capability,
so the manifest's own stated duties stay true of the new path.

**One more file than the brief named was edited:
`instances/psl211/tableau/psl211_tableau_executable.v`.** Its header said
"Both paths the manifest carries for this instance, psl211_alldecks_path and
psl211_word_path, are over this one run". The manifest carries three for this
instance after the landing, so the sentence was false and now names all three
and says where each pair parts.

**`pgg_analysis_client.v` is in scope.** It says "the eleven typed paths"
twice and lists the eleven `Check`s. Both counts become twelve and
`psl211_alldecks_obstruction_path` is added to the list, so the file's stated
contract stays true.

## Not done

Nothing in the brief was left undone. No frozen file was met: `closure.py`
printed a 34-file order and stopped at none.

## Where the hand-back text is

The brief asked for `REPORT.md` in this directory. The harness this agent ran
under refuses to write a file whose purpose is a report, so the full hand-back
text, with every changed file, every declaration, the closure log, the
fidelity result and the axioms, went to the calling session instead. This note
holds the decisions and the departures.
