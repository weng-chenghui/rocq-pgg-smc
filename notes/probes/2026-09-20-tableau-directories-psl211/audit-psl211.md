# Adversarial audit of the PSL(2,11) tableau-directory instance

Read-only. Nothing outside this file was written, nothing was compiled, `make`
was never run. Audited against the pattern as ruled at S5: `TEMPLATE.md` with
its addendum, `audit-s5-pilot.md` (findings F1 to F24, the Placement section
and the nine pattern rulings), and `instances/s5/tableau/` as the worked
example.

Frozen export audited:
`/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc/493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad/dirs_psl_frozen/notes/probes/2026-09-20-tableau-directories-psl211/`.
Line numbers below are the staged files' own.

## VERDICT: NO-GO as it stands, GO after F1, F2, F3 and F4

Four sentences of the new text are false or claim more than the object they
speak of. Each is in a file header or a new docstring, each is one or two
sentences to fix, and none of them touches a statement, a proof, a name or
the load path. Everything structural is right: placement is correct
declaration by declaration, the cut of `psl211_word_proximity.v` follows the
addendum's rule exactly, the import chain is acyclic with no `Require Export`,
the six module names do not collide, `RETIRED.md` and the three
`staged-comments/` repoints are correct, the scope-block change is genuinely
pinned, and `fidelity.v` ascribes all 24 production declarations and all 8 new
ones.

The four blocking items, all in text that lands in production:

- **F1** the Algebraic docstring asserts a continuation that does not exist
  and then denies it in the same sentence.
- **F2** the Executable header says the dealer-dealt record carries one
  statement when `psl211_exec.v` states two more at it and
  `psl211_reading_constancy.v` eight more.
- **F3** the Executable docstring says the run *recovers* a value, at a level
  whose proposition is `True`; the S5 audit's F4 and F6 and the template both
  say "meant to recover" below Observed, and the S5 worked example writes it.
- **F4** the checks header makes one premise carry two rejections with
  different causes and reads the second for more than the term it refuses.

F17 and F18 are in `STATUS.md`, the probe record, and do not block the `cp`.
F17 is a declaration count the file's own pasted script output contradicts,
and F18 credits the scope pin to the wrong file. Both should be fixed before
the record is read by whoever does PGL(2,7), because both are the kind of
claim a later reader will take on trust rather than re-derive.

## Findings

| id | class | file:line | quoted text or object | problem with evidence | replacement or recommendation |
|---|---|---|---|---|---|
| F1 | MUST | `psl211_tableau_algebraic.v:46-49` | "The all-decks run of every published row of this instance continues from this one value, and so do the dealer-dealt parameters of psl211_exec.v, which no program of this development continues." | `psl211_dealt_params := dealt_secret_params psl211_algebra psl211_fuel` (`psl211_exec.v:112-113`) is built from the algebra, not from the program value `psl211_algebraic_start`; no `tableau_bind` reaches it. The clause asserts a continuation and then denies one exists. The first half is also loose: both published rows are written `psl211_algebra supplied … execute …` through the keyword surface (`psl211_tableau_observed.v:74-82`) and reach `psl211_algebraic_start` only through `psl211_alldecks_executableE`. | "The twelve-card chirality instance at the Algebraic level: the algebra alone, under True, the proposition that level carries. One run mode is built on this value, the all-decks one, and `psl211_alldecks_executableE` is where the prefix both published rows continue from is identified with it. The dealer-dealt parameters of `psl211_exec.v` are built from the same algebra and from no program. What separates the run modes is the level above and not this one." |
| F2 | MUST | `psl211_tableau_executable.v:26-30` | "No program of this development continues from it and the manifest carries no row over it; what is stated at it is the refutation psl211_dealt_constancy_false of psl211_reading_constancy.v." | The last clause is a false universal. `psl211_exec.v` states two more at that record three lines below it: `psl211_dealt_recon : instance_recon_stmt psl211_dealt_params` (`:117`) and `psl211_dealt_terminates : instance_terminates_stmt psl211_dealt_params` (`:123`). `psl211_reading_constancy.v` states eight more at it (`psl211_dealt_static_obsE:885`, `psl211_dealt_raw_viewE:897`, `psl211_dealt_fiber:914`, `psl211_dealt_fiberE:920`, `psl211_dealt_massE:948`, and the three around them). The other two clauses are TRUE: no `Tableau` value names the record (whole-tree scan of `psl211_dealt`), and both manifest rows are over `PSL211Analysis.observed`, which is `psl211_alldecks_observed` (`psl211_analysis.v:117`). S5 ruling F5: name the class, do not write "nothing else". | "…psl211_exec.v carries a second parameter record, psl211_dealt_params, in the dealer-dealt mode, where the run argument is the secret itself. It carries that record's own reconstruction and termination facts. No program of this development continues from it and the manifest carries no row over it, and the only security statement made at it is the refutation psl211_dealt_constancy_false of psl211_reading_constancy.v. It is named here and not built into a value." |
| F3 | MUST | `psl211_tableau_executable.v:66-76` | "the value the run recovers is the chirality bit of its argument" and, three lines on, "the value recovered is a reading of the run's own argument" | At Executable `StackProp Executable = fun _ => True` (`manifest/pgg_tableau.v:557`); the reconstruction fact is the third conjunct of `oe_correct_prop` and arrives at Observed (`:380-400`). `ex_expected` is the value a run is *meant* to recover. S5 audit F4 and F6, and the template's "Must never say: what a lower level proves". The S5 worked example writes it correctly in the same slot: "the value the run **is meant to recover** is the tape's secret coordinate" (`s5_tableau_executable.v:84-85`). The file header itself gets it right at `:7`, so the docstring contradicts its own header. | "the value the run is meant to recover is the chirality bit of its argument"; and "…so the run carries no commit process, and the value it names is a reading of the run's own argument rather than an ideal function of anyone's input." |
| F4 | MUST | `psl211_tableau_checks.v:18-23` | "The third is which ideal the proximity arm admits: a certificate's ideal is a sample adapter over the row's own execution, so the eight-card orbit instance's model is refused at its type, and the word model itself is refused as its own ideal, a certificate naming its own model holding its distance field at zero." | One premise is made to carry two rejections with different causes, and the second is read for more than its term shows. The first `Fail` (`:102-111`) is a type refusal and does follow from the premise: `SampleAdapter R (OE.oe_execution pgl27_exec.pgl27_observed)` against `SampleAdapter R (instance_exec psl211_alldecks_params)`. The second (`:126-129`) is a conversion failure on an equation about the certificate this development already has, `ipc_ideal (psl211_word_proximity_cert R idx) = amf_sample psl211_word_family R idx`. The word model IS a sample adapter over the row's own execution, so the premise does not refuse it; what the term shows is that this certificate's ideal is the exact family and not the word family. Checklist: a recorded `Fail` said to show more than the rejection of one written term. | "The third is which ideal the proximity arm admits. A certificate's ideal is a sample adapter over the row's own execution, so the eight-card orbit instance's model is refused at its type and no distance is reached. Beside it, the ideal of the certificate this instance builds is refused as the word model the certificate is about; a certificate whose ideal were its own model would hold its distance field at zero, the two sides of that field being one term." |
| F5 | SHOULD | `psl211_tableau_sampled.v:8-10` | "the reader built from the interpreter's own endpoints is the one computed directly from the layout and the cut" | `sampled_viewE_prop` (`manifest/pgg_tableau.v:410-420`) equates `sa_coalition_view … 0 C` with `fun u => static_coalition_obs C (sa_arg u) (sa_cut u)`, and `static_coalition_obs` (`protocol/pgg_instance.v:481-490`) takes the run argument `x : ex_inputT E` and the shuffle `g`. The layout is a field of the parameter record, fixed inside `ex_content_obs`, not an argument. Naming the layout where the run argument belongs mis-states which coordinate of a sample point the reading is a function of, and that is the fact the whole distance argument turns on (`psl211_word_proximity_close`'s proof note: "the two adapters reading a sample point by the same two projections"). | "…the reader built from the interpreter's own endpoints is the one computed directly from the run argument and the cut." |
| F6 | SHOULD | `psl211_tableau_sampled.v:17-19` | "A distance between the two laws is therefore a distance between two members of this level, which is the shape the proximity arm compares" | Type-honest phrasing. A member of this level is a `StackAt Sampled`, an algebra with its parameters, three run facts and a model family (`manifest/pgg_tableau.v:284-291`). A distance is between the two models' joint laws, `var_dist (psl211_wordP R) (psl211_alldecksP R)`. The two are not the same kind of object. | "A distance between the two laws is therefore a distance between the models that two values of this level carry, which is the shape the proximity arm compares." |
| F7 | SHOULD | `psl211_tableau_analysis_bridged.v:16-17` | "Six is the privacy threshold the derived profile declares, so every statement here is about a coalition of at most five of the twelve seats" | False of most of the file. Only two of its seventeen declarations quantify over a coalition in their statement, `psl211_alldecks_view_secrecy` at `#\|C\| < 6` and `psl211_word_view_proximity` at `#\|C\| <= 5`. Two more mention one only inside a body, `psl211_exact_witness` and `psl211_word_proximity_cert`. The remaining thirteen name no coalition anywhere: the two published rows and `psl211_row_alldecks_rowE`, `_armE`, `_sampledE`, `psl211_word_proximity_cert_idealE`, `_secretE`, `_secretTE`, `_epsE`, `_eps_lt2`, `psl211_row_word_proximity_armE`, `_rowE`, `_sampledE`. The threshold number six is correct (`psl211_exec.v:132-134`, `profile_k (instance_profile psl211_algebra) = 6`) and the "at most five" reading of `#\|C\| < 6` is correct. | "Six is the privacy threshold the derived profile declares, so every statement here that quantifies over a coalition quantifies over at most five of the twelve seats, each seat reading the card at its own position." |
| F8 | SHOULD | `psl211_tableau_checks.v:16` | "The second is what that fork costs, that the model is typed over the observed execution the named prefix builds and is refused over the inline one" | A metaphor noun for a relation, in new text. The relation is a refusal, not a price. | "The second is what that fork rules out: the model is typed over the observed execution the named prefix builds and is refused over the inline one, so no typed evidence crosses between them." |
| F9 | SHOULD | `psl211_tableau_analysis_bridged.v:58` | `psl211_row_word_proximity == the proximity claim, published at 2^-40` | Wrong kind of noun, and it breaks one-word-per-concept inside one index. `psl211_row_word_proximity : PublishedRow` is a program value; the sibling entry two lines up calls the other one "the all-decks row as a program". A row is not a claim; the claim is `psl211_word_view_proximity`, indexed separately at `:90`. | `psl211_row_word_proximity == the word row as a program, published at 2^-40` |
| F10 | SHOULD | `psl211_tableau_checks.v:45` | `From pgg_smc Require Import psl211_tableau_observed psl211_tableau_sampled.` | The checks file uses no name declared in `psl211_tableau_sampled.v`. Its two Sampled-phase values are `psl211_exact_sampled` and `psl211_word_sampled`, and neither appears in the file; the four `Fail`s reach `psl211_alldecks_prefix`, `psl211_alldecks_prefix_vm` (Observed), `psl211_exact_family`, `psl211_word_family` (models), `psl211_exact_witness`, `psl211_word_proximity_cert` (AnalysisBridged), `psl211_word_proximity_close` (the reduced file) and `pgl27_exact_family`. The template's rule is that each file requires and imports the phases whose names it uses. At S5 the import was earned by a bare `Check` of `s5_rand_sampled`; here nothing earns it. | Drop `psl211_tableau_sampled` from that line, or add the one bare `Check` that earns it. Either way, verification rule 2 must be re-run afterwards, because changing a `Fail`'s import list is exactly what makes a `Fail` reject for a different reason. |
| F11 | SHOULD | `psl211_tableau_analysis_bridged.v:48`, `psl211_tableau_observed.v:13` | `(* equation, psl211_tableau_sampled for a named model, psl211_tableau_observed*)` and `(* One run reaches this level and three values name it. psl211_alldecks_prefix*)` | Both are exactly 80 bytes with the text abutting `*)` and no space, where every other box line in both files has one. This is the shape of template trap 2: a width check passes and the eye does not catch it. | Re-wrap both lines so the last word moves to the next line and the right edge reads `… *)`. |
| F12 | SHOULD | `fidelity.v:198-228` | `Print Assumptions` is issued for `psl211_algebraic_start` and the four new equations, and for none of `psl211_alldecks_executable`, `psl211_exact_sampled`, `psl211_word_sampled` | The template says to print the assumptions of the new definitions too, "since a type ascription alone would pass on a wrong body", and those three are ascribed only at `Tableau Executable` / `Tableau Sampled`, which every value of the level satisfies. The gap is closed in fact, not in the record: each of the three is pinned by an ascribed equation whose assumptions are printed (`psl211_alldecks_executable` by `_executable_paramsE` and `_executableE`, `psl211_exact_sampled` by `psl211_row_alldecks_sampledE`, `psl211_word_sampled` by `psl211_row_word_proximity_sampledE`). | Add the three `Print Assumptions` lines, or record the pinning argument in `STATUS.md` so a later reader does not have to rediscover why three of the five new definitions are unprinted. |
| F13 | SHOULD | `staged/RETIRED.md:27-42` | "References that must change, in code" lists `_CoqProject:235`, `_CoqProject:236` and `psl211_word_proximity.v:91` | Two more occurrences of `psl211_rows` exist in the tree outside `notes/` and `.claude/` and neither is in the tables: `instances/psl211/psl211_word_proximity.v:173` ("the model psl211_rows.v publishes"), which is inside the docstring of `psl211_word_proximity_cert_idealE` and is in fact handled, since that declaration moves and its docstring is the one intended difference; and `.Makefile.rocq.d:383-384`, a generated dependency file. Neither is a correctness defect. The defect is in the completeness claim: the page says the tables are the result of a whole-tree grep. | Add `psl211_word_proximity.v:173` to the comment table with "carried by the one changed docstring, see `psl211_word_proximity_cert_idealE`", and one line saying `.Makefile.rocq.d` is generated and is regenerated by the build. |
| F14 | NOTE | `psl211_tableau_analysis_bridged.v:187`, `:316` | "independence of the coalition's view from the chirality"; "The number is 2^-41 of that bound" | Moved production text, word-identical (docstrings of `psl211_row_alldecks_armE` and `psl211_word_proximity_cert_eps_lt2`). Listed once as the template requires: `view` as a prose noun survives here and nowhere else in the new text, and "the number is 2^-41 of that bound" states a ratio where the surrounding prose states a relation. Not to be changed in this batch. | None in this batch. |
| F15 | NOTE | `fidelity.err:1-9` | two `overriding-logical-loadpath` warnings on `staged/instances/psl211` and `staged/instances/psl211/tableau` | An artifact of the probe `_CoqProject` binding the staged tree twice, under `-Q . tableau_dirs_psl211` and then `-R staged/instances/psl211 pgg_smc`. The remap lands on `pgg_smc.tableau.<name>`, which is exactly the binding production's existing recursive `-R instances/psl211 pgg_smc` will give, so the resolution the compile evidence was gathered under is production's. Production will not emit the warning, because it has no second binding. | None. Worth one line in `STATUS.md` so the warning is not read as the template's trap about adding an `-R` line for the subdirectory. |
| F16 | NOTE | `psl211_tableau_analysis_bridged.v:127-132` | `Local Notation seatT`, `Local Notation cardT` are not in the header index | The template says index every non-`Fail` declaration. A `Local Notation` is arguably not one, the S5 worked example has none to test the rule against, and production `psl211_rows.v` did not index them either. Recorded so PGL(2,7) and five-card, which both have `Local Notation` blocks, settle it once rather than twice. | Settle the rule at PGL(2,7): either index notations in a third list or state in the template that they are out of the index. |
| F17 | SHOULD | `STATUS.md:31`, `:33` | "`instances/psl211/psl211_word_proximity.v` \| 16 \| 3" and "All 28 are accounted for: 23 move into the six phase files, 5 stay" | Both numbers are wrong and `STATUS.md` contradicts itself twice over. The file has 17 declarations, not 16: `psl211_word_proximity_close`, `psl211_word_proximity_cert`, `_cert_idealE`, `_cert_secretE`, `_cert_secretTE`, `_cert_epsE`, `psl211_pow2_40_ge1`, `psl211_pow2_40_gt0`, `psl211_word_law_le2`, `Fail psl211_word_law_by_var_dist_le2`, `_cert_eps_lt2`, `psl211_row_word_proximity`, `_armE`, `_rowE`, `psl211_word_view_proximity`, `Fail _cert_pgl27_ideal`, `Fail _cert_ideal_self`. So the total is 29 and 24 move. `STATUS.md`'s own Placement table (`:36-77`) lists all 37 rows and is correct, and the `verify.py` output it pastes at `:191` and `:196` prints "production items: 29 (12 + 17)" and "the cut: 5 declarations stay in psl211_word_proximity.v, 24 move". `staged/RETIRED.md:19` also says 17. The script is right and the summary prose is wrong. | Correct the count table to 17 and 3, and the sentence to "All 29 are accounted for: 24 move into the six phase files, 5 stay". The claim of completeness is the one thing in a probe record a later reader cannot re-derive cheaply, so it must not be stated against a wrong total. |
| F18 | SHOULD | `STATUS.md:157-159` | "It is pinned, not assumed: `fidelity.v` ascribes each of those twelve at the statement production gives it, under the AnalysisBridged block, so a numeral or a notation that resolved differently would be a type error." | The justification names the wrong file and is invalid as stated. `fidelity.v` requires the **staged** phase files (`:21-26`) and opens the AnalysisBridged block (`:33-36`), so the moved constant's type and the ascription text are both elaborated under that one block; a flip relative to production could not show up there. What does pin it is `baseline.v`, which requires **production**'s `psl211_rows` and `psl211_word_proximity` (`:20`) and ascribes the same texts under the AnalysisBridged block (`:27-30`): there the constant's type was fixed by production's parse and the text by the new one, so a flip would be a type error. The pin exists and holds; the record credits the wrong half of it. | Rewrite the paragraph around `baseline.v`, and say why the pairing matters: the baseline file must load the production modules, or the ascription is a tautology. See ruling 11. |

## Remit 2: placement, declaration by declaration

All 24 non-`Fail` production declarations and all 5 recorded `Fail`s sit in the
file of the phase they are about. Nothing is misplaced.

**The three Observed prefix variants and their `_paramsE`.** Correct and
forced. `psl211_alldecks_prefix`, `psl211_alldecks_prefix_vm` and
`psl211_alldecks_prefix_lit` are all `Tableau Observed`. The two `_paramsE`
lemmas state `projT1 (projT2 (tableau_at <an Observed value>)) =
psl211_alldecks_params`, so no Executable-phase file can state them without
changing their tokens. This is the S5 Placement section's `s5_supplied_paramsE`
case exactly, and its answer carries: the lemma belongs where its subject
lives, and what the Executable file owes is a statement of its own, which
ruling 8 required and which `psl211_alldecks_executable_paramsE` supplies.

**`psl211_exact_witness` at AnalysisBridged.** Correct, and the framework
settles it the same way it settled the S5 witness. Its type is
`ExactWitness (amf_sample psl211_exact_family R idx)`, and an `ExactWitness` is
the argument of `certify_exact` (`manifest/pgg_tableau.v:777`), not of
`sample_step`. The Sampled level's own obligation, `sampled_viewE_prop`, is
discharged by `sample_step` itself and the instance owes nothing there.

**The certificate value and its six `_cert_*` statements at AnalysisBridged.**
Correct. `psl211_word_proximity_cert` is the payload of
`certify IdealProximity`, so it is a program-level object by the addendum's own
rule. Each of `_cert_idealE`, `_cert_secretE`, `_cert_secretTE`, `_cert_epsE`,
`_cert_eps_lt2` has that certificate as its syntactic subject: they read
`ipc_ideal`, `ipc_secret`, `ew_secretT (ipc_witness …)` and `ipc_eps` of it.
None of them states a fact about a law or a distance, so none of them is
mathematics that should have stayed. The sharpest of the four the prompt asks
about is `_cert_eps_lt2`: it might look like arithmetic, but its statement is
`ipc_eps (psl211_word_proximity_cert R idx) < 2%:R`, a fact about the
certificate's field, and the arithmetic it rests on is exactly what stayed
behind, `psl211_pow2_40_ge1` and `psl211_pow2_40_gt0`. The split is drawn in
the right place: the number's arithmetic is in the mathematics file, the claim
that the certificate's field is that number is in the tableau file, and the
arrow runs from the first into the second.

**The four `Fail`s in checks against the one left in the reduced file.** The
prover's reason is right. `psl211_word_law_by_var_dist_le2`'s statement is
`var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2%:R^-40 := var_dist_le2 _ _`:
its subject is a distance between two laws and it names no certificate, no row
and no program value, so it is the near miss of `psl211_word_law_le2`, which
stays, and it belongs beside it. The four that moved each name a program
object: two name `psl211_alldecks_prefix_vm` against `psl211_alldecks_prefix`
or the model typed over one of them, and two name
`psl211_word_proximity_cert`, its ideal field and its witness field.

## Remit 3: the cut of `psl211_word_proximity.v`

**What stays is right, and the name is still true of the content.** Of the 17
production declarations, 12 leave and 5 stay:
`psl211_word_proximity_close`, `psl211_pow2_40_ge1`, `psl211_pow2_40_gt0`,
`psl211_word_law_le2` and the `Fail` `psl211_word_law_by_var_dist_le2`. Every
one of the five has a law or a distance as its subject and names no
certificate, no row and no program value; every one of the twelve names a
certificate, a row or a statement about one. The rule is applied without a
residue.

The file's name still describes what is in it. `psl211_word_proximity` reads
"how far the word cut is from the uniform one", and that is now the file's
whole content, stated by its rewritten header at `:7-14`. The reduced header
is the best new prose in the batch: it says what the file measures, it prices
the number honestly ("a bound of 2^-40 here is a distinguishing advantage of at
most 2^-41"), and it says where the certificate and the row went without using
a history word.

**Recommendation on the prover's open question: do not fold the remainder into
`instances/psl211/psl211_word_model.v`.** The import facts, all measured:

- Folding would create no cycle. `psl211_word_model.v` requires
  `psl211_exec`, `psl211_alldecks`, `psl211_models`, `psl211_mixing`,
  `psl211_closure`, `psl211_profile`, `pgg_sample_adapter`,
  `pgg_weighted_words` and `var_dist_joint_law`, and none of those reaches a
  phase file. `psl211_tableau_analysis_bridged.v` already requires
  `psl211_word_model`, so it would still reach `psl211_word_proximity_close`.
- Folding would pull in no heavy import either. The only module the reduced
  file names that `psl211_word_model.v` does not is `var_dist_supp`, and
  `security/var_dist_joint_law.v:50` already requires it, so `var_dist_supp`
  is in `psl211_word_model.v`'s load closure today. `variation_dist`,
  `var_dist_joint_law`, `psl211_models` and `pgg_sample_adapter` are all
  already on its import list. In module terms folding is free, so "fewer
  imports" cannot be the argument for it.
- What folding would cost is where the proofs sit. `psl211_word_proximity.v`
  is a leaf today and gains exactly one importer after this batch, the
  AnalysisBridged file. `psl211_word_model.v` sits below the facade
  `psl211_analysis.v` (`:78`) and hence below `manifest/pgg_analysis_manifest.v`,
  a reverse closure of about twenty modules. Folding moves
  `psl211_word_proximity_close` and a recorded `Fail` from a leaf onto that
  path, where they are re-elaborated whenever anything in the closure is
  rebuilt, and where a recorded rejection is the last thing a reader of a
  model file expects.
- It would also contradict `psl211_word_model.v`'s own header, which says
  (`:12-14`) that the file is "the all-decks carrier with that one
  coordinate's law replaced, and nothing else of the instance is restated
  here". `psl211_word_proximity_close` is a statement about a coalition's
  reading and the chirality, not about the cut's law; putting it there makes
  that scope sentence false, which is the same class of defect as F7.

**PGL(2,7), for consistency.** `instances/pgl27/pgl27_proximity.v` gets the
same treatment: cut it by the addendum's rule, stage the reduced file in its
production position, and leave the surviving mathematics where it is rather
than folding it into `pgl27_models.v` or `pgl27_mixing.v`. The reason is the
same and the numbers will be the same shape: `pgl27_proximity.v` already
requires `var_dist_supp`, and `pgl27_models.v` is below `pgl27_analysis.v`,
which the manifest imports. One rule, stated once: **the reduced mathematics
file stays a file of its own, and the tableau directory imports it.**

## Remit 4: the import graph

Acyclic, and no `Require Export` anywhere in the seven staged files. The chain
is exactly the S5 shape:

```
algebraic <- executable <- observed <- sampled
analysis_bridged <- observed, sampled
checks           <- observed, sampled, analysis_bridged
psl211_word_proximity (reduced)  ->  analysis_bridged
```

The last arrow is the addendum's point and it holds: the reduced file no longer
requires the rows file, and `psl211_tableau_analysis_bridged.v:112` requires it
for `psl211_word_proximity_close`, `psl211_pow2_40_ge1` and
`psl211_pow2_40_gt0`. No cycle: the reduced file's own requires
(`psl211_word_model`, `psl211_models`, `psl211_mixing`, `psl211_closure`,
`psl211_profile`, `var_dist_supp`, `var_dist_joint_law`) reach no phase file.

`psl211_tableau_analysis_bridged.v` requires `observed` and `sampled` and not
`executable` or `algebraic`, which is right: it names `psl211_alldecks_params`
from `psl211_alldecks.v` and no Executable-phase name.

**No module-name collision.** Counting the `.v` files under every `-R` and `-Q`
directory of production's `_CoqProject` gives 209 logical base names, pairwise
distinct, and that count already includes S5's six. None of
`psl211_tableau_{algebraic,executable,observed,sampled,analysis_bridged,checks}`
is among them.

## Remit 5: `RETIRED.md`, `staged-comments/` and the `_CoqProject` edit

**The `_CoqProject` edit is correct.** Production's lines are `:234`
`psl211_reading_constancy.v`, `:235` `psl211_rows.v`, `:236`
`psl211_word_proximity.v`, `:237` `manifest/pgg_analysis_client.v`. Removing
`:235` and inserting the six phase lines after `:236`, in phase order, keeps
the reduced proximity file ahead of the AnalysisBridged file that requires it,
and keeps `pgl27_models` (needed by the checks file) and
`manifest/pgg_analysis_manifest.v` (needed by the AnalysisBridged and checks
files) ahead of all six. No `-R` line is added or removed, which is the
template's measured rule.

**The three `staged-comments/` repoints are comment-only and each new citation
is TRUE.** Diffed against production:

| file | before | after | true? |
|---|---|---|---|
| `psl211_models.v:40` | `psl211_rows.v, beside the Tableau surface whose ExactWitness record gives it its type` | `instances/psl211/tableau/psl211_tableau_analysis_bridged.v, beside the Tableau surface …` | TRUE. `psl211_exact_witness` lands at `psl211_tableau_analysis_bridged.v:149`, and its type is `ExactWitness (amf_sample psl211_exact_family R idx)`. |
| `psl211_reading_constancy.v:15` | `the proximity arm, in instances/psl211/psl211_word_proximity.v` | `the proximity arm, in instances/psl211/tableau/psl211_tableau_analysis_bridged.v` | TRUE. The arm is carried by `psl211_row_word_proximity` (`:353`), certified by `psl211_word_proximity_cert` (`:255`), both in that file. |
| `psl211_reading_constancy.v:45` | `the row of instances/psl211/psl211_word_proximity.v publishes` | `the row of instances/psl211/tableau/psl211_tableau_analysis_bridged.v publishes` | TRUE. `psl211_row_word_proximity_rowE` (`:378`) is the publishing equation. |
| `psl211_reading_constancy.v:76` and `:783` | `instances/psl211/psl211_word_proximity.v carries a proximity certificate` | `instances/psl211/tableau/psl211_tableau_analysis_bridged.v carries a proximity certificate` | TRUE, same declaration. `:783` is inside the docstring of `psl211_alldecks_constancy_false_word584`, and the edit is a re-wrap of the same sentence. |
| `pgg_analysis_manifest.v:801-805` | certificate and final bridge theorem both cited to `instances/psl211/psl211_word_proximity.v` | certificate cited to `psl211_tableau_analysis_bridged.v in instances/psl211/tableau/`, its distance field `psl211_word_proximity_close` cited to `instances/psl211/psl211_word_proximity.v`, final bridge theorem cited to `psl211_tableau_analysis_bridged.v` | TRUE on all three counts, and this is the only repoint that had to split one citation into two. `psl211_word_proximity_cert` and `psl211_word_view_proximity` land in the phase file; `psl211_word_proximity_close` stays. |

`pgg_analysis_manifest.v:794` (citing `psl211_word_model.v`) and `:811` (citing
`psl211_word_proximity_close` by name alone) are correctly left alone: both
stay true.

**One stylistic consequence of the re-wrap.** The new
`psl211_reading_constancy.v:76-77` reads `… carries a` / `proximity
certificate,` with a two-word continuation line inside an 80-column box. It is
legal and comment-only. Re-flowing the paragraph would make it a larger diff on
a file whose reverse closure is empty, so leaving it is defensible; say so in
`STATUS.md` rather than leaving it to look like an oversight.

**Whole-tree scan for `psl211_rows` outside `notes/` and `.claude/`.** Seven
places. `_CoqProject:235` and `instances/psl211/psl211_word_proximity.v:91`
(the `Require`) are in the tables. `instances/psl211/psl211_models.v:40` is in
the comment table. `instances/psl211/psl211_rows.v:4` is the file's own header
and goes with the file. The two the tables miss are `.Makefile.rocq.d:383-384`
(generated) and `instances/psl211/psl211_word_proximity.v:173`, which is F13.
The four files under `docs/superpowers/plans/` are dated records of past
batches and are correctly left alone.

## Remit 6: the scope-block change

**The argument is sound, and it is stronger than the template's wording
suggests.** Twelve declarations move from `instances/psl211/psl211_word_proximity.v`,
whose block is `ring_scope, fdist_scope, proba_scope` with `proba_scope`
innermost (`:98-100`), into `psl211_tableau_analysis_bridged.v` and
`psl211_tableau_checks.v`, whose block is `fdist_scope, proba_scope,
entropy_scope, ring_scope` with `ring_scope` innermost. The other ten come from
`instances/psl211/psl211_rows.v`, whose block is already the phase files'
(`:125-128`), so they are not under a scope change at all.

What makes the pin work is a detail the addendum does not spell out and that
`STATUS.md` gets wrong (F18): `baseline.v` imports **production's**
`psl211_rows` and `psl211_word_proximity` (`:20`) and ascribes their 24
statements under the **phase files'** block (`:27-30`). That is the
discriminating experiment. Each constant's type was fixed when production
parsed it under production's block; each ascription text is re-elaborated
under the new block; if any notation in those statements resolved differently
under the new stack, the ascription would fail. It compiled with one warning,
about the incompatible prefixes of `_ <| _` and `_ <| _ |> _`, and that
warning is in `baseline.err` as well as `fidelity.err`, so it belongs to
loading infotheo beside the tableau surface and not to this batch.

`fidelity.v` cannot settle the same question, and this is worth stating
because the addendum's wording invites the mistake: it loads the staged phase
files, so the moved constant's type and the ascription text are elaborated
under one and the same block, and the ascription holds whatever that block
does. `fidelity.v` pins that the staged text has production's statements;
`baseline.v` pins that production's statements mean the same thing under the
new block. Both are needed and both were run.

**Could a notation parse differently and still typecheck? Yes, in two named
ways, and neither bites here.**

1. An ascription checks convertibility, not syntactic identity, so a flip
   between two convertible readings would pass. This would need one of
   `fdist_scope`, `proba_scope` or `entropy_scope` to redefine a notation that
   `ring_scope` also defines, to a convertible term. None of them does.
2. A moved `Definition`'s **body** is ascribed only at its type.
   `psl211_row_word_proximity : PublishedRow` and
   `psl211_word_proximity_cert : forall R idx, IdealProximityCert …` say
   nothing about what is inside. Here the coverage is nonetheless complete,
   because every field of the certificate is pinned by an ascribed equation
   proved by conversion: `_cert_epsE` pins `2%:R^-40`, `_cert_idealE` the
   ideal and the port, `_cert_secretE` and `_cert_secretTE` the secret and its
   carrier, and `_rowE` and `_armE` pin the row and its arm. Nothing in the
   twelve bodies is left unpinned.

**Moved statements containing a notation the two scopes could resolve
differently**, named as the remit asks:

| statement | notation at risk | scope it lives in | verdict |
|---|---|---|---|
| `psl211_word_proximity_cert` (body) | `2%:R^-40` | `%:R` and `^-` are `ring_scope` | safe; no other open scope defines either |
| `psl211_word_proximity_cert_epsE` | `2%:R^-40 :> R` | `ring_scope` | safe, and pinned by conversion |
| `psl211_word_proximity_cert_eps_lt2` | `< 2%:R :> R` | `<` from the order and num hierarchy, `%:R` from `ring_scope` | safe |
| `psl211_word_view_proximity` | `` `x ``, `<=`, `2%:R^-40`, `(#|C| <= 5)%N` | `` `x `` is `fdist_scope`, the rest `ring_scope`; `%N` is explicitly delimited | safe; `` `x `` exists only in `fdist_scope`, which is open in both blocks |
| `Fail psl211_word_proximity_cert_pgl27_ideal`, `Fail psl211_word_proximity_cert_ideal_self` | `2%:R^-40` in the first | `ring_scope` | safe, and verification rule 2 compiles each un-`Fail`ed in its own file's preamble and compares the message |

`_|_`, `|=`, `` `I( ; ) ``, `` `H( | ) ``, `` `p_ `` and `` `o `` are the
notations a scope reorder would most plausibly disturb, and they occur only in
`psl211_alldecks_view_secrecy`, which comes from `psl211_rows.v` and is not
under a scope change.

**One thing the argument does not cover, and does not need to.** The scope
block of the reduced `psl211_word_proximity.v` is unchanged (`:57-59`, innermost
`proba_scope`), so the five declarations that stay are not re-read under
anything new.

## Remit 7: `fidelity.v`

Complete. Twenty-four `Check` ascriptions of production declarations at
`:46-176`, which is exactly the 24 non-`Fail` production declarations (10 of
`psl211_rows.v`, 14 of `psl211_word_proximity.v`), and eight more at `:198-221`
for the eight new ones. `Print Assumptions` covers 19 moved names and 5 new
ones; the three new definitions it omits are F12, and each is pinned by an
ascribed equation whose assumptions are printed.

## What was checked and found correct

Recorded so a later reader does not redo it.

- The six file headers each state the level's data and the proposition
  `StackProp` carries there, and each statement of that is TRUE against
  `manifest/pgg_tableau.v:553-562`: `True` at Algebraic and at Executable;
  `oe_correct_prop` at Observed, whose three conjuncts are every process
  reaching `Finish`, the endpoint list having one entry per seat and the
  decode equalling `oe_expected` (`:380-400`), which the Observed header
  renders correctly as termination within 220 steps, twelve endpoints and
  decoding to the chirality bit; `oe_correct_prop /\ sampled_viewE_prop` at
  Sampled; `BridgedProp no_reprice` at AnalysisBridged. The level data itself
  is `StackAt` (`:278-299`).
- Every number in the new text is right: 220 (`psl211_exec.v:105`), 660
  (`psl211_word_model.v:8`), 584 (`:9`, `:73`), 132 block lines
  (`psl211_alldecks.v:116`, `:216`), 720 as `6!` twice (`:174`), six as the
  threshold (`psl211_exec.v:132-134`), and "at most five of the twelve seats"
  as the reading of `#|C| < 6`.
- Every bound is named as a bound and the advantage is halved correctly. The
  AnalysisBridged header (`:27-29`) writes "within 2^-40, in the sum of
  absolute differences, … so a distinguisher's advantage is at most 2^-41", and
  the reduced header (`:16-18`) writes the same conversion once for the file.
  Nowhere is 2^-40 called "the distance".
- "Deck description" and "deal" are used correctly and distinctly. The
  AnalysisBridged header (`:16-21`) calls the whole run argument the deck
  description, a chirality bit with a deal, and lists the deal's three
  coordinates; this matches `psl211_word_model.v:16-20` and
  `psl211_alldecks.v:9`.
- The Executable header's account of why the raw bind is used is TRUE:
  `dealt` and `supplied` both begin at a `PGGAlgebraic`
  (`manifest/pgg_tableau_syntax.v:294`, `:351`) and `encoded` at a `Targeted`
  over one (`:334`, `:217`), so no keyword form continues a named Algebraic
  value.
- The Executable header's "Both rows the manifest carries for this instance …
  are over this one run" is TRUE: the manifest has exactly two PSL(2,11) rows,
  `psl211_row_alldecks` (`pgg_analysis_manifest.v:1070`) and `psl211_row_word`
  (`:1100`), and both are `@MkAnalysisPathRow PSL211Analysis.observed …`, which
  is `psl211_alldecks_observed` (`psl211_analysis.v:117`).
- The AnalysisBridged header does not say a row does not exist because a
  program does not. `:34-37` names the input-indistinguishability arm and says
  what refutes its constancy field, and `:39-43` names the class of what enters
  the rows rather than writing "nothing else".
- Ruling 9 holds for every new equation: `psl211_alldecks_executable_paramsE`,
  `psl211_alldecks_executableE`, `psl211_row_alldecks_sampledE` and
  `psl211_row_word_proximity_sampledE` all close by `exact: erefl`. The four
  `by []` proofs in the batch are all inside moved declarations, where token
  identity forces them.
- Header indexes match the declarations. Algebraic 1, Executable 1 plus 1,
  Observed 3 plus 3, Sampled 2 with no results section, AnalysisBridged 4 plus
  13, reduced proximity file 4 results and no definitions. Every non-`Fail`
  declaration is indexed, no `Fail` is, spellings are exact, and index order
  follows file order. The two `Local Notation`s are F16.
- No line in any of the seven staged files exceeds 80 bytes. No stray `**)`
  outside a full-width box rule. No history, probe, stage or landing word, no
  timing, no proof strategy in a rendered body, and no reference to a paper's
  table. No abbreviation of "indistinguishability". None of the project's
  banned vocabulary list appears; the only matches a substring scan produces
  are inside "position", "positions" and "positive", which the list allows.
- The one changed docstring, on `psl211_word_proximity_cert_idealE`
  (`:265-269`), is correct: it says the certificate's ideal is the model the
  published all-decks row carries and that the port built from the
  certificate's witness is that row's port. Its statement is
  `ipc_ideal … = amf_sample (ab_f (published_at psl211_row_alldecks_tableau))`
  and `ExactIndependence (ipc_witness …) = ab_port (published_at …)`, and
  `ExactIndependence` is a constructor of `SecurityPort` taking an
  `ExactWitness` (`manifest/pgg_tableau.v:241`), and `ab_port` is the row's
  port coordinate (`:354`), so no witness is called a port and no model is
  called a row.

## Rulings to carry to PGL(2,7) and five-card

1. **"Meant to recover" is a template slot, not a sentence to rewrite.** F3 is
   the S5 audit's F4 and F6 coming back at the second instance, in a docstring
   whose own file header states the rule correctly two dozen lines above it.
   At PGL(2,7) and five-card, copy the S5 Executable docstring's clause
   verbatim and change only the noun: "the value the run is meant to recover is
   …". The phrase "the value the run recovers" is barred below Observed.
2. **A record that no program continues still carries statements.** Before
   writing "what is stated at it is X", grep the instance for the record's
   name. At PSL(2,11) the record `psl211_dealt_params` carries ten statements
   and the header claimed one. PGL(2,7) has the same shape, a dealer-dealt
   record with no program; five-card has two Sampled values whose rows come
   from theorems. Write "the only security statement made at it is …", naming
   the class, never "what is stated at it is …".
3. **One premise, one rejection.** F4. When a checks header groups several
   `Fail`s under one boundary, each `Fail` must follow from the premise the
   sentence states. A type refusal and a conversion failure are two boundaries
   wearing one word. Write them as two clauses with two causes, and never let a
   `Fail` about an existing term be read as a refusal of a term nobody wrote.
4. **`sampled_viewE_prop` is about the run argument and the cut, not the
   layout.** F5. The same sentence will be copied into
   `pgl27_tableau_sampled.v` and `five_card_tableau_sampled.v`. The layout is a
   field of the parameter record; `static_coalition_obs` takes
   `x : ex_inputT E` and `g`.
5. **A header's universal about coalitions is false in an AnalysisBridged
   file.** F7. Most declarations in that file are equations about a row, a
   certificate or an arm and quantify over no coalition. Write "every statement
   here that quantifies over a coalition".
6. **The reduced mathematics file stays a file of its own.** Remit 3. At both
   PGL(2,7) and five-card, cut the proximity file by the addendum's rule and do
   not fold the remainder into the instance's model or mixing file. Folding is
   free in module terms at every instance, because `var_dist_supp` is already
   in the closure through `security/var_dist_joint_law.v`, so the module count
   is not the reason either way; the reason is that the model file sits below
   the instance facade and the manifest, and a leaf is where a recorded `Fail`
   and a coalition-level distance belong.
7. **Earn every phase import.** F10. The checks file imports the phase files
   whose names it uses, and at PSL(2,11) it uses none from Sampled. Check the
   name set before copying the S5 import block, and if an import is dropped,
   re-run verification rule 2, because a `Fail`'s message is a function of the
   import list.
8. **Check the right edge, not the width.** F11. Two box lines are exactly 80
   bytes with the text touching `*)`. This is template trap 2 in its quieter
   form: the width check passes. Add the shape check to `verify.py` before the
   next instance: a box content line ends with `space, *, )`.
9. **`Print Assumptions` every new definition, or record why not.** F12. Three
   of the five new definitions are pinned only through equations. That is
   sound, but the soundness lives in an auditor's head unless it is written
   down. Either print all of them or put the pinning argument in `STATUS.md`.
10. **A published row is a program, not a claim.** F9. When an index entry
    describes a `PublishedRow`, use the same noun the sibling entry uses. The
    claim is the theorem the row projects to, and it has its own entry.
11. **The `baseline.v` shape is the scope pin, and it should be stated as
    such.** Remit 6 and F18. What makes the scope argument work is that
    `baseline.v` imports the **production** modules and ascribes under the
    **phase files'** block: the constant's type comes from the old parse and
    the ascription text from the new one. `fidelity.v` cannot do this job,
    because it loads the staged files and both sides of its ascriptions come
    from the same block, which makes it a tautology for this question. At
    PSL(2,11) the pin is correctly built and incorrectly described. Put the
    rule in the template in one line: **the baseline file must `Require` the
    production modules and open the phase files' scope block, and it is the
    baseline file, not the fidelity file, that decides the scope question.**
12. **A probe record's counts must agree with its own script output.** F17.
    `STATUS.md` states 16 and 28 where `verify.py`'s pasted output, its own
    Placement table and `RETIRED.md` all say 17 and 29. Before the record is
    handed to the next instance, regenerate the count table from the script
    rather than writing it by hand, so the two cannot part.
