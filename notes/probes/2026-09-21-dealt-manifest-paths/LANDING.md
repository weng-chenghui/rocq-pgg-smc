# Landing record: manifest paths for the two programs over the PSL(2,11) dealer-dealt model (2026-09-21)

Base: HEAD `f21ee60`. `git diff 108d869 HEAD -- '*.v'` touches only files under
`notes/probes/2026-09-21-dealt-manifest-paths/staged/` and `fidelity.v`, so no
production `.v` changed between the probe's base and the landing's base.

Sources: `LEDGER.md` (the staged tree), `AUDIT.md` (D1-D21), `RULINGS.md` (the
rulings win), `notes/20260921-manifest-paths-dealer-dealt-model-probe-design.md`.
Nothing committed.

## 1. Files changed or created

| file | how |
|---|---|
| `instances/psl211/psl211_dealt_model.v` | NEW, staged file, plus D11 (title), D9 (index order), D10 (index entry) |
| `instances/psl211/psl211_analysis.v` | staged file, plus D12 (box width), D15 (one clause), D21 (alias retargeted), D8 (comment and Check) |
| `instances/psl211/psl211_models.v` | D21: `psl211_dealt_observed_recovers` added beside its all-decks twin, plus its header index entry |
| `instances/psl211/psl211_colour_reading.v` | staged file, plus D7 (opening paragraph), D13 (81-byte proof line) |
| `instances/psl211/psl211_reading_constancy.v` | staged file, plus D6 (two file names) |
| `instances/psl211/tableau/psl211_tableau_dealt.v` | staged file, plus the two path-count sentences |
| `instances/psl211/tableau/psl211_tableau_executable.v` | the instance's path list and the dealer-dealt paragraph |
| `manifest/pgg_analysis_manifest.v` | staged file, plus D1, D2, D3, D4, D5, D14, D19, D8 |
| `manifest/pgg_analysis_client.v` | staged file, no ruling applied (its counts already read fourteen) |
| `_CoqProject` | the new file listed after `psl211_word_model.v`, before `psl211_recovery.v` |
| `notes/probes/2026-09-21-dealt-manifest-paths/landing_fidelity.v` | NEW |

`manifest/pgg_tableau.v`, `pgg_tableau_syntax.v` and `pgg_tableau_reading.v` are
byte-identical to production in the staged tree, so they were not copied.

`git add`: `instances/psl211/psl211_dealt_model.v`.

## 2. Decisions taken inside a ruling

- **D5.** The type of the all-decks run argument was checked before landing the
  amended sentence: `psl211_inputT := ((bool * psl211_deal)%type)`
  (`instances/psl211/psl211_alldecks.v:110`). It IS a chirality and a deal, so
  the ruling's sentence was landed as written.
- **D8, right-hand side.** The compiler arbitrated. `= x` typechecks, both in
  `psl211_analysis.v` and in the manifest, so the pin stands with `x` and the
  auditor's reading of `oe_expected` at these parameters is confirmed.
- **D8, the section label.** The `(* 5 Correctness: ... *)` line of the
  auditor's block was kept in `psl211_analysis.v`, where the all-decks checker
  block already labels each pin by section, and dropped in the manifest, where
  D19's own banner now heads the dealer-dealt block and the block's other pins
  carry no per-item label.
- **D21, the twin's statement.** `psl211_dealt_observed_recovers` is written in
  the shape of `psl211_alldecks_observed_recovers`, with
  `instance_exec psl211_dealt_params` spelled where the twin uses the local
  notation `eP` (which is bound to the all-decks execution), and `x : bool`
  where the twin has `x : psl211_inputT`. Its proof is the twin's:
  `exact: (OE.oe_run_recovers psl211_dealt_observed x w0 Gw0).`
- **D19, the banner.** Written in the manifest's own boxed style, as a
  `The deterministic checker: ...` heading beside the four facade headings,
  replacing the `(* --- the dealer-dealt aliases of the same facade --- *)`
  rule that sat under `--- 7 Transfer ---`.
- **`psl211_models.v` widened the closure.** As the ruling foresaw: closure 39
  files rather than the probe's 34, one pass, `frozen files met: none`.

## 3. Departures

1. `instances/psl211/tableau/psl211_tableau_dealt.v:286` carried a second
   negative sentence, `It is not the manifest's twelfth, which is over the
   all-decks run.`, on `psl211_dealt_obstruction_published_pathE`. It was
   deleted rather than rewritten: the sentence before it already states which
   path is published and over which run.
2. `landing_fidelity.v` pins fifteen declarations from
   `psl211_reading_constancy.v`, not the thirteen D18 names. The fifteen are
   every declaration the ledger's table lists with that file as donor. The
   extra coverage costs nothing.
3. `landing_fidelity.v` needs `psl211_closure` in its Require list, because
   `psl211_dealt_raw_viewE`'s statement names `psl211_ptbl`, which is defined
   there. The probe's `fidelity.v` did not pin that lemma.

## 4. The fourth edit of D16

`psl211_dealt_raw_countE` lost a three-line source comment when it moved:

```
(* vm_compute reads the closure table's body whatever the conversion oracle
   has been told, so this sentence is unaffected by the Local Opaque the
   block-line section leaves standing. *)
```

The deletion is correct. `psl211_dealt_model.v` issues no
`Local Opaque psl211_elem_table` before that lemma, so the condition the
comment asserts does not exist in the new file. The lemma's statement, its
docstring and its proof are byte-identical.

## 5. Verification

1. **Landed against staged.** Every remaining difference is one a ruling asked
   for; the list is section 1 above and the diffs are reproduced in
   `COMMENTS.md`.
2. **Moved declarations verbatim.** A scripted block-by-block comparison of the
   25 moved declarations against `git show HEAD:<donor>` finds them identical
   except for: the `seats`/`cards` to `seatT`/`cardT` notation rename that the
   ledger records; `psl211_colour_of_reading_collides`'s docstring, rewritten
   to name where the post-processing law is discharged (ledger section 2); and
   `psl211_dealt_raw_countE`'s deleted source comment (D16, section 4 above).
   Statements and proof scripts are byte-identical throughout.
3. **The closure pass.** `closure.py --changed HEAD`: `touched 9, closure 39`,
   `frozen files met: none`. `compile_closure.py`: 39 files, every one `ok`,
   `ALL OK`, 3 m 55 s wall. Saved output: section 6.
4. **Fidelity.** `landing_fidelity.v` compiles clean to
   `$SP/m13fid/landing_fidelity.vo`. All four `Print Assumptions` print the
   three classical axioms and nothing else.
5. **Word scan.** A word-boundary scan of the 1081 added lines finds no barred,
   economic or history word, no quotation mark, and no line over 80 bytes. The
   only `was` hits are `the chirality the dealer was given`, which states what
   the run was handed rather than any project history, and the only `row` hit
   is the Steiner-system row inside moved verbatim text.

## 6. The closure output (D20)

```
touched 9, closure 39
frozen files met: none
instances/psl211/psl211_models.v
instances/psl211/psl211_alldecks_input_distinguishability.v
instances/psl211/psl211_dealt_model.v
instances/psl211/psl211_word_model.v
instances/psl211/psl211_analysis.v
manifest/pgg_analysis_manifest.v
manifest/pgg_tableau.v
manifest/pgg_tableau_syntax.v
instances/kim2025/tableau/five_card_tableau_algebraic.v
instances/kim2025/tableau/five_card_tableau_executable.v
instances/kim2025/tableau/five_card_tableau_observed.v
instances/kim2025/tableau/five_card_tableau_sampled.v
instances/kim2025/tableau/five_card_tableau_analysis_bridged.v
instances/s5/tableau/s5_tableau_algebraic.v
instances/s5/tableau/s5_tableau_executable.v
instances/s5/tableau/s5_tableau_observed.v
instances/s5/tableau/s5_tableau_sampled.v
instances/s5/tableau/s5_tableau_analysis_bridged.v
instances/kim2025/tableau/five_card_tableau_checks.v
instances/pgl27/tableau/pgl27_tableau_algebraic.v
instances/pgl27/tableau/pgl27_tableau_executable.v
instances/pgl27/tableau/pgl27_tableau_observed.v
instances/pgl27/tableau/pgl27_tableau_sampled.v
instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v
instances/pgl27/tableau/pgl27_tableau_checks.v
instances/psl211/psl211_reading_constancy.v
manifest/pgg_tableau_reading.v
instances/psl211/psl211_colour_reading.v
instances/psl211/psl211_word_proximity.v
instances/psl211/tableau/psl211_tableau_algebraic.v
instances/psl211/tableau/psl211_tableau_executable.v
instances/psl211/tableau/psl211_tableau_observed.v
instances/psl211/tableau/psl211_tableau_sampled.v
instances/psl211/tableau/psl211_tableau_analysis_bridged.v
instances/psl211/tableau/psl211_tableau_checks.v
instances/psl211/tableau/psl211_tableau_dealt.v
instances/s5/tableau/s5_tableau_checks.v
manifest/pgg_analysis_client.v
manifest/pgg_tableau_security_property_relations.v
```

Compile log tail:

```
ok      4.4 instances/psl211/tableau/psl211_tableau_dealt.v
ok      3.5 instances/s5/tableau/s5_tableau_checks.v
ok      3.9 manifest/pgg_analysis_client.v
ok      3.8 manifest/pgg_tableau_security_property_relations.v
ALL OK
```

## 7. Not done

Nothing in the rulings is outstanding. `manifest/pgg_analysis_client.v` needed
no edit of its own, and no other file in the tree carries a stale count of the
manifest's paths.


## 8. Comments-only follow-up (2026-09-21, after the main session's recompile)

Two docstrings of `instances/psl211/psl211_models.v`. No compile, no commit.
The comment-stripped token stream of the file is identical to the landed
version (3361 tokens on both sides), and no line exceeds 80 bytes.

Both sentences named a coalition without a size and without a reading, while
over the dealer-dealt model a coalition of three seats does distinguish the
two chiralities at the card-identity reading (manifest Path 14). Each now
carries the hypothesis its theorem actually has.

Checked before landing:

- `psl211_colour_reading_indep` (`instances/psl211/psl211_colour_reading.v:203`)
  is `ReadingExactIndependence (psl211_dealt_sample secretP)
  psl211_colour_reading (psl211_secret secretP)`, which unfolds at
  `manifest/pgg_tableau_reading.v:230-237` to a quantification over every C
  with `(#|C| < profile_k (instance_profile psl211_algebra))%N`, and
  `profile_k_psl211_algebra` (`instances/psl211/psl211_exec.v:125-127`) says
  that threshold is six. It holds at every prior on the chirality, and the
  reading is the colour one. So "a coalition of fewer than six seats" and
  "from the colours of its cards" are both exact, and the sentence was landed
  as the coordinator wrote it.
- `psl211_alldecks_static_indep` (`instances/psl211/psl211_models.v:538-543`)
  has hypothesis `(#|C| <= 5)%N`, is at the card-identity reading
  `static_coalition_obs`, and is stated under `psl211_alldecksP R`, which is
  `(`U psl211_alldecks_gt0) `x (`U psl211_G_pos)` (`:204-206`): the deck
  description drawn UNIFORMLY, the cut uniformly, the two independent.
  `psl211_alldecks_exec_exact_view_indep` (`:574-577`) is the same statement
  at the executed sample layer, also at a coalition of at most five seats.
  One sharpening of the coordinator's wording follows from that check: the
  landed sentence says "drawn uniformly" rather than "being drawn", because
  uniformity is what the law supplies and what the counting argument uses.
