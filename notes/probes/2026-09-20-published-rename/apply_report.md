# PublishedRow -> Published: application report

Base `cca5e24`, branch `feat/tableau-extensions-probe`.  The fixed map of
`rename_map.tsv` (110 identifiers, 710 occurrences) was applied unchanged; no
name was invented and no name was added to the map.

## 1. Library collision probe

`locate_new_names.v` loads the union of the preambles of
`manifest/pgg_analysis_manifest.v`, `manifest/pgg_tableau.v`,
`manifest/pgg_tableau_syntax.v` and
`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v`, plus those
four files themselves, and then issues one `Locate` per new name.

    rocq compile <flags from _CoqProject> notes/probes/2026-09-20-published-rename/locate_new_names.v
    exit 0

Every one of the 110 names answered `No object of basename <name>`: 110
messages, 110 distinct names, none missing and none extra.  Eight of the
messages are line-wrapped by the printer, which is why the raw file has 118
lines.  Nothing collides, so the rename went ahead.  Output saved as
`locate_new_names.out` (the extension is in `.gitignore`, so the file is on
disk but git does not list it).

## 2. Files changed, with occurrence counts

`apply_rename.py` walked every tracked `.v` outside `notes/` and outside
`legacy/` (162 candidates).  16 held a name.  No file under `legacy/` holds
one, so the checker's "untouched but holds old names" arm stays silent.

| file | map occurrences | comment-only tokens |
|---|---|---|
| instances/kim2025/tableau/five_card_tableau_analysis_bridged.v | 184 | 6 |
| instances/kim2025/tableau/five_card_tableau_checks.v | 20 | 0 |
| instances/kim2025/tableau/five_card_tableau_sampled.v | 41 | 0 |
| instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v | 131 | 2 |
| instances/pgl27/tableau/pgl27_tableau_checks.v | 18 | 0 |
| instances/psl211/tableau/psl211_tableau_analysis_bridged.v | 41 | 0 |
| instances/psl211/tableau/psl211_tableau_checks.v | 1 | 0 |
| instances/psl211/tableau/psl211_tableau_executable.v | 2 | 0 |
| instances/psl211/tableau/psl211_tableau_sampled.v | 2 | 0 |
| instances/s5/tableau/s5_tableau_analysis_bridged.v | 17 | 0 |
| instances/s5/tableau/s5_tableau_observed.v | 6 | 0 |
| instances/s5/tableau/s5_tableau_sampled.v | 2 | 0 |
| manifest/pgg_analysis_client.v | 15 | 0 |
| manifest/pgg_analysis_manifest.v | 212 | 0 |
| manifest/pgg_tableau.v | 17 | 0 |
| manifest/pgg_tableau_syntax.v | 1 | 0 |
| total | 710 | 8 |

`git diff --stat`: 16 files changed, 683 insertions, 653 deletions.
`instances/psl211/psl211_endpoints.v` was neither read for compilation nor
edited, and none of the 35 files of its dependency cone is in the list above.
Nothing under `legacy/` or under `notes/` changed; the probe directory gained
`locate_new_names.v`, `locate_new_names.out`, `apply_rename.py` and this
report.

## 3. Acceptance check

    python3 notes/probes/2026-09-20-published-rename/check_rename.py cca5e24

    SAME  instances/kim2025/tableau/five_card_tableau_analysis_bridged.v  (code 2161/2161, comment words 5180/5180)
    SAME  instances/kim2025/tableau/five_card_tableau_checks.v  (code 431/431, comment words 985/985)
    SAME  instances/kim2025/tableau/five_card_tableau_sampled.v  (code 408/408, comment words 1331/1331)
    SAME  instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v  (code 2038/2038, comment words 4312/4312)
    SAME  instances/pgl27/tableau/pgl27_tableau_checks.v  (code 479/479, comment words 1265/1265)
    SAME  instances/psl211/tableau/psl211_tableau_analysis_bridged.v  (code 725/725, comment words 2018/2018)
    SAME  instances/psl211/tableau/psl211_tableau_checks.v  (code 251/251, comment words 552/552)
    SAME  instances/psl211/tableau/psl211_tableau_executable.v  (code 119/119, comment words 501/501)
    SAME  instances/psl211/tableau/psl211_tableau_sampled.v  (code 133/133, comment words 420/420)
    SAME  instances/s5/tableau/s5_tableau_analysis_bridged.v  (code 471/471, comment words 1068/1068)
    SAME  instances/s5/tableau/s5_tableau_observed.v  (code 290/290, comment words 1035/1035)
    SAME  instances/s5/tableau/s5_tableau_sampled.v  (code 93/93, comment words 451/451)
    SAME  manifest/pgg_analysis_client.v  (code 283/283, comment words 551/551)
    SAME  manifest/pgg_analysis_manifest.v  (code 4816/4816, comment words 7380/7380)
    SAME  manifest/pgg_tableau.v  (code 3459/3459, comment words 4436/4436)
    SAME  manifest/pgg_tableau_syntax.v  (code 1080/1080, comment words 2366/2366)
    16 files changed
    ALL OK

## 4. Code lines re-broken by hand

Ten code lines passed 80 bytes.  Each was re-broken in the shape the same file
already uses for the same construct; the tokens are unchanged.

1. `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:1075`
   (the sibling lemma at 712-722 has the same shape)

        -  /\ ap_transfer (published_path five_card_biased_proximity_published) = IdealFinite
        +  /\ ap_transfer (published_path five_card_biased_proximity_published)
        +     = IdealFinite

2. `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:1095-1096`
   (binder shape copied from 694-698 in the same file)

        -    (idx : amf_index (ab_f (published_at five_card_biased_proximity_published)) R) :
        -  security_arm_of five_card_biased_proximity_published R idx = IdealProximityArm.
        +    (idx : amf_index
        +             (ab_f (published_at five_card_biased_proximity_published)) R) :
        +  security_arm_of five_card_biased_proximity_published R idx
        +  = IdealProximityArm.

3. `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:1122`

        -Proof. exact: (view_proximity_of five_card_biased_proximity_published R tt C HC). Qed.
        +Proof.
        +exact: (view_proximity_of five_card_biased_proximity_published R tt C HC).
        +Qed.

4. `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:1208`

        -Proof. exact: (view_proximity_of five_card_biased_proximity_published R tt). Qed.
        +Proof.
        +exact: (view_proximity_of five_card_biased_proximity_published R tt).
        +Qed.

5. `instances/kim2025/tableau/five_card_tableau_checks.v:238-240`

        -    (idx : amf_index (ab_f (published_at five_card_biased_proximity_published)) R) :
        +    (idx : amf_index
        +             (ab_f (published_at five_card_biased_proximity_published)) R) :
           security_arm_of five_card_biased_proximity_published R idx
        -  <> security_arm_of five_card_biased_branch_indistinguishability_published R idx.
        +  <> security_arm_of
        +       five_card_biased_branch_indistinguishability_published R idx.

6. `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:483` (break after
   the `:`, as every neighbouring lemma statement does)

        -Lemma pgl27_word_published39_bindE : pgl27_word_published39 = pgl27_word_published39_bind.
        +Lemma pgl27_word_published39_bindE :
        +  pgl27_word_published39 = pgl27_word_published39_bind.

7. `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:515`

        -  security_arm_of pgl27_word_branch_published39 R idx = InputIndistinguishabilityArm.
        +  security_arm_of pgl27_word_branch_published39 R idx
        +  = InputIndistinguishabilityArm.

8. `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:419`

        -Proof. exact: (view_proximity_of psl211_word_proximity_published R tt C HC). Qed.
        +Proof.
        +exact: (view_proximity_of psl211_word_proximity_published R tt C HC).
        +Qed.

One further whitespace-only change in code: the field colons of the renamed
record in `manifest/pgg_tableau.v:925-928` were re-aligned, because
`published_path` is one character longer than `published_row`.

    Record PublishedAt (c : ConcludedBound) := MkPublished {
      published_at   : StackAt AnalysisBridged ;
      published_path : AnalysisPath ;
      published_thm  : BridgedProp c published_at }.

## 5. Comments: what moved

Every box line of a paragraph the rename touched was re-laid out to exactly 80
bytes with a space before the closing delimiter; a paragraph no token of the
map reaches is byte-identical to the base.  Prose paragraphs were re-filled
greedily at 75 content columns, which is the width the untouched paragraphs of
these files already use.  Table paragraphs (the ones whose lines carry `|`)
keep every cell where it was and only their trailing padding changed.  Four
`(** ... *)` docstring lines passed 80 bytes and were re-filled from the long
line to the end of their docstring, at the width of the rest of that
docstring: `pgl27_tableau_analysis_bridged.v:501`,
`psl211_tableau_analysis_bridged.v:198` and `:385`, and
`psl211_tableau_sampled.v:60`.  No word was added, dropped or reordered
anywhere, which is what the checker's comment-word arm decides.

### Boxed index entries wrapped onto continuation lines

Sixteen index entries no longer fit before their file's `==` column, so the
name now sits on a line of its own and the description starts at that column,
which is the shape those files already use for their longer names.

`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v`:
`pgl27_exact_published_armE`, `pgl27_exact_published_pathE`,
`pgl27_word_branch_published39`, `pgl27_word_published39_armE`,
`pgl27_word_published39_bind`, `pgl27_word_published39_bindE`,
`pgl27_word_published_armE`, `pgl27_word_published_certE`,
`pgl27_word_published_pathE`, `pgl27_word_published_sampledE`.

`instances/psl211/tableau/psl211_tableau_analysis_bridged.v`:
`psl211_alldecks_published_armE`, `psl211_alldecks_published_pathE`,
`psl211_word_proximity_published`.

`instances/s5/tableau/s5_tableau_analysis_bridged.v`:
`s5_rand_published_armE`, `s5_rand_published_pathE`,
`s5_rand_published_sampledE`.

No entry moved the other way: the entries whose new name is shorter
(`pgl27_exact_published`, `pgl27_word_published`, `s5_rand_published`) were
inline before and stay inline.

### Five box lines the rename did not touch

`manifest/pgg_analysis_manifest.v` carries five box lines that already filled
all 76 content columns at the base, so they have no space before their closing
delimiter.  The checker's box arm has no base exemption (its long-line arm
does), so it reports them as soon as the file changes anywhere.  They are
byte-identical to `cca5e24`, so these are reports about the base and not about
the rename.  To reach `ALL OK` without editing the checker, each was repaired
by the smallest layout move that keeps the words in order:

- `:218` and `:441`: prose paragraphs, re-filled at 75 columns.
- `:342`, `:408`: the last word of the line moved to the head of the line
  below, inside the same table cell.
- `:472`: the last word moved onto a line of its own at the cell's
  continuation indent, because the line below had no room.

If the owner would rather the base's own defects stay untouched, revert those
five hunks and the checker will report exactly these five box lines again.

## 6. Recorded `Fail` commands holding a renamed identifier

Sixteen, for the main session to re-check after its recompile.  Each is a
recorded rejection, so what matters is that it still fails for its own reason
and not because a name went missing.

| file:line | first line of the command |
|---|---|
| instances/kim2025/tableau/five_card_tableau_checks.v:98 | `Fail Definition five_card_s5_family_sampled : Tableau Sampled :=` |
| instances/kim2025/tableau/five_card_tableau_checks.v:114 | `Fail Definition five_card_biased_sampled_at_manifest_level` |
| instances/kim2025/tableau/five_card_tableau_checks.v:128 | `Fail Definition five_card_repeated_indistinguishability_published_uniform_pathE` |
| instances/kim2025/tableau/five_card_tableau_checks.v:142 | `Fail Definition five_card_repeated_published39_unindexed` |
| instances/kim2025/tableau/five_card_tableau_checks.v:214 | `Fail Definition five_card_repeated_proximity : Tableau AnalysisBridged :=` |
| instances/pgl27/tableau/pgl27_tableau_checks.v:88 | `Fail Definition pgl27_exact_published_leak7 : Published :=` |
| instances/pgl27/tableau/pgl27_tableau_checks.v:102 | `Fail Definition pgl27_word_published_arm_neq (R : realType)` |
| instances/pgl27/tableau/pgl27_tableau_checks.v:155 | `Fail Definition pgl27_word_published39_unindexed : PublishedAt pgl27_bound39 :=` |
| instances/pgl27/tableau/pgl27_tableau_checks.v:164 | `Fail Definition pgl27_word_published39_unindexed_bind` |
| instances/pgl27/tableau/pgl27_tableau_checks.v:178 | `Fail Definition pgl27_word_published41 : PublishedAt pgl27_bound41 :=` |
| instances/pgl27/tableau/pgl27_tableau_checks.v:196 | `Fail Definition pgl27_word_arm_is_not_exact (R : realType)` |
| instances/psl211/tableau/psl211_tableau_checks.v:87 | `Fail Definition psl211_vm_reuse_sampled : Tableau Sampled :=` |
| manifest/pgg_analysis_manifest.v:2272 | `Fail Check (@MkAnalysisPath S5Analysis.observed Sampled None` |
| manifest/pgg_analysis_manifest.v:2275 | `Fail Check (@MkAnalysisPath S5Analysis.observed Sampled tt` |
| manifest/pgg_analysis_manifest.v:2278 | `Fail Check (@MkAnalysisPath S5Analysis.rand_observed AnalysisBridged None` |
| manifest/pgg_analysis_manifest.v:2281 | `Fail Check (@MkAnalysisPath S5Analysis.observed Sampled` |

In eleven of the twelve `Fail Definition` cases the renamed identifier is the
name being defined, which cannot be what makes the command fail.  The four
`Fail Check` cases and `pgl27_tableau_checks.v:196` mention a renamed constant
inside the term.

## 7. Open points

- The word "row" is untouched in prose, as instructed, so a paragraph may now
  read "the row `five_card_uniform_path`".  That is for the separate prose
  pass.
- The five box lines of section 5 were repaired although the rename did not
  reach them; say the word and they go back.
- Nothing was compiled but the probe file.  The main session owns the recompile
  of the closure.
