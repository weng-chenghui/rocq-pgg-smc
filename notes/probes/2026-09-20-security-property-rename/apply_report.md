# Security-property / security-evidence rename: application report

Base: `49c55dd` (`feat/tableau-extensions-probe`). Date: 2026-09-20.
Map: `rename_map.tsv`, 36 identifiers, 166 occurrences, applied as written.
No name was invented; no comment prose was reworded.

## 1. Library collision probe

`locate_new_names.v` is the union of the `Require Import` preambles of
`manifest/pgg_tableau.v`, `manifest/pgg_tableau_syntax.v`,
`manifest/pgg_tableau_arm_relations.v`,
`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` and
`instances/pgl27/tableau/pgl27_tableau_checks.v`, plus those five modules,
then one `Locate` per new name, 35 in all (the module name is excluded).

Compiled through the lock wrapper, exit 0. Output in `locate_new_names.out`:
all 35 answers are `No object of basename <name>`. Nothing in mathcomp,
infotheo or the tree occupies a new name. The only other output is two
pre-existing warnings (`Lia` loaded without prefix; the `_ <| _` prefix
clash), both unrelated.

## 2. Move

`git mv manifest/pgg_tableau_arm_relations.v
manifest/pgg_tableau_security_property_relations.v` (the one writing git
command allowed). `_CoqProject` line 223 changed to the new path; nothing
else in `_CoqProject` changed.

Nothing in the tree `Require`s that module: its old name occurred exactly
once in tracked `.v` outside `notes/`, in its own header.

## 3. Substitution

`apply_rename.py` (this directory) does whole-identifier-token substitution
with the regex `[A-Za-z_][A-Za-z0-9_']*` and an exact token match, over the
code and the comments of every tracked `.v` outside `notes/` and `legacy/`;
in comments the two comment-only tokens `_armE` / `armE` of the lemma family
are substituted as well. 171 tokens: the map's 166 plus 5 comment-only.
No tracked `.v` under `legacy/` holds a mapped name.

| file | map tokens | comment-only | changed lines |
|---|---|---|---|
| `manifest/pgg_tableau.v` | 70 | 0 | 71 |
| `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` | 32 | 4 | 45 |
| `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` | 33 | 0 | 32 |
| `instances/pgl27/tableau/pgl27_tableau_checks.v` | 12 | 1 | 20 |
| `instances/psl211/tableau/psl211_tableau_analysis_bridged.v` | 9 | 0 | 9 |
| `instances/kim2025/tableau/five_card_tableau_checks.v` | 4 | 0 | 4 |
| `instances/s5/tableau/s5_tableau_analysis_bridged.v` | 4 | 0 | 3 |
| `manifest/pgg_analysis_manifest.v` | 1 | 0 | 3 |
| `manifest/pgg_tableau_security_property_relations.v` | 1 | 0 | 2 |

## 4. Layout

Whitespace only. Comment words kept in the same order; no code token added
or removed (a leading `|` would have been a new token, so the `Variant`
below keeps its first constructor bare).

### Re-broken code lines

| now at | first line | second line |
|---|---|---|
| `manifest/pgg_tableau.v:257` | `Variant SecurityProperty :=` | `  ExactIndependenceProperty` / `  \| InputIndistinguishabilityProperty` / `  \| IdealProximityProperty.` |
| `manifest/pgg_tableau.v:1012` | `  ab_security_property (tableau_at (@certify_exact x q p)) R idx` | `  = ExactIndependenceProperty.` |
| `manifest/pgg_tableau.v:1048` | `  ab_security_property (tableau_at (conclude c q pf p)) R idx` | `  = ab_security_property q R idx.` |
| `five_card_tableau_analysis_bridged.v:541` | `  security_property_of five_card_uniform_published R idx` | `  = ExactIndependenceProperty.` |
| `five_card_tableau_analysis_bridged.v:1103` | `Lemma five_card_biased_branch_indistinguishability_published_propertyE` | `    (R : realType)` |
| `five_card_tableau_analysis_bridged.v:1109` | `  security_property_of five_card_biased_branch_indistinguishability_published` | `    R idx` |
| `pgl27_tableau_analysis_bridged.v:452` | `  security_property_of pgl27_word_published R idx` | `  = InputIndistinguishabilityProperty.` |
| `pgl27_tableau_analysis_bridged.v:500` | `  security_property_of pgl27_word_published39 R idx` | `  = InputIndistinguishabilityProperty.` |
| `pgl27_tableau_analysis_bridged.v:798` | `  security_property_of pgl27_prior_exact_published R idx` | `  = ExactIndependenceProperty.` |
| `pgl27_tableau_analysis_bridged.v:947` | `  security_property_of pgl27_word_proximity_published R idx` | `  = IdealProximityProperty.` |
| `pgl27_tableau_checks.v:110` | `Lemma pgl27_word_published_property_neq (R : realType)` | `    (secretP : R.-fdist bool) :` |
| `psl211_tableau_analysis_bridged.v:196` | `  security_property_of psl211_alldecks_published R idx` | `  = ExactIndependenceProperty.` |
| `psl211_tableau_analysis_bridged.v:370` | `  security_property_of psl211_word_proximity_published R idx` | `  = IdealProximityProperty.` |

The `name R idx` / `= Constructor.` break is the shape the two files already
used at `five_card_tableau_analysis_bridged.v:710` and
`pgl27_tableau_analysis_bridged.v:1024` before this pass.

### Index entries whose name no longer fits before the `==` column

- `manifest/pgg_tableau.v:127-128`: `certify_exact_propertyE` (23 characters,
  the `==` column is 28 and the name starts at 5) now sits alone, with
  its unchanged description on the next line at the `==` column. This is the
  shape the same index already used for
  `certify_indistinguishability_propertyE` and `IndistinguishabilityCert`.
- `instances/pgl27/tableau/pgl27_tableau_checks.v:46-47`:
  `pgl27_word_published_property_neq` (33 characters) no longer fits inline.
  The entry now reads the name alone, then its unchanged description on one
  box line opening `(* == the two programs over the word model ...`. See the
  note in section 7.
- `manifest/pgg_tableau_security_property_relations.v:4-5`: the header title
  line wrapped onto a second line at column 3, the convention of
  `pgl27_tableau_analysis_bridged.v` and
  `five_card_tableau_analysis_bridged.v`.

### Re-padded index entries (name still clears the `==` column, no split)

`manifest/pgg_tableau.v` 84, 85, 86, 116, 125, 135, 136.

### Re-padded name-alone index entries (padding only)

`manifest/pgg_tableau.v` 129, 132;
`five_card_tableau_analysis_bridged.v` 205, 227, 229, 257, 268, 298, 300;
`pgl27_tableau_analysis_bridged.v` 156, 158, 163, 165, 188, 210;
`psl211_tableau_analysis_bridged.v` 66, 88;
`s5_tableau_analysis_bridged.v` 59;
`five_card_tableau_checks.v` 48.

### Re-flowed comment blocks (same words, same order)

- `manifest/pgg_tableau.v`: header prose 32-34; the free comments above
  `security_property_of`, `certify_exact_propertyE` and
  `certify_indistinguishability_propertyE`.
- `manifest/pgg_analysis_manifest.v`: header prose 18-21.
- `five_card_tableau_analysis_bridged.v`: the seven hanging-indent chain
  paragraphs of the header, 91-120.
- `pgl27_tableau_analysis_bridged.v`: six chain paragraphs, 56-78.
- `pgl27_tableau_checks.v`: the timing comment inside the proof of
  `pgl27_word_published_property_neq`, 115-124.

No record field colons needed re-aligning: `ab_evidence`,
`ab_security_property`, `evidence_property` and `evidence_conclude` are
`Definition`s and `Lemma`s, and no `Record` in the tree has a field whose
name is in the map.

## 5. Acceptance check

`python3 notes/probes/2026-09-20-security-property-rename/check_rename.py 49c55dd`

```
SAME  instances/kim2025/tableau/five_card_tableau_analysis_bridged.v  (code 2161/2161, comment words 5177/5177)
SAME  instances/kim2025/tableau/five_card_tableau_checks.v  (code 431/431, comment words 990/990)
SAME  instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v  (code 2038/2038, comment words 4317/4317)
SAME  instances/pgl27/tableau/pgl27_tableau_checks.v  (code 479/479, comment words 1265/1265)
SAME  instances/psl211/tableau/psl211_tableau_analysis_bridged.v  (code 725/725, comment words 2018/2018)
SAME  instances/s5/tableau/s5_tableau_analysis_bridged.v  (code 471/471, comment words 1068/1068)
SAME  manifest/pgg_analysis_manifest.v  (code 4816/4816, comment words 7388/7388)
SAME  manifest/pgg_tableau.v  (code 3459/3459, comment words 4445/4445)
SAME  manifest/pgg_tableau_arm_relations.v  (code 492/492, comment words 913/913)
9 files changed
ALL OK
```

The checker found nothing wrong and needed no edit.

## 6. Recorded `Fail` commands holding a renamed identifier

Both are in `instances/pgl27/tableau/pgl27_tableau_checks.v`. Their rejection
has to be re-checked after the production recompile, because a `Fail` guard
echoes nothing when it passes for the wrong reason.

- `instances/pgl27/tableau/pgl27_tableau_checks.v:102` (through 105)
  `Fail Definition pgl27_word_published_property_neq (R : realType)`
  holds `pgl27_word_published_property_neq`, `security_property_of`,
  `ExactIndependenceProperty`. Its name is shared with the `Lemma` at 110,
  and the file's header says the order is what lets both compile.
- `instances/pgl27/tableau/pgl27_tableau_checks.v:197` (through 199)
  `Fail Definition pgl27_word_property_is_not_exact (R : realType)`
  holds `pgl27_word_property_is_not_exact`.

No other `Fail` in the tree mentions a renamed name.

## 7. Unsure, for the owner

1. `pgl27_tableau_checks.v:46-47`. Its single Key-results entry was inline,
   with the `==` at column 35 and a continuation at column 30, a layout no
   other file uses. With the longer name it could not stay inline. The entry
   now matches its sibling `five_card_tableau_checks.v:48-49` byte for byte
   in shape, name alone then `== ...` at column 3, rather than inventing a
   third line at column 30. Revert to a column-30 continuation if the owner
   prefers the file's own former column.
2. `Variant SecurityProperty` at `manifest/pgg_tableau.v:257`. The repo's
   multi-line `Variant`s put a leading `|` on every constructor including the
   first. Adding one here would add a code token, which the acceptance check
   forbids, so the first constructor stays bare.
3. `five_card_tableau_analysis_bridged.v:1109-1110` puts `R idx` alone on a
   continuation line, the only place in the pass where an argument list is
   split rather than the `=`. The head plus the program name is already 77
   bytes.
4. The stale object file `manifest/pgg_tableau_arm_relations.vo` is still on
   disk under the old name. Nothing `Require`s it, but it should be removed
   before the production rebuild.
5. Production was not recompiled: only `locate_new_names.v` was compiled, and
   `make` was never run.
