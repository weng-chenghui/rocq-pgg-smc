# Renamed identifiers: trace-count lemmas, and bound variables spelled like a norm (2026-09-21)

Commit eaad140 (main). No `.tex` file was edited. A search of `paper/`,
`paper-wadt2026/` and `paper-wadt2026-baseline-application/` finds NONE of the
old names below, so no paper line needs to follow; the note exists so that a
later citation uses the new names.

## Global names (lemmas)

| old | new | file |
|---|---|---|
| `s5_nt_L1`, `s5_nt_L2`, `s5_nt_L3` | `s5_n_traces_natB1`, `s5_n_traces_natB2`, `s5_n_traces_natB3` | `instances/s5/pgg_raag_s5.v` (mentioned in the header of `instances/s5/rigidity_s5_instance.v`) |
| `star3_ntB0`, `star3_ntB1`, `star3_ntB2`, `star3_ntB3` | `star3_n_traces_natB0` ... `star3_n_traces_natB3` | `groups/pgg_raag_clique.v` |
| `free3_ntB2` | `free3_n_traces_natB2` | same |
| `abelian3_ntB2`, `abelian3_ntB3` | `abelian3_n_traces_natB2`, `abelian3_n_traces_natB3` | same |
| `path3_ntB2`, `path3_ntB3` | `path3_n_traces_natB2`, `path3_n_traces_natB3` | same |
| `path4_ntB_check`, `star3_ntB_check` | `path4_n_traces_natB_check`, `star3_n_traces_natB_check` | same |

Each lemma evaluates `n_traces_natB` (`groups/pgg_raag.v`) at a word length,
and the digit at the end is that word length. The two generated inventories
`audit-inventory/THEOREM_INDEX.md` and `audit-inventory/theorem_index.tsv`
carry the new names.

## Bound variables (no other file sees them)

The owner reads a capital letter L followed by the digit one or two as the
barred norm abbreviation; in this tree L is a word length or a code list.

| file | old | new |
|---|---|---|
| `security/pgg_schreier.v`, `security/pgg_schreier_weighted.v` | word lengths `L1 L2` | `L L'` |
| `instances/pgl27/pgl27_orbit.v`, `instances/psl211/psl211_alldecks.v`, `instances/psl211/psl211_orbit.v` | sorted lists `L1 L2 : seq nat` (in `psl211_orbit.v` also the line `Arguments list_to_set_inj [L L'].`) | `L L'` |
| `reconstruct/transitivity_privacy.v` | tuple indices `l1 l2` in three intro patterns | `i j` |

In `security/pgg_schreier.v` two comments spoke of the Euclidean norm by the
same abbreviation; they now say "sum-of-squares to total variation
conversion" (Saloff-Coste 1997, Theorem 2.6).

## The one exception

`smc/smc_interpreter.v` keeps `l1 l2` (two lenses, in `rstep_disjoint`, which
nothing uses): the file declares itself vendored verbatim from the infotheo
fork, and a rename would make that false and turn the next re-vendor into a
merge.
