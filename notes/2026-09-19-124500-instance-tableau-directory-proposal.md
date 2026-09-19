# One place per instance to read its security claims

Date: 2026-09-19. Status: proposal from the user, assessed, not started. It is
a batch of its own, to run after the Kim and PSL(2,11) landings and after the
probe of [[20260919-tableau-three-extensions-probe-design]], because three
probes are copying the rows files today and a move would make every copy
stale.

## Problem

A reader who wants to know what is claimed about one instance should open one
file and see the claims, each as a program. Every instance already has one
file that holds all of its Tableau programs, and no other file in the tree
defines one. But the programs are a small part of it.

| Instance | File | Programs | Declarations in the file |
|---|---|---|---|
| five-card | `instances/kim2025/five_card_rows.v` | 4 | 28 |
| PGL(2,7) | `instances/pgl27/pgl27_rows.v` | 5 | 31 |
| PSL(2,11) | `instances/psl211/psl211_rows.v` | 4 | 9 |
| S5 | `instances/s5/s5_rows.v` | 3 | 17 |

The rest is the assembly of witnesses and certificates, link lemmas, number
lemmas, recorded failures and the examples of `realises_expected`. After the
Kim landing and the new arm the five-card file will hold about ten programs
and many more declarations, so the claims will be harder to find than they are
now.

## The user's proposal

A directory in each instance for the Tableau files, one file per phase. Files
that do not show the Tableau stay outside it and are imported by it.

## Assessment

Agreed in direction. Split by where the tree of rows branches and not by every
phase. `Algebraic`, `Executable` and `Observed` are one definition of three to
seven lines, and a file per phase would make several files of a few lines. The
tree branches at `Sampled`, by model, and at `AnalysisBridged`, by claim.

Proposed layout, PGL(2,7) as the example:

```
instances/pgl27/tableau/
  pgl27_prefix.v    the trunk, Algebraic to Observed
  pgl27_sampled.v   one named Tableau Sampled value per model
  pgl27_payloads.v  witnesses and certificates assembled from the theorems
                    below, with their number lemmas
  pgl27_rows.v      published rows, their row equations and arm pins only:
                    the one file that answers "what is claimed here"
  pgl27_checks.v    recorded failures, mutations, realises_expected
```

Three constraints, read off the code.

1. The payload records `ExactWitness` and `SpectralCert` belong to the manifest
   layer (`manifest/pgg_tableau.v`), and an instance file below the manifest
   cannot import them without closing a cycle, as the header of
   `psl211_rows.v` records. So the payloads live inside this directory. What
   stays outside is the mathematics: the theorems below the analysis facade,
   such as the `five_card_mixing.v` of the Kim landing. The layers are instance
   theorems, facade, manifest, `pgg_tableau`, then this directory.
2. File names keep the instance prefix. `_CoqProject` maps every instance
   directory to the one logical root `pgg_smc`, so four files named
   `tableau/rows.v` would collide.
3. `pgl27_sampled.v` presupposes that two programs can continue from one named
   `Tableau Sampled` value. Nothing in the tree does that today. It is row T0
   of the extensions probe.

Cost. The four rows files have no importer, so moving them recompiles only
themselves. `_CoqProject` lists files by name and changes. Paths cited in the
manifest's header, in notes and in the paper change.

## What the batch would check

That every program and every row equation survives the split unchanged as a
term. That `pgl27_rows.v` after the split contains no declaration that is not a
published row, a row equation or an arm pin. That the recorded failures still
fail for their recorded reasons from their new file. That each new file's
header is true. That the four instances end up with the same five file roles,
so a reader who has seen one has seen all.
