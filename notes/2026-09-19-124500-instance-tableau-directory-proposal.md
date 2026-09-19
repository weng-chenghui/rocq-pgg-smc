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

Agreed, with one file per phase, as the user asked. A first version of this note
split the directory where the tree of rows branches and named the files
`prefix`, `sampled`, `payloads`, `rows`, `checks`. That hid three of the five
phases inside a file name of my own, and the user's point on reading it was
that the phases could not be seen. The directory listing should be the
Tableau's phases in order. That the first three files are a few lines each is
no objection: they are there to show the structure.

Layout, the five-card instance as the example, the same seven roles at every
instance:

```
instances/kim2025/tableau/
  five_card_algebraic.v         Algebraic: the algebra and the functionality
  five_card_executable.v        Executable: run mode, inputs, layout, fuel
  five_card_observed.v          Observed: the three run facts
  five_card_sampled.v           Sampled: one named value per model
  five_card_analysis_bridged.v  AnalysisBridged: one program per claim, with
                                its terminal, its row equation and its claim
                                pin; the one file that answers "what is
                                claimed here"
  five_card_certificates.v      the witness and certificate records the
                                AnalysisBridged step takes as payloads
  five_card_checks.v            recorded failures, mutations,
                                realises_expected
```

Each phase file imports the one before it. The terminals are not a phase of
their own: `publish` and `conclude` are the last line of a row and stay with
the row. `psl211_spectral_nogo.v` names `SpectralCert`, so it belongs in
`instances/psl211/tableau/` and moves there in this batch.

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
3. A phase file continues from the named value of the phase before it. Stage A
   of the extensions probe showed on 2026-09-19 that two programs continue from
   one named `Tableau Sampled` value with no change to the framework. The two
   steps below it are not yet checked. `execute` takes a `Tableau Executable`
   and `sample` a `Tableau Observed`, so those should behave the same way. The
   step from `Algebraic` to `Executable` is different: the keyword rules
   `A dealt fuel n` and `t encoded inputs ... fuel n` start from the algebra
   itself and not from a named `Tableau Algebraic` value, so continuing from
   the name in `*_algebraic.v` may need one more notation. This is the first
   ledger row of the batch.

Cost. The four rows files have no importer, so moving them recompiles only
themselves. `_CoqProject` lists files by name and changes. Paths cited in the
manifest's header, in notes and in the paper change.

## What the batch would check

That every program and every row equation survives the split unchanged as a
term. That each `*_analysis_bridged.v` after the split contains no declaration that
is not a program, a row equation or a claim pin. That the recorded failures still
fail for their recorded reasons from their new file. That each new file's
header is true. That the four instances end up with the same seven file roles,
so a reader who has seen one has seen all.
