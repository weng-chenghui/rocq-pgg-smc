# General dealer law: what the probe established

Date: 2026-09-18. Design note and claim ledger C1 to C10:
[[20260917-general-dealer-law-feasibility-design]]. Probe files, audits and the
running record: `notes/probes/2026-09-17-general-dealer-law/` (`STATUS.md` is
the record; `history/` keeps every superseded version). Nothing in the
production tree was edited and nothing is committed.

## Problem

The paper wants a dealer law $\delta_s$ in place of one fixed deck pair. The
risk is that the text ends up saying that any $\delta_s$ preserves privacy.
That sentence is false, and the existing proofs never said it: each instance
proves privacy for one particular dealer. The probe had to answer two
questions. Does a general dealer model plug into the existing PGL(2,7) and
PSL(2,11) proofs without redoing them? And what exactly is the condition on
$\delta_s$ under which privacy survives?

## Outcome

The general model is feasible. C1 to C9 compile, the naming audit (C10) and the
soundness audit both end in GO.

The joint law is
$P(s,d,g) = \mathrm{secretP}(s)\,\delta_s(d)\,\nu(g)$ (`dealer_shuffleP`,
pointwise form `dealer_shufflePE`). Privacy is independence of the coalition's
view from the secret under that law. Two sufficient conditions are proved:

1. **Mixed-law condition** (`dealer_shuffle_view_indep`). Every secret of
   positive mass has the same law of the view under $\delta_s \times \nu$.
2. **Per-deck condition** (`dealer_shuffle_view_indep_of_deck`). Every deck of
   positive mass is valid, and every valid deck has the same law of the view
   under $\nu$ alone. It implies the first condition.

Both are information-theoretic and exact. No computational assumption enters.

| Instance | Dealer law | Condition used | Coalition bound |
|---|---|---|---|
| PGL(2,7) deterministic | point mass at `orbit_encode s` | mixed-law, then carrier transport | $\lvert C\rvert \le 3$ |
| PGL(2,7) all decks | uniform on the class's decks | per-deck, `valid s d := uniq d` | $\lvert C\rvert \le 3$ |
| PSL(2,11) all decks | uniform on all deal descriptions | mixed-law only | $\lvert C\rvert \le 5$ |

Each bridge headline has a type convertible, in both directions, with the
production theorem it recovers (`pgl27_view_indep`,
`pgl27_view_indep_alldecks`, `psl211_alldecks_view_indep`). The soundness
auditor checked this by compilation.

## What the paper may claim

- Privacy is not a property of an arbitrary dealer law.
  `psl211_fixed_deal_view_dep`: at PSL(2,11), with the uniform prior on the
  chirality, the uniform law on the 660 shuffles, the production view and a
  coalition of three seats (threshold is five), replacing the dealer by the
  point mass at one deal description makes the view dependent on the chirality.
  Only the dealer changed. That dealer does not even depend on the chirality;
  the view still does, because one deal description names two different decks
  through the class table.
- The per-deck condition has no solution at PSL(2,11) under its own dealer law
  (`psl211_dealer_view_indep_of_deck_unsat`, for every validity predicate and
  every candidate law). The first premise forces validity at every deal,
  because the uniform dealer gives every deal positive mass
  (`psl211_dealer_valid_forced`).
- The underlying count (`psl211_perdeck_fiber_card_neq`, no axioms at all): at
  the deal `(ord0, 1, 1)`, seats 0, 1, 2, reading cards 0, 1, 5, the shuffles
  producing that reading number 0 for one chirality and 1 for the other.
- Exact wording: for PSL(2,11) privacy depends on which deal law the dealer
  uses. The uniform one delivers it, and that point mass does not.

## What the paper may not claim

- That the uniform deal law is necessary. Two sufficient conditions are on
  offer, one is shown unsatisfiable, and no third is excluded. Other
  non-uniform laws are undecided.
- That a hidden uniform deal leaks. In the refutation the deal is a point mass,
  so it is public.
- "Deterministic dealer: private at PGL(2,7), not private at PSL(2,11)" as an
  explanation. It is a fair report of two compiled facts. The explanatory
  variable already in the repository is transitivity: `pgl27_3transitive`
  (`instances/pgl27/pgl27_group.v:303`) against `psl211_2transitive`
  (`instances/psl211/psl211_group.v:321`), with no 3-transitivity result for
  PSL(2,11).
- That validity (`uniq d`) is needed for the PGL per-deck law to be true. It is
  shown needed for typing only. The proof that a deck with a repeated card
  breaks the law was estimated at 30 to 40 lines and not done.

## Flow (C9, `concrete_instances.v`)

```
object   Rc := Rdefinitions.R       enters via mathcomp Rstruct     // closed statements: 0
step     Require the real C1-C4 and the three bridges                 // 0
step     pgl27_view_indep_at_R            := pgl27_view_indep_via_dealer            // 1
step     pgl27_view_indep_alldecks_at_R   := pgl27_view_indep_alldecks_via_dealer   // 2
step     psl211_alldecks_view_indep_at_R  := psl211_alldecks_view_indep_via_dealer  // 3
step     psl211_dealerPE_at_R             := dealer_shufflePE at the PSL data       // 4
terminal Print Assumptions on all four: seven standard axioms         // 4
outside  the per-deck refutation and the fixed-deal refutation: boundary results
```

Every step is an `exact:` wrapper with nothing re-derived. The bridge flow
itself is a parameterised monad indexed by sample carrier and reader pair. Its
bind is `inde_RV_fdistmap` (one iff: independence under a pushforward law holds
exactly when it holds for the composed readers) together with the two reader
equations, and its laws hold propositionally through `fdistmap_comp`. The
accumulated loss is identically zero.

## Evidence

Seven probe files, each compiled alone, in dependency order, by the main
session after every change. Last run:

| File | Time | Peak memory | `Print Assumptions` |
|---|---|---|---|
| `dealer_kernel_probe.v` | 3.7 s | 1.64 GB | three `boolp` axioms |
| `carrier_transport_probe.v` | 3.6 s | 1.62 GB | three `boolp` axioms |
| `pgl27_deterministic_bridge.v` | 4.8 s | 1.69 GB | three `boolp` axioms |
| `psl211_alldecks_bridge.v` | 5.4 s | 1.74 GB | three `boolp` axioms |
| `psl211_per_deck_counter.v` | 27.7 s | 1.85 GB | closed, no axioms |
| `psl211_per_deck_law_counter.v` | 5.0 s | 1.73 GB | three `boolp` axioms |
| `concrete_instances.v` | 5.2 s | 1.78 GB | seven standard axioms |

The three are `propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`. At `Rdefinitions.R` add
`ClassicalDedekindReals.sig_forall_dec`, `ClassicalDedekindReals.sig_not_dec`,
`FunctionalExtensionality.functional_extensionality_dep`,
`Epsilon.epsilon_statement`. No project-local constant, no `Admitted`.

Seven `Fail Definition` mutations, three with a declared positive control. Every
recorded error text is a leftover arrow or a non-convertible `erefl`, which a
vacuous premise cannot produce.

Audits, all by independent Opus agents, reports in the probe directory: flow
sketch GO (its corrected sketch was adopted), soundness GO then delta GO,
naming NO-GO, NO-GO, then GO in round 3. The proving was done by Opus
`rocq-prover` agents and checked by the main session's own compiles and scans.

## Four shapes that hang, and none is helped by waiting or memory

1. `rewrite`, `move=> ->`, `done`, `simpl` on a goal from which the 132-row PSL
   block tables or the 660-row `psl211_elem_table` are reachable, worst when
   the two sides differ only in the chirality. Change set shape on abstract
   functions first, close with `exact:` on a syntactically equal goal, use
   `etrans`/`esym` in term mode, `exact: perm_refl`, `Local Opaque`.
2. `vm_compute` through `inord`, `{ffun 'I_n}`, `{set 'I_n}` or
   `psl211_alldecks_seq` never reduces, because `idP` is opaque. Count on raw
   nat lists and link back with symbolic lemmas.
3. `//` or `done` on a goal that still holds `#|pgg_G psl211_M|` tries to
   evaluate the 660-element closure. Close it with `exact: psl211_G_pos`.
4. `exact:` of an `etrans` against a goal that spells the cardinal differently
   succeeds after about 36 s, because the unifier falls back to conversion and
   recomputes the raw count. Ascribe the type: `have name : T := term`. Only
   `rocq compile -time` shows this one.

Tooling facts from the same campaign: `timeout` and `gtimeout` do not exist on
this machine, zsh does not word-split a flag variable, `grep -E '[[:<:]]'`
matches nothing without any diagnostic, and `rocq compile` prints nothing for a
`Fail` while `rocq repl` prints the error text.

## Decisions left open

1. The design note. Its C6 row names `ttrans_view_indep_alldecks` and asks for
   reuse of `alldecks_view_law`; its artifact list names
   `pgl27_alldecks_bridge.v` and `headline_decomposition.v`, which do not
   exist, and omits the two refutation files and `STATUS.md`; its list of
   proposed generic declarations has seven entries where the probe produced
   ten.
2. The route for PGL(2,7) all decks. Through the mixed-law condition it reuses
   `transitivity_privacy.alldecks_view_law` with no counting redone (that lemma
   states the mixed law, and the qualified name is reachable although the
   lemma is `Local`). Through the per-deck condition it needs the new per-deck
   law from `ktuple_encode_uniform`. Both routes are compiled. The per-deck
   route is the only thing that instantiates the per-deck condition at all.
3. File names still containing "bridge" and "counter".
4. Optional: the proof that validity is needed for truth, and four `Arguments`
   directives to remove the 65 `@`-spelled applications that
   `Set Implicit Arguments` made necessary (the coalition becomes implicit
   wherever a premise mentions its cardinality).

## Carried to the implementation plan

Proposed permanent homes, with statements, are tabulated in `STATUS.md`:
`uniform_fdistmap_pointE` first, then `uniform_fdistmap_fiberTE` and
`fdistmap_prod_sectionE`, into `reconstruct/design_privacy.v`, with
`uniform_fdistmap_fiberE` re-proved through the point lemma; `inde_RV_fdistmap`
and the `dealer_shuffle*` block into `reconstruct/transitivity_privacy.v`. Any
such edit invalidates the `.vo` chain up to `psl211_endpoints` (about 900 s and
17 GB), and `instances/psl211/psl211_endpoints.v` is already newer than its
`.vo` since commit c9634fd. Never run `make` in the production tree for this
work; compile single files with the command in `STATUS.md`.

Two gaps in what the instances exercise: the guard `secretP s != 0` is never
used non-trivially, since every instance has the uniform prior on a bit, and
only the two PGL(2,7) dealer laws depend on the secret.
