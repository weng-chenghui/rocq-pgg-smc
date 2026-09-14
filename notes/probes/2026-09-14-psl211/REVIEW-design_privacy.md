# Review record: reconstruct/design_privacy.v

Commits: f8450b3 (file, Sonnet implementer), 7453c24 (comment fixes), 1741d47
(registration in _CoqProject after reconstruct/transitivity_privacy.v).
Reviewer: one Opus agent, combined spec-compliance and code-quality review,
2026-09-14; independent compile from the repo root with the project flags
(exit 0, 4.07 s, only the repo-wide `_ <| _` notation-prefix warning).

## Statement surface

The file is notes/probes/2026-09-14-psl211/probe_bridge.v lines 25-130 (the
probe the plan audit compiled, `audit-plan/chk_bridge.v`, rc 0) with four
renames: `uniform_fdistmap_of_fibres -> uniform_fdistmap_fiberE`,
`colour_view_indep_of_laws -> colour_view_indep_laws`,
`colour_view_indep_of_fibres -> colour_view_indep_fibers`, `fibre -> fiber`.
Comment-stripped, whitespace-normalised diff against the probe: zero
differences. Exported: `uniform_fdistmap_fiberE` (equal fiber cardinalities
over a set give equal pushforwards of the uniform law on it), `colour_view`,
`colour_law`, `colour_view_indep_laws`, `colour_view_indep_fibers`. The
probe's `orbit_fibre_card` (ledger L10, superseded by mathcomp `amove_act`)
and its tautology and toy sections are correctly absent. No `Local` on any
name Task 7 consumes; `About` from an external file resolves all five to
`pgg_reconstruct.design_privacy.*`.

## Print Assumptions

`uniform_fdistmap_fiberE`, `colour_view_indep_laws`,
`colour_view_indep_fibers`: each exactly `boolp.propositional_extensionality`,
`boolp.functional_extensionality_dep`,
`boolp.constructive_indefinite_description`, the floor of
reconstruct/transitivity_privacy.v (`inde_prod_fst`, `ttrans_view_indep_gen`
report the same three). No Admitted, Abort or Axiom in the file.

## Comment rule findings, all applied in 7453c24

1. `colour_view`: the pad value `false` outside the coalition is also a real
   colour value; the comment now says why the collision is harmless (C is
   fixed in the statement, so those coordinates do not vary with the sample).
2. `colour_law`: now states that the uniform-shuffle assumption enters the
   bridge exactly here (the pushforward of `` `U card_G_gt0 ``).
3. `colour_view_indep_fibers`: "equal fiber counts of the two encodings" was
   type-dishonest (the fibers counted are those of the view over the group,
   not of `encode`); rewritten as "equal counts, under the two secrets, of
   the group elements producing each view value".
4. Header: the sentence making the transitivity bridge a formal special case
   of this one was an informal relation (the transitivity bridge is proved on
   its own, not through this file); marked as such.
   Header box lines re-padded to 80 columns.

Recorded as minor and not applied: the naming precedent
`fdistmap_uniform_fiberE` (head-symbol first) versus the plan-pinned
`uniform_fdistmap_fiberE`, and the copied-from-the-sibling import block
(eight of nine mathcomp tokens droppable; kept for parity with
transitivity_privacy.v). Verdict: spec compliant, approved with minor fixes,
fixes applied.
