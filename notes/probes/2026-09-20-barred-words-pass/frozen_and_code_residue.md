# What the barred-words pass could not touch (for the owner's reminder, tracker 2.6d)

Frozen (forward closure of `instances/psl211/psl211_endpoints.v`), comments:

- `reconstruct/algebraic_rigidity.v:125`: the norm abbreviation in its caret
  spelling ("un-halved ... var_dist convention; 1/2 in standard TV").
- `reconstruct/algebraic_rigidity.v:155`: field comment of `sw_bound_eps`
  ("the stated full-... upper bound on one endpoint marginal"). Suggested:
  "sw_bound_eps is the stated upper bound on one endpoint marginal, in the sum
  of absolute differences with no factor one half."

Code identifiers that spell the abbreviation as two WORD LENGTHS (list
variables or length variables named with a capital letter and the digits one
and two), with the comments that mirror them:

- editable: `security/pgg_schreier.v` (9 code uses, comments at 59, 60, 376,
  394), `security/pgg_schreier_weighted.v` (6 code uses, comment at 202),
  `instances/pgl27/pgl27_orbit.v` (9), `instances/psl211/psl211_alldecks.v` (6);
  a lemma name with that suffix in `instances/s5/pgg_raag_s5.v:59` and
  `instances/s5/rigidity_s5_instance.v:31`.
- frozen: `instances/psl211/psl211_orbit.v` (8), and lower-case variants in
  `reconstruct/transitivity_privacy.v` (3), `smc/smc_interpreter.v` (5).

Renaming them changes code tokens and proof scripts; it is the owner's call.
