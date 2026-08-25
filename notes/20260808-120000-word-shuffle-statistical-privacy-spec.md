# Word-shuffle statistical privacy: probe-first spec

Date: 2026-08-08
Status: POST-PROBE, POST-AUDIT (two rounds). All ledger rows resolved.
All five declarations compile in one unit, axiom-clean. Ready for a plan.
Skill: `rocq-probe-first-spec`

Evidence base: three concurrent agents in round one (probe build, soundness
audit, naming audit), one adversarial re-audit of the revised spec in round two,
plus two direct compiles by the orchestrator to adjudicate inter-agent
conflicts. Round two compiled a consolidated candidate file, exit 0.

## Problem

The PGL(2,7) instance proves **perfect** coalition privacy under the uniform
shuffle law `U_G` (`pgl27_view_indep`, `pgl27_coalition_trace_secrecy`), and a
**mixing bound** under the 200-letter word law (`pgl27_word_mixing`,
`pgl27_endpoint_mixing`, `pgl27_joint_mixing`). No theorem connects them.

The paper's conclusion calls the missing piece "a separate two-model security
result" (`main.tex`, in the conclusion; the working tree is dirty so line
numbers drift). The body says the development "stops before a theorem about
approximate coalition-view privacy" and needs "a separate argument that
transports distributional proximity through the coalition view and the
interpreter".

## The four theorems

All compile. Proof scripts in the "Verbatim compiled source" section below.

| # | Name | Statement | Bound |
|---|---|---|---|
| 1 | `pgl27_word_run_recovers` | decoding the executed endpoints returns `s`, for every 200-letter word | exact, probability one |
| 2 | `pgl27_word_view_indist` | two secrets give coalition-view laws this close | `2^-39` |
| 3 | `pgl27_word_trace_indist` | the same for the executed coalition trace | `2^-39` |
| 4 | `pgl27_view_mixing` | the joint law is this close to the ideal independent execution | `2^-40` |

Theorem 2 is the **primary** result: it is the textbook secret-sharing
statistical-privacy definition, and it is prior-free. Theorem 4 is a secondary
form and must **not** be labelled as the privacy definition; it implies theorem 2
only at `4 eps = 2^-38`, which is worse than proving theorem 2 directly.

Supporting helper, also compiled: `pgl27_view_cond_law`, about 30 lines.

```coq
Notation pgl27_Msym := (Gen_PGGTypes pgl27_sym_sigmas).

Definition rho_word : R.-fdist (pgg_gT pgl27_M) :=
  @rho_from_words_weighted R 6 4 200 pgl27_sym_sigmas (Wuni R).

Definition pgl27P_word : R.-fdist (bool * pgg_gT pgl27_M)%type :=
  (fdist_uniform card_bool) `x rho_word.
```

## Connection to the executed chain

### Joint 1: the word substitutes into the run

`pgl27_procs s w0` takes a **concrete group element**, so running at
`w0 := @word_eval pgl27_Msym 200 w` is a substitution. There is nothing to
prove at the process level.

Correctness then follows for every word, at probability one, because
`pgl27_run_recovers` has the single hypothesis `w0 \in pgg_G pgl27_M`. The
discharge route is narrow and must be written out in the plan:

- `word_eval_in_G` is a `Local Lemma` (`pgl27_mixing.v:742`). Its short name is
  not reachable; `pgl27_mixing.word_eval_in_G` is.
- Its statement is about `pgl27_mixing.weval`, itself a `Local Definition`
  (`:516`), **not** about `word_eval`.
- The bridge `@word_eval pgl27_Msym 200 w = pgl27_mixing.weval w` closes
  **`by []`**, after which `exact: pgl27_mixing.word_eval_in_G` discharges the
  membership.

The plan must never write `word_eval_in_G` unqualified.

**Withdrawn: the `exchange_dealer_from_words` mechanism.** An earlier revision of
this spec claimed that `exchange_dealer_from_words` (`card_exchange_pismc.v:285`)
makes "running on a word" and "running at `word_eval w`" the same term at pgl27.
It does not instantiate at pgl27 at all. That definition is typed at
`Tg := (@pgg_ngens' M).+1`, and by compiled `erefl`,
`(@pgg_ngens' pgl27_M).+1 = 3` while
`(@pgg_ngens' (Gen_PGGTypes pgl27_sym_sigmas)).+1 = 5`. The 200-letter word is
over the 5-letter symmetrized alphabet, so
`Fail Check (fun w : 200.-tuple 'I_5 => exchange_dealer_from_words pgl27_PI 200
pgl27_players w 0)` **passes**, while the same at `200.-tuple 'I_3` typechecks as
a positive control. No `PGGInterface (Gen_PGGTypes pgl27_sym_sigmas)` exists in
the repo. Theorem 1 never used that mechanism and is unaffected.

Root cause worth carrying: **`T` is overloaded in the protocol layer.** In
`pgg_interface.v:518` a local `Let T := m.+1` counts generators, while
`card_exchange_pismc.v:277-278` has `Let T := (pi_T' PI).+1` for players
alongside `Let Tg := (@pgg_ngens' M).+1` for generators. For pgl27: N = 8, eight
players, three generators, five symmetrized letters.

### Joint 2: swap the law under unchanged random variables

The trace and view random variables are plain functions `bool * gT -> ...`;
`{RV P -> T}` carries `P` only as a phantom (row C7). The law changes from
`pgl27P` to `pgl27P_word` with **no change to any function body**. Only the
conclusion shape changes, from an equality to a variation distance.

### The interpreter never sees a word

```coq
rho_from_words_weighted := fdistmap (@word_eval M L) word_weighted
```

`word_weighted` is the product law of `L` independent letters. The 200 dice
throws are already inside `rho_word`; the interpreter receives only the product.

### Modelling assumption to state in the paper

The dealer performs 200 physical moves and the model exposes only their product.
This is **structurally forced**, not a simplification chosen here:
`exchange_dealer`'s argument `W : seq gT` is a list of *alternative* cuts, since
`dealt_hand_content content W i = [seq content (rho w (tnth starts i)) | w <- W]`
(`card_exchange_pismc.v:200`). A 200-element `W` would model 200 **parallel**
deals, not a 200-step composition. The formal witness is
`pgl27_dealer_run` (`pgl27_run.v:66`), whose cut slot is the singleton
`[:: w0]`.

The exact model already makes the same assumption, since one atomic uniform
shuffle is likewise unobserved. It becomes conspicuous under the word law
because the 200 moves genuinely happen. State it in the security-model section.

### The exact chain it plugs into is verified

Reproduced independently by the orchestrator and by the round-two audit:

| Object | `Print Assumptions` |
|---|---|
| `pgl27_run_recovers` | **Closed under the global context** (zero axioms) |
| `pgl27_coalition_trace_E` | boolp trio only |
| `pgl27_coalition_trace_secrecy` | boolp trio only |

`pgl27_player_trace` (`pgl27_trace.v:318`) is *defined* as a projection of
`run_interp` output. `pgl27_procs_abs` (`:251`) proves
`pgl27_procs s w0 = pgl27_aprocs_abs (tnth (orbit_encode s)) w0` **`by []`**, so
the abstract-leaf technique names the readout function rather than substituting a
simplified model. Leaf lemmas are `vm_compute; reflexivity. Qed.` `Admitted`,
`Axiom`, and `Hypothesis` are absent from `pgl27_run.v`, `pgl27_trace.v`, and
`pgg_trace_secrecy.v`.

### Why this was never done

Three work streams that never met, per `git log`:

- `rho_from_words_weighted` was born in `31be3cb`, whose message reads verbatim
  "Part of weighted generator extension for Kim & Cetinkaya (2511.05111)
  formalization within PGG framework". It is mixing infrastructure built for a
  different instance. `pgg_weighted_words.v` has four commits, three of them
  mixing and one a comment pass.
- `exchange_dealer_from_words` has exactly one user,
  `instances/star/rigidity_star_instance.v:251`. Star is out of scope and that
  file is not in `_CoqProject`.
- The trace-bridge **results** in the `d67f4f1`..`ee2073f` arc are all on the
  exact law, though the arc itself also contains realistic-shuffle mixing
  commits. `ee2073f` names its own goal as filling "the last three
  **exact-shuffle** claim-matrix cells".

Decisive: `pgl27_mixing.v` was **created** in `caf3604` (2026-07-13 17:37), a
descendant of `ee2073f` (2026-07-13 09:47) per `git merge-base --is-ancestor`.
The word-shuffle column did not exist when the claim matrix closed. The absence
is a history artifact, not a design boundary.

## Pinned carrier

```
R : realType                              (* section variable, not a concrete field *)
gT := pgg_gT pgl27_M                       (* = {perm 'I_8}, by erefl *)
Omega := (bool * gT)%type
Pexact := pgl27P
Pword  := pgl27P_word
```

`pgl27_M` is a Notation for `@Gen_PGGTypes 2 6 pgl27_gens` (`pgl27_group.v:100`).
`Gen_PGGTypes` sets `gT := {perm 'I_n.+2}` (`pgg_interface.v:519-520`, definition
at `:542`). Compiled: `(pgg_N' pgl27_M).+1 = 8` and `(pi_T' pgl27_PI).+1 = 8`,
both by `erefl`.

**`Wuni` takes its `realType` explicitly** after section discharge:
`Wuni : forall R : realType, {fdist 'I_5}`. Bare `Wuni` does not elaborate,
confirmed by a passing `Fail`. Every occurrence must read `(Wuni R)`.

## Claim ledger, resolved

| # | Claim | Verdict | Evidence |
|---|---|---|---|
| C1 | carrier alignment | **GO, definitional** | `pgg_gT pgl27_M = {perm 'I_8} :> Type` by `erefl` |
| C2 | `Wuni`, `pgl27_sym_sigmas` exported | **GO with spelling fix** | plain `Definition`s at `pgl27_mixing.v:791,58`; write `(Wuni R)` |
| C3 | `pgl27_joint_mixing` exported | **GO** | `pgl27_mixing.v:937`, as cited |
| C4 | `pgl27P` convertible to the product | **GO, no rewriting** | `exact: (pgl27_joint_mixing (fdist_uniform card_bool))` closes it |
| C5 | DPI at the pair map | **GO** | `var_dist_fdistmap` needs nothing of the map; `pgg_rho` is `gen_incl_morph` |
| C6 | "no such lemma in infotheo" | **NO-GO, row was false** | `inde_dist_of_RV2` exists at `probability/proba.v:2715` and is used in theorem 4. Zero new library lemmas needed. `Search "inde_RV" "prod"` misses it; `Search (dist_of_RV [% _, _]).` finds it |
| C7 | RV reuse against the word law | **GO** | `` `p_ (pgl27_view R C) = fdistmap (pgl27_view R C) (pgl27P R) `` closes `by []`; the same against `pgl27P_word` does not. Phantom resolution confirmed both ways |
| C8 | composition | **GO** | all five declarations compile as one unit, exit 0 |
| C9 | non-vacuous | **GO** | concrete `C` with `#|C| = 3`, headline instantiable at it |
| C10 | not a definitional triviality | **GO** | `Fail exact: lexx` passes. The `Fail reflexivity` test is worthless here; its message concerns the `is_true` coercion |
| C11 | conditional (textbook) form | **GO, promoted to primary** | prior-free statement, better constant, no internals touched |

## Soundness invariants

- **No new axiom.** Theorem 1 is closed under the global context. The other four
  declarations list exactly the boolp trio.
- **No distributional-equality claim.** All four are inequalities except
  theorem 1, which is an equality about a decoded value, not about laws.
- **Theorem 4 is not the privacy definition.** Label it ideal-proximity.
- **Which marginals.** Only the view marginal is at issue. Compiled:
  `` `p_ (pgl27_secret R) = fdist_uniform card_bool `` and
  `fdistmap fst pgl27P_word = fdist_uniform card_bool`, both via `fdist_prod1`.
- **Only the product of the 200 moves is observed.** Structurally forced by the
  parallel-alternatives reading of `W : seq gT`; witness is `pgl27_dealer_run`
  (`pgl27_run.v:66`). Must appear in the paper's security-model section.
- **Correctness is not approximated.** Theorem 1 holds for every `w`,
  unconditionally. Only privacy carries an epsilon.
- **Fixed-representative deck, and no theorem escapes it.** All four go through
  `orbit_encode` or `ts_encode orbit_scheme`. `pgl27_view_indep_alldecks` uses
  `alldecksP` and `pgl27_view_indep_deck_prior` uses `uniform_deckP`
  (`pgl27_secrecy.v:213,230`), genuinely different sample spaces that
  `pgl27_joint_mixing` cannot reach at its `bool * gT` type.
- **Scope.** Passive adversaries. Coalitions of at most three positions. Single
  execution, no composition. The verifier learns the secret by design
  (`pgl27_secrecy.v:29-30`, verbatim correct). Unhalved `L_1`, so `2^-39`
  unhalved reads as `2^-40` halved.
- **Cited objects.** `var_dist_fdistmap` `pgg_collusion_bound.v:73`;
  `var_dist_triangle` same file `:44`; `symmetric_var_dist`
  `probability/variation_dist.v:37` (**load-bearing**, was previously uncited);
  `splitr` from mathcomp-analysis; `inde_dist_of_RV2` `probability/proba.v:2715`;
  `pgl27_joint_mixing` `pgl27_mixing.v:937`; `pgl27P`:60,
  `pgl27_secret`:65, `pgl27_view`:70, `pgl27_view_indep`:77, all in
  `pgl27_secrecy.v`.

## Verbatim compiled source

Copy these into the plan unchanged. Round two compiled them as one unit, exit 0.

```coq
Corollary pgl27_word_run_recovers (s : bool) (w : 200.-tuple 'I_5) : ... = s.
Proof. apply: pgl27_run_recovers; exact: pgl27_mixing.word_eval_in_G. Qed.
```

```coq
Lemma pgl27_view_cond_law (C : {set 'I_8}) (s : bool) : (#|C| <= 3)%N ->
  fdistmap (fun g : pgg_gT pgl27_M => pgl27_view R C (s, g)) (`U pgl27_G_pos)
  = `p_ (pgl27_view R C).
Proof.
move=> HC; have Hind := pgl27_view_indep R HC.
apply: fdist_ext => x.
have Hjoint : `Pr[ [% pgl27_view R C, pgl27_secret R] = (x, s) ]
  = (fdist_uniform card_bool) s
    * fdistmap (fun g : pgg_gT pgl27_M => pgl27_view R C (s, g))
        (`U pgl27_G_pos) x.
  rewrite pfwd1E /Pr.
  under eq_bigl => ab do rewrite inE /= xpair_eqE.
  rewrite (eq_bigr (fun ab : bool * pgg_gT pgl27_M =>
    (fdist_uniform card_bool) ab.1 * (`U pgl27_G_pos) ab.2)); last first.
    by move=> ab _; rewrite /pgl27P fdist_prodE.
  rewrite (reindex_onto (fun g : pgg_gT pgl27_M => (s, g)) (fun i => i.2));
    last by move=> [b g] /= /andP[_ /eqP ->].
  under eq_bigl => g do rewrite /= !eqxx !andbT.
  rewrite (eq_bigr (fun g : pgg_gT pgl27_M =>
    (fdist_uniform card_bool) s * (`U pgl27_G_pos) g)); last by [].
  by rewrite -big_distrr /= fdistmapE.
have Hsec : `Pr[ (pgl27_secret R) = s ] = (fdist_uniform card_bool) s.
  rewrite pfwd1E.
  have -> : finset (preim (pgl27_secret R) (pred1 s))
          = (finset (preim (@id bool) (pred1 s)) `*T).
    by apply/setP => -[b g]; rewrite !inE.
  rewrite -Pr_fdist_fst fdist_prod1.
  have -> : finset (preim (@id bool) (pred1 s)) = [set s].
    by apply/setP => y; rewrite !inE.
  by rewrite Pr_set1.
move: (Hind x s); rewrite Hjoint Hsec dist_of_RVE => Heq.
apply: (mulfI (_ : (fdist_uniform card_bool) s != 0)).
  by rewrite fdist_uniformE card_bool invr_neq0// pnatr_eq0.
by rewrite Heq mulrC.
Qed.
```

```coq
Let pow2_split : (2%:R : R)^-40 + 2%:R^-40 = 2%:R^-39.
Proof. by rewrite [RHS]splitr exprSr invfM. Qed.

Theorem pgl27_word_view_indist (C : {set 'I_8}) (s s' : bool) : (#|C| <= 3)%N ->
  var_dist (fdistmap (fun g => pgl27_view R C (s, g)) rho_word)
           (fdistmap (fun g => pgl27_view R C (s', g)) rho_word) <= 2%:R^-39.
Proof.
move=> HC.
apply: (Order.POrderTheory.le_trans (var_dist_triangle _
  (fdistmap (fun g => pgl27_view R C (s, g)) (`U pgl27_G_pos)) _)).
rewrite -pow2_split; apply: lerD.
- apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
  exact: pgl27_word_mixing.
- rewrite (pgl27_view_cond_law (C:=C) s HC) -(pgl27_view_cond_law (C:=C) s' HC).
  rewrite symmetric_var_dist.
  apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
  exact: pgl27_word_mixing.
Qed.

Theorem pgl27_word_trace_indist (C : {set 'I_8}) (s s' : bool) : (#|C| <= 3)%N -> ...
Proof. by rewrite (pgl27_coalition_trace_E R C); exact: pgl27_word_view_indist. Qed.

Theorem pgl27_view_mixing (C : {set 'I_8}) : (#|C| <= 3)%N -> ... <= 2%:R^-40.
Proof.
move=> HC; rewrite -(inde_dist_of_RV2 (pgl27_view_indep R HC)).
apply: (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _)).
exact: (pgl27_joint_mixing (fdist_uniform card_bool)).
Qed.
```

### Traps the plan must carry

- `` `Pr[ X = a ] `` rejects an applied head. `` `Pr[ pgl27_secret R = s ] `` is a
  syntax error; write `` `Pr[ (pgl27_secret R) = s ] ``.
- `C` is implicit in `pgl27_view_cond_law` under `Set Implicit Arguments`; call it
  `pgl27_view_cond_law (C:=C) s HC`.
- `2^-40 + 2^-40 = 2^-39` must go through `splitr`. Hand-rolled routes via
  `mulr_natl`/`mulr_natr` fail, because the ring numeral `2` is itself a `natmul`
  and the rewrite fires inside it, yielding `(2 * 1) ^- 40`.
- The route description "the middle term collapses to zero" is **wrong** and was
  removed. Leg two identifies the two uniform-law pushforwards via
  `pgl27_view_cond_law` at both `s` and `s'`, then applies
  `symmetric_var_dist`, then DPI and mixing.

## Naming and placement

| Object | Name | H-series tag |
|---|---|---|
| word shuffle law | `rho_word` | `@intent:` |
| word-law sample space | `pgl27P_word` | `@intent:` |
| conditional-law helper | `pgl27_view_cond_law` | `@composes: pgl27_word_view_indist` |
| correctness under the word law | `pgl27_word_run_recovers` | `@main correctness:` |
| primary headline | `pgl27_word_view_indist` | `@main security:` |
| trace form | `pgl27_word_trace_indist` | `@main security:` |
| secondary joint form | `pgl27_view_mixing` | `@main bound:` |

An earlier revision called the secondary form `pgl27_view_mixing` in the naming
table and `pgl27_word_statistical_privacy` in the code block. `pgl27_view_mixing`
wins: it joins the `_mixing` family whose slot names the observable, with `word`
for the group law, `endpoint` for one card, `joint` for secret-and-shuffle, and
`view` for the coalition view.

`_indep` is rejected because the invariants forbid phrasing any result as
independence. `_privacy` is rejected because no lemma in the repo uses that
suffix. All seven names return zero grep hits repo-wide and pass I001. H001/H002
gate at error severity, so every declaration needs its tag before commit.

**Placement.** The consolidated file compiles as one unit, so a single
`pgg-smc/instances/pgl27/pgl27_word_privacy.v` after `pgl27_mixing.v` in
`_CoqProject` is viable. Optional split: put theorem 1 in `pgl27_word_run.v` and
keep `pgl27_word_privacy.v` purely probabilistic, since theorem 1 alone drags in
`card_exchange_pismc`, `pgg_input_commitment`, `pgg_run`, `smc_interpreter`,
`pismc`, and `smc_session_types`. `pgl27_secrecy.v` cannot host any of it: it is
`_CoqProject:252` and `pgl27_mixing.v` is `:255`.

## Real hazards

- **`Local` declarations in `pgl27_mixing.v`.** `word_eval_in_G` (`:742`),
  `weval` (`:516`), and `var_dist_prodR` (`:920`) are all `Local`. Short names are
  blocked; fully qualified names resolve. Adjudicated by direct compile:
  `Fail Check var_dist_prodR` passes while `Check pgl27_mixing.var_dist_prodR`
  prints a type. Two separate agents asserted these were unreachable without
  testing the qualified name.
- **`ttrans_view_indep_gen`** (`reconstruct/transitivity_privacy.v:619`) proves
  the conditional-law fact internally but exports only the `inde_RV` conclusion;
  the witness is a `pose`d local. Re-deriving downstream is the right call.
  `inde_prod_fst` (`:62`) is an exported lemma stating the converse, and its
  `reindex_onto` idiom at `:76-80` is what `pgl27_view_cond_law` reuses.
- **Stale `.vo`.** Round one lost time to `pgl27_mixing.vo` being stale. Rocq
  validates by **library digest, not mtime**, so a timestamp check is neither
  necessary nor sound as a gate. Correct check: compile a one-line probe file
  that `Require`s the full import set. Diagnostic signature of staleness is a
  `Require` that succeeds while every name in the module reports "not found";
  rocq-mcp masks the real cause and only the CLI reports "makes inconsistent
  assumptions over library".

## Residual risk

- **The prior-free derivation.** The *statement* of `pgl27_view_cond_law` is
  prior-free, but the only compiled proof runs through `pgl27_view_indep`, which
  is fixed at the uniform Boolean prior, and the cancellation step needs
  `(fdist_uniform card_bool) s != 0`. Not unsound, since the conclusion mentions
  no prior. A reviewer asking "is this prior-free" gets yes about the theorem and
  no about the derivation. `ttrans_view_indep_gen` is generic over `secretP`, so
  a fully prior-free derivation exists if wanted. Not attempted.
- **`var_dist_fdistmap` carries an in-source warning** (`pgg_collusion_bound.v:66-72`)
  that DPI "should NOT be used to derive endpoint bounds from group-level
  spectral analysis". Judged non-binding here because `pgl27_word_mixing` is an
  exact counting certificate rather than a spectral bound, so there is no
  `sqrt(|G|)` blowup. Not independently verified. If the paper presents `2^-39`
  as tight, this deserves a sentence.
- **H-series tags** have not been run through the audit pipeline against the
  candidate file.
- **Paper line numbers** drift; `main.tex` is dirty in the working tree.

## Round three: two strengthenings, both landed

Executed by a probe agent, both GO. Final source lives in the plan,
`20260808-140000-word-shuffle-statistical-privacy-plan.md`. Corrections below
supersede the corresponding rows above.

### The helper is now prior-free in the derivation, not only in the statement

Route 2 landed on the first attempt, direct from `pgl27_3transitive` via
**`ktuple_encode_uniform`** (`transitivity_privacy.v:536`), the exported k-tuple
entry point that `ttrans_view_indep_gen` itself calls. `ttrans_point_uniform`,
which an earlier revision cited, is the single-point lemma and is the wrong
tool.

`pgl27_view_indep`, `Pr`, `dist_of_RVE`, `mulfI`, and the `!= 0` side condition
are all gone from the derivation, confirmed by grep over the landed file. Cost
is about twelve extra lines. **The residual-risk row "the prior-free derivation
… Not attempted" is resolved and deleted, not softened.**

### The helper is split into a named base and a corollary

Two persistent `Definition`s name the sides, so the statement says what it is
about. `Let` was rejected: a section-level `Let` is discharged and expanded at
section close, so the exported statement would lose the names.

Polarity confirmed from source: `equianharmonic l := (l == 3) || (l == 5)`
(`pgl27_orbit.v:75`), `subset_class` is the equianharmonic verdict (`:104`),
`orbit_class_split` gives 28 (`:517`) against 42 (`:528`). With `orbit_encodeK`,
`true` is equianharmonic and `false` is harmonic.

### Non-triviality: three independent witnesses

The concern that `forall s s', F s = F s'` might be a tautology is closed.

1. **Not convertible.** Four `Fail Check (erefl : ...)` probes all pass,
   including at a concrete three-position coalition where the lemma is *true*.
   The fdist equality holds but is not a conversion.
2. **The hypothesis is consumed.** Dropping `#|C| <= 3` breaks the proof at
   `have Hk : (k <= 3)%N by rewrite /k -cardE` with "No applicable tactic".
   Instantiating at a four-position coalition leaves the residual goal
   `(4%R <= 3)%N`.
3. **The conclusion is FALSE at four positions**, and this is proved, not merely
   unproved. `law_classes_false_k4` is a `Qed`'d refutation via `inde_prod_fst`
   and `inde_RV_sym` against `pgl27_view_dep_k4` (`pgl27_secrecy.v:112`).

Also: `Fail (by move=> HC; case: s; case: s')` passes, so the corollary's case
split does not close on its own. The base lemma is genuinely consumed.

### The joint form is now generic over the Boolean prior

`pgl27_view_indep_gen` instantiates `ttrans_view_indep_gen` at an arbitrary
`secretP`, and `pgl27_view_mixing` follows in three lines. **No `secretP s != 0`
is needed anywhere**, because nothing conditions on the secret.

`pgl27P_word` is dead and was dropped; it is `pgl27P_word_gen (fdist_uniform
card_bool)`. The naming table's row for it is replaced by `pgl27P_gen` and
`pgl27P_word_gen`.

### Seven new traps, all paid for

1. **`R.-fdist` ascription is mandatory.** Once both sides of the helper are
   `` `U pgl27_G_pos ``, nothing pins `R` and elaboration fails with "Cannot
   infer the implicit parameter R of fdistmap". Write
   `` (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M)) `` at both occurrences.
2. **`` `p_ `` at a non-uniform prior is a silent-wrong-statement hazard.** It
   is not a type error and it prints identically; the phantom resolves to
   `pgl27P R`, the uniform prior. The failure surfaces only as a later rewrite
   mismatch. Use explicit `fdistmap` in the generic statement.
3. **`` `x `` binds tighter than application.** `` fdistmap f P `x fdistmap g Q ``
   is a parse error. Parenthesise both factors.
4. **`ktuple_encode_uniform` drops `secretP` on discharge.** Explicit argument
   order is `N' gT G rho t Htrans R HG encode k p b Hdt Hk Hub Hp`; the
   named-argument spelling fails with "Wrong argument name HG".
5. **`vm_compute` on a set-comprehension cardinality over `'I_8` explodes**,
   unfolding the whole `Finite` instance into a 170 KB goal. Use an
   explicit-elements set with `-setUA !cardsU1 !inE cards1`.
6. `` `Pr[ X = a ] `` rejects an applied head; write `` `Pr[ (pgl27_secret R) = s ] ``.
7. `2^-40 + 2^-40 = 2^-39` must go via `splitr`.

### One open decision, settled in the plan

`pgl27_view_indep` (`pgl27_secrecy.v:77`) is a second unnecessary specialisation,
exactly parallel to the old theorem 4. The plan keeps it untouched rather than
retiring it.

## Still out of scope

- **Entropy form** `|H(S | V_C) - H(S)| <= eps`. Because the secret is one bit at
  a uniform prior, only a quantitative modulus for `H_2` near one half is needed,
  not general Fannes-Audenaert. `lib/binary_entropy_function.v:142` has
  qualitative `continuous_H2` but no modulus. Grep-verified: no `Fannes` or
  `Audenaert` in any `.v`.
- **All-decks and shuffle-free dealers under the word law.** Different sample
  spaces; needs a new mixing statement at those types.
- **Channel duality for pgl27.** `channels_dual` is proven only for the 2-player
  test configuration in `card_exchange_pismc.v`, not for pgl27's ten processes.
  Session *typing* is carried by the `sproc` type ascription and is free.
