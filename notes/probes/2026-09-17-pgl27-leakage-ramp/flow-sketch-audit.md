# Flow-sketch audit 2: the new lines of `2026-09-17-pgl27-entropy-completion.md`

Read-only audit. Subject: the lines `step rep -> orbit`, `join |C| <= 3`,
`join |C| = 8`, `final`, `post`, and the size-seven representative. The first
five lines were audited in `notes/probes/2026-09-15-pgl27-view-entropy/flow-sketch-audit.md`.

Every "compiled" claim below was checked with `rocq compile` against the
installed `.vo` files, under the `-R` flags of `Makefile.rocq.conf`. The scratch
files are in
`/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc/2477f90e-ff86-442c-893f-7f5043718ae4/scratchpad/aud/`:
`q1_transport.v`, `q2_local.v`, `q345.v`, `q6_seven.v`, `q7.v`, `q8_final.v`.
Nothing in the repository was written, and no `make` was run.

## Findings

| # | Question | Verdict | Evidence | Required fix |
|---|---|---|---|---|
| Q1a | Transport statement true? | **FIX (statement), GO (mathematics)** | Proved and compiled generically as `coalition_view_transport` in `aud/q1_transport.v`, `Print Assumptions` = the three `boolp` axioms only. The true form is the FORWARD image under `rho g`, for `g \in G`. `g @: C` does not typecheck in `Section transitivity_privacy_gen` because `gT` is an abstract `finGroupType`. | Write `rho g @: C` (identical to `[set rho g x | x in C]`). Drop `t` and `rhoG_ntrans` from the new file: the transport needs neither. |
| Q1b | `pgl27_view` convertible with `coalition_view`? | **GO** | `pgl27_secrecy.v:98-106` proves `pgl27_view_leakage_le` by `exact: (@coalition_view_mutual_info_le ...)`. Independently, `aud/q345.v` closes `pgl27_view_transport` by a single `exact:` on the generic theorem, with `g @: C` (not `rho g @: C`) in the statement. | none |
| Q1c | Existing supporting lemmas | **FIX** | Only `view_mutual_info_le` (`reconstruct/transitivity_privacy.v:562`) is directly reusable. No lemma exists for injective post-processing preserving `I`, for support-restricted `fdistmap` congruence, or for translation invariance of the product law. | Three small helpers, all compiled in `aud/q1_transport.v`: `fdistmap_eq_supp`, `mutual_info_RV_inj`, `P_transl`. |
| Q2 | Orbit lemma statements; size seven | **GO** | Statements confirmed verbatim below. Same `g @: S` action as Q1's true form. Size seven: the `pgl27_six_subset_orbit` pattern works from 1-transitivity, obtained by `ntransitive_weak (isT : (1 <= 3)%N) pgl27_3transitive`; compiled as `q2_seven_subset_orbit` in `aud/q2_local.v`, `Print Assumptions` = closed under the global context. | There is no `pgl27_1transitive`; only `pgl27_2transitive` (`instances/pgl27/pgl27_recovery.v:78-80`). Inline the `ntransitive_weak` call. See the Local-helper note below. |
| Q3 | Representatives as sets | **GO** | `aud/q345.v` compiles `#\|pgl27_code_coalition rep_five\| = 5` (and 4, 4, 6, 7 for the others), `pgl27_code_coalition rep_harmonic = pgl27_leak_coalition`, `subset_class (pgl27_code_coalition rep_harmonic) = false`, `subset_class (pgl27_code_coalition rep_equianharmonic) = true`. Class values are the right way round, see the cross-check below. | Cardinalities by `-sum1dep_card big_mkcond` + eight `big_ord_recl`, exactly as `pgl27_view_dep_k4` does. Class values by the `heart_set` route, NOT by computation: `Fail by vm_compute` and `Fail by native_compute` both succeed on `subset_class (pgl27_code_coalition rep_harmonic) = false` (checked in `aud/q345.v`). |
| Q4 | `indep -> I = 0` | **GO** | `inde_cond_entropy` (`lib/proba_entropy_ext.v:561-571`) plus `mutual_info_RVE` (infotheo `information_theory/entropy.v:989`). Compiled as `q4_zero` in `aud/q345.v`. | Argument order already matches `pgl27_view_indep`; no symmetry lemma is needed. infotheo has only the converse, `mutual_info_RV0_indep` (`entropy.v:959`). |
| Q5 | `I <= H X`, `H(uniform bool) = 1`, 7-subsets | **GO** | `q5_le_entropy`, `q5_entropy_bool`, `q5_seven_sub` in `aud/q345.v`; `q7_secret_uniform` in `aud/q7.v`; `fin8` in `aud/q8_final.v`. | `I(X;Y) <= H \`p_X` is not a named lemma; one line from `mutual_info_RVE` + `centropy_RV_ge0` (`entropy.v:456`). `H (uniform bool) = 1` from `entropy_uniform` (`entropy.v:108`) + `card_bool` + `realType_ln.log2`, the same combination used inside `mutual_info_binary_ambiguityE`. `\`p_(pgl27_secret R) = fdist_uniform card_bool` is three lines from `fdist_prod1`. |
| Q6 | Size-seven view lists unique | **GO** | `aud/q6_seven.v` compiles `uniq (code_views false rep_seven) && uniq (code_views true rep_seven)` by `vm_compute`, and `pgl27_collisions rep_seven = 0`, and `size (code_views false rep_seven) = 336`. The eight-position analogues are also true. | none |
| Q7 | Items outside the flow; wrong names | **FIX** | Eight items, listed below. | see below |

## Q1 in detail

### The identity that makes it true

`coalition_view` (`reconstruct/transitivity_privacy.v:493-497`) is

    fun u => [ffun i => if i \in C then tnth (encode u.1) (rho u.2 i) else ord0]

so position `i` of the view reads the card at `rho g i`. With `permM :
(s * t)%g x = t (s x)` (permutations act on the right) and `morphM`, for
`h, g \in G`:

    coalition_view (rho h @: C) (b, g) = psi_h (coalition_view C (b, (h * g)%g))

where `psi_h v := [ffun i => v ((rho h)^-1%g i)]` is a bijection of the
finfun space. The sample change is LEFT translation by `h` on the group
coordinate, which preserves `P = secretP \`x (\`U card_G_gt0)` because `h \in G`
and `G` is a group. So the joint law of `(dealt_secret, coalition_view (rho h @: C))`
equals the joint law of `(dealt_secret, psi_h \`o coalition_view C)`, and `psi_h`
being cancellable leaves the mutual information fixed.

The `rho g^-1` variant is equally true, since `g` ranges over the whole group,
but the forward form is the one that composes with the orbit lemmas as they are
already written (`T = g @: S`).

### The trap

`morphM` is `{in G &, ...}`. The identity above FAILS at samples with `g \notin G`,
where `rho g` is junk. So the proof cannot be a pointwise equality of random
variables; it must be a support-restricted congruence of the pushforward. This
is the single non-obvious step, and it is why `fdistmap_eq_supp` is needed. A
plan task that assumes "rewrite the view, then apply `view_mutual_info_le`" will
stall here.

### Free strengthening

`coalition_view` and `dealt_secret` do not mention `t` or `rhoG_ntrans` (checked
with `About coalition_view`: the arguments are `N' gT G rho R secretP card_G_gt0
encode C` only). The transport therefore holds with NO transitivity hypothesis.
`reconstruct/coalition_view_transport.v` should open a section with `N'`, `gT`,
`G`, `rho`, `R`, `secretP`, `card_G_gt0`, `encode` and nothing else.

## Q2 in detail: exact statements

    (* instances/pgl27/pgl27_leakage_census.v:109 *)
    Lemma pgl27_five_subset_orbit (S T : {set 'I_8}) :
      #|S| = 5 -> #|T| = 5 ->
      exists2 g : pgg_gT pgl27_M, g \in pgg_G pgl27_M & T = g @: S.

    (* instances/pgl27/pgl27_leakage_census.v:124 *)
    Lemma pgl27_six_subset_orbit (S T : {set 'I_8}) :
      #|S| = 6 -> #|T| = 6 ->
      exists2 g : pgg_gT pgl27_M, g \in pgg_G pgl27_M & T = g @: S.

    (* instances/pgl27/pgl27_orbit.v:701 -- note: exists ... /\, not exists2 *)
    Lemma subset_class_orbit (S T : {set 'I_8}) :
      #|S| = 4 -> #|T| = 4 ->
      (subset_class S = subset_class T <->
       exists g : pgg_gT pgl27_M, g \in pgg_G pgl27_M /\ T = g @: S).

    (* instances/pgl27/pgl27_orbit.v:544 *)
    Lemma subset_class_invariant (g : pgg_gT pgl27_M) (S : {set 'I_8}) :
      g \in pgg_G pgl27_M -> subset_class (g @: S) = subset_class S.

The `g @: S` in all four is `imset` of the permutation's underlying function,
which is the same action the transport uses: `pgg_gT pgl27_M` is `{perm 'I_8}`
and `pgg_rho` is the inclusion morphism of `Gen_PGGTypes`
(`protocol/pgg_interface.v:451-458`), so

    Lemma q2_rho_id (g : pgg_gT pgl27_M) (C : {set 'I_8}) :
      (@pgg_rho pgl27_M g) @: C = g @: C.
    Proof. by []. Qed.

compiles (`aud/q2_local.v`). This is why the instance corollary can be stated
with the reader-friendly `g @: C` while the generic lemma says `rho g @: C`.

### Local-helper note

`ntransitive_subset_orbit` (`:83`), `perm_imsetC` (`:67`) and `cardsC8` (`:79`)
are `Local`. A `Fail Check ntransitive_subset_orbit` succeeds from another file,
but `Check pgl27_leakage_census.ntransitive_subset_orbit` also succeeds: the
fully qualified names are reachable. Writing `pgl27_seven_subset_orbit` in a new
file is therefore possible but ugly.

**This is now moot.** The working tree already carries
`pgl27_seven_subset_orbit` and `pgl27_seven_subset_orbitE` inside
`instances/pgl27/pgl27_leakage_census.v` (uncommitted edit, `git diff`), with
exactly the proof audited here, along with `rep_seven` and
`pgl27_views_uniq_seven`, and `pgl27_collisions_seven` restated over `rep_seven`.
See item 5 of Q7.

## Q3 in detail: the class values are the right way round

| representative | set | `subset_class` | four-subset orbit size | collisions | `I` |
|---|---|---|---|---:|---:|---|
| `rep_harmonic` | {0,1,2,3} | `false` | 42 | 96 | 5/7 |
| `rep_equianharmonic` | {0,1,2,4} | `true` | 28 | 72 | 11/14 |

Cross-checks. `orbit_class_split` (`pgl27_orbit.v:517`) gives 28 four-subsets
with `subset_class = true`; `orbit_class_split_complement` (`:527`) gives 42 with
`subset_class = false`. The census gives `pgl27_orbit_harmonic_size = 42` and
`pgl27_orbit_equianharmonic_size = 28`. The two agree, so harmonic is the
`false` fiber of size 42 and equianharmonic the `true` fiber of size 28.

Both class values are proved the same way `pgl27_view_dep_k4` proves
`subset_class pgl27_leak_coalition = false`: exhibit the coalition as
`heart_set (orbit_encode b)` by an eight-case `case: x` on the ordinal, then
apply `orbit_encodeK b`. For the equianharmonic case `orbit_encode true` is
`[tuple 0;1;2;4;3;5;6;7]`, whose heart positions are exactly {0,1,2,4}.

`pgl27_code_coalition rep_harmonic = pgl27_leak_coalition` is a one-line `setP`
plus the same eight-case split, so the `post` line's "value 5/7 at
`pgl27_leak_coalition`" follows from the harmonic representative value.

## Q7: items outside the flow, or misnamed

1. `g @: C` in the sketch's transport line is not well-typed in the generic
   section. Write `rho g @: C`.
2. The transport needs no transitivity premise. `t` and `rhoG_ntrans` should not
   appear in `reconstruct/coalition_view_transport.v`.
3. `pgl27_secret_uniform` is still `Admitted` in the probe
   (`notes/probes/2026-09-15-pgl27-view-entropy/headline_decomposition.v:26-28`).
   It is load-bearing on TWO sketch lines, not one: `eval representative` uses it
   through `mutual_info_binary_ambiguityE`, and `join |C| = 8` uses it for the
   `I <= H(secret) = 1` half. Verified provable in three lines (`q7_secret_uniform`).
4. `join |C| = 8` also consumes the size-seven value. Its true dependency is
   `pgl27_view_leakage_le` + `I <= H(secret) = 1` + `I(rep_seven) = 1`, so the
   line depends on T6 as well as on T7. The task table's `T8 depends on T7` is
   right; the sketch line hides the T6 edge.
5. `pgl27_seven_subset_orbit` has landed in `instances/pgl27/pgl27_leakage_census.v`,
   not in the new `pgl27_leakage_ramp.v` that T7 names. That contradicts the
   plan's build rule 2 and invalidates `pgl27_leakage_census.vo` and everything
   downstream of it. It also already broke this audit's scratch chain once
   ("makes inconsistent assumptions over library pgg_smc.pgl27_leakage_census").
   Either amend rule 2 and the T7 row to say the census file is edited, or move
   the lemma out.
6. `_CoqProject` registers `lib/support_posterior.v` (line 33),
   `instances/pgl27/pgl27_table_bridge.v` (182) and
   `instances/pgl27/pgl27_view_census.v` (183), but has NO entry for
   `reconstruct/coalition_view_transport.v` or
   `instances/pgl27/pgl27_leakage_ramp.v`. They must be added after line 170
   (`reconstruct/transitivity_privacy.v`) and after line 184
   (`instances/pgl27/pgl27_mutual_info.v`), and `Makefile.rocq` regenerated, or
   `make instances/pgl27/pgl27_leakage_ramp.vo` will have no rule.
7. The `post` line needs `pgl27_leak_coalition = pgl27_code_coalition rep_harmonic`,
   which the sketch does not name. One line.
8. Every other existing lemma the sketch names exists with the statement the
   sketch assumes: `pgl27_view_indep` (`pgl27_secrecy.v:82`),
   `pgl27_view_leakage_le` (`:98`), `mutual_info_binary_ambiguityE`
   (`lib/proba_entropy_ext.v:65`), `subset_class_orbit`, `subset_class_invariant`,
   `pgl27_five_subset_orbit`, `pgl27_six_subset_orbit`, `pgl27_collisions_*`,
   `pgl27_views_uniq_*`. The probe-only names (`pgl27_table_perm_*`,
   `pgl27_view_codesE`, `pgl27_ambiguous_probabilityE`,
   `support_posterior_entropy_ambiguousE`) are exactly the ones T1 to T3 copy.

## Recommended statement shapes

### `reconstruct/coalition_view_transport.v`

    Section coalition_view_transport.
    Local Open Scope ring_scope.
    Local Open Scope proba_scope.
    Local Open Scope entropy_scope.
    Variables (N' : nat) (gT : finGroupType) (G : {group gT}).
    Variable rho : {morphism G >-> {perm 'I_N'.+1}}.
    Variable R : realType.
    Variable secretP : R.-fdist bool.
    Hypothesis card_G_gt0 : (0 < #|G|)%N.
    Variable encode : bool -> N'.+1.-tuple 'I_N'.+1.

    Theorem coalition_view_transport (g : gT) (C : {set 'I_N'.+1}) : g \in G ->
      `I(dealt_secret secretP card_G_gt0 ;
           coalition_view rho secretP card_G_gt0 encode (rho g @: C))
      = `I(dealt_secret secretP card_G_gt0 ;
           coalition_view rho secretP card_G_gt0 encode C).

    End coalition_view_transport.

Three supporting declarations, in this order (all compiled):

    Lemma fdistmap_eq_supp (A B : finType) (d : R.-fdist A) (f g : A -> B) :
      (forall a, d a != 0 -> f a = g a) -> fdistmap f d = fdistmap g d.

    Lemma mutual_info_RV_inj (U TS TV TW : finType) (Q : R.-fdist U)
        (S : {RV Q -> TS}) (V : {RV Q -> TV}) (f : TV -> TW) (f' : TW -> TV) :
      cancel f f' -> `I(S ; f `o V) = `I(S ; V).

    Lemma P_transl (h : gT) : h \in G ->
      fdistmap (fun u : bool * gT => (u.1, (h * u.2)%g)) P = P.

`fdistmap_eq_supp` goes through `/fdistmap !fdistbindE; apply: eq_bigr`, not
`fdistmapE`, because `fdistmapE`'s index predicate differs on the two sides.
`mutual_info_RV_inj` is `le_anti` plus `view_mutual_info_le` used in both
directions. `P_transl` can also be routed through the existing
`fdist_uniform_supp_bij` (`transitivity_privacy.v:275`); the direct
`fdist_uniform_supp_in` / `fdist_uniform_supp_notin` case split is shorter.

### Instance corollary

    Lemma pgl27_view_transport (R : realType) (g : pgg_gT pgl27_M) (C : {set 'I_8}) :
      g \in pgg_G pgl27_M ->
      `I(pgl27_secret R ; pgl27_view R (g @: C))
      = `I(pgl27_secret R ; pgl27_view R C).
    Proof.
    exact: (@coalition_view_transport (pgg_N' pgl27_M) (pgg_gT pgl27_M)
      (pgg_G pgl27_M) (@pgg_rho pgl27_M) R (fdist_uniform card_bool)
      pgl27_G_pos orbit_encode g C).
    Qed.

### `pgl27_view_mutual_infoE`

    Theorem pgl27_view_mutual_infoE (R : realType) (C : {set 'I_8}) :
      `I(pgl27_secret R ; pgl27_view R C) =
        if (#|C| <= 3)%N then 0
        else if #|C| == 4 then
          (if subset_class C then 11%:R / 14%:R else 5%:R / 7%:R)
        else if #|C| == 5 then 25%:R / 28%:R
        else if #|C| == 6 then 27%:R / 28%:R
        else 1.

Compiled in `aud/q8_final.v` from the five representative values taken as
section hypotheses, together with

    Lemma fin4_harmonic (C : {set 'I_8}) :
      #|C| = 4 -> subset_class C = false -> `I(...) = 5%:R / 7%:R.
    Lemma fin4_equi (C : {set 'I_8}) :
      #|C| = 4 -> subset_class C = true -> `I(...) = 11%:R / 14%:R.
    Lemma fin5 (C : {set 'I_8}) : #|C| = 5 -> `I(...) = 25%:R / 28%:R.
    Lemma fin6 (C : {set 'I_8}) : #|C| = 6 -> `I(...) = 27%:R / 28%:R.
    Lemma fin7 (C : {set 'I_8}) : #|C| = 7 -> `I(...) = 1.
    Lemma fin8 (C : {set 'I_8}) : #|C| = 8 -> `I(...) = 1.
    Lemma fin_ge7 (C : {set 'I_8}) : (7 <= #|C|)%N -> `I(...) = 1.
    Lemma fin_zero_iff (C : {set 'I_8}) :
      (`I(pgl27_secret R ; pgl27_view R C) = 0) <-> (#|C| <= 3)%N.

`fin8` is the only new reasoning on the `join |C| = 8` line: `C = [set: 'I_8]`
by `eqEcard subsetT cardsT card_ord`, then `le_anti` between
`I <= H \`p_secret = 1` and `1 = I(rep_seven) <= I(setT)` through
`pgl27_view_leakage_le`.

`fin_zero_iff` is the `post` line. The forward direction extracts a four-subset
of `C` with `card_geqP`, splits on `subset_class`, and uses that 5/7 and 11/14
are strictly positive, then contradicts monotonicity.

## What was compiled

| file | contents | result |
|---|---|---|
| `aud/q1_transport.v` | the generic transport plus its three helpers | clean; `Print Assumptions coalition_view_transport` = `propositional_extensionality`, `functional_extensionality_dep`, `constructive_indefinite_description` |
| `aud/q2_local.v` | `Local`-name reachability probes, `q2_1transitive`, `q2_seven_subset_orbit`, `q2_rho_id` | clean; `Print Assumptions q2_seven_subset_orbit` = closed under the global context |
| `aud/q345.v` | the Q3 cardinalities and class values, the `Fail vm_compute` probe, `pgl27_view_transport`, `q4_zero`, `q5_le_entropy`, `q5_entropy_bool`, `q5_seven_sub` | clean |
| `aud/q6_seven.v` | `vm_compute` uniqueness and collision counts at seven and eight positions | clean |
| `aud/q7.v` | `q7_secret_uniform`, `q7_four_split`, `q7_seven` | clean |
| `aud/q8_final.v` | `fin4_*`, `fin5`, `fin6`, `fin7`, `fin8`, `fin_ge7`, `fin_zero_iff`, `pgl27_view_mutual_infoE` | clean |

Nothing was `Admitted`, and nothing imports a probe file.

VERDICT: GO
