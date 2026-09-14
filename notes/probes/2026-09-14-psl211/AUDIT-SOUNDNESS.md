# Adversarial soundness audit: PSL(2,11) twelve-card chirality spec

Spec audited: `notes/2026-09-14-003000-psl211-chirality-instance-proposal.md`,
all sections. Probe files read as they are, never edited. Counter-probes kept
in `notes/probes/2026-09-14-psl211/audit-soundness/`.

**Headline restated in English, no symbols.** A dealer fixes one twelve-card
arrangement for each of the two secret classes, shuffles it by a group element
drawn uniformly from the 660 shuffles, and deals. The claim is that the list of
card colours visible at any five or fewer positions has exactly the same
probability distribution whichever of the two mirror Steiner systems the secret
names, for every prior on the secret. The record-level lemma
`psl211_colour_view_indep` (`probe_decomposition.v:164-168`) says exactly that,
and its variables trace to: `R` and `secretP` section variables at
`probe_decomposition.v:139`, `card_G_gt0` at line 140, `C` universally
quantified at line 164, the deck from the opaque `orbit_encode` at line 68, the
shuffle from `pgg_rho psl211_M` inside `colour_view` at line 145. It is not
vacuous and has no trivial instantiation: see finding 12.

## Findings

| # | Claim (spec location) | Verdict | Evidence (file:line / compiled snippet / Fail-check / script output) | Fix |
|---|---|---|---|---|
| 1 | Design-strength criterion: two orbits that are both t-designs of the same block size give identical coalition laws up to size t, because lambda_i is fixed by the parameters and lambda_t/b = C(h,t)/C(v,t) (spec:46-56) | TRUE, and it is the right mathematics | `audit-soundness/audit_psl211.out`: both orbits have lambda_1..lambda_5 = 66, 30, 12, 4, 1; "design-parameter prediction matches every A-count for \|C\|<=5: True" recomputes every count by inclusion-exclusion from (v,k,t,b) = (12,6,5,132) alone and matches; pattern counts equal for all 12+66+220+495+792 = 1585 coalitions and every sub-pattern, unequal at size 6. Compiled: `probe_orbit.v:106` `count_okT` Qed, whole file 70.4 s | none |
| 2 | "Privacy threshold of a secret pair = min design strength of the two orbits" (spec:55-56) | Overclaim as a general criterion, true for this pair | Design theory gives only `>=`: two t-designs may agree accidentally at t+1. For this pair the size-6 leak is proved, `probe_orbit.v:117-120` `leak6` Qed, and `audit_psl211.out` shows the first size-6 witness (0,1,2,3,4,10) | Write `>=` for the criterion and cite `leak6` for the equality at this instance |
| 3 | The count certificate L6 is what the criterion licenses (spec:145-149, ledger L6) | TRUE here, but the certificate is strictly narrower than the criterion | The criterion is about normalised laws, so it is independent of the block count b. L6 certifies raw count equality, which additionally needs b equal. Both orbits have 132 blocks, verified in `audit_psl211.out`, so the certificate is sound. The census row M12 (792,5)+(132,5) at spec:69 satisfies the criterion and would fail a raw-count certificate | Say in section 5 that the count form needs equal block counts, so it does not transfer to the M12 pair |
| 4 | Colour-view law under fixed representative and uniform shuffle equals (#blocks with B cap C = A)/\|orbit\|, both orbits of size 132 (spec:116-118, ledger L10, L11) | TRUE | `audit_psl211.out`: `orbit(tblA[0]) == set(tblA): True size 132`, same for B; every fibre of `g \|-> g(H)` has size exactly 5 for both classes, and 660 = 132*5; `law(C) == #{B in orbit : B cap C = pattern}/132 : True` for every coalition up to size 6 | none |
| 5 | Section 8 scope: the raw CODE view is not independent for coalitions of size 3..5 and is false there (spec:219-220) | TRUE under the fixed-representative dealer, FALSE as an unqualified statement | `audit_psl211.out` "raw CODE view, fixed representative + uniform shuffle": equal at sizes 1 and 2, unequal from size 3, witness C = (0,1,2). But under the all-decks dealer the same section 8 sentence is wrong: the code-view law is equal for every coalition up to size 5 and differs only at 6, witness C = (0,1,2,3,4,10). Derivation from already-certified data: the number of class-s decks with prescribed distinct codes on C is N_A(s) * (6-\|A\|)! * (6-\|C\|+\|A\|)!, and \|class_decks s\| = 132 * 6! * 6! for both s, so equal N_A gives equal laws | Name the dealer in the sentence. The count certificate already proves the stronger all-decks statement, so the spec is giving away a result it has paid for |
| 6 | `ttrans_view_indep_alldecks` is "the existing point of contact" for this instance (spec:141-143) | Claim true, this route impossible | `reconstruct/transitivity_privacy.v:746` puts `Hypothesis rhoG_ntrans : ntransitive t (rho @* G) [set: 'I_N'.+1] 'P` over the whole all-decks section, and `ttrans_view_indep_alldecks` at line 840 concludes only for `#\|C\| <= t`. Compiled: `audit_route.v` `transitivity_route_floor` shows any such premise at t >= 3 forces `#\|3.-dtuple([set: 'I_12])\| <= #\|A\|`, and 12*11*10 = 1320 > 660. Independently `audit_psl211.out` reports 2 orbits on ordered triples, so the group is not 3-transitive | Drop the sentence or replace it with a new all-decks lemma whose premise is the count equality. Such a lemma would deliver the code view at 5, a stronger headline than the colour view at 5 |
| 7 | `ts_private` at k = 5 from count equality, with distinct codes (spec:197 ledger L12, `probe_decomposition.v:72-75`) | TRUE, and sharp | Agreement on C in codes forces `H' :&: C = H :&: C`. Count equality at `#\|C\| <= 5` gives such an `H'` in the other class. The remaining 6 - \|H cap C\| heart codes fill H' \ C and the remaining club codes fill the rest, and the two counts match, so a bijection exists. Exhaustive check in `audit_psl211.out`: "every A-block/coalition(<=5) pattern is matched by some B-block: True", and at \|C\| = 6 it fails, witness C = (0,1,2,3,4,10) with the A-block {5,6,7,8,9,11}. Compiled abstract shape: `audit_bridge.v` `redeal_pattern` Qed | none for the claim. See finding 8 for the probe |
| 8 | L12 miniature `redeal_mini` is "Qed at coalition size <= 1" (spec:197, `probe_bridge.v:148-150`) | FALSE statement | Compiled refutation: `audit_bridge.v` `redeal_mini_false` Qed, `~ (forall i : 'I_4, exists S', ...)`. Both disjuncts force `(i \in SA) = (i \in SB)`, which fails at i = 1. The toy premise is false too: `toy_counts_differ` Qed shows SA = {0,1} and SB = {0,2} do not share one-point counts. The miniature also never mentions a code re-deal, so it does not exercise `psl211_private` | Delete the miniature and use `redeal_pattern` from `audit_bridge.v`, which states the real implication from equal intersection patterns to the existential re-deal |
| 9 | L8 `uniform_fdistmap_of_fibres` "Qed generically" (spec:193, `probe_bridge.v:35-37`) | Statement does not elaborate, so L8, L9, L10 and L12 are all unverified | `sh run.sh probe_bridge.v` exits 1 at line 37: `Cannot infer the implicit parameter R of fdistmap`. `` `U `` is `Notation "'`U' C0" := (fdist_uniform_supp _ C0)` at `infotheo/probability/fdist.v:509`, so R is left to unification and nothing in the equation pins it. The file stops there, so nothing after line 37 was ever checked. Compiled Fail-check reproducing it: `audit_bridge.v` `Fail Lemma uniform_fdistmap_of_fibres_asWritten` | Annotate one side: `fdistmap f0 (`U HA : R.-fdist X)`. The mathematics is right: mass on the support is `#\|C\|%:R^-1` and 0 off it (`fdist.v:516`, `fdist.v:520`), so the fibre mass is `#\|fibre :&: A\| / #\|A\|`. Both lemmas now compile: `audit_bridge.v` `fibre_mass` and `uniform_fdistmap_of_fibres`, Qed |
| 10 | L10 `orbit_fibre_card` "Qed at `'P^*` on `{set 'I_12}`" (spec:195, `probe_bridge.v:60-63`) | Statement wrong twice | (a) `probe_bridge.v` opens only `fdist_scope`, `proba_scope` and `ring_scope`, so `'C_G[x \| to]` has no interpretation. Compiled Fail-check: `audit_bridge.v` `Fail Lemma orbit_fibre_card_asWritten`. (b) the action is typed `action G {set 'I_12}`, an action whose domain is G, while `'P^*` is total. Compiled: `Fail Check (fun (to : action G {set 'I_12}) => to) ('P^*)%act` succeeds as a Fail, and `Check (fun (to : {action {perm 'I_12} &-> {set 'I_12}}) => to) ('P^*)%act` prints `{action {perm 'I_12} &-> {set 'I_12}}`. The bound `S : {set {set 'I_12}}` is also unused | Open `group_scope`, type the action as `{action gT &-> rT}` and keep G a separate group argument. Corrected form compiled to Qed: `audit_bridge.v` `orbit_fibre_card`, plus `orbit_fibre_const` which is the form the count-to-fibre step actually consumes |
| 11 | L14, L15 status "probe_mixing" (spec:199-200) | L14 verified, L15 unverified, file does not compile | `sh run.sh probe_mixing.v` exits 1 at line 91: `"1 :: nseq 659 0" has type "seq nat" while it is expected to have type "seq N"`. In mathcomp `%N` is nat_scope. `pgl27_mixing.v:210` writes `1%num :: nseq 335 0%num`. Everything before line 89 did compile, in 8.9 s: `size_elem_table = 660`, `uniq_elem_keys`, `elem_closed_okT`, `size_closure_r4 = 2`, so L14 stands | Write `%num` for the BinNat literals |
| 12 | L15 cost: 660 x 3 x 570 walk updates, "estimate five to ten minutes" (spec:126-130) | Wrong by two orders of magnitude, in the safe direction | With the scope bug repaired, `audit_mixing570.v` runs the full 570-step walk and the certificate check in 18.28 s, and `audit_mixing584.v` Qeds in 18.81 s. `audit_mixing.v`, which runs walks at L = 1, 50, 100 and 200, takes 16.45 s total. The probe's `pred_table` is a filter over all 660 states per state, unlike `pgl27_mixing.v:174-176` which looks up the five predecessors directly, but the difference costs nothing here and the table is 3-regular: `audit_mixing.v` `pred_table_regular` Qed | Replace the estimate with the measured 19 s. No design change needed |
| 13 | "L = 570" for the pgl27_mixing.v shape at 660 states (spec:124-125, spec:152-154) | The certificate at L = 570 is FALSE in the kernel | `audit_mixing570.v` writes the `pgl27_mixing.v:224-228` bound at 660 states and L = 570 and `by vm_compute` fails with "No applicable tactic", so the boolean is false. That inequality encodes total variation at most 2^-41, not 2^-40. `audit-soundness/walk_threshold.py`: "least L with 2^39*S <= 660*3^L (TV <= 2^-40): 570", "least L with 2^40*S <= 660*3^L (the pgl27_mixing.v shape): 584". Compiled at 584: `audit_mixing584.v` `mixing_bound_okT` Qed | Either state L = 584 for the pgl27-shaped certificate, or state L = 570 together with the weaker 2^39 constant. Section 8's "2^-39-close laws in the word model" is consistent with the second reading, two secrets times 2^-40 |
| 14 | L16 recovery: "eleven reveals determine the class (uniq pigeonhole)" (spec:201, `probe_decomposition.v:78-81`) | TRUE but content-free, and it is about the wrong observer | Compiled: `audit_recovery.v` `deck_eleven` Qed shows two uniq twelve-tuples agreeing at eleven positions are the same tuple, for any deck whatever, with no reference to the Steiner systems. So `psl211_eleven_reveal_class` is that fact composed with `orbit_class`. The privacy half of the spec is stated for the colour observer, and the colour statement is different. Compiled: `audit_recovery.v` `colour_eleven` Qed, two six-element heart sets agreeing at eleven positions are equal | Add the colour form to the ledger, or restate L16 on colours so that privacy and recovery speak about the same observer |
| 15 | Section 1: "It reaches the M12 privacy rung with a group 144 times smaller" (spec:10-11) | Arithmetic right, comparison overclaims | 95040/660 = 144, and `audit_m12.out` confirms `\|M12\| = 95040`. But M12 is 5-transitive, so under the same fixed-representative dealer M12 gives the raw CODE view independent at 5 through the existing `ttrans_view_indep_gen` route, while PSL(2,11) gives only the COLOUR view at 5 and the code view provably leaks at 3 (finding 5). Different observer, so it is not the same rung | Write "the same coalition threshold for a colour-only observer", and say the code view is where the two differ |
| 16 | L13: ThresholdScheme with `ts_k' = 5` and ReconPlug with `rp_content := colour collapse` typecheck (spec:198) | Records typecheck, but the content breaks the downstream recon route | `probe_decomposition.v` compiles, exit 0 in 4.1 s, and `orbit_recon_invariant` is a real Qed. `ReconPlug` (`covering_scheme.v:122-128`) puts no condition on `rp_content`, so the record is fine. But `pgg_recon_monodromy_correct` (`pgg_sharing_framework.v:277-289`) requires `ts_valid ts s [tuple content (...)]`, and `orbit_valid`'s `deck_ok` is `uniq`. Compiled: `audit_route.v` `colour_content_not_uniq` Qed, the colour collapse of any distinct-card deck repeats. Every other in-tree plug uses `id` for content: `pgl27_scheme.v:96`, `rigidity_s5_instance.v:252`, `s5_profile.v:47` | Make `ts_valid` colour-aware, for example "six of each colour and the heart set is a block", instead of `uniq`, or route recon correctness through a lemma that does not ask for validity of the content tuple |
| 17 | L11: "the orbit of a table representative under `pgg_G` is the table's set" (spec:196) | TRUE, but the ledger states only the A side | `audit_psl211.out` confirms both orbits equal their tables, size 132. `probe_decomposition.v:91-92` states `setsA_orbitE` only. The step from equal block counts to equal group-element fibre counts needs both stabilisers to have order 5, which needs the B-side orbit statement plus L17 `#\|pgg_G\| = 660` | Add `setsB_orbitE` to the ledger, and record that L6 to L9 passes through L10, L11 on both sides and L17 |
| 18 | Section 4: "No other physical operation from the pool of 520 lies in `<r4, m6>`" (spec:131-133), under the header "Scratch `notes/probes/psl211_physical.py`; every claim is a full enumeration" (spec:107) | Unsupported by any script in the tree | `psl211_physical.py` produces no such output, run and captured above. Neither `small_candidates.py` nor `m12_check.py` mentions a pool of 520 or block reversals, cuts, faro, block swaps or parallel block operations as a search space | Either add the enumeration to a script or mark the bullet as not enumerated |
| 19 | Vacuity of the record-level hypotheses: `secretP` arbitrary, `card_G_gt0`, `#\|C\| <= 5` | Jointly satisfiable, statement not vacuous, bound sharp | `R` is any `realType`, `secretP` any `R.-fdist bool`, for instance `fdist1 true` or the uniform law on bool; `card_G_gt0` holds because a group is non-empty and `#\|pgg_G psl211_M\| = 660`; `C` can be any of the 792 five-element subsets. Nothing degenerates: both classes carry 132 blocks, the classes are disjoint (`audit_psl211.out`), the group is non-trivial, and the bound is sharp because size 6 leaks (`probe_orbit.v:117-120` `leak6` Qed). One caveat: no file in the repository instantiates `R` at a concrete real type, every occurrence is a `Variable` or `Context`, so the statement is never exercised at a closed carrier in-tree | Optional: add one instantiation at a concrete `realType` somewhere so the whole chain is closed |
| 20 | `orbit_encode` as used by the headline (`probe_decomposition.v:68`) | Shape probe only, the headline attests to composition and nothing else | `Definition orbit_encode (b : bool) : 12.-tuple 'I_12. Admitted.` makes it an opaque constant, so `psl211_fibres_eq` at lines 156-160 is unprovable in that file for any reason other than its being Admitted, and the headline at 164-168 is a two-line composition. This is by design for a decomposition probe, but it means the real content of L9 and L12 lives only in `probe_bridge.v`, which does not compile (finding 9) | Record in the ledger that L13's Qed is a composition check, and move L9's evidence to a file that compiles |
| 21 | Section 2 census table (spec:60-69), section 3 generators and M12 containment (spec:84-103), section 4 group facts (spec:109-125) | TRUE, every row checked | `design_census.py` output matches every census row: PGL(2,7) (42,3)(28,3) k=3, PSL(2,7) (42,3)(14,3)(14,3) k=3, AGL(3,2) (56,3)(14,3) k=3, M11 (396,4)(66,4) k=4, PSL(2,11) h=4 (330,3)(165,3) k=3, PSL(2,11) h=6 (132,5)(132,5)(330,3)(110,3)x3 k=5, faro groups k=1, Monge on 8 order 32 strength 1. `m12_check.py`: M12 order 95040, 6-subset orbits [132, 792]. `audit_m12.out`: r4 and m6 both lie in M12, `<r4,m6>` is a subgroup of M12 of order 660, the M12-orbit of {0,1,3,7,10,11} has 132 blocks and equals tblB, the M12-orbit of {2,3,5,7,8,9} has 792, the relabelling pi conjugates `<r4,m6>` onto PSL(2,11), the map z to 2z carries the A-system onto the B-system, and the Carmichael block lies in the A-system. `psl211_physical.py`: order 660, 2-transitive not 3-transitive, orbits (110,3)x3 (132,5)x2 (330,3), colour law equal at sizes 1 to 5 and unequal at 6, ten reveals never determine, Cayley diameter 12, L = 570 and L = 406 for the two alphabets | none |
| 22 | L1, L2, L3, L4, L5 statement, L6, L7 (spec:186-192) | Verified | `probe_group.v` exit 0 in 3.4 s, including `psl211_N'` Qed and both `Fail Definition` mutation checks. `probe_orbit.v` exit 0 in 70.4 s, including `design5_okA`, `design5_okB`, `design5_mut = false`, `stable_r4A/B`, `stable_m6A/B`, `stable_rev12A_false`, `count_okT`, `count_ok5_mut_false`, `leak6`, all Qed by `vm_compute`. The 70 s figure meets the spec's own "< 5 min" target at spec:191 | none |

## Blocking findings

These must be resolved before a plan is written.

1. **Finding 9.** `probe_bridge.v` does not compile. Ledger rows L8, L9, L10 and
   L12 are recorded as probed and none of them was ever checked. The fix is one
   type annotation, and the corrected L8 is proved in
   `audit-soundness/audit_bridge.v`.
2. **Finding 10.** L10's statement is wrong in two independent ways, a missing
   scope and an action domain that cannot accept `'P^*`. A prover told to keep
   every statement cannot make it compile. Corrected statement proved in
   `audit-soundness/audit_bridge.v`.
3. **Finding 8.** The L12 miniature `redeal_mini` is a false proposition.
   Refuted in `audit-soundness/audit_bridge.v`. A prover instructed to replace
   every Admitted by a Qed will burn on it.
4. **Finding 11.** `probe_mixing.v` does not compile. L15 is unverified. The fix
   is `%num` for `%N`.
5. **Finding 13.** The pgl27-shaped mixing certificate at L = 570 evaluates to
   false in the kernel. Either L = 584 or the weaker constant. This is a
   quantitative parameter that a plan would otherwise carry forward.
6. **Finding 5.** Section 8's scope sentence asserts that the raw code view is
   false at sizes 3 to 5 without naming the dealer. It is false for the
   fixed-representative dealer and true for the all-decks dealer. As written the
   spec claims something false about its own model and also understates what its
   certificate buys.

Findings 2, 3, 6, 12, 14, 15, 16, 17, 18, 20 are corrections to the write-up or
to the ledger rather than to the mathematics, and do not block a plan on their
own.

## What I compiled

Rocq 9.0, MathComp 2.5, infotheo 0.9.7, all through
`cd notes/probes/2026-09-14-psl211 && sh run.sh <file>`.

Probe files, read-only, compiled as they are:

- `probe_group.v` exit 0, 3.41 s
- `probe_orbit.v` exit 0, 70.39 s
- `probe_decomposition.v` exit 0, 4.11 s
- `probe_bridge.v` **exit 1**, 3.76 s, error at line 37
- `probe_mixing.v` **exit 1**, 8.90 s, error at line 91

Counter-probes written for this audit, all exit 0, kept in
`notes/probes/2026-09-14-psl211/audit-soundness/`:

- `audit_bridge.v`: `Fail` on L8 as written, `fibre_mass` and
  `uniform_fdistmap_of_fibres` Qed, `Fail` on L10 as written, `Fail Check` on the
  action-domain mismatch and a passing `Check` for the total form,
  `orbit_fibre_card` and `orbit_fibre_const` Qed, `redeal_mini_false` and
  `toy_counts_differ` Qed, `redeal_pattern` Qed
- `audit_route.v`: `transitivity_route_floor`, `transitivity_route_floor5`,
  `colour_content_not_uniq`, all Qed
- `audit_recovery.v`: `deck_eleven`, `colour_eleven`, both Qed
- `audit_mixing.v`: 16.45 s, `pred_table_regular`, `walk1_total`,
  `walk50_total`, `walk100_total`, `walk200_total`, all Qed
- `audit_mixing570.v`: 18.28 s, `by vm_compute` **fails**, the certificate is
  false at L = 570
- `audit_mixing584.v`: 18.81 s, `mixing_bound_okT` Qed

Compile logs: `audit-soundness/log-probe_orbit.txt`,
`log-probe_group.txt`, `log-probe_bridge.txt`, `log-probe_decomposition.txt`,
`log-probe_mixing.txt`, `log-audit_mixing.txt`, `log-audit_mixing570.txt`,
`log-audit_mixing584.txt`.

Scripts run with `python3`:

- `notes/probes/psl211_physical.py`, 1.1 s
- `notes/probes/design_census.py`
- `notes/probes/m12_check.py`
- `audit-soundness/audit_psl211.py`, 9 min 9 s, output in `audit_psl211.out`.
  Rebuilds the group and both orbits from the tables parsed out of
  `psl211_tables.v`, so a bug in the spec's own scratch script cannot propagate
- `audit-soundness/audit_m12.py`, output in `audit_m12.out`
- `audit-soundness/walk_threshold.py`, exact-integer walk, least admissible L
  for each bound convention

Read but not compiled, since another session is editing them:
`instances/pgl27/pgl27_mixing.v` lines 150 to 230.

VERDICT: NO-GO
