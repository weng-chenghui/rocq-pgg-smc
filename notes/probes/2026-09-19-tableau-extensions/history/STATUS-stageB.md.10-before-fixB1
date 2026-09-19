# Stage B of the Tableau extensions probe

Directory `notes/probes/2026-09-19-tableau-extensions/`, logical path
`tableau_ext_probe`. Branch `feat/tableau-extensions-probe`. No permanent file
was edited, `instances/psl211/psl211_endpoints.v` was never touched and never
compiled, and no `make` was run.

Stage B covers ledger rows P1, P2, P3, P4, P7, P8, P9, G1, G2, G3, K1, D1 and
D2: the third security arm, "close to a private ideal model", in the copy of
the Tableau, and Kim's biased five-card row through it. Six new files, three
edited copies.

## Verdict table

| Row | Verdict | Where |
|---|---|---|
| P1 | GO | `p1_joint_law_distance.v`, `var_dist_fdistmap_pair` and `var_dist_prodR` |
| P2 | GO | `pgg_tableau.v`, `IdealProximityCert`, `IdealProximityPropAt`, `idealproximity_tail`, `certify_idealproximity`, `certify_idealproximity_armE` |
| P3 | GO | `p4_kim_biased_proximity.v`, `kim_biased_cert_idealE`, by `split` alone |
| P4 | GO, published at 1/25 | `p4_kim_biased_proximity.v`, `five_card_row_biased_proximity` |
| P7 | GO | `p7_mutations.v`, `idealproximity_ceiling` and six recorded failures |
| P8 | partial: the spec's implication is refuted by compile, the converse is argued | `p8_spectral_relation.v`, `spectral_prop_cert_free` |
| P9 | GO, k = 3 | `p9_actual_marginals.v`, `var_dist_own_marginals` |
| G1 | GO | compile table below, and every affected recorded failure re-read |
| G2 | GO, the rule costs no keyword | `pgg_tableau_syntax.v`, `g2_keyword_measure.v` |
| G3 | GO | the sentence list below |
| K1 | GO | `p4_kim_biased_proximity.v`, two `_armE` lemmas |
| D1, D2 | lists below, built by searching the tree with Python | 136 production `.v` files scanned |

## The three key statements

The certificate record, verbatim:

```coq
Record IdealProximityCert (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) :=
  MkIdealProximityCert {
    ipc_ideal   : SampleAdapter R (instance_exec E) ;
    ipc_witness : ExactWitness ipc_ideal ;
    ipc_secret  : {RV (sa_sampleP sa) -> ew_secretT ipc_witness} ;
    ipc_eps     : R ;
    ipc_close   : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
      (#|C| < profile_k (instance_profile A))%N ->
      var_dist
        (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                               (sa.(sa_cut) u), ipc_secret u))
           (sa_sampleP sa))
        (fdistmap (fun u => (static_coalition_obs C (ipc_ideal.(sa_arg) u)
                               (ipc_ideal.(sa_cut) u),
                             ew_secret ipc_witness u))
           (sa_sampleP ipc_ideal))
      <= ipc_eps }.
```

The proposition, stated at `sa_coalition_view` and in the shape of
`pgl27_view_mixing`:

```coq
Definition IdealProximityPropAt (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IdealProximityCert sa) (c : R) : Prop :=
  forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
    (#|C| < profile_k (instance_profile A))%N ->
    var_dist
      (fdistmap (fun u => (@sa_coalition_view R (instance_profile A)
                             (instance_exec E) sa 0 C u, ipc_secret cert u))
         (sa_sampleP sa))
      ((fdistmap (@sa_coalition_view R (instance_profile A) (instance_exec E)
                    (ipc_ideal cert) 0 C) (sa_sampleP (ipc_ideal cert)))
       `x (fdistmap (ew_secret (ipc_witness cert))
             (sa_sampleP (ipc_ideal cert))))
    <= c.
```

The composition law, ending in `Qed`:

```coq
Lemma idealproximity_tail (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IdealProximityCert sa)
    (Hview : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
       @sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C
       = (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u)))
    (Hideal : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
       @sa_coalition_view R (instance_profile A) (instance_exec E)
         (ipc_ideal cert) 0 C
       = (fun u => static_coalition_obs C ((ipc_ideal cert).(sa_arg) u)
                     ((ipc_ideal cert).(sa_cut) u))) :
  IdealProximityPropAt cert (ipc_eps cert).
Proof.
move=> C HC.
rewrite (Hview C) (Hideal C).
rewrite -(inde_dist_of_RV2 (@ew_indep _ _ _ _ (ipc_witness cert) C HC)).
exact: (@ipc_close _ _ _ _ cert C HC).
Qed.
```

The `certify` statement supplies `Hview` from the accumulated proposition, as
`certify_exact` does, and `Hideal` by the same `sa_coalition_viewE` that
`sample_step` uses, which applies because the certificate's ideal adapter runs
the row's own execution.

## The published number

`five_card_row_biased_proximity` publishes **1/25**, exactly, which is
**0.04** as a decimal. It is the number `five_card_row_biased_inv25` publishes
for the spectral arm over the same model, so the two arms are read in one
column.

The certificate's own number is `sw_bound_eps (kim_biased_marginal_bound R)`,
which `kim_biased_proximity_cert_epsE` puts in closed form as
`Num.sqrt 5%:R * (1 / 80)`, a decimal 0.0279508497187474. The terminal's
obligation is `kim_biased_proximity_le_inv25`, that number against 1/25.
`kim_biased_proximity_eps_halfE` says, by conversion alone, that the spectral
arm's number at this model is exactly twice the proximity arm's: both are read
off `kim_biased_cut_mixing`, and the spectral arm spends it once for each of
the two committed pairs it compares while the proximity arm compares one law
with one law.

## The size of the change to `pgg_tableau.v`

Counted by script against `history/pgg_tableau.v.7-before-stageB`:

| measure | before | after | delta |
|---|---|---|---|
| declarations | 67 | 74 | +7 |
| lines | 837 | 998 | +161 |
| lines with comments stripped | 414 | 504 | +90 |
| unified-diff lines | | | +199, -38 |

The seven declarations are `IdealProximityCert`, `IdealProximityPropAt`,
`IdealProximityPayload`, `idealproximity_tail`, `certify_idealproximity`,
`certify_idealproximity_armE` and `view_proximity_of`. Beside them the change
adds one constructor to `SecurityPort`, one to `SecurityArm`, and one arm to
each of the four `match` sites on a port: `port_arm`, `PortProp`,
`ConcludePayload`, and the `match` in `port_conclude`'s statement, whose proof
gained one case. Nothing was removed.

## Compile table

Every file of the probe's `_CoqProject`, in its order, from a fresh copy: all
`.vo`, `.vok`, `.vos` and `.glob` deleted first, one file at a time through the
machine-wide lock, `rocq compile -time`, return codes from a Python driver.
Wall times include queueing behind the auditor's own Rocq runs; only the
per-sentence figures are attributable.

| file | rc | wall | slowest sentence |
|---|---|---|---|
| `p1_joint_law_distance.v` | 0 | 4.3 s | 1.84 s, line 38, `From mathcomp Require Import s...` |
| `pgg_tableau.v` | 0 | 13.9 s | 4.16 s, line 321, `Definition ab_port (q : StackA...` |
| `pgg_tableau_syntax.v` | 0 | 5.0 s | 1.54 s, line 110, `From mathcomp Require Import m...` |
| `pgl27_rows.v` | 0 | 6.9 s | 2.11 s, line 102, `From mathcomp Require Import f...` |
| `five_card_rows.v` | 0 | 5.0 s | 1.52 s, line 195, `From mathcomp Require Import z...` |
| `s5_rows.v` | 0 | 4.3 s | 1.92 s, line 108, `From mathcomp Require Import m...` |
| `psl211_rows.v` | 0 | 5.9 s | 1.51 s, line 106, `From mathcomp Require Import m...` |
| `t0_sampled_branch.v` | 0 | 4.1 s | 1.89 s, line 44, `From mathcomp Require Import r...` |
| `t0_sampled_branch_pgl27.v` | 0 | 4.7 s | 2.28 s, line 54, `From mathcomp Require Import f...` |
| `p4_kim_biased_proximity.v` | 0 | 11.8 s | 3.39 s, line 336, `by [  ].` |
| `p8_spectral_relation.v` | 0 | 4.1 s | 2.25 s, line 29, `From mathcomp Require Import b...` |
| `p9_actual_marginals.v` | 0 | 4.2 s | 2.44 s, line 29, `From mathcomp Require Import b...` |
| `p7_mutations.v` | 0 | 4.1 s | 2.45 s, line 37, `From mathcomp Require Import b...` |
| `g2_keyword_measure.v` | 0 | 4.1 s | 1.99 s, line 25, `From mathcomp Require Import f...` |
| `assumptions_report.v` | 0 | 53.9 s | 22.24 s, line 52, `Print Assumptions psl211_row_a...` |
| `assumptions_report_stageB.v` | 0 | 24.4 s | 2.02 s, line 20, `From mathcomp Require Import f...` |

No sentence outside a `Print Assumptions` command reaches 5 s. The slowest
sentence of the whole probe is `Definition ab_port` in `pgg_tableau.v`, which
was already the slowest before stage B. The slowest stage B sentence is the
`by []` closing `five_card_row_biased_arm_neq`, an inequality between the arms
of the two rows over one model; it is under the bound and was left as it is.
Row-coordinate equations follow the rule the coordinator set: `exact: erefl`
where it is fast, and `reflexivity` where it is not.

## Assumptions

`assumptions_report_stageB.v` prints one `Print Assumptions` for every lemma
and every published program stage B writes, 35 blocks. The output was scanned
with a regular expression allowing dots in a constant name,
`^([\w.]+)\s*:`, and the whole scan returns four distinct tokens: the header
word `Axioms` and the three boolp constants
`constructive_indefinite_description`, `functional_extensionality_dep` and
`propositional_extensionality`.

- 34 blocks hold exactly those three constants and nothing else.
- 1 block reports `Closed under the global context`:
  `five_card_singleton_below_threshold`, which speaks only of a finite set.
- The list of lines matching the scan that are not one of the four expected
  tokens is empty. There is no axiom, no assumed constant, no `Admitted` and
  no `Abort` anywhere in stage B, and no decomposition probe was needed.

## Recorded failures, with the decisive line of each

`rocq compile` is silent on a passing `Fail`, so each sentence below was
compiled again with the `Fail` removed, in a copy under the scratchpad, and
the error read. Nine failures are new; six were already recorded and are
re-read because the change adds a branch to every `match` on a port.

### New

| failure | file | decisive line |
|---|---|---|
| `idealproximity_prop_cert_free` | `p8_spectral_relation.v` | `Error: No applicable tactic.` |
| `spectral_cert_in_proximity_prop` | `p8_spectral_relation.v` | `The term "cert" has type "SpectralCert sa" while it is expected to have type "IdealProximityCert ?sa".` |
| `five_card_biased_proximity_by_computation` | `p7_mutations.v` | `Unable to unify "true" with "var_dist (fdistmap (fun u => (sa_coalition_view 0 C u, ipc_secret (kim_biased_proximity_cert R idx) u)) ...) ... "` |
| `five_card_biased_proximity_by_done` | `p7_mutations.v` | `Error: No applicable tactic.` |
| `idealproximity_tail_without_independence` | `p7_mutations.v` | `Error: Cannot apply lemma (ipc_close cert HC)` |
| `kim_biased_cert_s5_ideal` | `p7_mutations.v` | `The term "amf_sample s5_rand_family R idx" has type "SampleAdapter R (OE.oe_execution s5_rand_observed)" while it is expected to have type "SampleAdapter R (instance_exec five_card_params)".` |
| `kim_centi_proximity_from_biased` | `p7_mutations.v` | `The term "kim_biased_proximity_cert R idx" has type "IdealProximityCert (amf_sample kim_biased_family R idx)" while it is expected to have type "IdealProximityCert (amf_sample kim_centi_family R idx)".` |
| `five_card_row_repeated_proximity` | `p7_mutations.v` | `cannot unify "IdealProximityCert (amf_sample kim_biased_family R idx)" and "IdealProximityCert (amf_sample (sp_f (tableau_at five_card_row_repeated_tableau)) R idx)"` |
| `kim_biased_spectral_from_centi` | `p7_mutations.v` | `The term "kim_centi_cert R idx" has type "SpectralCert (amf_sample kim_centi_family R idx)" while it is expected to have type "SpectralCert (amf_sample kim_biased_family R idx)".` |

The two-adapter mutation is therefore rejected by the types, in both
directions, and by the same coordinate in both arms: a certificate is typed
over the sample adapter, and two model families of one instance carrying one
index type still give two adapters. Nothing weaker than the type was needed.

### Re-read because a `match` on a port gained a branch

| failure | file | decisive line, unchanged |
|---|---|---|
| `pgl27_row_word_arm_neq` | `pgl27_rows.v` | `cannot unify "security_arm_of pgl27_row_word_tableau R idx" and "ExactIndependenceArm"` |
| `pgl27_word_arm_is_not_exact` | `pgl27_rows.v` | `The term "HC" has type "is_true (#\|C\| < 4)%N" while it is expected to have type "ex_inputT ..."` |
| `pgl27_row_word41` | `pgl27_rows.v` | `The term "ssr_ext.eqW (pow2_split R)" has type "is_true (2 ^- 40 + 2 ^- 40 <= 2 ^- 39)" while it is expected to have type "match ab_port ... with ... end"` |
| `pgl27_row_word39_unindexed` | `pgl27_rows.v` | the same term, `while it is expected to have type "forall idx : amf_index ..., match ab_port ..."` |
| `five_card_row_repeated39_unindexed` | `five_card_rows.v` | `The term "Order.POrderTheory.ltW (kim_centi_cert_eps_lt R tt)" ... while it is expected to have type "forall idx : amf_index ..."` |
| `pgl27_row_word39_unindexed_bind` | `pgl27_rows.v` | the bind spelling of the line above, same reason |

The printed `match` in the last four now carries the `IdealProximity` arm, so
the branch is visibly there and the reason for each failure is unchanged: a
missing index binder, or a relation the payload does not have.

The other recorded failures of the probe (`five_card_row_s5_family`,
`five_card_row_biased_at_manifest_level`,
`five_card_row_repeated_spectral_uniform_rowE`, `five_card_F_or`,
`pgl27_row_exact_leak7`, `pgl27_inline_neq`, `pgl27_inline_reuse`,
`psl211_alldecks_prefix_vm_neq`, `psl211_row_vm_reuse`, `s5_dealt_rand`,
`s5_F_k5`, the four cross-instance failures of the two T0 files) turn on a
family, a completion level, a manifest row or a functionality and mention no
port, so the change could not touch them; all of them still fail, since their
files compile.

## G3, the header sentences

The arm-count sentences F4 of the stage A note lists were already written so
that they stay true at three arms, and every one of them was re-read against
the code it describes. Two sentences carry a count that is the point of the
sentence:

- `pgg_tableau.v`'s "There are five statements" becomes **"There are six
  statements"**, and the sentence naming them becomes "certify_exact,
  certify_spectral and certify_idealproximity adjoin a security witness of one
  arm".
- `pgg_tableau_syntax.v`'s count of nineteen keywords is **unchanged**. The
  new rule writes `s 'certify' 'IdealProximity' c`: `certify` follows the slot
  `s` and was already one of the nineteen, and `IdealProximity` follows the
  literal `certify`, so it stays an identifier. Measured in
  `g2_keyword_measure.v`: `Check IdealProximity.` and
  `Check IdealProximityCert.` both print, and
  `Definition idealproximity_stays_bindable (IdealProximity : nat) : nat :=
  IdealProximity.` compiles.

Three further sentences carried a count and are settled here:

- `pgg_tableau.v`'s banner "The two security witnesses" becomes "The security
  witnesses of the arms".
- `pgg_tableau_syntax.v`'s "which is what keeps the two port constructors and
  the conclude terminal usable by name" becomes "the three port
  constructors", and `IdealProximity` joins the list of tokens that follow a
  literal.
- `pgg_tableau_syntax.v`'s banner "The two typed builders" **stays true**. No
  builder was added: the proximity rule takes the certificate whole, because
  four of its five fields are terms of the instance and the fifth is the
  number, so a builder would display the plumbing and not the mathematics.

Three paragraphs of `pgg_tableau.v` were rewritten so that they describe three
arms: the statement paragraph, the composition-law paragraph, which now names
`idealproximity_tail`, and the paragraph on what stays outside the program,
where "for a spectral port is an inequality" becomes "for a spectral or a
proximity port". The index gained five lines and the Key results three.

## D1, names and homes

The tree's pattern is `ExactWitness`/`ew_*`, `SpectralCert`/`sc_*`,
`certify_spectral`, `spectral_tail`, `SpectralPayload`, `SpectralPropAt`, and
the arm tag is the surface literal plus `Arm`. Stage A's note reserved
`IdealProximity` and `certify_idealproximity` in its E6 list and
`IdealProximityArm` in its D1 list; all three are kept, and nothing in the
tree's pattern contradicts them. The field prefix follows `ew_` and `sc_`,
which are the initials of the record name, so a three-word record takes three
letters.

| declaration | kind | probe file | home a landing would give it |
|---|---|---|---|
| `IdealProximityCert`, `ipc_ideal`, `ipc_witness`, `ipc_secret`, `ipc_eps`, `ipc_close` | Record | `pgg_tableau.v` | `manifest/pgg_tableau.v` |
| `IdealProximity` | `SecurityPort` constructor | `pgg_tableau.v` | `manifest/pgg_tableau.v` |
| `IdealProximityArm` | `SecurityArm` constructor | `pgg_tableau.v` | `manifest/pgg_tableau.v` |
| `IdealProximityPropAt`, `IdealProximityPayload` | Definitions | `pgg_tableau.v` | `manifest/pgg_tableau.v` |
| `idealproximity_tail` | Lemma | `pgg_tableau.v` | `manifest/pgg_tableau.v` |
| `certify_idealproximity`, `certify_idealproximity_armE` | statement, pin | `pgg_tableau.v` | `manifest/pgg_tableau.v` |
| `view_proximity_of` | Definition | `pgg_tableau.v` | `manifest/pgg_tableau.v` |
| the `certify IdealProximity` rule | Notation | `pgg_tableau_syntax.v` | `manifest/pgg_tableau_syntax.v` |
| `var_dist_fdistmap_pair`, `var_dist_prodR`, `var_dist_prodL`, `fdist_prod_snd`, `fdist_uniform_prod` | Lemmas | `p1_joint_law_distance.v` | `lib/var_dist_supp.v` |
| `var_dist_own_marginals` | Lemma | `p9_actual_marginals.v` | `lib/var_dist_supp.v` |
| `idealproximity_ceiling` | Lemma | `p7_mutations.v` | `manifest/pgg_tableau.v`, beside the arm |
| `spectral_prop_cert_free`, `idealproximity_reading_le` | Lemmas | `p8_spectral_relation.v` | `manifest/pgg_tableau.v` |
| `five_card_uniform_pairE`, `five_card_reading_secretE`, `five_card_arg_cut_prodE`, `kim_biased_proximity_close` | Lemmas | `p4_kim_biased_proximity.v` | `instances/kim2025/five_card_mixing.v` |
| `kim_biased_proximity_cert`, the two programs, their row, coordinate, arm and number equations, `five_card_biased_view_proximity` | Definitions and Lemmas | `p4_kim_biased_proximity.v` | `instances/kim2025/five_card_rows.v` |
| `five_card_singleton_below_threshold`, `five_card_biased_proximity_at_singleton`, `five_card_biased_view_own_marginals` | Fact, Definition, Theorem | `p7_mutations.v`, `p9_actual_marginals.v` | `instances/kim2025/five_card_rows.v` |

The word *proximity* is used for the arm throughout, in the identifiers, in
the prose and in this note. The words stage A settled are kept:
identification, reading, run argument, the number, arm.

## D2, what a landing would change in production

Built by scanning 136 production `.v` files with Python, not from memory.

1. **Stage A has to land first.** Production `manifest/pgg_tableau.v` has no
   `SecurityArm`, no `port_arm`, no `ab_arm` and no `security_arm_of`: the
   search for those names over the whole tree returns nothing. Its terminal is
   still `RepricePayload` and `port_reprice`, at `manifest/pgg_tableau.v:610`
   and `:622`, and its obligation is an equality,
   `cert_eps cert = odflt (cert_eps cert) (c R)` at `:614` and `:628`. Stage
   B's `ConcludePayload`, `port_conclude` and `certify_idealproximity_armE`
   are written against stage A's names and against the inequality, so a stage
   B landing on top of today's production would not compile.
2. `manifest/pgg_tableau.v` gains the seven declarations, the two
   constructors and the four `match` arms counted above. The file mentions
   `SecurityPort` at `:50`, `:149`, `:186`, `:243`, `:365` and `:624`, which
   are the index line, the variant, the stack type, `ab_port`, `PortProp` and
   `port_reprice`; the last two are the `match` sites, and the first four are
   unaffected.
3. `manifest/pgg_tableau_syntax.v` gains one `Notation` after the
   `SpectralDecay` rule at `:377`. Its header changes at `:68`, where
   "ExactIndependence and SpectralDecay follow a literal" gains
   `IdealProximity`, and the nineteen-keyword paragraph at `:60`, `:73` and
   `:78` keeps its count.
4. `instances/kim2025/five_card_rows.v` gains the certificate, the two
   programs and their equations, and its header changes at `:59`, "one of the
   two arms of certify", and at `:451`, "neither arm of certify takes a bound
   of that kind"; both are arm-count sentences the stage A copy already
   rewrites.
5. `instances/kim2025/five_card_mixing.v` gains the four distance lemmas of
   `p4_kim_biased_proximity.v`.
6. `instances/kim2025/five_card_analysis.v`, the facade, gains aliases in the
   pattern it already uses at `:227` to `:420`, one per new instance-level
   name, and an entry in its own index.
7. `lib/var_dist_supp.v` gains the six generic lemmas. Two production files
   hold a `Local Lemma var_dist_prodR` that the landed copy replaces:
   `instances/pgl27/pgl27_mixing.v:1077`, used once at `:1100`, and
   `instances/psl211/psl211_mixing.v:577`, used once at `:601`.
   `var_dist_le2` is already in `lib/var_dist_supp.v:51` and is cited, not
   moved; the spec's claim that it exists only in the Kim probe is stale, as
   the brief said.
8. `manifest/pgg_analysis_manifest.v` needs no new `Check (erefl : ...)` pin.
   Its three pins for `five_card_row_biased`, at `:1943`, `:1945` and `:1947`,
   are about the `AnalysisPathRow`, and the proximity row publishes that same
   row; `five_card_row_biased_proximity_rowE` says so by `erefl`. A manifest
   column naming the arm needs stage A's `security_arm_of` and is stage A's
   item, not stage B's.
9. `instances/pgl27/pgl27_rows.v:574`, "The two arms are different claims", is
   an arm-count sentence; the stage A copy already rewrites it.
10. No production file outside `manifest/pgg_tableau.v` matches on a
    `SecurityPort`, so no other file gains a branch. The port constructors are
    written in four instance rows files, at
    `instances/kim2025/five_card_rows.v:392`, `:598`, `:608`,
    `instances/s5/s5_rows.v:278`, `instances/pgl27/pgl27_rows.v:273`, `:284`,
    `:298` and `instances/psl211/psl211_rows.v:198`, and every one of them is
    a `certify` clause, not a `match`.

## Fixes carried from audit round 4 of stage A

Five `.v` fixes arrived from the stage A audit while stage B was running and
were applied here, after snapshotting each file as
`history/<name>.8-before-fix4`. `STATUS.md` and `audit-stageA-4.md` were not
touched.

1. `five_card_rows.v`, the docstring of `five_card_row_biased_inv25`: the
   bundle's number is sqrt 5 over eighty, and sqrt 5 over forty is what
   `kim_biased_cert` publishes. The last sentence now reads "a row publishes a
   number at least its certificate's, and the bound kim_biased_cert publishes
   is twice the bundle's number, sqrt 5 over forty, which is above one
   twenty-fifth".
2. `t0_sampled_branch.v`, `five_card_row_uniform_branch_ideal_atE`: the sides
   are swapped so that the branch is on the left, mirroring
   `pgl27_row_exact_branch_ideal_atE`. The docstring above it and the index
   line both still read true after the swap, since the equation still says
   that the second continuation holds the same coordinate.
3. `five_card_rows.v`, the non-rendered comment above
   `five_card_row_repeated39_atE`: the sentence cost was 147 s, not 151 s,
   and the reference is now the full path
   `notes/probes/2026-09-19-tableau-extensions/STATUS.md`, section F2.
4. `five_card_rows.v`, the docstring of `kim_centi_cert40`: it now opens "A
   certificate over the repeated row's model with the constant in the
   marginal-bound field", since no row carries that certificate.
5. The three arm-counting sentences are handled in the G3 section above: the
   `pgg_tableau.v` banner and the `pgg_tableau_syntax.v` port-constructor
   sentence are rewritten, and the `pgg_tableau_syntax.v` banner "The two
   typed builders" stays true because no builder was added.

The coordinator's rule for row equations was applied: `exact: erefl` where it
is fast, `reflexivity` where `exact: erefl` is slow, and both numbers
recorded. Stage B added three row-coordinate equations
(`five_card_row_biased_branch_spectral_atE`,
`five_card_row_biased_branch_spectral_rowE`,
`five_card_row_biased_proximity_rowE`); all three close under `exact: erefl`
in well under a second, so no `reflexivity` swap was needed.

## What in the brief or the spec turned out wrong

1. **The spec's P8 claim is false.** It says that at PGL(2,7) and at the
   five-card instance "`SpectralPropAt` implies the new proposition with
   constant 1". `spectral_prop_cert_free` refutes it by compile:
   `SpectralPropAt cert c = SpectralPropAt cert' c` holds by conversion for
   any two certificates over one model, because `SpectralPropAt`'s body does
   not mention `cert` at all. The spectral arm's published proposition is
   therefore a statement about the actual cut law and the number alone; the
   ideal cut and the constancy field are consumed inside `spectral_tail` and
   have left the claim. A proposition that does not mention any ideal cannot
   imply a bound on the distance to one, at any instance and at any constant.
   The converse is argued and not compiled: the proximity proposition compares
   two laws at one run argument while the spectral one compares two run
   arguments under one law, so a proximity bound gives no control over a
   conditional at a fixed run argument without a lower bound on the prior of
   that argument. What is compiled of the relation is
   `idealproximity_reading_le`, which reads the proximity number on the
   reading carrier the spectral arm states its bound on, and, at the five-card
   instance, `kim_biased_proximity_eps_halfE`, which says the spectral number
   there is exactly twice the proximity one.
2. **The certificate has five fields, not four.** The spec lists an ideal
   adapter, its witness, the actual secret and the distance. The number has to
   be a field of its own: the spectral arm computes `cert_eps` from the
   marginal bound, and the proximity arm has no such structure to compute a
   number from, so `ipc_eps` is written and `ipc_close` is stated against it.
3. **The ideal's link lemma is not an instance of the accumulated one.** P2
   asks for a tail that consumes the `Sampled` link lemma "for BOTH models".
   `sampled_viewE_prop` quantifies over the members of the row's own analysis
   family, and the certificate's ideal adapter is not a member of it, so the
   ideal's link lemma cannot be read off the accumulated proposition. The tail
   takes two hypotheses of link-lemma shape; `certify_idealproximity` supplies
   the first from `proj2 q` and builds the second by `sa_coalition_viewE`, the
   lemma `sample_step` itself uses, which applies exactly because the ideal
   adapter runs the row's own execution. That is what the spec's phrase "an
   ideal sample adapter over the row's own execution" buys, and it is the
   reason the ideal may not be an arbitrary adapter.
4. **The threshold is not used by the instance's distance.**
   `kim_biased_proximity_close` holds at every coalition, not only below the
   threshold: the two models differ only in the law of the rotation and the
   reading is a deterministic function of the sample point at any coalition
   size. The threshold enters the arm's proposition, where it belongs, and the
   certificate field discards its own hypothesis.
5. **A third reader name was needed.** P2's list does not mention a
   projection, but `view_secrecy_of` and `view_indist_of` are the exact arm's
   and the spectral arm's names for one term, so a proximity row using either
   would break one word per concept. `view_proximity_of` was added beside
   them, which is an addition to P2's list and not a change to the design.
6. **Two of P1's helper lemmas were already in the tree at this instance.**
   `fdist_uniform_prod` and `fdist_prod_snd` are stated generically in
   `p1_joint_law_distance.v`, but the five-card route needs neither: production
   already has `five_card_sample_uniform_prodE` at
   `instances/kim2025/five_card_exec.v:733` and
   `five_card_sample_snd_uniformE` at `:745`. `fdist_prod_snd` is used by P9
   and both are kept as the generic form a second instance would want; a
   landing may drop `fdist_uniform_prod` if no second instance asks for it.
7. **No named `Tableau Sampled` value had to be written for P4.**
   `five_card_row_biased_tableau` of `five_card_rows.v` already is one, so the
   two continuations branch from it and `five_card_rows.v` needed no stage B
   edit. The brief reads as though a new value were owed.
8. **rocq-mcp cannot reach the probe.** The PET session resolves no
   `tableau_ext_probe` module, so an interactive session on any file that
   requires the copies fails at its first `Require`. Every iteration of stage B
   went through scratch compiles under the lock wrapper instead. The one
   exception is a file that requires only production, such as
   `p1_joint_law_distance.v`, whose own prefix PET does process.
