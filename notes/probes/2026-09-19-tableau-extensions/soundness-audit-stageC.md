# Independent soundness audit of stage C

Date: 2026-09-19. Auditor: an Opus session with no part in writing stage C.
Object: the frozen export of `notes/probes/2026-09-19-tableau-extensions/` at
commit `777f5cf`, read at
`<scratchpad>/extC_frozen/notes/probes/2026-09-19-tableau-extensions/`. I
compared the frozen copies of `p5_pgl27_prior_ideal.v`,
`p5_pgl27_word_proximity.v`, `p5_mutations.v`, `assumptions_report_stageC.v`,
`STATUS-stageC.md`, `pgg_tableau.v`, `pgl27_rows.v` and
`t0_sampled_branch_pgl27.v` against `git show 777f5cf:` and all eight hash the
same. Spec: `notes/20260919-tableau-three-extensions-probe-design.md`. Prior
audits read first so as not to repeat them: `soundness-audit-stageB.md`,
`naming-audit-stageB.md`. Nothing in the repository was edited except this
file. `instances/psl211/psl211_endpoints.v` was never opened and never
compiled, and no `make` was run.

## What I compiled

From the frozen source in a fresh directory `<scratchpad>/extC_sound/work`,
through the machine-wide lock, with the production `_CoqProject` flags and
`-Q <work> tableau_ext_probe` last. No `.vo` written by the prover was read.
Wall times include queueing behind other agents, so only the `-time`
per-sentence figures are attributable.

| file | rc | wall | sentences above 3 s |
|---|---|---|---|
| `p1_joint_law_distance.v` | 0 | 3.8 s | none |
| `pgg_tableau.v` | 0 | 13.0 s | 4.01 s `Definition ab_port`, 3.50 s `Definition ab_f` |
| `pgg_tableau_syntax.v` | 0 | 4.4 s | none |
| `pgl27_rows.v` | 0 | 6.3 s | none |
| `t0_sampled_branch_pgl27.v` | 0 | 4.3 s | none |
| `p5_pgl27_prior_ideal.v` | 0 | 4.2 s | none |
| `p5_pgl27_word_proximity.v` | 0 | 4.9 s | none |
| `p5_mutations.v` | 0 | 4.2 s | none |
| `assumptions_report_stageC.v` | 0 | 26.0 s | none |

`assumptions_report_stageC.v` in my run prints 24 `Axioms:` blocks, zero
`Closed under the global context`, and scanning the output for a name before a
colon with dots allowed gives exactly `propositional_extensionality`,
`functional_extensionality_dep` and `constructive_indefinite_description` and
no fourth name. No `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, `Abort` or
`admit` occurs in any stage C source.

Beside those I compiled five experiment files of my own.

`e1.v`, rc=0, 4.6 s, six declarations, no sentence above 0.01 s:

- `aud_profile_k : profile_k (instance_profile pgl27_algebra) = 4`, `erefl`.
- `aud_obs_prox_vs_sampled : ab_obs (published_at pgl27_row_word_proximity) =
  sp_obs (tableau_at pgl27_word_sampled)`, `exact: erefl`.
- `aud_obs_branch_vs_sampled`, the same for `pgl27_row_word_branch39`.
- `aud_ipc_secret_is_arg : ipc_secret (pgl27_word_proximity_cert secretP) =
  sa_arg (s := amf_sample pgl27_word_family R secretP)`, `exact: erefl`.
- `aud_cert_eps_double : cert_eps (pgl27_word_cert secretP) =
  sw_bound_eps (pgl27_word_marginal_bound R) + sw_bound_eps (pgl27_word_marginal_bound R)`,
  `exact: erefl`.
- `aud_prox_cert_loose`, a second `IdealProximityCert` over the same model and
  the same ideal with `ipc_eps = 1`, and `aud_half_not_arm_level`, which
  proves `cert_eps (pgl27_word_cert secretP)` differs from that certificate's
  number added to itself.

`e2.v`, rc=0, 4.4 s: `aud_var_dist_point_uniform` and
`aud_wrong_prior_distance_false`, the compiled form of the argued half of
recorded rejection 2. See C2.

`e3.v`, rc=0, no sentence above 3 s: `aud_close_no_threshold`, the distance
field of `pgl27_word_proximity_close` with the threshold premise removed. See
C7.

`e6.v`, rc=0, 4.3 s: `aud_prior_row_full`, the whole manifest row the ideal
program publishes. See C5.

`f1.v`, `f2.v`, `f3.v`, `e5.v`, each rc=1: the three recorded `Fail`s of
`p5_mutations.v` recompiled with `Fail` removed, and the withdrawn manifest
equation of D2 compiled to read its error.

## Findings

| ID | Severity | File:line | Claim | Evidence | Checked replacement |
|---|---|---|---|---|---|
| C1 | SHOULD | `p5_pgl27_word_proximity.v:190-195`, header `:22-27`; `STATUS-stageC.md` "The two numbers" | "The spectral arm's number at this model is twice the proximity arm's"; "the proximity number is half the spectral one at this model" | An arm has no number. `cert_eps cert = sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert)` by definition (`pgg_tableau.v:436-438`), recompiled as `aud_cert_eps_double`, and the proximity certificate chooses that same marginal bound as `ipc_eps`. `aud_prox_cert_loose` builds a second proximity certificate over the same model and the same ideal at the number `1`, and `aud_half_not_arm_level` proves the doubling then fails. The relation holds between these two chosen certificates. This is the recurrence of stage B's `S1`. | R1 below |
| C2 | SHOULD | `STATUS-stageC.md`, "Recorded rejections", item 2 | "Compiling that argument needs a lower bound on `var_dist` by one of its terms and an evaluation of `var_dist (fdist1 true) (fdist_uniform card_bool)`, neither of which the tree carries; it was judged not cheap against the turn budget and left as an argument" | The tree carries the first: `var_dist_fdistmap` at `security/pgg_collusion_bound.v:126`, which the same paragraph names one sentence earlier. The second is eight lines. The whole refutation compiles in one file, rc=0, 4.4 s wall, no sentence above 3 s. | R2 below, two lemmas, both compiled |
| C3 | SHOULD | `STATUS-stageC.md`, same paragraph | "so no proof of the distance field could exist at a non-uniform prior" | The argument bounds the distance between the two joint laws below by the distance between the two secret marginals. That lower bound is `1` at a point mass and is small at a prior near the uniform one, so nothing is refuted at a prior within `2^-40` of uniform. What the argument refutes is the definition as written, which quantifies over every prior, and specifically the point mass. | "so no proof of the distance field could exist at a prior further than `2^-40` from the uniform one in the sum of absolute differences, and in particular not at the point mass `fdist1 true`, which refutes the definition as written." Checked against `aud_wrong_prior_distance_false`, whose prior is `fdist1 true`. |
| C4 | SHOULD | `p5_mutations.v:16-19`, `:66-76` | "its one member fixes the uniform secret, so it is not within `2^-40` of a word model at another prior"; "The rejection is the arm refusing to compare two models whose secrets are drawn from different laws" | The `Fail` fails on a type mismatch and on nothing else. Recompiled as `f2.v`: `The term "pgl27_word_proximity_close secretP HC" has type ... while it is expected to have type ...`, the two differing in the ideal side alone. The semantic claim is marked "argued and not compiled" in `STATUS-stageC.md` but nowhere in the file that carries it, which is the file a reader of the rejection opens. This is the shape of stage B's `S5`. | With C2 the claim is no longer argued: cite the compiled refutation in the comment. Failing that, add the words "argued and not compiled" to `p5_mutations.v:66-76` and to the header at `:16-19`. |
| C5 | SHOULD | `p5_pgl27_prior_ideal.v:146-157` | The comment says the published row "is the ideal's own and not `pgl27_row_exact` under another name", and the lemma states the completion, the transfer and the assumptions | Those three coordinates are `AnalysisBridged`, `StaticExecutedOnly` and `BaselineClassicalOnly`, which are exactly `pgl27_row_exact`'s three (`manifest/pgg_analysis_manifest.v:800-802`), so the lemma cannot tell the two rows apart. The coordinate that does is `apr_model`, which `publish` fills with `ab_f q` (`pgg_tableau.v:890-894`) and `AnalysisPathRow` records (`manifest/pgg_analysis_manifest.v:773`). | R3 below, compiled as `aud_prior_row_full` |
| C6 | SHOULD | `p5_pgl27_word_proximity.v:274-285`; `STATUS-stageC.md`, "the one weakening" and "What in the brief or the spec turned out wrong" item 2 | "The equation on the two rows' `Sampled` data cannot be stated on the observed execution"; the 48.1 s and 96.0 s measurements | Both rows' observed executions against the named `Sampled` value close by `exact: erefl` at under 0.01 s each, `aud_obs_prox_vs_sampled` and `aud_obs_branch_vs_sampled`, and together they give the row-to-row equality. The expensive pairing is row against row, not row against the name. Further, the landed `ab_f` equation already forces the observed executions to convert, since `ab_f q : AnalysisModelFamily (ab_obs q)` (`pgg_tableau.v:318-320`) against `sp_f q : AnalysisModelFamily (sp_obs q)` (`:301-302`), so the statement typechecks only when `ab_obs` and `sp_obs` convert. There is no weakening left to report. | R4 below, both lemmas compiled |
| C7 | NOTE | `p5_pgl27_word_proximity.v:89-91` | "The bound holds at every coalition and not only below the threshold; the threshold enters the arm's proposition and not this distance" | Asserted in a comment and compiled nowhere in the file. The landed lemma carries the premise and its proof spends it twice, on `pgl27_view_indep_gen` and on `pgl27_view_mixing`. The claim is true: `aud_close_no_threshold` compiles with no premise on `C`, through `var_dist_fdistmap_pair` and `var_dist_prodR` of `p1_joint_law_distance.v:61,84` and `pgl27_word_mixing`, and it never mentions the ideal's independence. | either land `aud_close_no_threshold` beside the certificate, or write "the distance is bounded at every coalition by the cut-group distance alone, which this proof does not use" |
| C8 | NOTE | `STATUS-stageC.md`, D2 item 1 | `published_row pgl27_row_prior_exact_tableau = pgl27_row_exact` "does not typecheck by conversion" | It typechecks. `e5.v` elaborates the statement and fails at the proof with `Error: Cannot apply lemma erefl`. The two sides are well-typed and not convertible. | "is not provable by conversion and was withdrawn" |
| C9 | NOTE | `STATUS-stageC.md`, G1 | "Stage C edits no file that stage A or stage B produced" | `git diff 8ea05d5 777f5cf --numstat` shows `_CoqProject` at `4 0`. The head of the same file discloses this, and every `.v` and `.md` file the G1 paragraph names is byte-identical, so this is a wording slip in that paragraph. | "Stage C edits no source file that stage A or stage B produced, and appends four entries to `_CoqProject`." |

### R1, the number relation

Checked against `pgg_tableau.v:436-438`, `pgl27_word_proximity_cert:155-163`
and my two compiled lemmas.

> Both certificates read their numbers off one quantity, the marginal bound
> `sw_bound_eps (pgl27_word_marginal_bound R)`. The proximity certificate
> takes that quantity as its own number, and `cert_eps` is that quantity added
> to itself, so the spectral certificate's number is twice the proximity
> certificate's. `ipc_eps` is a free field, so this is a fact about the two
> certificates written here and not about the two arms.

### R2, the wrong-prior rejection, compiled

Both lemmas compiled in `<scratchpad>/extC_sound/work/e2.v`, rc=0. The second
needs `pgg_collusion_bound` in the requires.

```coq
Lemma aud_var_dist_point_uniform (R : realType) :
  var_dist (fdist1 true : R.-fdist bool) (fdist_uniform (R := R) card_bool)
  = 1.

Lemma aud_wrong_prior_distance_false (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  ~ (var_dist
       (fdistmap (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params C
                              ((pgl27_word_sample P1).(sa_arg) u)
                              ((pgl27_word_sample P1).(sa_cut) u),
                            pgl27_word_secret P1 u))
          (sa_sampleP (pgl27_word_sample P1)))
       (fdistmap (fun u => (@static_coalition_obs pgl27_algebra pgl27_dealt_params C
                              ((pgl27_sample R).(sa_arg) u)
                              ((pgl27_sample R).(sa_cut) u),
                            pgl27_secret R u))
          (sa_sampleP (pgl27_sample R)))
     <= 2%:R^-40).
```

with `P1 := fdist1 true`. The proof pushes both joint laws along the secret
coordinate by `var_dist_fdistmap`, reads the two pushforwards off
`fdist_prod1` as `P1` and `fdist_uniform card_bool`, and closes on
`aud_var_dist_point_uniform` against `2%:R^-40 < 1`.

### R3, the ideal row's manifest row

Compiled as `aud_prior_row_full` in `<scratchpad>/extC_sound/work/e6.v`,
rc=0. It also states exactly the row D2 says a landing owes the manifest.

```coq
Lemma pgl27_row_prior_exact_publishedE :
  published_row pgl27_row_prior_exact_tableau
  = @MkAnalysisPathRow PGL27Analysis.observed AnalysisBridged
      pgl27_prior_exact_family StaticExecutedOnly BaselineClassicalOnly.
Proof. exact: erefl. Qed.
```

### R4, the shared `Sampled` data on the observed execution

Both compiled in `<scratchpad>/extC_sound/work/e1.v`, rc=0, under 0.01 s each.

```coq
Lemma aud_obs_prox_vs_sampled :
  ab_obs (published_at pgl27_row_word_proximity)
  = sp_obs (tableau_at pgl27_word_sampled).
Proof. exact: erefl. Qed.

Lemma aud_obs_branch_vs_sampled :
  ab_obs (published_at pgl27_row_word_branch39)
  = sp_obs (tableau_at pgl27_word_sampled).
Proof. exact: erefl. Qed.
```

## Verdict per item

**1. The ideal. GO.** `pgl27_prior_exact_family` carries index type
`fun R => R.-fdist bool`, the one `pgl27_word_family` carries
(`instances/pgl27/pgl27_models.v:417-419`), over the same observed execution,
so the two are read at one index. Its member is
`pgl27_prior_sample secretP`, whose law is `pgl27P_gen secretP`, defined at
`instances/pgl27/pgl27_word_privacy.v:96-97` as the product of `secretP` with
the uniform law on `pgl27_G_pos`, with the run argument the first
projection and the cut the second. The witness exists at every prior including
degenerate ones: `pgl27_view_indep_gen` is a `Lemma` in `secretP` with no
support hypothesis, and its own proof passes only `#|C| <= 3` and
`orbit_encode_deck` to `ttrans_view_indep_gen`, whose extra hypothesis is
`forall b, uniq (encode b)` and not a condition on the prior
(`reconstruct/transitivity_privacy.v:674`). `pgl27_prior_exact_witness` is a
`Definition` in `secretP`, so it is inhabited at a point mass as at any other
prior, and nothing assumes full support. The ideal is literally the one
`pgl27_view_mixing` is stated against: that theorem's right side is the
product of the two marginals under `pgl27P_gen secretP`.

**2. The distance field. GO.** The word side is
`amf_sample pgl27_word_family R secretP`, which reduces to
`pgl27_word_sample secretP` by the family's own `fun R p => pgl27_word_sample p`,
so the sample space, the secret and the reading are the word model's own. The
`f2.v` error confirms it: the two types printed there agree on the word side
and differ on the ideal side alone. The premise is
`#|C| < profile_k (instance_profile pgl27_algebra)` and `profile_k` is 4 at
this instance, compiled as `aud_profile_k`, so the premise converts to
`#|C| <= 3`, which is `pgl27_view_mixing`'s premise. The number is
`sw_bound_eps (pgl27_word_marginal_bound R)`, which is `2%:R^-40` at word
length 200 with the uniform weights `Wuni`
(`instances/pgl27/pgl27_word_privacy.v:89-91`), and that is the number
`pgl27_view_mixing` gives. The proof is the one step claimed,
`inde_dist_of_RV2` of the ideal witness's independence, plus
`pgl27_static_obsE`, `fdistmap_comp` and `pgl27_word_sample_joint_distE`, none
of which is a probabilistic fact. See C7 for the comment beside it.

**3. The row. GO.** `PortProp` for the proximity arm is
`ipc_eps cert <= odflt (ipc_eps cert) (c R)` (`pgg_tableau.v:802`), so the
payload proves the certificate's number is under the published one and the
direction is the safe one. `pgl27_word_proximity_le39` discharges it. The row
therefore publishes `2^-39` while the certificate supports `2^-40`, which
`STATUS-stageC.md` states in its own table and the file header states in its
key-results list. That is truthful. The sibling spectral row is unchanged:
`git diff 8ea05d5 777f5cf --numstat` reports no line touched in
`t0_sampled_branch_pgl27.v`, and the file's hash matches `777f5cf`. See C1 for
the sentence that reads the halving as a fact about arms.

**4. Deviation 1. GO with C5 and C8.** The reason is the stated one, checked
two ways. `e5.v` elaborates
`published_row pgl27_row_prior_exact_tableau = pgl27_row_exact` and fails at
the proof, so the obstacle is conversion and not typing. `aud_prior_row_full`
compiles the same left side against the row that carries
`pgl27_prior_exact_family`, so the model family is the coordinate that
differs, as `AnalysisPathRow`'s `apr_model` field and `publish`'s
`MkAnalysisPathRow (ab_obs q) AnalysisBridged (ab_f q) t a` predict. The
program as written does publish a row the manifest does not hold, and D2 item
1 says a landing must add it at `AnalysisBridged`, `StaticExecutedOnly`,
`BaselineClassicalOnly` over the new family, which is what
`aud_prior_row_full` names. Spec P3 asks for an `erefl` lemma between the
certificate's ideal data and the data of the published exact program, and
`pgl27_word_proximity_cert_idealE` is exactly that, on the model and on the
port, both closed by conversion. P3 is honestly met. The lemma that states the
ideal row's own coordinates is the one that falls short, and C5 replaces it.

**5. Deviations 2 and 3. Deviation 2 is unnecessary, see C6. Deviation 3, GO.**
`pgl27_row_word_arm_neq` states `security_arm_of ... <> security_arm_of ...`,
which unfolds to the implication into `False`, so it is the inequality it is
named for and not a weaker statement. Assuming the arm equation first is a
proof shape, not a change of statement: the hypothesis is introduced from the
negation's own goal. The two arms are the ones the two `_armE` lemmas give,
`IdealProximityArm` and `SpectralDecayArm`, and the contradiction is by
`discriminate` on the constructors. The comments on both deviations say what
the statements say, with the one exception in C6.

**6. Deviation 4. GO with C2, C3, C4.** The argument is correct as
mathematics, and I compiled it. Push both joint laws along the secret
coordinate, which is `var_dist_fdistmap`. The two pushforwards are the word
model's prior and the uniform law, by `fdist_prod1` on each side. At the point
mass they are one apart in the sum of absolute differences, and one is above
`2^-40`. The `Fail`'s failure reason is the stated one and no other, read from
`f2.v`. It is not marked as argued in every place it appears: `p5_mutations.v`
states the semantic half as fact in two places and marks it nowhere.

**7. P7 at this instance. GO.** The number is `2^-40` against the ceiling `2`
that `var_dist_le2` gives (`lib/var_dist_supp.v:51`), which
`pgl27_word_proximity_cert_eps_lt2` states and which is about 4.5e-13 of the
ceiling, so the claim is not vacuous. Each of the three recorded `Fail`s fails
for the stated reason and no other, read by recompiling each without `Fail`:
`f1.v` gives the index-type mismatch, `f2.v` the distance field, `f3.v` the
cross-arm index unification, and each error line matches the one quoted in
`STATUS-stageC.md`. Hypotheses are all discharged at the concrete instance:
every declaration closes with `Qed`, seventeen of them, with no `Admitted` and
no `Abort`, and the only free hypotheses are `#|C| <= 3` and the prior, which
are premises of the claim. On the tautology probe of the distance field, the
proposition is not certificate-free, since `IdealProximityPropAt` mentions
`ipc_secret`, `ipc_ideal` and `ipc_witness`, and the freedom stage B recorded
in `N2` is closed at this instance: `aud_ipc_secret_is_arg` proves the
certificate's secret is the model's own run argument by conversion, so no
degenerate secret is being certified. What remains free is `ipc_eps`, and
`aud_prox_cert_loose` exhibits that freedom, which is C1.

**8. G1 and the invariants. GO with C9.** Stage A and B sources are unchanged
between `8ea05d5` and `777f5cf`: the diff is five files, all additions, four
of them new, plus four appended `_CoqProject` lines. Invariant 1, no new
axiom, assumed constant, `Admitted` or `Abort`: held, 24 blocks on the three
`boolp` constants, verified in my own run. Invariant 2, every distance a
variation distance between exact laws and no computational assumption: held,
every number is a `var_dist` bound and `pgl27_word_mixing` is a counting fact.
Invariant 3, the claim an average over the run argument: held, both laws are
pushforwards of whole sample laws, and no fixed-deck refutation is cited
beside it, which the invariant's second half asks for. Invariant 4, the ideal
a model with a witness: held, and this stage goes further by publishing the
ideal as its own row. Invariant 5, one claim per row and two claims from one
named value: held, `pgl27_word_sampled` is that value and R4 compiles the
observed half. Invariant 6, no row publishes a number below the one it proved:
held, `2^-40 <= 2^-39` in the direction `PortProp` asks for. Invariant 7,
nothing removed: held. Invariant 8, no permanent file edited and
`psl211_endpoints` never compiled: held for the stage and for this audit.

**9. Domain position of the statement comments. GO with C1, C4, C5, C7.** A
cryptographer reading only the comments can tell the wanted statement from
another one in most places. `pgl27_word_proximity_close`'s comment names the
threshold, the prior, the two models and what each contributes.
`pgl27_prior_exact_witness`'s comment says the reading carries no information
about the secret at all rather than a small amount, and that the independence
holds whatever the law of the secret is, which is the sentence that separates
this ideal from a law the word model happens to be near.
`pgl27_row_word_proximity`'s comment names the coalition size, the ideal and
the product form. The comments that say more than the lemma proves are the
four listed: the halving read as a fact about arms (C1), the wrong-prior
distance stated as fact and not as an argument (C4), the ideal row described
as distinguishable by a lemma that cannot distinguish it (C5), and the bound
claimed at every coalition by a lemma that carries the premise (C7). Stage C
does not repeat stage B's "advantage" wording, and it does not drift between
two meanings of "the spectral number": in this file it always means
`cert_eps`. The `IdealProximityCert` and `IdealProximityPropAt` comments that
stage B's `S2` and `S3` flagged are inherited unchanged and are not stage C's
to fix.

## Overall verdict

**GO** for folding stage C's result into the spec. No theorem in stage C is
wrong, no recorded `Fail` fails for a reason other than the stated one, no new
axiom enters, the payload direction is the safe one, and the ideal is the one
the instance's own mixing theorem is stated against. Nine findings, none
blocking. Three of them, C2, C5 and C6, replace a hedge or a weakening with
something I compiled, so folding in stage C should carry those replacements
rather than the sentences they replace.

## What I did not check

The 48.1 s and 96.0 s measurements of the row-against-row `ab_obs` equation,
and the 78.7 s and 24.3 s and 24.1 s figures in `STATUS-stageC.md`: I did not
reproduce them, since C6 makes the statement they justify unnecessary. The
proof of `pgl27_word_mixing` itself and the counting argument under it. The
production files beyond the declarations I quote. Stage A and stage B beyond
confirming their sources are unchanged and reading the two prior audits.
Whether a proximity certificate at this model can be built at a number below
`2^-40`, which is the open half of C1. Whether the distance field is refutable
at a prior between the uniform one and a point mass. Naming and style, which
belong to the naming audit.
