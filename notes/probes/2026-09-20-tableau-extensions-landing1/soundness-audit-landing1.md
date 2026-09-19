# Adversarial soundness audit of landing 1 (staged text, repo 16066cd)

## Verdict

**GO, conditional on the two MUST rows.** No compiled statement of the staged
text is wrong, no axiom beyond the classical trio and production's
`s5_group_order_eq` reaches a landed declaration, the seven staged files are
exactly the production importers of the framework, and the two retired names
occur nowhere else in production. The two MUST rows are one header sentence
whose freedom claim is refuted by a theorem inside the same landing, and one
declaration the landing adds to production that `landing_fidelity.v` does not
pin at all.

Both are one-edit fixes and neither blocks the `cp` once applied.

## Findings

Line numbers are the staged files' own; each lands at the production path the
layout table gives. `L1F` = `landing_fidelity.v`.

| id | class | file:line | quoted text | problem, with evidence | replacement |
|---|---|---|---|---|---|
| S1 | MUST | `staged/manifest/pgg_tableau.v:44-47` | "The other two arms are chosen with the same freedom: ic_ideal is any law on the group, and a constant ew_secret satisfies ew_indep at every coalition. So the proximity arm adds no freedom the tree did not already carry." | The `ic_ideal` clause reads the field's type and not the record. `ic_ideal : R.-fdist (pgg_gT (mp_M (instance_profile A)))` (`:187`) is any law only as a type; two further fields constrain the choice: `ic_close : var_dist (sw_rho_dist ic_b) ic_ideal <= sw_bound_eps ic_b` (`:188`) and `ic_const : forall C, (#\|C\| < profile_k …)%N -> forall x x', fdistmap (static_coalition_obs C x) ic_ideal = fdistmap (static_coalition_obs C x') ic_ideal` (`:189-193`). The paragraph is about what an instance is free to choose, and the landing's own `staged/instances/psl211/psl211_reading_constancy.v:705` proves the choice can fail: `psl211_alldecks_no_small_eps_cert … : sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert) < (#\|pgg_G psl211_M\|%:R)^-1 -> False`, with `psl211_alldecks_no_zero_eps_cert` (`:724`) the epsilon-zero case. So at the all-decks model there is no `ic_ideal` at all satisfying both fields at a small epsilon, where `ipc_ideal := sa` with `ipc_secret := ew_secret ipc_witness` is always available on the proximity side. The `ew_secret` clause is TRUE and I compiled it (below). | "The exact arm leaves its secret the same latitude: a constant ew_secret satisfies ew_indep at every coalition. The input-indistinguishability arm leaves its ideal less, because ic_close holds ic_ideal within the marginal bound's epsilon of that bound's own law and ic_const asks that at every coalition below the threshold the ideal read the same at every two run arguments, and at a small epsilon the two together may leave no such law. So the latitude the proximity arm's ideal and its secret carry is the exact arm's and not a new kind." |
| S2 | MUST | `landing_fidelity.v` (whole file) | — | `IdealProximityPropAt` is one of the seventeen declarations the landing adds to `manifest/pgg_tableau.v` (production has none of `ConcludePayload`, `IdealProximityCert`, `IdealProximityPayload`, `IdealProximityPropAt`, `SecurityArm`, `ab_arm`, `certify_*_armE`, `certify_idealproximity`, `conclude_armE`, `idealproximity_tail`, `port_arm`, `port_conclude`, `publish_armE`, `security_arm_of`, `view_proximity_of`). It is the proximity arm's PUBLISHED proposition, and the fidelity file neither restates it nor runs `Print Assumptions` on it. It is also not exercised by any staged row, because no landing-1 row takes the proximity arm. The gap matters because `ipc_close` (restated in full at `L1F:65-77`) and `IdealProximityPropAt` (`pgg_tableau.v:483-496`) are DIFFERENT statements: the field compares two joint laws, the proposition compares a joint law against the PRODUCT `` `x `` of the ideal's two marginals. A reader of the fidelity file sees only the joint-joint form. I compiled the restatement and the mutation: `gap_idealproximity_propE` closes by `exact: erefl`, and the same statement with the ideal side taken as a joint law instead of a product is rejected (`c_gap.v`, rc=0, 26.3 s). | Add to `L1F`, after `landing_port_conclude`: `Lemma landing_idealproximity_propE (R : realType) (A : PGGAlgebraic) (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) (cert : IdealProximityCert sa) (c : R) : IdealProximityPropAt cert c = forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}, (#\|C\| < profile_k (instance_profile A))%N -> var_dist (fdistmap (fun u => (@sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C u, ipc_secret cert u)) (sa_sampleP sa)) ((fdistmap (@sa_coalition_view R (instance_profile A) (instance_exec E) (ipc_ideal cert) 0 C) (sa_sampleP (ipc_ideal cert))) `x (fdistmap (ew_secret (ipc_witness cert)) (sa_sampleP (ipc_ideal cert)))) <= c. Proof. exact: erefl. Qed.` Compiled verbatim in my experiment directory. |
| S3 | SHOULD | `staged/instances/kim2025/five_card_rows.v:679-683` | "An input-indistinguishability certificate publishes its marginal bound twice, once for each of the two committed pairs, so a row at the constant bound publishes a sum of two equal terms, and this identity is what bounds that sum by a single constant." | This is the probe's text, byte-identical (probe `:682-686`), written when `kim_centi_cert40` existed. After E2 withdraws that certificate, "a row at the constant bound" has no referent for `2^-40` anywhere in the file, and the clause mis-describes the identity's actual use: `five_card_pow2_39_split : (2%:R : R)^-40 + 2%:R^-40 = 2%:R^-39` is used at `:708-710` to split the TARGET `2^-39`, after which `ltrD` and `kim_bound_centi` bound each SPECTRAL term by `2^-40`. Nothing in the file now publishes a sum of two copies of `2^-40`. | "Two copies of two to the minus fortieth make two to the minus thirty-ninth. A certificate's cert_eps is its marginal bound twice, once for each of the two committed pairs, and this identity splits the constant the repeated row publishes into the two halves kim_bound_centi bounds each spectral term by." |
| S4 | SHOULD | `staged/instances/kim2025/five_card_rows.v:747-752` | "…the data, the model and the certificate are the same terms, so what a coalition of at most one seat is shown is what the certificate proved, stated at the number a reader cites." | The route is `ltW (kim_centi_cert_eps_lt R idx)` and `kim_centi_cert_eps_lt (idx : unit) : cert_eps (kim_centi_cert R idx) < 2%:R ^- 39` (`:704-705`) is STRICT. `cert_eps (kim_centi_cert R idx) = Num.sqrt 5%:R * (1 / 80) ^+ 7 + Num.sqrt 5%:R * (1 / 80) ^+ 7` (`kim_centi_cert_epsE`, `:697-699`), strictly below `2^-39`. So the published `IndistinguishabilityPropAt cert (2^-39)` is stated at a number strictly above the one the certificate proved; it is not "what the certificate proved". The sibling PGL(2,7) comment states the relation correctly ("no more than the certificate proved", `pgl27_rows.v:490-492`), where the payload is `eqW` of an equality and the two numbers coincide. This is one-word-per-concept drift between two files landing together. | "…the data, the model and the certificate are the same terms. The inequality is strict, so the number the row publishes is strictly above the one the certificate proved and the row asserts about a coalition of at most one seat no more than the certificate did, at the number a reader cites." |
| S5 | SHOULD | `staged/instances/psl211/psl211_reading_constancy.v:698-699` (E5 edit 2) | "and the proposition the row carries is IndistinguishabilityPropAt cert c, a variation distance bounded above by c." | `c` carries two meanings in one sentence. The clause before it writes the published number as `odflt (cert_eps cert) (c R)`, where `c : Reprice` and `c R : option R`; `IndistinguishabilityPropAt : … -> R -> Prop` takes a real, so `IndistinguishabilityPropAt cert c` is not typeable. The framework's own `PortProp` reads `IndistinguishabilityPropAt cert (odflt (cert_eps cert) (c R))` (`pgg_tableau.v:519-520`); I compiled that unfolding (`gap_portPropE`, `c_gap.v` rc=0). The slip is inherited from the "Before" text, not introduced, but the passage is one the landing rewrites. | "and the proposition the row carries is IndistinguishabilityPropAt cert (odflt (cert_eps cert) (c R)), a variation distance bounded above by that number." |
| S6 | SHOULD | `landing_fidelity.v:312, 317-319` | `Check (pgl27_row_word_branch39 : PublishedRowAt pgl27_reprice39).` and `landing_pgl27_branch39_rowE : published_row pgl27_row_word_branch39 = published_row pgl27_row_word39` | `pgl27_row_word_branch39` is one of the two declarations E3 inserts, and these are the only two things said about it. `published_row` projects the manifest row, which is descriptive metadata: the file's own `five_card_row_biased_forms_publishedE` is the demonstration that two rows with DIFFERENT certificates publish one manifest row, so this equation pins nothing about the branch's certificate or its accumulated stack. Two strictly stronger pins are available and cheap; I compiled both by `exact: erefl` in `b_mutate.v` (rc=0, 4.1 s): `published_at pgl27_row_word_branch39 = published_at pgl27_row_word39`, and `security_arm_of pgl27_row_word_branch39 R idx = InputIndistinguishabilityArm`. The probe's own `pgl27_row_word_branch39_atE` cannot be restated here because it names `pgl27_row_word_branch`, which Q1 keeps in the probe; the `published_at` form against `pgl27_row_word39` is the available substitute. | Add `Lemma landing_pgl27_branch39_atE : published_at pgl27_row_word_branch39 = published_at pgl27_row_word39. Proof. exact: erefl. Qed.` and `Lemma landing_pgl27_branch39_armE (R : realType) (idx : amf_index (ab_f (published_at pgl27_row_word_branch39)) R) : security_arm_of pgl27_row_word_branch39 R idx = InputIndistinguishabilityArm. Proof. exact: erefl. Qed.` Keep the existing `published_row` equation. |
| S7 | NOTE | `STATUS.md`, E4 clause table | "`ipc_ideal : SampleAdapter R (instance_exec E)`, `pgg_tableau.v:213`"; "`:215`"; "`ic_ideal : …`, `:175`"; "`ew_secret … ew_indep …`, `:156-160`" | Four of the seven citations do not resolve. In the staged file `ipc_ideal` is at `:211`, `ipc_witness` `:212`, `ipc_secret` `:213`, `ic_ideal` `:187`, `ew_secret`/`ew_indep` `:168-172`. The `ic_*`/`ew_*` numbers match the probe (staged minus the twelve lines E4 inserts); the `ipc_*` numbers match neither. The same table's `pgg_tableau.v:826-827` for the `conclude` obligation is the probe's numbering too; the staged inequality is at `:838-839`. Nothing landed is wrong; the table is harder to audit than it reads. | Renumber the E4 and E3 clause tables against the staged file, or say once at the head of each table that its line numbers are the probe's. |
| S8 | NOTE | `staged/instances/psl211/psl211_reading_constancy.v:689` (E5 edit 1) | "at its own conclude coordinate c" | The tree after landing 1 still spells the coordinate's type `Reprice` and its instances `pgl27_reprice39`, `pgl27_reprice41`, `five_card_reprice39`, `five_card_reprice_inv25` (Q4 leaves the rename to the owner), and `pgg_tableau.v:504` calls it "the reprice". This line is now the only place in the seven files that calls it a "conclude coordinate", so a reader looking the phrase up finds no such type. Not wrong, but it is the drift Q4 predicted, arriving one file early. | Either keep "reprice coordinate" until the Q4 rename lands, or write "at its own coordinate c" and leave the naming to the rename. |
| S9 | NOTE | `staged/instances/kim2025/five_card_rows.v:98-99` | "kim_biased_cert_exact == the one-cut certificate with a constant in the marginal-bound field" | True (`ic_b` is `kim_biased_marginal_bound_exact R`, whose epsilon is one fiftieth, and `five_card_inv50_split : (1 / 50 : R) + 1 / 50 = 1 / 25` is what the row's `conclude` payload uses), but the E5 rewording drops the word the declaration's own comment and the name both carry. The declaration reads "The one-cut row's certificate at the exact number one fiftieth" (`:788`). | "kim_biased_cert_exact == the one-cut certificate at the exact number one fiftieth" |
| S10 | NOTE | `staged/manifest/pgg_tableau.v:35-36, 47-48` | — | The E4 paragraph is inserted with two blank comment lines above it and none below, so it runs straight into "Each arm has one composition law". Every other paragraph break in the header is one blank comment line. | Delete one blank comment line at `:36` and add one between `:47` and `:48`. |
| S11 | NOTE | `landing_fidelity.v` | — | `view_proximity_of` is also added by the landing and absent from the fidelity file. It is `proj2 (published_thm r)`, the same term as `view_secrecy_of` and `view_indistinguishability_of` (`pgg_tableau.v:967-968`), so a drift in it can only be a drift in the alias. Lower stakes than S2; recorded so the coverage claim is honest. | Optional: `Lemma landing_view_proximity_of (c : Reprice) (r : PublishedRowAt c) : view_proximity_of r = view_indistinguishability_of r. Proof. exact: erefl. Qed.` |

## What I checked and found correct

### 1. The forced edits E1 to E5

**E2, the withdrawal.** No comment in the seven staged files names a constant
repeated certificate other than the one at S3. The only surviving `2^-40`
sentences in `five_card_rows.v` are the `five_card_pow2_39_split` block
(S3), the proof line `:708`, and `five_card_row_repeated_endpoint_lt`'s
comment at `:845`, which is about the endpoint marginal and is untouched by
the withdrawal. The section banner "The same two rows at the constants they
publish" (`:740`) stays true: the two rows are `five_card_row_repeated39` at
`2^-39` and `five_card_row_biased_inv25` at `1/25`. The reworded index entry
at `:98-99` is true (S9 is a wording note, not a falsity). Every number
stated for `five_card_row_repeated39` is true of the `ltW` route except the
identity phrasing at S4: the payload is
`(fun R idx => Order.POrderTheory.ltW (kim_centi_cert_eps_lt R idx))`
(`:758`), the certificate is `kim_centi_cert` and not a withdrawn one, and
`2^-39` is `five_card_reprice39`'s value. The index entries at `:104-107`,
`:144-146` and `:151-158` all hold.

**E3, the word branch point.** Every clause of the rewritten comment of
`pgl27_row_word_branch39` (`:485-494`) checks out against the declaration
(`:495-499`) and against the staged `ConcludePayload`:

- "continued from the named value pgl27_word_sampled" — the definition's
  first line, `:496`.
- "certified by the input-indistinguishability arm" — `certify
  InputIndistinguishability pgl27_word_cert`, `:496`.
- "concluded at 2^-39 before it is published" — `|> conclude
  pgl27_reprice39 …` then `|> publish …`, `:497-498`, with
  `pgl27_reprice39 : Reprice := fun R => Some (2%:R^-39 : R)` at `:415`.
- "the accumulated bound is 2^-40 twice" — `cert_eps cert = sw_bound_eps
  (ic_b cert) + sw_bound_eps (ic_b cert)` (`pgg_tableau.v:463-466`, which I
  compiled as `gap_cert_epsE`), and `pgl27_word_reprice41_false`'s proof
  reduces `cert_eps (pgl27_word_cert)` to that sum by `rewrite /cert_eps /=`
  before rewriting with `pow2_split` (`:516`).
- "pow2_split adds the two copies" — `pow2_split : (2%:R : R)^-40 + 2%:R^-40
  = 2%:R^-39`, `instances/pgl27/pgl27_word_privacy.v:181`.
- "eqW reads that identity as the inequality the terminal's obligation asks
  for" — the obligation is `cert_eps cert <= odflt (cert_eps cert) (c R)`,
  staged `pgg_tableau.v:838-839`.
- "asserts about a coalition below the privacy threshold no more than the
  certificate proved" — correct, and here the two numbers coincide, so the
  weaker phrasing is the safe one.
- "Continuing from a named Sampled value is what lets a further row over this
  model be written without repeating the dealt prefix" — a statement about
  the surface; `pgl27_word_sampled := pgl27_dealt sample pgl27_word_family`
  (`:480-481`) contains the prefix, and `pgl27_row_word39` (`:423-428`)
  repeats it where the branch row does not.

The comment of `pgl27_word_sampled` needs no edit for the reason Q1 gives.
The two added index entries (`:57-60`) are true.

**E4, the header paragraph, clause by clause against the three records.**

- "ipc_ideal is an adapter the instance chooses" — `ipc_ideal : SampleAdapter
  R (instance_exec E)`, `:211`. TRUE.
- "ipc_secret a random variable on the actual model's sample space, valued in
  the carrier the ideal's witness names" — `ipc_secret : {RV (sa_sampleP sa)
  -> ew_secretT ipc_witness}`, `:213`. TRUE.
- "At a one-point carrier ipc_close compares the two models' readings and
  mentions no secret at all" — TRUE, argued and not compiled. With
  `ew_secretT := unit` both `fdistmap` arguments of `ipc_close` (`:215-225`)
  pair the reading with `tt`, and `var_dist` over `TA * unit` sums over the
  single second coordinate, so the field reduces to a comparison of the two
  reading laws. A `unit` witness exists whenever a constant secret satisfies
  `ew_indep`, which S1's compiled miniature settles.
- "at an ideal that is the actual adapter … the two joint laws are one term
  and ipc_close holds at zero" — TRUE. With `ipc_ideal := sa`,
  `ipc_witness := w`, `ipc_secret := ew_secret w` the two `fdistmap`
  arguments and the two distributions are the same terms, `var_dist d d = 0`,
  and `0 <= 0`.
- "which the record permits whenever that adapter carries an exact witness" —
  `ipc_witness : ExactWitness ipc_ideal`, `:212`, is the only field
  constraining `ipc_ideal` by itself. TRUE.
- "a constant ew_secret satisfies ew_indep at every coalition" — **TRUE and
  compiled.** `ew_indep` is `sa_sampleP sa |= (fun u => static_coalition_obs
  C (sa.(sa_arg) u) (sa.(sa_cut) u)) _|_ ew_secret` (`:169-172`), and
  infotheo's `inde_RV := forall x y, `Pr[ [% X, Y] = (x, y)] = `Pr[ X = x ] *
  `Pr[ Y = y ]` (`infotheo/probability/proba.v:2340`). I proved the general
  fact in my experiment directory: `Lemma const_RV_indep : P |= X _|_ ((fun=>
  b) : {RV P -> TB})`, by `inde_RV_events` and the two cases `finset ((fun=>
  b) @^-1 b) = [set: U]` and `= set0` (`a_const_indep.v`, rc=0). The
  coalition quantifier plays no part, so the claim holds at every coalition.
- "ic_ideal is any law on the group" — **S1.**
- "So the proximity arm adds no freedom the tree did not already carry" —
  survives once S1 is applied, because the exact arm's constant secret is the
  route the sentence needs. It does not survive on the `ic_ideal` leg.

I looked for the overclaim the brief asks about and did not find a second
one: the paragraph does not say the proximity arm is vacuous, and the record
comment at `:195-207` already carries the `ipc_eps` freedom. I also checked
whether `ipc_eps` is a freedom the other arms lack and concluded it is not:
`sw_bound_eps` is a bare real field of `ShuffleMarginalBound`
(`reconstruct/algebraic_rigidity.v:157`) constrained by the `sw_bound` proof
field, which is the same shape as `ipc_eps` constrained by `ipc_close`.

**E5, the four rows files.** Nothing to do, as recorded. The two payloads are
`(fun R _ => ssr_ext.eqW (pow2_split R))` (`pgl27_rows.v:497`) and
`(fun R idx => Order.POrderTheory.ltW (kim_centi_cert_eps_lt R idx))`
(`five_card_rows.v:758`).

### 2. `psl211_reading_constancy.v` under the `<=` obligation

Every sentence that speaks of what a row publishes, of `cert_eps`, or of a
lower bound on a published number stays true.

- `:35-38` "The obligation of conclude bounds the published number below by
  cert_eps cert, which is that epsilon twice, so every row over this model
  that publishes its certificate's own number publishes at least 1/660."
  TRUE. `psl211_alldecks_no_small_eps_cert` gives `sw_bound_eps + sw_bound_eps
  >= 1/660`, hence `cert_eps cert >= 1/660`, and the obligation gives
  `cert_eps cert <= odflt (cert_eps cert) (c R)`.
- `:35` "no certificate carries a shuffle bound epsilon strictly below
  1/1320". TRUE, the same theorem halved.
- `:58-62` "a certificate at that ideal exists with an epsilon near 2. Its
  cert_eps is that epsilon twice, near 4, while infotheo's var_dist sums the
  absolute differences of two laws and so never exceeds 2, and the row such a
  certificate gives publishes a number no pair of laws can exceed and bounds
  nothing." TRUE under `<=`, and the `<=` makes it stronger, not weaker: the
  published number is at or above four, so it cannot drop under the ceiling
  of two. The `var_dist` gloss is the honest one.
- `:68-69` "psl211_alldecks_constancy_false_word584 reaches eps < 1/1320 -
  2^-40, and no weighted-word sample adapter exists for this instance."
  Still true after landing 1: the hypothesis of that lemma (`:776`) is
  `(2%:R^-40 + eps) + (2%:R^-40 + eps) < (#|pgg_G psl211_M|%:R)^-1`, which is
  `2^-40 + eps < 1/1320`; and no staged file defines a `SampleAdapter` for a
  weighted word, the landing-4 file `p6_psl211_word_model.v` being the one
  that would. `:768-771` likewise stays true.
- `:686-696` the doc of `psl211_alldecks_no_small_eps_cert`. TRUE, including
  "the value 1/1320 itself not excluded" (the theorem refutes the strict
  inequality only) and "no row over this model publishes less". S5 is the one
  wording flaw in the block.
- `:702-704` "The excluded range of epsilon is bounded above…" — untouched
  and about a different argued step, as STATUS says.
- I found no sentence anywhere in the file saying a row publishes EXACTLY
  `cert_eps`, and no sentence saying a number "cannot be restated". The
  file's code tokens are production's, and the staged copy compiles against
  the staged framework (recorded 22.1 s in STATUS).

### 3. Production importers

Confirmed by `Require`-line scan over every `.v` outside `notes/`, `.git/`
and `.claude/`. The production files that `Require` `pgg_tableau` or
`pgg_tableau_syntax` are exactly `manifest/pgg_tableau_syntax.v`,
`instances/s5/s5_rows.v`, `instances/pgl27/pgl27_rows.v`,
`instances/kim2025/five_card_rows.v`, `instances/psl211/psl211_rows.v` and
`instances/psl211/psl211_reading_constancy.v`; with `manifest/pgg_tableau.v`
itself that is the seven staged files and nothing else. No production `.v`
outside the seven `Require`s any of the seven either, so the `cp` has no
downstream importer to rebuild.

`RepricePayload` and `port_reprice` occur only in production's
`manifest/pgg_tableau.v` (`:88`, `:633`, `:640`, `:646`, `:657`, `:664`,
`:668`). `kim_centi_cert40` and `kim_centi_cert40_epsE` occur only in
production's `instances/kim2025/five_card_rows.v` (`:100`, `:151`, `:737`,
`:749`, `:750`, `:765`, `:776`). Both files are replaced. Outside `.v` the
four names appear only under `notes/`, which the landing does not touch.

### 4. `landing_fidelity.v`

**It resolves the staged framework, and two things in it would fail against
production's.** `Fail Check RepricePayload.` and `Fail Check port_reprice.`
(`:183-184`) error out if production's `pgg_tableau.vo` loads, because those
names exist there; and `Check (ipc_ideal cert : …)` at `:51` fails first,
because production has no `IdealProximityCert`. `Fail Check
kim_centi_cert40.` (`:295`) is the same witness for the staged
`five_card_rows`. I reproduced the mechanism in my own directory: against the
staged framework `Fail Check RepricePayload.` succeeds and `Check
certify_idealproximity.` succeeds (`b_mutate.v`, rc=0).

**The ascriptions pin. Mutation-checked, three mutations, all rejected**
(`b_mutate.v`, rc=0, 4.1 s; a surviving mutation would have made the file
fail):

| mutation | result |
|---|---|
| `ipc_close` ascription with `<= ipc_eps cert` turned into `< ipc_eps cert` | rejected |
| `ipc_close` ascription with the ideal side's `ew_secret (ipc_witness cert)` replaced by `ipc_secret cert` | rejected |
| `landing_conclude_obligation` with the `InputIndistinguishability` branch read as `odflt (cert_eps cert) (c R) <= cert_eps cert` | rejected |

The honest forms of all three compile in the same file.

**Coverage.** Of the seventeen declarations the landing adds to
`manifest/pgg_tableau.v`, fifteen are pinned by a statement or an unfolding:
the five fields of `IdealProximityCert` including `ipc_close` in full;
`port_arm` at all three constructors and `SecurityArm` through them;
`security_arm_of` against `ab_arm`; the five `*_armE`; `ConcludePayload` by
full unfolding; `port_conclude` by restatement. `IdealProximityPropAt` (S2)
and `view_proximity_of` (S11) are not. `certify_idealproximity`,
`IdealProximityPayload` and `idealproximity_tail` appear only as the type of
a hypothesis or under `Print Assumptions`, so their existence is pinned and
their statements are not; I did not raise that separately because
`landing_certify_idealproximity_armE` exercises all three.

Of the staged rows files' pin lemmas, all seven `_rowE`, the one `_atE` and
`five_card_row_biased_forms_publishedE` are restated and under `Print
Assumptions`, and six of the six `_armE` are restated. The two remaining
`_publishedE` lemmas (`five_card_row_repeated_indistinguishability_publishedE`
at `:654`, `five_card_row_biased_indistinguishability_publishedE` at `:667`)
are neither restated nor under `Print Assumptions`; both already exist in
production (`:642`, `:655`), so the landing adds nothing there and I treat
the omission as intended rather than as a miss. STATUS's phrase "all eight
`_rowE` and `_publishedE` equations" counts seven `_rowE` plus one
`_publishedE` out of the three `_publishedE` that exist; the sentence reads
as total coverage and is not.

Five published rows plus `pgl27_row_word39_bind` and
`pgl27_row_word_branch39` are under `Print Assumptions` for PGL(2,7), five
for the five-card rows, one each for S5 and PSL(2,11). No published row of a
staged file is missing from that list. The two Sampled-only programs
(`five_card_row_repeated_tableau`, `five_card_row_biased_tableau`) and
`pgl27_word_sampled` are not published rows; `pgl27_word_sampled` is pinned by
`landing_pgl27_word_sampled` instead.

### 5. Vacuity and type honesty in the comments the landing wrote or changed

No occurrence of the banned words in any staged file, and the sum of absolute
differences is never given its barred short name. `var_dist` is glossed as the sum of
absolute differences and as twice the literature's total variation at
`pgg_tableau.v:474-477` and again at
`psl211_reading_constancy.v:59-61`; `landing_fidelity.v:60-64` repeats it and
adds that a distinguisher's advantage is at most half of it. No changed
comment calls an upper bound "the distance". "Indistinguishability" is
spelled out everywhere. The one type-honesty slip in changed text is S5, and
the one identity-where-an-inequality-is-strict is S4.

## What I did not do

The probe's mathematics was not re-audited. I did not compile the whole
staged tree: I compiled `staged/manifest/pgg_tableau.v`,
`staged/manifest/pgg_tableau_syntax.v` and
`staged/instances/pgl27/pgl27_rows.v` (rc=0 each, the last in 6.3 s) to get
the `.vo` my miniatures need, and three miniatures of my own. `instances/psl211/psl211_endpoints.v`
was never compiled and no `make` was run. Nothing outside
`/private/tmp/.../scratchpad/land1_sound/` was written except this file.
