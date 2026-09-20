# Audit: the security and hybrid rows of the economic-metaphor comment pass

Read-only audit of the 34 passages the prover's table classifies R1 (8), R2 (9),
R3 (2), R4 (3), RA (1), RB (11), plus the three sentences the prover left
unchanged and flagged.  Working tree on top of 6a20f7d.  Nothing compiled,
nothing edited but this file.

## VERDICT: NO-GO

Two MUST items, both one-line fixes.  Thirty-one of the 34 passages are true of
their declarations and on the owner's vocabulary; the R4 pair (two sites, one
sentence) states a wrong hypothesis count for a named lemma and uses the
reserved word for a margin on the hypotheses themselves, and the R2 row is not
exhaustive: the sentence rewritten at `instances/pgl27/pgl27_profile.v:99` has a
word-for-word twin at `instances/psl211/psl211_profile.v:102` that still says
"price ... is paid".  After A1 and A6 the remaining items are SHOULD and NOTE
and the 34 may go in.

Hop counting, the certificate arithmetic, the perfect-against-statistical
sentences, the RA sentence and all eleven RB sentences check out.

## Findings

| id | grade | file:line | old sentence | new sentence | problem with the declaration's type or proof step | replacement |
|----|-------|-----------|--------------|--------------|---------------------------------------------------|-------------|
| A1 | MUST | `instances/s5/s5_mixing.v:396` and `instances/pgl27/pgl27_spectral.v:517` (passages 52, 68, R4) | "Column dominance, the second half of the budget `psd_of_dominant` spends." | "Column dominance, the second of the two slack conditions `psd_of_dominant` needs." | `psd_of_dominant` (`security/pgg_mixing.v:939`) takes FOUR hypotheses: `forall i j, i != j -> E i j <= A i j`, `forall i j, i != j -> - E i j <= A i j`, the row sum `\sum_(j \| j != i) A i j <= E i i`, and the column sum `\sum_(i \| i != j) A i j <= E j j`.  Row and column dominance are the third and fourth, so "the two ... conditions `psd_of_dominant` needs" reads as its whole interface and undercounts it by two.  Separately, the owner's row reserves "slack" for the margin of a bound or of a dominance inequality against the exact value; here it is attached to the conditions, not to their margin, so the reserved word is used off-label at the one place the pass was meant to fix it. | "Column dominance, the second of the two sum conditions `psd_of_dominant` needs beside its two entrywise ones."  (Same edit at both sites.  If a shorter line is wanted, mirror the row lemma's own wording two declarations above: "Column dominance; with row dominance it holds the off-diagonal sums under the diagonal, which is what `psd_of_dominant` turns into nonnegativity of the quadratic form.") |
| A6 | MUST | `instances/psl211/psl211_profile.v:78`, `:102`, `:132` (not in the pass's 35 files) | (no change made) | (no change made) | The R2 rewrite at `instances/pgl27/pgl27_profile.v:99` reads "the cut is drawn from the group itself, and the loss of that idealisation is bounded by `pgl27_word_mixing`, not here".  `psl211_profile.v:102` still carries the identical sentence for the sibling instance: "cut is drawn from the group itself, and the price of that idealisation is paid by `psl211_word_mixing`, not here."  `:78` adds "no error to price ... the only price paid anywhere is the ..." and `:132` "Two-transitivity buys the single-card marginal".  These are the same R2 relation over the same record (`ShuffleMarginalBound`, epsilon zero, word length zero) in the instance that sits beside PGL(2,7) in every table, so the two files now disagree on the word for one relation.  This does not falsify any of the 34; it means the R2 row is incomplete. | Apply the R2 rewrite to the three `psl211_profile.v` sites: `:102` to "and the loss of that idealisation is bounded by `psl211_word_mixing`, not here"; `:78` to "the idealised shuffle has no loss to bound, so every epsilon in this instance's marginal layer is zero and the only loss anywhere is the ..." (check the tail against the declaration before writing it); `:132` to "Two-transitivity gives the single-card marginal above and nothing".  Twenty-two further survivals of the same vocabulary sit outside the pass's 35 files, listed under "Scope" below. |
| A2 | SHOULD | `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:1053` and `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:896` (passages 9, 16, R1) | "The number is spent once, against the input-indistinguishability row's twice." | "The certificate crosses to the ideal once and so loses that number once, where the input-indistinguishability row crosses twice." | The count is right: `idealproximity_tail` (`manifest/pgg_tableau.v:756`) discharges `ipc_close` after one rewrite by the witness's independence, which adds no distance, while `indistinguishability_tail` goes through `var_dist_fdistmap_transfer` and concludes at `cert_eps cert = sw_bound_eps + sw_bound_eps`.  The defect is the word.  The same file says "hop" for this count at `:1053`'s siblings (kim `:569`, `:995`; pgl27 `:371`, `:843`) and "crosses" here, so one concept carries two names within one file.  At pgl27 `:370` "crosses from the walk to the ideal cut and back again" describes the path shape rather than the count and may stay. | kim `:1053`: "The certificate hops to the ideal once and so loses that number once, where the input-indistinguishability row hops twice."  pgl27 `:896`: the same with "certificate" for "row" in the second clause, and reflow, since `:898` is left a short line by the rewrite. |
| A3 | SHOULD | `security/var_dist_joint_law.v:150` (passage 99, R1; a comment inside `Proof`) | "replacing the two factors one at a time costs d each, so the number is spent three times" | "replacing the two factors one at a time loses d at each hop, so the three hops together give 3 * d" | The proof of `var_dist_own_marginals` sets ``3%:R * d = d + (d + d)`` and then applies `var_dist_triangle` twice, giving three summands: ``var_dist J (Mr `x Ms) <= d`` by the hypothesis `H`, ``var_dist (Mr `x Ms) (Mr `x fdistmap snd J) <= d`` by `var_dist_prodR` and `Hs`, and ``var_dist (Mr `x fdistmap snd J) (fdistmap fst J `x fdistmap snd J) <= d`` by `var_dist_prodL` and `Hr`.  Only the second and third replace a factor.  The first is the hypothesis itself, so "replacing the two factors one at a time" accounts for two of the three hops and not three.  The arithmetic and the total are right. | "Each marginal of the joint law is within d of the corresponding factor by data processing.  The hypothesis gives the first hop, replacing the two factors one at a time gives the other two, and the three hops each lose d, so the total is 3 * d." |
| A4 | SHOULD | `instances/psl211/psl211_reading_constancy.v:754` (passage 21, R2) | "The first distance is the price of replacing the exact shuffle by one a dealer can perform, the second is a certificate's own distance field, and a row over any cut law but the group-uniform one pays both." | "The first distance bounds the loss of replacing the exact shuffle by one a dealer can perform, the second is a certificate's own distance field, and a row over any cut law but the group-uniform one loses both." | `psl211_alldecks_constancy_false_word` takes `var_dist (U) W <= d`, `var_dist W ideal <= eps` and `(d + eps) + (d + eps) < #\|G\|^-1`, and concludes that `coalition_reading_constancy` fails at `ideal`.  Constancy is a field of `IndistinguishabilityCert` only; `IdealProximityCert` has none, as the very next declaration's comment says at `:786`.  So "a row over any cut law but the group-uniform one loses both" is a universal over rows that the lemma does not support: the psl211 word row published in `psl211_tableau_analysis_bridged.v` carries a proximity certificate with one number.  (The universal is inherited from the old sentence; the rewrite restated it with "loses", which is now a defined term, so it reads as a stronger claim than "pays" did.)  "The first distance" and "the second" also name `d` and `eps`, which are bounds and not distances. | "The first number bounds the loss of replacing the exact shuffle by one a dealer can perform, the second is a certificate's own distance field, and an input-indistinguishability certificate reached through such a law loses at both, so its constancy field fails unless the two together reach half the reciprocal of the group order." |
| A5 | SHOULD | `manifest/pgg_tableau_syntax.v:153` (passage 77, R3) | "what makes the two currencies of the port visible where it is written: the fourth component is the only inexact one, and the fifth is exact." | "what makes the port's perfect and statistical halves visible where it is written: the fourth component is the only statistical one, and the fifth is exact." | `mk_indistinguishability` takes five components in the order `b`, `Hd`, `u`, `Hc`, `Hk`.  The fourth, `Hc`, is `var_dist (sw_rho_dist (b R idx)) (u R idx) <= sw_bound_eps (b R idx)`, and the number it is stated at belongs to the FIRST component: `b` is a `ShuffleMarginalBound`, which carries `sw_bound_eps` and a per-position bound at it.  So the fourth is not the only statistical component; it is the only inequality, and its number is the first component's.  Swapping "inexact" for "statistical" turned a loose adjective into a security-model term, which makes the miscount checkable. | "what makes the port's perfect and statistical halves visible where it is written: the fourth component is the only inequality, at the first component's epsilon, and the second and fifth are equations." |
| A7 | NOTE | `manifest/pgg_tableau.v:456`, `:490`, `:837`, `:860`, `:1033`; `manifest/pgg_tableau_syntax.v:414`; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:843` | "the constant a paper cites", "the one a paper cites among them", "the constant a text cites" | (no change made; `:860` is the site the prover flagged) | The RB row removed seven sentences that asserted what an outside document prints.  These six-plus-one say what an outside document cites, which is the same kind of reference, and only one of them was flagged.  They differ from the RB sentences in one way that matters: each states why a terminal exists (a row may be concluded at a round constant at or above its own bound) rather than asserting a fact about that document, and `ConcludePayload` (`:844`) and `port_conclude` (`:862`) do exactly that.  In scope for consistency, not for truth. | Either leave all seven, which is defensible, or replace the phrase uniformly with "a round constant a reader expects to cite".  Flagging one of seven is the only outcome to avoid. |
| A8 | NOTE | `instances/pgl27/pgl27_exec.v:352`; same sentence at `instances/s5/s5_exec.v:364` and `instances/psl211/psl211_exec.v:110`; related at `s5_exec.v:911`, `instances/s5/tableau/s5_tableau_executable.v:87`, `psl211_exec.v:16`, and six sites in `protocol/pgg_instance.v` | "The dealer-dealt mode is what leaves the instance owing termination alone among the three run facts." | (no change made; the site the prover flagged) | In scope: "owing" is on the list the pass removed, and the pass did replace "owes" elsewhere (for instance the four file headers "instance owes an arm" to "instance gives an arm").  The content is true: `protocol/pgg_instance.v:635` proves `instance_recon_stmt (dealt_secret_params A fuel)` and `:759` proves `instance_endpoints_stmt (dealt_secret_params A fuel)` generically, so of the three run facts only `instance_terminates_stmt` is left to the instance. | "The dealer-dealt mode is why termination is the only one of the three run facts the instance has to prove itself."  Apply at all three `*_exec.v` sites; the `pgg_instance.v` and `s5_tableau_executable.v` occurrences want the same treatment and lie outside the pass's 35 files. |
| A9 | NOTE | `manifest/pgg_tableau_syntax.v:420` | "so that a row's last statement reads in the order the manifest column headings run." | (no change made; the site the prover flagged) | Not an outside-document reference, so not RB: the manifest is `AnalysisPathRow` in `manifest/pgg_analysis_manifest.v:940`, whose fields run `apr_completion`, `apr_observed`, `apr_model`, `apr_transfer`, `apr_assumptions`, and the notation `s \|> publish t a` does write the transfer status before the assumption status, against `publish`'s own argument order.  The sentence is true.  "Column headings" is table language for a record's field order and no claim rests on it. | Keep.  If the table image is unwanted: "so that a row's last statement reads in the order the manifest row's two status fields run." |
| A10 | NOTE | `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:848` | "erefl takes spent 147 s here against reflexivity's 0.07 s" | "erefl takes costs 147 s here against reflexivity's 0.07 s" | Two finite verbs in one clause; the substitution was applied without dropping "takes".  This is passage 5, row R5, so it belongs to the other auditor's share, but it is the one outright broken sentence in the commit and is recorded here so it is not missed. | Drop the stranded verb: "the refine path ssreflect's `erefl` takes costs 147 s here against reflexivity's 0.07 s" becomes "the refine path ssreflect's `erefl` takes 147 s here against reflexivity's 0.07 s".  A measured time may keep "costs", so "costs 147 s here" is the other legal repair, but not both verbs. |

## Scope: where the vocabulary survives outside the 35 files

A scan of the project's `.v` sources for the pass's own word list, outside
`notes/` and the worktree copies, returns 57 lines.  Excluding the measured
times the R5 row permits (`s5_mixing.v:211`, `pgl27_tableau_checks.v:115`,
`:118`, `:120`, `psl211_endpoints.v:6`-`:15`, the interpreter "budget" of
`psl211_exec.v`, `pgg_execution_plug.v:85`, `pgg_instance.v:303`,
`pgg_security_solver.v:71`), the substantive survivals are:

- `instances/psl211/psl211_profile.v:78`, `:102`, `:132` (A6 above, R2).
- `security/pgg_collusion_bound.v:161`, `:468`: "the generic price, in TV" and
  "the unconditional TV price of that ideal posterior".  Both are R2: a bound on
  what replacing an ideal posterior loses, in a distance that is the sum of
  absolute differences in this code base.
- `protocol/pgg_instance.v:19`, `:23`, `:25`, `:28`, `:54`, `:365`, `:457`,
  `:691`, `:709`, `:756`, `:765`, `:800`; `protocol/pgg_algebra_syntax.v:41`,
  `:83`, `:150`; `protocol/pgg_session_types.v:111`; `instances/s5/s5_exec.v:911`;
  `instances/s5/tableau/s5_tableau_executable.v:87`;
  `instances/psl211/psl211_exec.v:16`, `:18`, `:103`, `:116`: obligations and
  reductions, the R6 and R5 rows.
- `groups/pgg_raag.v:1042` ("is spent" of a mixin field),
  `reconstruct/algebraic_rigidity.v:194`, `:391`,
  `reconstruct/covering_scheme.v:189` ("price cap" for a genus bound).

Only the first two bullets touch the security and hybrid rows.  The rest is
recorded so the owner can decide whether the pass is meant to be tree-wide
before it is committed as a vocabulary decision.

## Coverage: the passages found correct

Checked against the declaration and, where the sentence counts hops or names
what is applied, against the proof.

**R1, hop and loss of a hybrid (8).**

- Passage 3, `kim_biased_epsE`, kim tableau `:568`.  "the comparison through the
  ideal cut is a two-hop hybrid, one hop for each of the two committed pairs,
  and each hop loses that number".  `cert_eps cert = sw_bound_eps (ic_b cert) +
  sw_bound_eps (ic_b cert)` (`manifest/pgg_tableau.v:471`), discharged by
  `indistinguishability_tail` through `var_dist_fdistmap_transfer`
  (`security/pgg_collusion_bound.v:987`), whose proof is one `var_dist_triangle`
  through `fdistmap fx Q` and two `var_dist_fdistmap` steps, one at the run
  argument `x` and one at `x'`.  In this instance `ex_inputT` is the committed
  pair, so the two hops are one per pair.  The number, `Num.sqrt 5 * (1 / 80)`,
  is the lemma's own right-hand side, and twice it is `sqrt 5 / 40`.
- Passage 7, `kim_biased_proximity_eps_halfE`, kim tableau `:995`.  "the
  input-indistinguishability arm loses that distance at one hop for each of the
  two committed pairs it compares, and the proximity arm compares one law with
  one law".  The lemma is `cert_eps (kim_biased_cert_exact R idx) = ipc_eps +
  ipc_eps` by `erefl`; `ipc_close` is a single comparison and
  `idealproximity_tail` adds no second hop, using the witness's independence
  only to turn the ideal joint law into a product.  The tail of the sentence
  (`kim_biased_cert` at `sqrt 5 / 80`, publishing `sqrt 5 / 40`) matches
  `kim_biased_marginal_bound` and `kim_biased_epsE`.
- Passage 9, `five_card_row_biased_proximity`, kim tableau `:1053`.  Count
  correct; word choice at A2.
- Passage 14, `pgl27_row_word_tableau`, pgl27 tableau `:371`.  "each of the two
  hops loses the same mixing bound".  The row publishes at `2^-40 + 2^-40` and
  the two hops are the two `var_dist_fdistmap` steps of the transfer inequality,
  both bounded by `pgl27_word_mixing`.
- Passage 15, `pgl27_word_proximity_eps_halfE`, pgl27 tableau `:843`.  "loses
  that bound at each of two hops, one per dealt secret".  Here `ex_inputT` is
  `bool`, the dealt secret, and `pgl27_word_view_const` quantifies over `x x' :
  bool`, so the two hops are one per secret.
- Passage 16, `pgl27_row_word_proximity`, pgl27 tableau `:896`.  Count correct;
  word choice at A2.
- Passage 66, `kim_centi_static_obs_indistinguishability`,
  `five_card_mixing.v:406`.  "the bundle's spectral one lost at one hop for each
  pair ... the constancy of the ideal reading is exact and adds nothing".  The
  statement concludes at `sw_bound_eps + sw_bound_eps` and the proof supplies
  `kim_centi_cut_mixing` and `five_card_static_obs_const` to
  `var_dist_fdistmap_transfer`; the constancy premise is an equality of
  pushforwards and contributes zero, so "adds nothing" is exact and not a bound.
- Passage 99, `var_dist_own_marginals`.  Total correct; attribution at A3.

A convention worth recording: the pass counts a hop as one summand of the chain,
so one `var_dist_triangle` through one intermediate law is two hops.  That is the
hybrid-argument convention and it is used consistently in all eight passages.
The owner's row glosses a hop as one application of the triangle inequality,
which counts the applications instead.  The two glosses differ by one at every
site.  Nothing needs changing in the files; the row's gloss is what should be
reworded if the two are to agree.

**R2, loss of replacing an ideal object (9).**

- Passage 21, `psl211_alldecks_constancy_false_word`.  Clauses one and two
  correct; clause three at A4.
- Passage 22, `psl211_alldecks_constancy_false_word584`,
  `psl211_reading_constancy.v:776`.  "2^-40 bounds the whole
  information-theoretic loss of that replacement".  The lemma's hypothesis is
  the word law at `2^-40` from group-uniform, supplied in the proof by
  `psl211_word_mixing`, whose own comment records the bound as unconditional and
  information-theoretic, a counting fact over the `3^584` words.  "Bounds"
  rather than "is" is the right verb, the underlying statement being `<=`.
- Passage 79, `psl211_word_mixing`, and passage 93, `pgl27_word_mixing`.
  "transfers to the shuffle a dealer can actually perform, losing at most
  2^-40".  Both statements are `var_dist ... <= 2%:R^-40`, so "at most" is the
  right form; the old "at a cost of 2^-40" had read as an equality.
- Passage 80, `psl211_endpoint_mixing`, and passage 94, `pgl27_endpoint_mixing`.
  "2^-40 bounds the whole loss of replacing the exact shuffle by a finite word".
  Each is the single-position marginal at `<= 2^-40`, against the exact
  shuffle's exactly uniform marginal, so "whole" is right for that marginal.
- Passage 81, `psl211_joint_mixing`.  "Tensoring with an independent binary
  secret prior loses nothing."  Exact: the proof is `rewrite var_dist_prodR`,
  and `var_dist_prodR` is the equality ``var_dist (P `x Q1) (P `x Q2) = var_dist
  Q1 Q2``, whose own comment says the tensoring neither creates nor destroys
  variation distance.  "Nothing" is therefore an equality and not an upper
  bound, which is what the sentence needs.
- Passage 95, `pgl27_marginal_bound`.  "the loss of that idealisation is bounded
  by `pgl27_word_mixing`, not here".  The record is at word length 0 and epsilon
  0 over `pgl27_rho_dist`, so nothing is lost here and the finite-word
  comparison is the other lemma's.  (Sibling not yet done: A6.)
- Passage 96, `pgl27_word_marginal_bound`.  "2^-40 here bounds the loss of
  replacing that draw by a finite word, and it is the number a word row's
  spectral arm carries".  The record is `MkShuffleMarginalBound ... 200
  (2%:R^-40) rho_word (@pgl27_endpoint_mixing R)`, and `pgl27_word_cert` feeds
  exactly this bound to the arm.

**R3, perfect against statistical (2).**

- Passage 13, `pgl27_word_cert`, pgl27 tableau `:318`.  "Perfect and statistical
  security are both visible in the fields: everything about the ideal cut is
  exact and three-transitive, and the only statistical quantity anywhere in this
  row is the walk's 2^-40."  True of the five fields: `ic_Hd` is an equation,
  `ic_ideal` is the uniform law on the group, `ic_const` is
  `pgl27_word_view_const`, an equality of pushforwards quantified over both
  dealt secrets `x x' : bool` and not over an instance-chosen constant one, and
  the single number is `2^-40`, carried by `ic_b` and used by `ic_close`.  Said
  of the arm's own fields, so the perfect half is the ideal cut's constancy and
  not a claim that the row proves perfect security; the row's own conclusion is
  `2^-40 + 2^-40` in the sum of absolute differences, an advantage of at most
  `2^-41`.
- Passage 77, `mk_indistinguishability`.  First clause correct; component count
  at A5.

**R4, tight and slack (3).**

- Passage 4, `kim_biased_exact_le_eps`, kim tableau `:578`.  "The certificate's
  number is therefore not tight: it exceeds the distance it certifies by about
  two fifths, the slack left by quoting the bundle's number rather than the
  exact one."  Arithmetic: `sqrt 5 / 80 = 0.02795085`, `1 / 50 = 0.02`, excess
  `0.00795085`, which is `0.3975` of `1/50`, so "about two fifths" as a relative
  excess is right, and it is the same construction the old sentence used.  The
  thing exceeded is a genuine distance and not a bound miscalled one:
  `kim_one_cut_centiE` (`instances/kim2025/five_card_kim.v:661`) is the EQUALITY
  `var_dist (fdistmap (fun sigma => sigma s) ...) (fdist_uniform (card_ord 5)) =
  1 / 50`, and `kim_one_cut_centi_le` is its `<=` form.  "Tight" and "slack" are
  used for a bound against the exact value, which is the reserved sense.  The
  declaration itself proves only `1 / 50 <= sw_bound_eps ...`; the strictness
  and the ratio come from the equality above, and both were in the old sentence.
- Passages 52 and 68: A1.

**RA (1).**

- Passage 108, `pgl27_algebraic_start`,
  `instances/pgl27/tableau/pgl27_tableau_algebraic.v:57`.  "The three analyses
  part three levels above, at Sampled, where each names its own family."  This
  is the fix the residue called for and it agrees with the header of
  `instances/pgl27/tableau/pgl27_tableau_sampled.v`, which names three FAMILIES
  and says in as many words that the exact and the prior-indexed exact family
  are a difference of families and not of models, both drawing the uniform cut.
  The old "three probability models" contradicted that header.  "Three levels
  above" is right: `manifest/pgg_analysis_status.v:61` orders the levels
  `Algebraic | Executable | Observed | Sampled | AnalysisBridged`.

**RB, eleven sentences about a table outside the development.**

Each removed clause was an assertion about what an outside document prints, and
each replacement states a fact of the development that the declaration proves or
that a named lemma of the development settles.  All eleven check out.

- 109, `publish_armE` (`manifest/pgg_tableau.v:1046`): "the step that carries the
  three certify statements' arm equations out to a published row".  The lemma is
  `security_arm_of (publish a q pf t) R idx = ab_arm q R idx`, and the three
  equations are `certify_exact_armE`, `certify_indistinguishability_armE`,
  `certify_idealproximity_armE`.
- 115, `security_arm_of` (`:983`): "It reads `ab_arm` past the publish statement,
  and `publish_armE` is why the publish statement does not change the answer".
  the definition is `ab_arm (published_at r) R idx`.
- 110, `s5_row_rand_armE`; 112, `five_card_row_uniform_armE`; 113,
  `five_card_row_repeated_indistinguishability_armE`; 114,
  `psl211_row_alldecks_armE`: all four now end "The certify statement the
  program wrote settles which arm that is", and all four are closed by
  conversion on a row whose certify line names the constructor the lemma asserts.
- 111, `pgl27_row_exact_armE`: the same with the two lemmas named,
  "through `certify_exact_armE` and `publish_armE`", which is the route.
- 116, `five_card_row_repeated39_armE`, and 118, `pgl27_row_word39_armE`:
  "carry the same arm" / "carries the arm the row at its own sum carries".
  `conclude_armE` (`manifest/pgg_tableau.v:1035`) gives `ab_arm (tableau_at
  (conclude c q pf p)) R idx = ab_arm q R idx`, so concluding at `2^-39` leaves
  the arm alone, and the companion lemmas at the unconcluded rows give
  `InputIndistinguishabilityArm`.
- 119, `pgl27_row_word_branch39_armE`: "the branch row carries the arm
  `pgl27_row_word39` carries".  The two programs differ only in continuing from
  the named Sampled value, and both are closed by `erefl`.
- 117, the `Fail Definition pgl27_row_word_arm_neq`
  (`instances/pgl27/tableau/pgl27_tableau_checks.v:101`): "Recording the word row
  at the exact arm is rejected by conversion, so the row carries the arm its
  certify statement wrote and no other".  The `Fail` wraps exactly `(erefl :
  security_arm_of pgl27_row_word_tableau R idx = ExactIndependenceArm)`.

## What was not checked here

R5 (13) and R6 (72) belong to the second auditor, except A10, which is recorded
because it is a broken sentence.  Nothing was compiled and no file but this one
was written.
