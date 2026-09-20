# Landing naming and style audit (read-only), 2026-09-20

Working tree on top of `ef190d4`. Audited: `git diff HEAD` and the new file
`lib/fdist_prod_cond.v`, against `notes/2026-09-20-221500-p8-landing-plan.md`,
the earlier naming audit `audit-naming.md` in this directory and `LANDING.md`
in this directory. Nothing was compiled, no Rocq process was started, no
repository file other than this one was written, no git command that writes
was run.

The earlier naming audit predates the vocabulary rule and one rename, so
production's current identifiers were treated as the truth and the earlier
audit only as a checklist of what had to change.

## Verdict

**NO-GO until X1 to X5 are fixed. The names themselves are GO.**

No finding touches a statement, a proof or a name in the sense of requiring a
rename. Every one of the thirty-one landed declarations plus three sections is
named as the earlier audit's final list asks or departs from it for a reason
that holds (see "Departures", below), and no name collides anywhere in the
tree or in infotheo. What is not ready is the prose and the index:

- the home file's index is missing six of its own declarations (X1);
- one header sentence in the new library file is false and contradicts the
  sentence after it (X2);
- one docstring says a bound is an equality (X3);
- two instance docstrings claim the generic construction applies at their
  model, which no landed statement gives (X4);
- two index lines in the boxed header are 79 bytes where the box is 80 (X5).

The fix is a comment, index and layout pass over four files. It changes no
statement and no proof.

## Declarations the landing introduces

Thirty-one named declarations, three sections and one recorded rejection.

`lib/var_dist_supp.v`: `var_dist_xx`, `fdistmap_notin_codom0`,
`var_dist_supp_disjoint_eq2`.

`lib/fdist_prod_cond.v` (new): `inde_RV_cst`, section `fdist_prod_cst_cond`,
`sum_prod_fibreE`, `fdistmap_pair_fst_condE`, `fdistmap_prod_mixtureE`,
`fdistmap_pair_fst_prodE`.

`security/var_dist_joint_law.v`: `var_dist_fdistmap_prodR_le`.

`manifest/pgg_tableau_security_property_relations.v`: `profile_k_gt0`, section
`idealproximity_cert_over_any_model`, `exact_witness_cst_true`,
`idealproximity_cert_cst_secrets_true_false`,
`idealproximity_prop_cst_secrets_lt2_false`,
`idealproximity_prop_lt2_uniform_in_cert_false`,
`indistinguishability_prop_idealproximity_lt2_false`, section
`idealproximity_from_indistinguishability`, `ideal_prod_adapter`,
`ideal_prod_reading_arg_prodE`, `ideal_prod_reading_indep_arg`,
`exact_witness_ideal_prod`, `arg_read_distE`, `var_dist_joint_reading_arg_le`,
`idealproximity_close_of_indistinguishability`,
`idealproximity_cert_of_indistinguishability`,
`idealproximity_prop_of_indistinguishability`, the recorded rejection
`idealproximity_prop_of_indistinguishability_by_conversion`, and nine
`Arguments` lines.

`instances/pgl27/pgl27_models.v`: `pgl27_word_arg_cut_prodE`,
`pgl27_word_arg_readE`.

`instances/kim2025/five_card_models.v`: `kim_biased_arg_cut_prodE`,
`kim_biased_arg_readE`.

`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v`:
`pgl27_word_proximity_eps_sw_boundE`.

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v`:
`kim_biased_proximity_eps_sw_bound_exactE`,
`kim_biased_proximity_eps_le_sw_bound`.

### Do the names state the statement

Yes, in every case. Each was read against the statement it sits on:

- `var_dist_xx` is `var_dist P P = 0`; `xx` is MathComp's published fragment
  for an operation at one argument twice (`eqxx`, `lexx`, `ltxx`) and infotheo
  carries `lub_xx`.
- `var_dist_supp_disjoint_eq2` is `= 2%:R` under disjoint supports; main
  symbol first, carrier qualifier `supp` where `var_dist_fdistmap_supp_inj`
  already puts it, `eq2` published.
- `fdistmap_notin_codom0` is `fdistmap g P b = 0` when `b` is outside the
  image; it sits beside `fdistmap_neq0_codom`, whose contrapositive it is.
- `inde_RV_cst` parallels infotheo's `inde_RV_unit`, `inde_RV_comp`,
  `inde_RV_sym`; `cst` is published (`Convn_cst`, `cvg_cst`).
- `sum_prod_fibreE`, `fdistmap_pair_fst_condE`, `fdistmap_prod_mixtureE`,
  `fdistmap_pair_fst_prodE` all name a product law and a first coordinate,
  which is what the four statements quantify over; no domain word leaked into
  `lib/`.
- `var_dist_fdistmap_prodR_le` puts the main symbol first, names the map, the
  shared factor's side and the relation, matching `var_dist_prodR`,
  `var_dist_prodL`, `var_dist_own_marginals` in the same file.
- Every manifest declaration that names a certificate carries the
  `idealproximity_` or `indistinguishability_` prefix the file already uses
  (`idealproximity_prop_at2`, `idealproximity_reading_le`,
  `indistinguishability_prop_cert_free`), and `lt2` replaces the unpublished
  `below2`.
- `profile_k_gt0` is `(0 < profile_k (instance_profile A))%N`; `gt0` published.
- The instance names keep the bare `proximity` the instance tree already uses
  (`pgl27_word_proximity_cert`, `kim_biased_proximity_cert`).

One name is imperfect rather than wrong: `kim_biased_proximity_eps_sw_bound_exactE`
(X15).

### Collisions

None. Every one of the thirty-four introduced names was searched as a
declaration head across all tracked `.v` files outside `notes/`, legacy
included, and none appears twice. The four names searched in
`~/Projects/coq/infotheo` (`inde_RV_cst`, `var_dist_xx`,
`fdistmap_notin_codom0`, `var_dist_supp_disjoint_eq2`, and the three
`fdistmap_*` equations) are absent there too.

One near-duplicate stands, knowingly: `legacy/security/pgg_uniform_security.v:86`
declares `Lemma var_dist_self (P : R.-fdist A) : var_dist P P = 0` in the same
`pgg_smc` namespace (`_CoqProject:28`, file at `_CoqProject:99`). The two names
differ so nothing collides, but the tree now proves one fact twice. Plan
decision 2 accepts this; see X7.

### Departures from the earlier audit's final list

| earlier audit | landing | right? |
|---|---|---|
| `kim_biased_proximity_epsE` | `kim_biased_proximity_eps_sw_bound_exactE` | Yes. `kim_biased_proximity_cert_epsE` already gives `ipc_eps (kim_biased_proximity_cert R idx) = 1 / 50` at `five_card_tableau_analysis_bridged.v:1018`, so the earlier name would restate it. What the tree lacked is the identification with `sw_bound_eps (ic_b (kim_biased_cert_exact R idx))`, and that is what landed. The spelling is still imperfect (X15). |
| `exact_witness_ideal_prod` | unchanged | Yes. `ExactWitness` over `ideal_prod_adapter`, secret `fun z => z.1`. |
| `idealproximity_prop_cst_secrets_lt2_false` | unchanged | Yes, and the `Q` parameter the earlier audit's V10 objected to is gone. |
| `inde_RV_cst` in `lib/proba_entropy_ext.v` | in `lib/fdist_prod_cond.v` | Yes on placement (plan decision 1: the reverse closure of `proba_entropy_ext.v` is 57 files for a three-line lemma). No on the file's name, which does not cover it (X18). |
| `sum_prod_fibreE`, `fdistmap_pair_fst_condE`, `fdistmap_prod_mixtureE`, `fdistmap_pair_fst_prodE`, section `fdist_prod_cst_cond` | unchanged | Yes. |
| `sa_cut_dist_of_prodE` | not landed | Yes. Under decision 5 the product hypothesis names `sa_cut_dist sa` itself, so the lemma would read `sa_cut_dist sa = sa_cut_dist sa`. |
| `cert_eps_dbl` in `manifest/pgg_tableau.v` | not landed | Defensible but leaves the header's "twice" without a general lemma (X22). |
| `idealproximity_cert_cst_secrets_true_true`, `idealproximity_prop_at0_cst_secrets_true_true`, `var_dist_xx_le0` | not landed | Yes for the three. But `var_dist_xx`, which existed to serve them, landed anyway and has no consumer (X7). |
| `kim_biased_indistinguishability_epsE` | not landed | Yes; it duplicated `kim_biased_epsE`. |
| `Search`, `Print Assumptions` in production | removed | Yes. Zero occurrences in the landed files. |
| one `Arguments` line per section-B declaration | nine lines present | Yes, one per declaration, with the implicit set each declaration's own discharge forces. |

## Findings

| id | class | file:line | the name or sentence | rule and problem | replacement |
|---|---|---|---|---|---|
| X1 | MUST | `manifest/pgg_tableau_security_property_relations.v:73-113` | the `Definitions:` and `Lemmas:` index blocks | Index complete, every landed declaration, in the file's order. Six are missing: `exact_witness_cst_true` (:291) and `exact_witness_ideal_prod` (:466) from `Definitions:`; `ideal_prod_reading_arg_prodE` (:410), `ideal_prod_reading_indep_arg` (:431), `var_dist_joint_reading_arg_le` (:486) and `idealproximity_close_of_indistinguishability` (:513) from `Lemmas:`. The nine entries present are in file order, so the six insert at fixed places. | Add, at the `==` column 32 and continuation column 36 the block already uses. Before `idealproximity_cert_cst_secrets_true_false`: `exact_witness_cst_true == the exact witness over an arbitrary model whose secret is the constant true`. After `ideal_prod_adapter`: `exact_witness_ideal_prod == the ideal model's exact witness, its secret that model's own run argument`. In `Lemmas:`, after `indistinguishability_prop_idealproximity_lt2_false`: `ideal_prod_reading_arg_prodE == below the threshold the ideal model's joint law of a coalition's reading and the run argument is the product of its two marginals`; `ideal_prod_reading_indep_arg == the same as an independence`; then `arg_read_distE` as it stands; then `var_dist_joint_reading_arg_le == the two models' joint laws of the reading and the run argument are no further apart than the two cut laws`; then `idealproximity_close_of_indistinguishability == the distance field of the built evidence, at the marginal-bound epsilon`. |
| X2 | MUST | `lib/fdist_prod_cond.v:20-21` | "inde_RV_cst is the same conclusion in the case where the reading is one value." | False, and it contradicts the next sentence. In `inde_RV_cst` the arbitrary random variable is `X` and the constant is the second argument, `(fun=> c)`. At the one use, `exact_witness_cst_true` (`manifest/...relations.v:291-297`), `X` is instantiated with the coalition reading and the constant with the secret `true`. So the coordinate that is one value is the one the reading is compared against, not the reading. The following sentence already says "a constant secret", so the paragraph disagrees with itself inside two sentences. | "inde_RV_cst is the same conclusion in the case where the coordinate the reading is compared against is one value." |
| X3 | MUST | `manifest/pgg_tableau_security_property_relations.v:481-484` | "The two models draw the run argument from one law and read one function of the pair, so a distance on the cut group transfers unchanged." | Type-honest phrasing. The lemma concludes `<=`, through `var_dist_fdistmap_prodR_le`, whose own first step is the data processing inequality. A distance along a map does not transfer unchanged, it does not increase. The sentence also contradicts the docstring's own first sentence ("no further apart than"), and it is proof strategy, which belongs beside the proof. | Drop the sentence from the docstring and put `(* Rewrite the actual side as one map on a product with the same left factor, then var_dist_fdistmap_prodR_le. *)` above `have HL` in the proof. If a position sentence is wanted in its place: "Both models draw the run argument from one law and read one function of the pair, so the only quantity the two sides can differ in is the cut law." |
| X4 | MUST | `instances/kim2025/five_card_models.v:455-460` and `instances/pgl27/pgl27_models.v:444-448` | "It is the hypothesis a construction of ideal-proximity evidence from an input-indistinguishability certificate places on a model, so this model is one such a construction applies to." | The statement does not give this. The generic hypothesis is `Hprod : fdistmap (fun u => (arg_read u, sa_cut u)) (sa_sampleP sa) = (fdistmap arg_read (sa_sampleP sa)) `x (sa_cut_dist sa)` (`manifest/...relations.v:391-394`). The two landed lemmas name their right-hand sides concretely, `fdist_uniform card_bool2 `x fdistmap (fun k => fc_sigma ^+ k) (kim_weight_dist ...)` and `secretP `x rho_word R`, and no landed statement identifies either factor with `fdistmap arg_read (sa_sampleP sa)` or with `sa_cut_dist sa`. `LANDING.md` says so itself: "The generic construction is not instantiated end to end at either production instance." The second clause is therefore an unproved claim about this model. | kim: "It is the product hypothesis a construction of ideal-proximity evidence from an input-indistinguishability certificate places on a model, written with this model's own two factors. Reaching the hypothesis in the shape the construction states it needs, in addition, the uniform law identified with the pushforward along five_card_sample_arg and the rotation law with sa_cut_dist." pgl27: the same with "the secret prior identified with the pushforward along the first projection and rho_word with sa_cut_dist". |
| X5 | MUST | `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:330,331` | `(*                           == the certificate's number is the marginal     *)` and `(*                              bound kim_biased_cert_exact carries          *)` | Boxed headers exactly 80 bytes. Both are 79. Every other line of that box, and both lines of the sibling entry at :333-334, are 80. | One extra space before `*)` on each: `…is the marginal      *)` and `…kim_biased_cert_exact carries           *)`. Measured: both then read 80 bytes. |
| X6 | SHOULD | `instances/kim2025/five_card_models.v:50-51` | `(*   kim_biased_arg_cut_prodE == the one-cut model's run argument and its cut *)` | Index entries at the file's own `==` column and continuation column, a long name alone on its line. The name is 24 characters, so `==` lands at columns 31-32 and the description at 34, while the entry's own continuation line 51 starts at column 32 and the sibling entry at :52 puts `==` at columns 29-30 with its description at 32. The new entry therefore disagrees with its own continuation and with its sibling. | Put the long name alone: line 1 `(*   kim_biased_arg_cut_prodE` padded to 80; line 2 `(*` + 26 spaces + `== the one-cut model's run argument and its cut` padded to 80; line 3 `(*` + 29 spaces + `have a product joint distribution` padded to 80. All three measured at 80 bytes with a space before `*)`. |
| X7 | SHOULD | `lib/var_dist_supp.v:76-77` | `Lemma var_dist_xx` | Keep only claimed or premise. Nothing in production cites it: the only reference outside `notes/` is its own index entry, and the one consumer the earlier audit named, `var_dist_xx_le0` with the second constant-secret certificate, was deliberately not landed (`LANDING.md`, departure 3). It also proves the same proposition as `var_dist_self` in `legacy/security/pgg_uniform_security.v:86`, in the same `pgg_smc` namespace. | Either land the consumer, or drop `var_dist_xx` and its index entry and record in the probe that the legacy file already holds the fact. If it stays, the docstring should say that `legacy/security/pgg_uniform_security.v` states the same equation under another name. |
| X8 | SHOULD | `lib/var_dist_supp.v:72-73` | "a number a certificate publishes lies between this value and two" | False as a universal. `IdealProximityCert` (`manifest/pgg_tableau.v:230-236`) constrains `ipc_eps` by nothing at all; `ipc_close` bounds a distance by it, which is the other direction. What lies between zero and two is the distance the number bounds, not the number. | "the distance a certificate's number bounds lies between this value and two, and the certificate says something about a coalition only in so far as the number is below two". |
| X9 | SHOULD | `lib/var_dist_supp.v:173-176` | "It is the contrapositive of fdistmap_neq0_codom in the form a support argument consumes" | Meta, the "Used by" shape: it describes how the lemma is consumed rather than what it is or where it sits. The earlier audit flagged the same clause (V4) and the landing kept it. The rest of the sentence is already the position. | "It is the contrapositive of fdistmap_neq0_codom: a reading that never returns a value leaves that value with mass zero, which is how two laws are shown to carry mass at no common point." |
| X10 | SHOULD | `lib/var_dist_supp.v:189-194` | "Each law contributes its whole mass of one, so the value meets the bound var_dist_le2 gives." | Proof strategy in a docstring; it is true of the proof, not of the statement. The earlier audit asked for it to move (V6). | Move to a plain comment beside the proof: `(* On a disjoint support the absolute difference splits into the two masses, and each sums to one. *)`. Keep in the docstring only the fact, "are exactly two apart in the sum of absolute differences", and the scale sentence that follows it. |
| X11 | SHOULD | `manifest/pgg_tableau_security_property_relations.v:288-289` | "so holding exact-independence evidence is by itself no statement about what a model hides" | One word per concept, file-wide. The object is an `ExactWitness`, and this file's word for it, used in the same docstring's first sentence and in `exact_witness_ideal_prod`'s, is "witness" or "exact witness". "Evidence" is the file's word for what a program certifies a property with, and "exact-independence evidence" is a third spelling for neither. | "so holding an exact witness is by itself no statement about what a model hides". |
| X12 | SHOULD | `manifest/pgg_tableau_security_property_relations.v:471-474` | "and the number below measures the coupling of that secret with a coalition's reading alone" | Type-honest phrasing, twice. The number is an upper bound on a variation distance between two joint laws; it does not measure a coupling, and a bound that is not attained measures nothing. "Below" is also a reference to a position in the file rather than to a named result. | "and idealproximity_close_of_indistinguishability then bounds the distance between the two joint laws of that secret with a coalition's reading". |
| X13 | SHOULD | `manifest/...relations.v:471,481,546-547`; `instances/kim2025/five_card_models.v:470-474`; `instances/pgl27/pgl27_models.v:456-459` | "reading" | One word per concept, file-wide and with the home file. The agreed word "reading" is a coalition's static reading, and `ideal_prod_reading_arg_prodE`, `ideal_prod_reading_indep_arg` and `var_dist_joint_reading_arg_le` use it that way. The two instance docstrings and `arg_read`'s prose use the same word for the finite read-off of the run argument ("a finite reading of the sample point", "here the reading is the run argument itself"), so one word names two coordinates that the statements keep apart. | Keep "reading" for the coalition's reading. For `arg_read`, write "the finite coordinate arg_read takes off the sample point" and "here that coordinate is the run argument itself and the decoding is the identity". In `idealproximity_prop_of_indistinguishability`'s docstring, "the run argument read is constant" becomes "that coordinate is constant". |
| X14 | SHOULD | `manifest/pgg_tableau_security_property_relations.v:54-61` | "an input-indistinguishability certificate does build ideal-proximity evidence over that same model, and the ideal-proximity proposition holds there at the certificate's marginal-bound epsilon once" | The paragraph prices the hypotheses it names and omits two the statement carries. `idealproximity_prop_of_indistinguishability` takes `Hendp : instance_endpoints_stmt E` as a premise, and the section carries `Harg : forall u, sa_arg u = arg_decode (arg_read u)` beside `Hprod`. The paragraph names only the independence. | After "at one run.", add: "Two further hypotheses are carried, not proved: the run argument factors through a finite coordinate, and the model's executed coalition reading is its static one, which every program at Sampled holds. The statement's strength is the fineness of that coordinate, and at a one-point carrier it is true and says nothing." |
| X15 | SHOULD | `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:1272` | `kim_biased_proximity_eps_sw_bound_exactE` | Names state the claim, spelled out; carrier qualifiers last. `_exact` reads as modifying `sw_bound`, as though there were an exact and an inexact marginal bound, when it names the certificate `kim_biased_cert_exact`. The sibling `kim_biased_proximity_eps_le_sw_bound` leaves its certificate unnamed, so the pair does not say which certificate distinguishes them. | `kim_biased_proximity_eps_cert_exact_sw_boundE` for the equality and `kim_biased_proximity_eps_le_cert_sw_bound` for the inequality, or leave both and disambiguate in the two index entries, which currently both open "the certificate's number" without saying which certificate. |
| X16 | SHOULD | `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:1033-1034` | "so at this model the built number is the number the hand-built certificate publishes" | Meta: "hand-built" is a fact about how the object was written, not about the object. The sentence also repeats what the first two sentences already say. | Drop the clause. The docstring's first two sentences, "The number pgl27_word_proximity_cert carries is the marginal bound pgl27_word_cert carries, the two-hundred-letter walk's 2^-40. A proximity certificate built from that input-indistinguishability certificate over this model would carry that same number.", state the fact and its position and need nothing after them. Both numbers check out: `pgl27_word_proximity_cert_epsE` gives 2^-40 and `pgl27_word_marginal_bound` is `MkShuffleMarginalBound R pgl27_M 200 (2%:R^-40) rho_word`. |
| X17 | SHOULD | `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:1278` | "the spectral square root of five over eighty" | The adjective attaches to the wrong noun: a square root is not spectral. The number is `Num.sqrt 5%:R * (1 / 80)`, and what is spectral is the bound it comes from. | "the square root of five over eighty, the number the spectral bound carries". |
| X18 | SHOULD | `lib/fdist_prod_cond.v` filename and `:4-5` | `fdist_prod_cond: a reading of a product law whose conditional law is one law` | The name does not say what the file holds. `inde_RV_cst` is about a constant random variable on an arbitrary space; it names no product law and no conditional law, which is why the header needs a separate paragraph for it. | Either rename to `fdist_prod_cst_cond.v` (matching the section, and `cst` then covers `inde_RV_cst` as well) and widen the header line to "constant conditional laws and constant random variables", or move `inde_RV_cst` back to `lib/proba_entropy_ext.v` as the earlier audit's placement table has it. A rename touches `_CoqProject:36` and the one import at `manifest/pgg_tableau_security_property_relations.v:127`. |
| X19 | NOTE | `manifest/pgg_tableau_security_property_relations.v:125-129` | four `Require Import` lines in the order pgg_smc, pgg_reconstruct, pgg_smc, pgg_reconstruct | The two new lines were appended rather than merged, so the block alternates namespaces. The eight lines above it are grouped. | `From pgg_smc Require Import pgg_collusion_bound var_dist_supp.` then `From pgg_smc Require Import fdist_prod_cond var_dist_joint_law.` then `From pgg_reconstruct Require Import algebraic_rigidity pgg_sharing_framework.` then `From pgg_smc Require Import pgg_tableau.` |
| X20 | NOTE | `manifest/pgg_tableau_security_property_relations.v:507-512` | `idealproximity_close_of_indistinguishability`'s docstring | Write what a thing omits and why. The proof opens `move=> _`: the threshold hypothesis is the `ipc_close` field's shape and is not used, so the bound holds at every coalition. The docstring does not say so, while `var_dist_joint_reading_arg_le`'s next door does. | Add: "The threshold hypothesis is the field's shape; the bound holds at every coalition." |
| X21 | NOTE | `lib/fdist_prod_cond.v:90-92, 103-104, 114-116` | the docstrings of `sum_prod_fibreE`, `fdistmap_pair_fst_condE`, `fdistmap_prod_mixtureE` | Each states the fact and no position. Acceptable here, because the file header carries the position for all three in one place ("The three equations before it are the mass computations of its proof"), which is where long exposition belongs. Recorded so a later pass does not read the omission as an oversight. | none |
| X22 | NOTE | `manifest/pgg_tableau_security_property_relations.v:57-58` | "where the input-indistinguishability proposition holds at that epsilon twice" | True by `cert_eps cert := sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert)` (`manifest/pgg_tableau.v:493-496`) and `indistinguishability_tail`, but no general lemma writes it; only the instance version `pgl27_word_proximity_eps_halfE` does. The earlier audit's `cert_eps_dbl` was not landed. | Optional: land `cert_eps_dbl (cert : IndistinguishabilityCert sa) : cert_eps cert = sw_bound_eps (ic_b cert) *+ 2` beside `cert_eps`, and cite it here. |
| X23 | NOTE | `manifest/pgg_tableau_security_property_relations.v:269-271` | "A threshold scheme's parameter is a successor by construction" | This is the proof (`by rewrite /profile_k /ts_k`, with `ts_k' : nat` and `ts_k = ts_k'.+1` at `reconstruct/pgg_sharing_framework.v:49,89`). It is also the reason the statement is true, so it reads as content rather than as narration. Left as a note rather than a fix. | none, or move to a plain comment above the proof and keep only "so the empty coalition is below the threshold at every algebra". |
| X24 | NOTE | `manifest/pgg_tableau_security_property_relations.v:100-102` | `idealproximity_prop_lt2_uniform_in_cert_false == below two the ideal-proximity proposition fails of some certificate over a model` | The statement is `~ (forall cert, IdealProximityPropAt cert c)`, a negated universal; "fails of some certificate" writes an existential the statement does not. The docstring's own first sentence has it right. | "== below two the ideal-proximity proposition does not hold of every certificate over a model". |
| X25 | NOTE | `manifest/pgg_tableau_security_property_relations.v:313-315` | "The disagreement between the two secrets is the whole of the argument" | Proof narration. The sentence after it, "no property of the model enters", is the scope statement and survives on its own. | Drop the first clause, keep "No property of the model enters." |
| X26 | NOTE | `manifest/pgg_tableau_security_property_relations.v:564-568` | "The two joint laws the proposition compares are two laws and its number is read off neither" | Tautological ("two joint laws … are two laws"). The point is that neither law reduces to the other by conversion. | "Neither of the two joint laws the proposition compares reduces to the other, and its number is read off neither, so the term is rejected." |
| X27 | NOTE | `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:1035` | `pgl27_word_proximity_eps_sw_boundE` beside `pgl27_word_proximity_eps_halfE` (:892) | Keep only claimed or premise. The file already proves `cert_eps (pgl27_word_cert secretP) = ipc_eps (…) + ipc_eps (…)`, which with `cert_eps`'s definition gives the new equation. It earns its place because it is the only statement naming `sw_bound_eps (ic_b …)`, which is the field a construction would read; recorded so the overlap is on the record. | keep |
| X28 | NOTE | `lib/fdist_prod_cond.v:15-18` | "The three equations before it are the mass computations of its proof" | Proof strategy, but in the file header, a plain `(* … *)` comment, which is where the rule sends it. Correct as placed. | none |

## The new file `lib/fdist_prod_cond.v`

- **Boxed style with an index.** Yes. Two infotheo copyright lines, the
  80-column rule, the `name: description` line in the tree's form, three
  prose paragraphs, a `Lemmas:` block with five entries at `==` column 29 and
  continuation column 33, the closing rule. All 38 header lines measure 80
  bytes. It matches `lib/var_dist_supp.v:1-30` line for line in shape.
- **Does the name say what it holds.** Not for `inde_RV_cst`. See X18.
- **Imports minimal.** `From HB Require Import structures.`,
  `all_boot all_order all_algebra`, `boolp reals`, and from infotheo
  `realType_ext fdist proba`. This is `lib/var_dist_supp.v`'s import block
  minus `lra` and `variation_dist`, which the file does not use, and it does
  not pull `entropy` or `variation_dist`. The scope opens
  (`ring_scope`, `fdist_scope`, `proba_scope`) are each used:
  `proba_scope` for `|=` and `_|_`. Minimal for this tree's idiom.
- **Listed in `_CoqProject`.** Yes, line 36, directly after
  `lib/var_dist_supp.v:35` and before the `smc/` block, beside the other
  `lib/` files.

## The rewritten header of `manifest/pgg_tableau_security_property_relations.v`

- **Index complete.** No. Six entries missing, X1.
- **Index order.** The nine entries present are in file order, and the
  `Definitions:` block precedes `Lemmas:` as the tree's other headers have it.
- **One spelling of each proposition.** Yes. "the ideal-proximity
  proposition" and "the input-indistinguishability proposition" are the only
  spellings in the new prose and the new index entries; no abbreviation of
  indistinguishability appears anywhere in the landing. "Security property",
  "security evidence", "certificate", "witness", "model", "ideal", "program",
  "path", "run argument", "cut" are each used in one sense. The one word that
  carries two senses is "reading", X13.
- **The "Not claimed." paragraph.** It now excludes exactly what the landing
  does not prove, and both exclusions check out against the sources: the
  refutation is of a universal over certificates
  (`idealproximity_prop_lt2_uniform_in_cert_false`), and the construction
  produces its own certificate
  (`idealproximity_cert_of_indistinguishability`), so neither reaches a
  certificate an instance chose. The paragraph before it over-claims by
  omission, X14.
- **Claims checked against the statements.** The refutation paragraph is
  accurate: `MkIdealProximityCert`'s field order
  (`manifest/pgg_tableau.v:230-236`) puts the ideal first, so
  `idealproximity_cert_cst_secrets_true_false` does have ideal `sa`, ideal
  secret `fun=> true`, own secret `fun=> false` and number two;
  `IdealProximityPropAt` (`:514-527`) does compare the actual joint law with a
  product whose second factor is the ideal secret's marginal, so "carry mass
  at no common point of the secret coordinate" is the right description;
  `indistinguishability_tail` (`:757-760`) does prove
  `IndistinguishabilityPropAt cert (cert_eps cert)` with no hypothesis.
- **Banners.** Three new banners, each three lines, one content line, all 80
  bytes with a space before the closing delimiter.

## Placement

Upward only. The one direction worth checking is the two model files, and
both hold:

- `instances/pgl27/pgl27_models.v` and
  `instances/kim2025/five_card_models.v` gained no import in this landing
  (the diff adds only lemmas and index lines to both), and neither contains
  the token `pgg_tableau`, `Tableau` or `manifest` anywhere. Each imports
  `manifest/pgg_analysis_status.v`, which despite its directory is a status
  enumeration that both files already imported and that the Tableau
  framework sits above, not below. Everything the four new instance lemmas
  name was in scope: `fdistmap_prodr` and `sa_arg`/`sa_cut`/`sa_sampleP` from
  `security/pgg_sample_adapter.v`, `five_card_sample_arg` from
  `instances/kim2025/five_card_exec.v`, `rho_word` from
  `instances/pgl27/pgl27_word_privacy.v`.
- `lib/fdist_prod_cond.v` requires mathcomp and infotheo only.
- `security/var_dist_joint_law.v` gains `var_dist_fdistmap_prodR_le`, proved
  from `var_dist_fdistmap` (`security/pgg_collusion_bound.v`) and
  `var_dist_prodR` (the same file); no new import.
- `manifest/pgg_tableau_security_property_relations.v` is the only file that
  gained imports, and all four targets are below it: `lib/fdist_prod_cond.v`,
  `security/var_dist_joint_law.v`, `reconstruct/pgg_sharing_framework.v`
  (whose sibling `algebraic_rigidity` it already imported), and it keeps
  `manifest/pgg_tableau.v` last. Nothing imports this file.
- The two `tableau/*_analysis_bridged.v` files gained no import; `ipc_eps`,
  `sw_bound_eps` and `ic_b` come from `manifest/pgg_tableau.v`, already there.

`_CoqProject` order is not the build order in this tree, so the arrows above
were read from the `Require` lines rather than from line numbers.

## Layout

Every added line was measured in bytes.

- No added line exceeds 80 bytes, none carries trailing whitespace, a tab or a
  non-ASCII byte.
- Every new banner is 80/80/80 with a space before the closing delimiter.
- Two index lines are 79 where the box is 80: X5.
- One index entry disagrees with its own continuation column: X6.
- The in-proof comment at `security/var_dist_joint_law.v:155` is 77 bytes,
  which is correct: it is a plain comment, not a box line.
- Continuation columns: `lib/fdist_prod_cond.v` 33 throughout,
  `lib/var_dist_supp.v` 36, `security/var_dist_joint_law.v` 36,
  `manifest/...relations.v` 36, the two `tableau/*_analysis_bridged.v` 32,
  `instances/pgl27/pgl27_models.v` 36. Each matches its own file's existing
  entries. Only `instances/kim2025/five_card_models.v` is mixed, and that file
  was mixed before the landing.
- No orphan short line mid-paragraph in any new header paragraph or docstring.

## Vocabulary

Clean. Neither barred noun appears in any landed file, in any new identifier,
comment or index entry. No token of a capital letter followed by a digit
appears in any comment (the only matches are proof-local hypothesis names
`H2`, `H2c` and the variable names `Q1`, `Q2`, which are not comments). No
abbreviation of "indistinguishability" appears. No plan, ledger or audit
token, no "Used by", no status or history word ("now", "already", "landed",
"no longer", "still"), no "key lemma" or "headline", no word from the owner's
barred list. "The sum of absolute differences" is written in full wherever the
concept is named.
