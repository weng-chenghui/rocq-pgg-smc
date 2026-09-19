# Naming and style audit of landing 3 (PGL(2,7))

Adversarial audit of the permanent text of landing 3, read from the frozen
export
`/private/tmp/claude-501/.../scratchpad/land3_frozen/notes/probes/2026-09-20-tableau-extensions-landing3/staged/`
(same text as the repository at `0c4a4ef`). Read-only on the repository except
this file. Nothing was compiled: two other sessions hold the Rocq lock. Where a
finding needs a compile to settle, the row says so.

Text audited:

- NEW `staged/instances/pgl27/pgl27_proximity.v`, in full (24 non-`Fail`
  declarations, 3 recorded `Fail`s, the file header, every section banner and
  every in-proof comment).
- The added text only of `staged/instances/pgl27/pgl27_exec.v` (20 lines),
  `staged/instances/pgl27/pgl27_models.v` (8), `staged/instances/pgl27/pgl27_analysis.v`
  (7), `staged/manifest/pgg_analysis_manifest.v` (89) and
  `staged/manifest/pgg_analysis_client.v` (2), each obtained by diffing the
  staged file against production's file of the same path.

The other thirteen staged files are chain copies and were not read.

---

## VERDICT: NO-GO

Four MUST, sixteen SHOULD, fifteen NOTE.

Every MUST and every SHOULD is a comment, a header entry or one identifier
rename. Not one touches a statement, a proof term, a `Require`, or an
identifier cited by a production file. The single rename (L3) is a name new in
this landing whose only other citation is the landing's own
`landing_fidelity.v`, so it is free. Soundness is untouched by the whole punch
list. A recompile of `pgl27_proximity.v` and of the manifest is owed after the
edits, because a comment edit can break a delimiter; nothing else needs
rebuilding.

The mechanical checks are clean: no line over 80 bytes in the new file or in
the added text of the five edited files, no box-comment line whose closing
`*)` is off column 80, no word of the project's banned vocabulary list, no
abbreviation of "indistinguishability", and no occurrence of the metaphor noun
the landing-2 fix pass removed. The collision scan returns nothing.

The four MUST are: a header paragraph that attributes both of the instance's
numbers to a lemma that does not carry them and is not stated on the carrier
the sentence names, while duplicating the declaration comment 290 lines below
it (L1); a docstring that says the manifest's row is read off the program when
the manifest declares that row itself (L2); a lemma whose name says it is
about the arms when its statement is about the model family (L3); and two
copies of a sentence about a document outside the development that landing 2
already removed from the sibling file (L4).

Two of the four MUST (L1 in its second half, L4) and eight of the sixteen
SHOULD (L5, L6, L7, L10, L11, L12, L19, L20) are recurrences of defect classes
the landing-2 audit named and the landing-2 fix pass applied to
`instances/kim2025/five_card_proximity.v`. Each is listed with its landing-2
identifier in the evidence column, together with the production line where the
fixed wording now sits. The two MUST that are new to landing 3 are L2, a false
claim about where the manifest's row comes from, and L3, a name that states a
different object than its statement.

---

## Findings

| id | class | file:line | quoted text | problem, with evidence | replacement |
|---|---|---|---|---|---|
| L1 | MUST | `pgl27_proximity.v:29-36` | "Both numbers this instance carries come from one distance, **pgl27_view_mixing on the cut group**. The certificate below carries 2^-40, and pgl27_word_cert of pgl27_rows.v carries that number added to itself, **because the input-indistinguishability arm spends the distance once for each of the two dealt secrets it compares and the proximity arm compares one law with one law. The relation is between those two certificates and not between the two arms**" | Two defects in one paragraph. (a) False attribution. `pgl27_view_mixing` (`instances/pgl27/pgl27_word_privacy.v:235`) is stated on the joint law of a coalition's reading and the secret against the product of the two exact-shuffle marginals, not on the cut group. Neither number is read off it: `ipc_eps (pgl27_word_proximity_cert …)` is `sw_bound_eps (pgl27_word_marginal_bound R)` (`pgl27_proximity.v:294`), and `cert_eps cert` is by definition `sw_bound_eps (ic_b cert) + sw_bound_eps (ic_b cert)` (`manifest/pgg_tableau.v:470-473`) with `ic_b (pgl27_word_cert …) = pgl27_word_marginal_bound R` (`instances/pgl27/pgl27_rows.v:271`). `pgl27_word_marginal_bound` is `@MkShuffleMarginalBound R pgl27_M 200 (2%:R^-40) rho_word (@pgl27_endpoint_mixing R)` (`instances/pgl27/pgl27_word_privacy.v:90-92`), and `pgl27_endpoint_mixing` (`instances/pgl27/pgl27_mixing.v:1064`) is proved by `le_trans … pgl27_word_mixing` (`:1070`). The distance on the cut group is `pgl27_word_mixing` (`:1048`), which is the lemma the declaration comment at `:321` names correctly, so the file names two different lemmas for one role and the header names the wrong one. (b) Duplication. The two bolded clauses are verbatim in `pgl27_word_proximity_eps_halfE`'s docstring at `:320-329`, at `:322-326`. Landing-2 N3 and N4 on the same shape: a header is exposition anchored to nothing, not a copy of a declaration comment that sits hundreds of lines below it and will drift against it. | "Both certificates over the word model carry one number, the walk's single-card marginal number 2^-40 of pgl27_word_marginal_bound, which rests on pgl27_word_mixing, the distance between the word walk and the uniform cut on the group. The proximity certificate carries it once and the input-indistinguishability certificate twice, and pgl27_word_proximity_eps_halfE says which is which. The row concludes at 2^-39, the number pgl27_row_word_branch39 publishes for the other arm, so the two rows over this model are read in one column, and the terminal's obligation is met strictly. Each of these numbers bounds a sum of absolute differences, twice the total variation distance, so a distinguisher's advantage against the published row is at most 2^-40." Re-box to column 80. |
| L2 | MUST | `pgl27_proximity.v:189-194` | "Its five coordinates are the observed execution the program runs on, the completion level the publish terminal reaches, the model family the sample step named, and the two statuses the terminal was given, **so the manifest's description of this path is read off the program and not written beside it**." | False. `pgl27_row_prior_exact` is a hand-written `Definition` in `staged/manifest/pgg_analysis_manifest.v` (`@MkAnalysisPathRow PGL27Analysis.observed AnalysisBridged PGL27Analysis.prior_exact_family StaticExecutedOnly BaselineClassicalOnly`), (`:986-988`), with a 60-line table block written beside it at `:699-758` of the same file. Nothing is read off the program. What the lemma says is that the hand-written row and the row the program publishes are one value, decided by conversion (`Proof. exact: erefl. Qed.`), and that the two sides are written in different vocabularies, the manifest's facade aliases against this file's raw names. That is the position, and it is stronger than the sentence as written: the manifest cannot drift from the program. | "The manifest's typed row for the eight-card orbit instance at the prior-indexed exact shuffle is the row this program publishes. Its five coordinates are the observed execution the program runs on, the completion level the publish terminal reaches, the model family the sample step named, and the two statuses the terminal was given. The manifest writes them in the facade's vocabulary and the program in this file's, and conversion decides the equation, so the row the manifest declares cannot describe a path the program does not run." |
| L3 | MUST | `pgl27_proximity.v:413` (also header `:89`, `landing_fidelity.v:207-212`, `:305`) | `Lemma pgl27_row_word_arms_sampledE` | The name says the lemma is about the arms; the statement is about the model family. It equates `ab_f (published_at …)` with `sp_f (tableau_at pgl27_word_sampled)`, and `ab_f` is the `AnalysisModelFamily` accessor (`manifest/pgg_tableau.v:351-353`), `sp_f` its `Sampled` counterpart (`:334`). The arm is `security_arm_of`, and this file uses `arm` in that sense in `pgl27_row_word_arm_neq` (`:440`), `pgl27_row_prior_exact_armE` (`:184`) and `pgl27_row_word_proximity_armE` (`:404`). The sibling lemma `pgl27_row_word_obs_sampledE` (`:425`) names the field it is about, `ab_obs`, so the pair is asymmetric. The file's own header entry contradicts the name: `:89-92` reads "both rows over the word model read their **model family** off the one named Sampled value". There is no `ab_arms` field anywhere. The name is new in this landing; the only other citation is `landing_fidelity.v:207-212` and `:305`, both in the landing's own probe instrument, so the rename is free. No production file cites it. | `pgl27_row_word_families_sampledE`. Update the declaration, the header entry at `:89`, and the two lines of `landing_fidelity.v`. |
| L4 | MUST | `pgl27_proximity.v:182-183` and `:402-403` | "This is the value a paper's table prints in the arm column for the ideal row." / "This is the value a paper's table prints in the arm column for this row." | A claim about a document outside the development, unverifiable from the artifact, and a usage pointer of the kind the statement-comment rule excludes. Landing-2 N16 flagged the single occurrence of this sentence in `five_card_proximity.v` and the fix pass deleted it; production `instances/kim2025/five_card_proximity.v:394-396` now carries only "The arm the proximity row carries, at every real field and index: the distance to a private ideal model, and not the distance between two readings of one model." The landing reintroduces the sentence twice. In both places the sentence before it already gives the fact and the position, in mathematical terms. | Delete both sentences. What remains at `:180-182` is "The arm the ideal row carries, at every real field and prior: independence of the dealt secret, and not a distance to some other model." and at `:400-402` "The arm the proximity row carries, at every real field and prior: the distance to a private ideal model, and not the distance between two readings of one model." |
| L5 | SHOULD | `pgl27_proximity.v:379-381` | "The number is spent once, against the input-indistinguishability row's twice, and **the transfer status is the one the input-indistinguishability row earns**, since the same ideal cut is what both certificates compare against." | `IdealFinite` is written into the `publish` clause at `:386`; it is chosen, not derived, so nothing is earned. Landing-2 N27 raised the identical sentence in `five_card_proximity.v` and the fix pass applied its replacement; production `five_card_proximity.v:357-359` now reads "Its transfer status is IdealFinite, the same the input-indistinguishability row carries, and the two certificates compare against the same ideal cut." | "The number is spent once, against the input-indistinguishability row's twice. Its transfer status is IdealFinite, the same the input-indistinguishability row carries, and the two certificates compare against the same ideal cut." |
| L6 | SHOULD | `pgl27_proximity.v:19-23` | "pgl27_view_indep_gen is three-transitivity of PGL(2,7) on the eight points read as a privacy statement, and three-transitivity says nothing about how the secret is drawn" | Duplicates the docstring of `pgl27_prior_exact_witness` at `:150-152`: "The independence is pgl27_view_indep_gen, three-transitivity of PGL(2,7) read as a privacy statement, which holds whatever the law of the secret is." Landing-2 N4, second instance of the same class as L1(b). The header's own frame, which no declaration states, is the first sentence and the last: the ideal's privacy is a theorem and not an assumption, and which two declarations carry it. | Cut the paragraph to "The ideal's own privacy is a theorem and not an assumption. pgl27_row_prior_exact_tableau publishes the exact execution through the exact arm at every law of the dealt secret, and pgl27_word_proximity_cert_idealE says that the model the proximity certificate calls ideal and the model that row publishes are one term." |
| L7 | SHOULD | `pgl27_proximity.v:357-359` | "At about 4.5e-13 of that bound it is a cryptographic separation and not a weak one, **as the proximity certificate of Kim's one-cut model is**." | The trailing clause attaches to either predicate, so the sentence reads either as "Kim's is also a cryptographic separation", which is false, or as "Kim's is a weak one", which is what the tree holds: production `five_card_proximity.v:311-314` says of that certificate "At one percent of that bound it is a weak separation and not a cryptographic one". Landing-2 N13 named this ambiguity at the five-card side and the fix pass replaced it with the unambiguous "as is X at N" form. Here the polarity is inverted, which makes the wrong reading the one a careless reader takes. | "At about 4.5e-13 of that bound it is a cryptographic separation, where the proximity certificate of Kim's one-cut model at one percent of the same bound is a weak one." |
| L8 | SHOULD | `pgl27_proximity.v:218-221` | "The premise is the arm's threshold at this instance, four seats, and **the proof spends it twice, on the ideal model's own independence and on pgl27_view_mixing**." | A proof account with the names of the two lemmas the proof applies, inside the docstring. The rule puts those in a plain `(* *)` comment inside the proof, and the file already carries one at `:240-243` which is the right home and already names `pgl27_view_mixing`. The sibling `kim_biased_proximity_close` (`five_card_proximity.v:208-217`) states instead what the bound does not need, which is the scope fact and survives a reproof. | Docstring: "The premise is the arm's threshold at this instance, four seats." Then in the proof comment at `:240-243`, append: "The threshold is used twice, once for the ideal witness's independence and once for pgl27_view_mixing." |
| L9 | SHOULD | `pgl27_proximity.v:344-345`, header `:81` | "The certificate's number **is under 2^-39**" / "pgl27_word_proximity_le39 == the certificate's number **is under** 2^-39" | The statement is `ipc_eps (pgl27_word_proximity_cert secretP) <= 2%:R^-39` (`:349`). "Under" is strict and the statement is not. The `conclude` terminal's obligation is the non-strict one, which is why the lemma is stated that way, and the strictness is a separate remark the next sentence already makes. | Docstring: "The certificate's number is at most 2^-39, the constant the word row publishes for the input-indistinguishability arm. It is the obligation of the terminal that concludes the proximity row at that constant, and the obligation is met strictly, the certificate's number being half of the published one." Header entry: "== the certificate's number is at most 2^-39". |
| L10 | SHOULD | `pgl27_proximity.v:73-74` | header entry "pgl27_word_proximity_cert_idealE == the certificate's ideal **is the ideal row**" | Two defects, both already raised at the five-card side. (a) A model is not a row (landing-2 N26); the lemma equates `ipc_ideal …` with `amf_sample (ab_f (published_at pgl27_row_prior_exact_tableau)) R secretP`, which is the model that row publishes. (b) The lemma is a conjunction (`:302-308`) whose second half equates `ExactIndependence (ipc_witness …)` with `ab_port (published_at …) R secretP`, which the entry omits (landing-2 N28). Production `five_card_proximity.v:77-80` carries the fixed form. The declaration's own comment at `:299-301` is already correct and says "the model … publishes". | "pgl27_word_proximity_cert_idealE == the certificate's ideal and witness are the ideal row's model and port" |
| L11 | SHOULD | `pgl27_proximity.v:77-78` | header entry "pgl27_word_proximity_eps_halfE == pgl27_word_cert's number is twice **it**" | "It" has no antecedent inside the entry. Landing-2 N25 raised the identical entry at the five-card side and the fix pass replaced it; production `five_card_proximity.v:83-86` now reads "the exact input-indistinguishability certificate's number is twice the proximity certificate's". | "pgl27_word_proximity_eps_halfE == the input-indistinguishability certificate's number is twice the proximity certificate's" |
| L12 | SHOULD | `pgl27_proximity.v:62-64` and `:135-136` | "the framework's reading of a coalition at the prior-indexed exact shuffle is the instance's **coalition view**" / "The framework's static reading of a coalition at this model is the instance's **coalition view**, with the secret left inside the sample point." | Landing-2 N10 settled the vocabulary: "reading" in prose, "view" only where it spells an identifier. These are the file's only two prose uses of "view"; the other 20 occurrences spell `pgl27_view`, `sa_coalition_view`, `pgl27_view_indep_gen`, `pgl27_view_mixing`, `pgl27_word_view_proximity` or `view_proximity_of`. The replacement must keep the sentence's real content, which is that two different readers are identified: `static_coalition_obs …` on the left and `pgl27_view R C` on the right. | Header entry: "== the framework's reading of a coalition at the prior-indexed exact shuffle is the instance's own reading, pgl27_view". Docstring: "The framework's static reading of a coalition at this model is the instance's own reading pgl27_view, with the secret left inside the sample point." |
| L13 | SHOULD | `pgl27_proximity.v:97` | header entry "pgl27_word_view_proximity == **what the row states at this instance**" | Says nothing a reader can check, and names neither the bound nor the number, where every other entry of the block does. The sibling entry, `five_card_proximity.v:109-110`, reads "five_card_biased_view_proximity == the proximity row's security statement". The theorem (`:472-482`) bounds the distance between the word model's joint law of reading and secret and the product of the exact model's two marginals by `2%:R^-39`, at `#|C| <= 3`. | "pgl27_word_view_proximity == the proximity row's security statement, at 2^-39" |
| L14 | SHOULD | `pgl27_proximity.v:75-76` | header entry "pgl27_word_proximity_cert_epsE == the certificate's number **in closed form**" | The statement is `ipc_eps (pgl27_word_proximity_cert secretP) = 2%:R^-40` (`:317`). "In closed form" describes the shape of the statement rather than saying what the number is, where the sibling entry `five_card_proximity.v:81-82` reads "the certificate's number is one fiftieth". | "pgl27_word_proximity_cert_epsE == the certificate's number is 2^-40" |
| L15 | SHOULD | `pgl27_proximity.v:545` (and header `:100`) | `Lemma pgl27_word_uniform_ideal_not_close` | The statement is the negation of the certificate's `ipc_close` field, so `close` in the name is right, but the tree spells a refutation with a `_false` suffix and not with a `not_` infix: `kim_biased_conclude_below_false` (`five_card_proximity.v:482`) and `psl211_alldecks_constancy_false_word584` (`instances/psl211/psl211_reading_constancy.v`). A second thing the name and the entry both miss: the statement carries no coalition premise, so it holds at every `C` and is strictly stronger than the field, which is asked only below four seats. The docstring at `:537-544` states the mathematics well and says nothing about that. | Rename to `pgl27_word_uniform_ideal_close_false`. Header entry: "== the distance field is false at every coalition, with the uniform-secret exact model as the ideal of the word model at a point-mass prior". Add to the docstring: "It is stated at every coalition and not only below four seats, so it refutes more than the field asks." |
| L16 | SHOULD | `pgl27_proximity.v:514`, `:98-99` | `Lemma var_dist_fdist1_uniform` and its home | The lemma is general: `var_dist (fdist1 true : R.-fdist bool) (fdist_uniform (R := R) card_bool) = 1`, with no PGL(2,7), no PGG object and no framework type in it. It is declared global and unprefixed inside an instance file. The tree's precedent for a general variation-distance lemma inside an instance file is `Local`: `instances/pgl27/pgl27_mixing.v:1077` and `instances/psl211/psl211_mixing.v:577`, both `Local Lemma var_dist_prodR`. The orchestrator's own R7 decision (`notes/2026-09-20-000000-tableau-extensions-landing-design.md:1228`) resolved the parallel case for `pow2_40_ge1` and `pow2_40_gt0` by prefixing them with the instance, and R8 (`:1230`) states the principle that declarations naming no instance do not go to an instance file. Neither treatment was applied here. Two ways out, and neither is a one-file change. (a) `Local`: one line, but it breaks `landing_fidelity.v:243-246` and `:309`, which restate the lemma by name. (b) Move to `lib/var_dist_supp.v`: that file's imports are `all_boot all_order all_algebra boolp reals` plus infotheo `realType_ext fdist proba variation_dist` (`lib/var_dist_supp.v:27-30`) and do not include `lra`, which this proof uses at `:529`, and `pgl27_proximity.v` does not `Require var_dist_supp`, so the move costs an import in `lib/`, a `Require` line here, and a compile of both files. Needs a compile either way. | Owner's call. My reading: (b), because the header of `lib/var_dist_supp.v` already advertises itself as the home of the distance facts a certificate's number is read against, and the PSL(2,11) landing will want the same refutation shape. If (b) is declined, prefix the name `pgl27_var_dist_fdist1_uniform`, matching the R7 treatment of the two `pow2_40` facts, so that no unprefixed general name is declared from an instance file. |
| L17 | SHOULD | `staged/manifest/pgg_analysis_manifest.v:756-758` (Row 10 block, which runs `:699-758`) | "Row 1 records the same instance and the same cut at the uniform secret alone, its family being indexed by the unit type; **the two rows differ in that index and in nothing else**." | The two rows differ in one of their five coordinates, the model family: `pgl27_row_exact` carries `PGL27Analysis.exact_family` and `pgl27_row_prior_exact` carries `PGL27Analysis.prior_exact_family`. What differs inside the family is both the index type and the member at each index: `pgl27_exact_family` is `@MkAnalysisModelFamily pgl27_observed (fun _ => unit) (fun R _ => pgl27_sample R)` (`instances/pgl27/pgl27_models.v:417-419`) and `pgl27_prior_exact_family` is `@MkAnalysisModelFamily pgl27_observed (fun R => R.-fdist bool) (fun R p => @pgl27_prior_sample R p)`. "Differ in that index and in nothing else" is false of the families and imprecise about the rows. | "Row 1 records the same instance and the same cut at the uniform secret alone, its family being indexed by the unit type. The two rows agree in their other four coordinates and differ in the model family, which here is indexed by the law of the dealt secret." |
| L18 | SHOULD | `staged/manifest/pgg_analysis_manifest.v:983-985` (the `pgl27_row_prior_exact` docstring, `:975-985`) | "It differs from pgl27_row_exact **in the index type of its model family alone**" | Same fact as L17 at a second place. The two families differ in the index type and in the sample map; at the unit family's one index the member is `pgl27_sample R`, whose law is `pgl27P R = (fdist_uniform card_bool) `x (`U pgl27_G_pos)` (`instances/pgl27/pgl27_secrecy.v:66-67`), while this family's member at a prior `p` has law `p `x (`U pgl27_G_pos)`. The two coincide at the uniform prior; they are not one term. | "It differs from pgl27_row_exact in its model family, whose index is the law of the dealt secret where the other's is the unit type, and that index is what lets a row over the word model and a row over this one be read at one law of the secret." |
| L19 | SHOULD | `staged/instances/pgl27/pgl27_exec.v:636-639` (in the `pgl27_prior_sample` docstring, `:632-639`) | "It differs from pgl27_sample only in refusing to fix the prior, which is **the coordinate** a comparison with the word model at that prior needs to hold." | The factual half is right: `pgl27_sample` is `@MkSampleAdapter … (pgl27P R) fst snd` (`:439-441`) and `pgl27P` is `(fdist_uniform card_bool) `x (`U pgl27_G_pos)` (`instances/pgl27/pgl27_secrecy.v:66-67`), so the only difference is the first factor of the law. The word "coordinate" is the defect. `pgl27_exec.v` already uses it in a fixed framework sense, the coordinate law `ord_coordE`, at `:20`, `:31`, `:329`, `:399` and `:411`. Landing-2 N11 is the same class: one word carrying two senses inside one file. | "It differs from pgl27_sample only in leaving the law of the dealt secret free, which is what a comparison with the word model at the same law requires." |
| L20 | SHOULD | `pgl27_proximity.v:624-626` | "The payload type is IdealProximityPayload at **the coordinate** the Sampled value holds, so the clause is checked first against the index type **that coordinate's** family carries" | Third sense of "coordinate" in this file, used twice in one sentence. At `:190` it is a field of an `AnalysisPathRow` ("Its five coordinates are …") and at `:388` a field of a published row ("an equation between two rows' coordinates"). Here it means the model-family slot of the `Tableau Sampled` state, which is `sp_f` (`manifest/pgg_tableau.v:334`). Landing-2 N11. | "The payload type is IdealProximityPayload at the model family the Sampled value names, so the clause is checked first against that family's index type, unit against a distribution on the booleans." |
| L21 | NOTE | `pgl27_proximity.v:487-489` (section banner) | "The ideals the proximity arm refuses" | The sibling file splits this material into two sections, "A number below the certificate's is refused" (`five_card_proximity.v:468-470`) for the proved refutation and "What a certificate may name as its ideal" (`:527-529`) for the recorded `Fail`s. The new file merges them, and the merged banner attributes refusal to the arm where two of the three rejections are the kernel's and the middle pair is a theorem. Against that, the interleaving here is content-driven: the `Fail` at `:612` is explained by the lemma at `:545` directly above it, which the comment at `:605-611` says explicitly. Splitting would break that. | Optional. If the two files are to read alike, rename the banner to "What a certificate may name as its ideal, and what refutes one" and leave the order alone. |
| L22 | NOTE | `pgl27_proximity.v:98-99` | header entry "var_dist_fdist1_uniform == **a point mass** and the uniform law on the booleans are one apart" | The statement is at one point mass, `fdist1 true` (`:515`). The fact is true of either, but only the one is proved. | "== the point mass at true and the uniform law on the booleans are one apart" |
| L23 | NOTE | `pgl27_proximity.v:592-594` | `have Hge : (1:R) <= 2%:R^+39 …` and `have Hpos : (0:R) < 2%:R^+40 by rewrite exprn_gt0 // ltr0n.` | `Hpos` is `pgl27_pow2_40_gt0` (`:341-342`) proved again by the same one-line script fifty lines below the `Fact`, and `Hge` is the `_ge1` shape at 39. The two `Fact`s are declared as premises of `pgl27_word_proximity_le39` and are used there and in `_cert_eps_lt2` (`:364-365`), so their position claim is already earned; the duplication only makes the file say a thing twice. | Optional: `have Hpos := pgl27_pow2_40_gt0 R.` Needs a compile to confirm the implicit-argument spelling. |
| L24 | NOTE | `pgl27_proximity.v:388-389` | `(* exact: erefl and not by []: done does not return on an equation between two rows' coordinates. *)` | Correctly a plain `(* *)` comment and not part of a docstring, which is what the rule asks. Its placement differs from the sibling's: `five_card_proximity.v:338-339` puts the same comment between the docstring and the `Lemma`, where this one sits before the docstring of `pgl27_row_word_proximity_rowE` and so reads as attached to the `Definition` above it. Landing-2 N31 recorded the same convention question. | Optional: move it inside `Proof. … Qed.` of `pgl27_row_word_proximity_rowE`, which is the placement the rule names and which `pgl27_row_word_obs_sampledE` (`:431-433`) already uses. |
| L25 | NOTE | `pgl27_proximity.v:431-433` and `:444-453` | the two in-proof timing comments, "96.0 s by exact: erefl and 48.1 s by reflexivity", "costs 78.7 s in the statement alone" | Correctly placed: proof strategy in a plain comment inside `Proof`, which is where the rule puts it, and each number is the reason one line reads as it does. Two qualifications. The numbers carry no machine, date or toolchain, so they cannot be reproduced or falsified; and `five_card_proximity.v` carries no timing numbers at all, so the two sibling files differ in this. | Owner's call. If they stay, they are in the right place. |
| L26 | NOTE | `pgl27_proximity.v:357` | "At about 4.5e-13 of that bound" | The figure is right: `2%:R^-40 / 2%:R = 2^-41 = 4.547e-13`. The probe's stage C audit (N3) recorded it as the only scientific-notation literal in any rendered comment of the probe, against a tree that writes numbers in words ("sqrt 5 over eighty", "one twenty-fifth", "one fiftieth"), and offered an optional rewrite. The landing kept the literal. | Optional, and unchanged from stage C: "At about four and a half parts in ten million million of that bound". Nothing turns on it. |
| L27 | NOTE | `pgl27_proximity.v:36`, `:59`, `:372` | "The row **concludes at** 2^-39" / "the proximity claim, **published at** 2^-39" / "certified by the proximity arm and **concluded at** 2^-39" | Two phrases for one number inside one file. Both are anchored to a real keyword: `conclude` is the terminal at `:385` and `publish` the terminal at `:386`, and the framework's own gloss of `conclude` is "the terminal publishing an upper bound of the accumulated bound". The sibling file uses "published at" only, its row having no `conclude` step. | Optional. Keep "concluded at" for the terminal and "publishes" for the number a finished row carries, and make the header entry at `:59` read "the proximity claim, concluded at 2^-39". |
| L28 | NOTE | `staged/manifest/pgg_analysis_manifest.v:712-713` against production `:129` | "random variable on the law of prior_sample at the row's index" against Row 1's "prior R, the distribution of exact_sample" | The manifest already uses "prior" as a name for a sample law (`pgl27P`), at `:129`, `:131`, `:260`, `:262`, `:264`. Landing 3 introduces `prior_sample` and `prior_exact_family`, where "prior" means the law of the dealt secret. Row 10's text avoids the clash by spelling out "the law of prior_sample at the row's index", which is the right call, but the two senses now sit in one file. Stage C N1 settled the identifier names and found "prior" to be the tree's word for the law on the dealt secret (44 and 28 occurrences in the two PGL(2,7) files). | No action on the names. Optional, and outside landing 3's remit: a later pass could change the manifest's capability column from "prior R" to "the law of exact_sample" so that "prior" has one sense in the file. |
| L29 | NOTE | `staged/instances/pgl27/pgl27_exec.v:632`, `pgl27_models.v:428`, `pgl27_analysis.v:176`, `:186` | the leading-name convention and its dash | Checked as the remit asks. The three edited instance files do use the convention for their other declarations, and the dash is the em-dash in every case: 53 of 53 docstrings in `pgl27_exec.v`, 19 of 19 in `pgl27_models.v`, 45 of 45 in `pgl27_analysis.v`, all with `—`. The four added docstrings follow it with the same character. No mix anywhere. `pgl27_rows.v` (49 docstrings) and `five_card_proximity.v` (32) use no leading name, and the new `pgl27_proximity.v` follows those two and contains no em-dash and no en-dash at all. Both conventions are applied to the right files. | Clean. No action. |
| L30 | NOTE | `staged/instances/pgl27/pgl27_analysis.v:176`, `:186` | "prior_sample — the **exact-uniform** model at an arbitrary secret prior." / "prior_exact_family — the **exact-shuffle** model family indexed by the secret prior" | Checked for drift and clean. `pgl27_analysis.v` already uses "exact-uniform" for the adapter aliases at `:34`, `:163` and `:170`, and "exact-shuffle" for the family alias at `:177`. The two new aliases take the word their layer already uses. | Clean. No action. |
| L31 | NOTE | `pgl27_proximity.v`, whole file | recorded `Fail`s and the header | The file has three recorded `Fail`s and indexes none of them, which is the tree's precedent (`pgl27_rows.v` indexes none of its 10, `five_card_rows.v` none of its 4, production `five_card_proximity.v` none of its 6) and agrees with landing-2 N22 as the fix pass left it. | Clean. No action. |
| L32 | NOTE | whole tree | collisions | A walk over every `.v` file outside `notes/`, `docs/`, `.claude/`, `legacy/`, `blueprint/`, `audit-inventory/` and the paper directories, matching every `Definition`, `Lemma`, `Theorem`, `Fact`, `Corollary`, `Notation`, `Record`, `Inductive`, `Axiom`, `Variable`, `Let`, `Example`, `Instance`, `Fixpoint`, `Remark`, `Proposition`, `Structure` and `Class` head against the 29 landed names including the two facade aliases, returns zero hits. | Clean. No action. |
| L33 | NOTE | `pgl27_proximity.v:106-120` (the `Require` block) against `:358` | the file names `var_dist_le2` in a comment and does not import it | `var_dist_le2` is `lib/var_dist_supp.v:50`; `pgl27_proximity.v` has no `Require` of `var_dist_supp`, where the sibling `five_card_proximity.v:136` does. Naming a lemma from an unimported file in a comment is not wrong, but it is the one place a reader cannot follow the reference from the file, and the import becomes necessary anyway if L16(b) is taken. | Optional, and free if L16(b) is taken: add `var_dist_supp` to the `From pgg_smc Require Import pgg_collusion_bound.` line. Needs a compile. |
| L34 | NOTE | placement of `pgl27_prior_viewE` and `pgl27_prior_exact_witness` | — | The design note's landing-3 table (`notes/2026-09-20-000000-tableau-extensions-landing-design.md:174`, `:247-248`) puts both in `instances/pgl27/pgl27_models.v`; the staged text puts both in `pgl27_proximity.v`. This is a recorded decision, not a drift: `STATUS.md:633` (Q1) accepts it and gives the reason, that `pgl27_static_obsE` is `pgl27_rows.v:159` and `ExactWitness` is `pgg_tableau.v:171`, both strictly below `pgl27_models.v`, so neither could be stated where the table put them. Row 10's "distribution-to-observer bridges" and "final bridge theorem" fields both name `instances/pgl27/pgl27_proximity.v`, so the manifest is consistent with the as-built placement. | Clean. No action. |
| L35 | NOTE | the six files | mechanical | No line over 80 bytes in `pgl27_proximity.v` or in any of the 126 added lines of the five edited files. No box-comment line whose closing `*)` is off column 80, including the 89-line Row 10 block. No hit for any word of the project's banned vocabulary list. No abbreviation of "indistinguishability" and no `_indist` segment; `InputIndistinguishabilityArm` and `IdealProximityArm` are spelled in full at `:457` and `:406`. The metaphor noun for a bound that landing 2's fix pass removed does not occur; both places that need it say "the bound two var_dist_le2 gives", matching production `five_card_proximity.v:311`. The first two lines of `pgl27_proximity.v` are the project's standard licence lines. | Clean. No action. |

---

## Coverage

**Remit 1, permanent-text read.** Every comment of `pgl27_proximity.v` and
every added comment of the five edited files was read in full. No sentence
anywhere speaks of a probe, a stage, a ledger row (P1, P3, P7, P8, K1, T0,
G2), an audit, a fix pass, "the spec", "this batch", "the landing", or a date.
No sentence narrates a rename or an ordering of the work: the words "renamed",
"formerly", "no longer", "used to" and "predate" do not occur, and "already"
occurs four times, each time as a mathematical claim about a term that exists
(`:285-286` "the terms the ideal row already publishes", `:171-172` about the
shared observed prefix, `:493-494`, `:601-602`), not as a history. The
measurement sentences are L25 and are inside proofs, which is where the rule
puts proof engineering; the scientific-notation figure is L26. The only
history-shaped claim I found is `:167` "from the observed prefix the two
existing PGL(2,7) rows share", where "existing" is a fact about the tree at
the moment of reading rather than about the order of writing, and the clause
is load-bearing (it is why the three rows can be compared); I did not flag it.

**Remit 2, statement-comment discipline, every declaration.** All 24 non-`Fail`
declarations of `pgl27_proximity.v` were walked one at a time against the
declaration text, together with the two added definitions
(`pgl27_prior_sample`, `pgl27_prior_exact_family`), the two added facade
aliases, the `pgl27_row_prior_exact` definition and the Row 10 comment block.
Defects: L1, L2, L4, L5, L8, L9, L12, L17, L18, L19, L20, L23, and L7 and L15
in part. The remaining comments state the fact and the position. Four are
worth naming as the standard the rest of the file should be held to:
`pgl27_prior_viewE` (`:135-139`), which says why one equation is the whole of
what carries a row's security statement to an instance theorem;
`pgl27_prior_exact_witness` (`:148-155`), which prices the arm honestly, "The
reading carries no information about the secret at all and not a small
amount"; `pgl27_word_secret` (`:203-206`), which says why the carrier is the
one the ideal's witness names; and `pgl27_word_uniform_ideal_close_false`
(`:537-544`), which states its own scope boundary, "It says nothing at a prior
near the uniform one, where the same lower bound is small."

I could not compile, so every claim rests on reading the declaration. Where a
comment asserts a numeric fact I checked the arithmetic by hand: `2^-40` added
to itself is `2^-39`, so `pgl27_word_proximity_eps_halfE`'s doubling and the
header's "met strictly, 2^-40 being half of 2^-39" are right; `2^-41` is
`4.547e-13`, so L26's figure is right; half of the published `2^-39` is
`2^-40`, so the header's advantage sentence at `:39-41` is right; and
`#|C| < profile_k = 4` is `#|C| <= 3`, so Row 10's "at most three of the eight
seats, the profile's own privacy threshold being four" is right. Three places
I am unsure of and that need a compile. Whether `ipc_secret` of the
certificate is literally the `ew_secret` field of the witness, which
`pgl27_word_secret`'s comment at `:205-206` asserts in words; the type at
`manifest/pgg_tableau.v:220` makes it well-typed but the equality of the two
functions is a separate fact. Whether L23's replacement spells the implicit
arguments right. And whether `ipc_eps` reduces to `2%:R^-40` by conversion as
`pgl27_word_proximity_cert_epsE`'s `exact: erefl` needs; I read that off the
literal `2%:R^-40` in `MkShuffleMarginalBound` at
`instances/pgl27/pgl27_word_privacy.v:91` and believe it, but it is a
conversion claim.

**Remit 3, the file header of `pgl27_proximity.v`.** Every entry of the
`Definitions:` and `Key results:` blocks names an identifier declared in that
same file with that exact spelling: checked mechanically, zero bad entries.
Coverage is total in both directions: 5 definitions and 19 results, 24 of the
file's 24 non-`Fail` declarations, and none of its three `Fail`s. Landing-2 N1,
the MUST of that round, does not recur. Descriptions against declarations:
the `E` entries name both sides in every case except L10, which names one half
of a conjunction; the bound entries are L9 (`<=` written as "under") and
correct at `_cert_eps_lt2` (`<`, written as "below"); the number entries are
L14 and correct elsewhere; L13 and L22 are the two remaining wording defects.
Header prose anchored to nothing: true of paragraphs one and four; L1 and L6
are the two paragraphs that copy declaration comments. Section order against
the sibling: sections 2 to 6 of `pgl27_proximity.v` carry the same five
banners as sections 1 to 5 of production `five_card_proximity.v`, in the same
order and with the same wording. Section 1 is new and is the ideal row, which
five-card takes from `five_card_rows.v` and PGL(2,7) builds here. Section 7 is
L21. Rows, certificates, arm equations and recorded failures are presented in
the same shapes and with the same vocabulary as the sibling, with L5, L7, L10,
L11, L13 and L14 the places where the sibling's fixed wording was not carried
across.

**Remit 4, names.** Each of the 29 landed names was read against its
declaration and against the two sibling files. The `E` suffix is used for an
equation in all ten places it appears, two of them a conjunction of equations,
which is the shape `five_card_row_biased_proximity_publishedE` already uses.
`_le39` is an inequality `<=` and `_lt2` an inequality `<`, matching
`var_dist_le2` and `kim_biased_cert_eps_lt2`; the glued digits follow this
instance's own precedent (`pgl27_reprice39`, `pgl27_row_word39`,
`pgl27_row_word_branch39`), which stage C N2 settled. `_armE`, `_rowE`,
`_tableau`, `_cert`, `_witness`, `_family`, `_sample` all follow
`pgl27_rows.v` and `five_card_rows.v` exactly. `pgl27_prior_*` reads as the
tree's other `pgl27_*` names and stage C N1 settled it with evidence; I have
nothing to add. `pgl27_pow2_40_ge1` and `pgl27_pow2_40_gt0` are the
orchestrator's own R7 decision and are recorded without action. The two facade
aliases `prior_sample` and `prior_exact_family` match `PGL27Analysis`'s
existing alias naming (`exact_sample`, `fixed_exact_sample`, `exact_family`,
`word_family`) and its existing wording, which is L30. The names I would
change are L3 (the name states a different object than the statement), L15
(the refutation suffix) and L16 (the home of the one general lemma). The
collision scan is L32 and is clean.

**Remit 5, one word per concept.** Drift found: L12 ("view" as a prose noun,
twice, where the file otherwise says "reading" and reserves "view" for
identifiers), L19 and L20 ("coordinate" in three senses across the landing's
text, one of them clashing with the fixed framework sense in the file it lands
in), L27 ("concludes at" against "published at" for one number), L28 ("prior"
in two senses inside the manifest). Checked and clean: "the sum of absolute
differences, twice the total variation distance" appears once in the new
file's header as the gloss of `var_dist` and matches the settled formula in
`lib/var_dist_supp.v`, `security/var_dist_joint_law.v` and production
`five_card_proximity.v`; "variation distance" appears twice, both times inside
the phrase "the bound var_dist_le2 gives for a variation distance", which is
the sibling's own wording and not a second name for the quantity the bound is
on; "proximity arm" and "input-indistinguishability arm" are used throughout
with no synonym, and "ideal-proximity arm" appears nowhere; "ideal" is used
for the model a certificate names and "the prior-indexed exact shuffle" for
the model itself, with `pgl27_word_proximity_cert_idealE` the equation between
them, so the two words are not two names for one thing; "secretP" appears only
as an identifier and the prose says "prior" or "the law of the dealt secret",
which stage C found to be the tree's settled word.

**Remit 6, mechanical.** L35, clean on every count.

**Not in remit, not audited.** The thirteen unchanged chain copies under
`staged/`; `landing_fidelity.v` except where L3 and L16 name lines of it;
`verify.py`, `compile.py`, `restage.py`, `_CoqProject`; the probe's own naming
audit `notes/probes/2026-09-19-tableau-extensions/naming-audit-stageC.md`,
which was read for what it settled and not redone; and everything in the five
edited files other than the added text, which was obtained by diff.
