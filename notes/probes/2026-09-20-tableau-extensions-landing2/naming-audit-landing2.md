# Naming and style audit of landing 2

Adversarial audit of the permanent text of landing 2, read from the frozen
export
`/private/tmp/claude-501/.../scratchpad/land2_frozen/notes/probes/2026-09-20-tableau-extensions-landing2/staged/`
(same text as the repository at `b5c4094`). Read-only on the repository except
this file. Nothing was compiled: another session holds the Rocq lock. Where a
finding needs a compile to settle, the row says so.

Files audited as permanent text, comments included:

- `staged/lib/var_dist_supp.v` (production minus `card_tnth_count`)
- `staged/instances/kim2025/five_card_mixing.v` (production plus
  `card_tnth_count`, minus the two withdrawn declarations)
- NEW `staged/security/var_dist_joint_law.v`
- NEW `staged/manifest/pgg_tableau_arm_relations.v`
- NEW `staged/instances/kim2025/five_card_proximity.v`

---

## VERDICT: NO-GO

Three MUST, sixteen SHOULD, twelve NOTE.

Every MUST and every SHOULD is a comment or a header edit. Not one of them
touches a statement, a proof, an identifier that another file cites, or a
`Require`, with the single exception of the one identifier rename proposed in
N12, which is a new name no file outside `pgg_tableau_arm_relations.v` uses.
Soundness is therefore untouched by the whole punch list. A recompile of the
three edited files is still owed after the edits, because a comment edit can
break a delimiter; nothing else needs rebuilding.

The mechanical checks are clean: no line over 80 bytes in any of the five
files, no box-comment line whose closing `*)` is off column 80, no word of the
project's banned vocabulary list, and no abbreviation of "indistinguishability"
anywhere. The collision scan over the whole tree outside `notes/`, `docs/` and
`.claude/` returns nothing beyond the two known `Local` copies of
`var_dist_prodR`.

The three MUST are: a header that indexes 12 of its 26 declarations where the
tree's own rows files index 98 of 98 (N1); one sentence that narrates history
with the word the remit names (N2); and a file header that restates the proof
of one of its own recorded failures near-verbatim (N3).

---

## Findings

| id | class | file:line | quoted text | problem, with evidence | replacement |
|---|---|---|---|---|---|
| N1 | MUST | `five_card_proximity.v:51-80` | the `Definitions:` and `Key results:` blocks | The header indexes 12 of the file's 26 non-`Fail` declarations. The tree's convention is total coverage: `instances/pgl27/pgl27_rows.v` indexes 40 of its 40 non-`Fail` declarations, `instances/kim2025/five_card_rows.v` 58 of its 58. The 14 with no entry are `five_card_uniform_pairE` (:122), `five_card_reading_secretE` (:131), `five_card_arg_cut_prodE` (:152), `kim_biased_proximity_cert_epsE` (:243), `kim_biased_proximity_cert_eps_lt2` (:266), `five_card_row_biased_branch_indistinguishability_atE` (:291), `..._rowE` (:297), `five_card_row_biased_proximity_rowE` (:321), `..._publishedE` (:326), `five_card_row_biased_branch_indistinguishability_armE` (:336), `five_card_row_biased_proximity_armE` (:349), `five_card_singleton_below_threshold` (:444), `five_card_biased_proximity_prop_holds` (:529), `five_card_biased_indistinguishability_implies_proximity` (:540). The two new sibling files are already total: `var_dist_joint_law.v` indexes 5 of 5 and `pgg_tableau_arm_relations.v` 6 of 6. | Add the 14 entries. Proposed wording, each checked against the declaration it names, is in the block below this table. |
| N2 | MUST | `var_dist_joint_law.v:85-88` | "Two section-local proofs of this statement **predate** the one here, at instances/pgl27/pgl27_mixing.v and instances/psl211/psl211_mixing.v; each is used once, inside its own file's joint mixing lemma, and neither is visible outside it." | "predate" narrates the order in which the three proofs were written, which is history and not mathematics. The rest of the sentence is a checked fact: `instances/pgl27/pgl27_mixing.v:1077` and `instances/psl211/psl211_mixing.v:577` each declare `Local Lemma var_dist_prodR (A B : finType) (P : R.-fdist A) (Q1 Q2 : R.-fdist B) : var_dist (P `x Q1) (P `x Q2) = var_dist Q1 Q2`, the same statement; each has exactly one use, at `:1100` inside `pgl27_joint_mixing` and at `:601` inside `psl211_joint_mixing`; both are `Local`. | "Two files carry a section-local proof of the same statement, instances/pgl27/pgl27_mixing.v and instances/psl211/psl211_mixing.v. Each is used once, inside that file's joint mixing lemma, and neither is visible outside it." |
| N3 | MUST | `pgg_tableau_arm_relations.v:40-46` | "The recorded failure of the composition law says where the arm's mathematics is spent. With the ideal witness's independence deleted from the proof, what remains is the certificate's distance between two joint laws and the two link lemmas; the arm's proposition compares the actual joint law with a product, so the step that turns the ideal joint law into the product of its marginals is where the witness is spent, and without it the final application does not typecheck." | The header restates, near-verbatim, the declaration comment of `idealproximity_tail_without_independence` at `:211-216`: "What remains is the certificate's distance between two joint laws and the two link lemmas, and the arm's proposition compares the actual joint law with a product, so the step that turns the ideal joint law into the product of its marginals is where the witness is spent. Without it the final application does not typecheck." A header is long exposition anchored to nothing, not a copy of a proof explanation that sits 170 lines below it and will drift against it. | Cut the paragraph to the one sentence that is exposition and is not in the body: "One recorded failure below says where the arm's mathematics is spent: the ideal witness's independence is what turns the ideal joint law into the product of its marginals, and the arm's proposition compares the actual joint law with exactly that product." |
| N4 | SHOULD | `pgg_tableau_arm_relations.v:13-38` | three further header paragraphs | Same duplication, three more times. Header `:17-19` "An ideal that a proximity certificate names can therefore not be recovered from an input-indistinguishability premise, and a bound on the distance to that ideal has to be proved from something else" is the declaration comment at `:136-138` with one word changed. Header `:29-31` "The secret leaves the proximity statement by data processing along the first projection, and the ideal's joint law is a product, so its first marginal is the ideal reading outright" is the declaration comment at `:167-169` verbatim. Header `:34-36` "so a row publishing two rules nothing out, and a published number says something about a coalition exactly in so far as it is below two" is the declaration comment at `:113-114` verbatim. Four of the header's five prose paragraphs are copies. | Keep the header's own frame, which no declaration states: what the three arms are, that two of them carry a number, that both numbers can be read off one variation distance on the cut group, that all statements here are at an arbitrary algebra, and the `Not claimed.` paragraph. Delete the three duplicated explanations, which the declarations already carry at the point where they are checkable. |
| N5 | SHOULD | `var_dist_joint_law.v:8-11` | "the lemmas here are the steps between them, **each** stated on the sum of the absolute differences of two laws, which is twice the total variation distance of the literature and bounds twice a distinguisher's advantage" | False for one of the five. `fdist_prod_snd` (`:120`) states `fdistmap snd (P `x Q) = Q`, an equality of laws, and no sum of absolute differences occurs in it. The other four are stated on `var_dist`. | "the lemmas here are the steps between them. Each distance step is stated on the sum of the absolute differences of two laws, which is twice the total variation distance of the literature and bounds twice a distinguisher's advantage. fdist_prod_snd is the marginal identity those steps consume." |
| N6 | SHOULD | `var_dist_joint_law.v:82-85` | "Tensoring a shuffle law with a run argument drawn independently of it therefore neither creates nor destroys **variation distance**" | The same file's header, 75 lines above, has just told the reader that the quantity here is "the sum of the absolute differences of two laws, which is twice the **total variation distance** of the literature", and states this very lemma as "tensoring with a common factor neither creates nor destroys **the sum**" (`:18-19`). Two words for one quantity inside one file, where the reader has just been given a second quantity a factor of two away. | "Tensoring a shuffle law with a run argument drawn independently of it therefore neither creates nor destroys the sum, which is what lets a bound proved on the cut group be read as a bound on the joint law of argument and cut." |
| N7 | SHOULD | `var_dist_supp.v:16-17` | "The distance between two joint laws of a reading and a secret **is** security/var_dist_joint_law.v." | A distance is not a file. The sentence as written equates a real number with a path. | "security/var_dist_joint_law.v carries the distance between two joint laws of a reading and a secret." |
| N8 | SHOULD | `five_card_proximity.v:209-211` | "**Every field** is a term the uniform row already publishes **except the number**, which is the bound kim_biased_cut_mixing_exact proves on the cut group's own distance, and the distance between the two joint laws is at most it." | False. The definition at `:212-220` gives five fields: the ideal `amf_sample five_card_uniform_family R idx`, the witness `five_card_exact_witness R idx`, the secret `five_card_leakage.Secret R`, the number `1 / 50`, and the distance `fun C _ => @kim_biased_proximity_close R C`. The fifth is `kim_biased_proximity_close`, declared in this file at `:172`, so at least two fields are not terms the uniform row publishes. Only the first two are, and `kim_biased_proximity_cert_idealE` (`:226`) is exactly the statement that those two are. | "The ideal and the witness are the terms the published uniform row already carries, which kim_biased_proximity_cert_idealE states. The secret is the conjunction of the committed bits. The number is the bound kim_biased_cut_mixing_exact proves on the cut group's own distance, and the distance field is the statement that the two joint laws are within it." |
| N9 | SHOULD | `five_card_proximity.v:387` | "**The same statement** with the den Boer uniform model removed: at fewer than two colluding seats, …" | It is not the same statement. `five_card_biased_view_proximity` (`:373`) bounds the distance to the den Boer product at `1 / 50`; `five_card_biased_view_own_marginals` (`:394`) bounds the distance to the executed law's own two marginals at `3%:R * (1 / 50)`. Different comparand and a different constant. | "The one-cut row's bound restated against the executed law's own two marginals: at fewer than two colluding seats, the joint law of the coalition's reading with the conjunction of the committed bits is within three fiftieths of the product of that same law's two marginals. The den Boer uniform model has left the statement. What remains is a bound on how far the one-cut run is from making a coalition's reading and the secret independent, and the advantage a distinguisher gets from it is at most three hundredths." |
| N10 | SHOULD | `five_card_proximity.v:387-393`, also `:367-369` | "the joint law of the coalition's executed **view** with the conjunction of the committed bits … a bound on how far the one-cut run is from making a coalition's **reading** and the secret independent" | One object, `sa_coalition_view`, named twice in one comment by two words. The file's prose elsewhere says "reading" (13 occurrences) and reserves "view" for identifiers, and `security/var_dist_joint_law.v` says "reading" 8 times and "view" never. The sibling theorem at `:368` also says "the executed coalition view". | Use "reading" in prose throughout, and leave "view" only where it spells an identifier (`sa_coalition_view`, `five_card_biased_view_proximity`, `view_proximity_of`). At `:368` write "the joint law of the coalition's executed reading and the conjunction of the committed bits"; the replacement in N9 already does this at `:387`. |
| N11 | SHOULD | `five_card_proximity.v:514` | "The proximity arm and the input-indistinguishability arm are rejected by the same **coordinate**" | The file uses "coordinate" for a slot of a published row at `:20` ("hold one coordinate"), `:286` ("one AnalysisBridged coordinate"), `:289` ("an equation between two rows' coordinates") and `:325` ("The three coordinates the proximity row publishes"). Here it means something else: the sample-adapter argument the certificate type is indexed by. The two recorded failures at `:501` and `:517` are rejected because `amf_sample kim_biased_family R idx` and `amf_sample kim_centi_family R idx` are different adapters, which is a type index and not a row slot. | "The proximity arm and the input-indistinguishability arm are rejected at the same argument, the sample adapter each certificate type is indexed by, so the proximity arm adds no new way for two models of one instance to be confused." |
| N12 | SHOULD | `pgg_tableau_arm_relations.v:115` | `Lemma idealproximity_ceiling` | "Ceiling" is a metaphor noun for a bound in an identifier. A scan of every `.v` file outside `notes/` and `docs/` finds the word in 20 places and every one of them is prose; no identifier in the tree carries it. The tree's identifiers for exactly this shape state the relation: `var_dist_le2`, `kim_biased_cert_eps_lt2`, `five_card_reprice_inv25_lt2`, `kim_centi_cert_eps_lt`. The statement is `IdealProximityPropAt cert 2%:R`, so the claim is that the proposition holds at two. The name is new in this landing and is cited by no other file, so the rename is free. Remit 4(d) exempts the `idealproximity_` prefix, not the suffix. | `idealproximity_prop_at2`, which matches the `_prop_` segment the sibling `indistinguishability_prop_cert_free` already uses in this file. Update the header entry and the two prose mentions at `:33` and `:139`. |
| N13 | SHOULD | `five_card_proximity.v:263-265` | "At one percent of the ceiling it is a weak separation and not a cryptographic one, **as the input-indistinguishability certificate of the same model is**." | The trailing clause can attach to either predicate, so the sentence reads either as "the input-indistinguishability certificate is also a weak separation" or as "the input-indistinguishability certificate is a cryptographic one". The first is what the tree holds: `five_card_rows.v:758` proves `kim_biased_cert_eps_lt2` at one twenty-fifth, and `five_card_mixing.v:478-480` already says of the same arm "Its number is about three percent of the ceiling var_dist_le2 gives, so it is a weak separation bound and not a cryptographic one." | "At one percent of the ceiling it is a weak separation and not a cryptographic one, as is the input-indistinguishability certificate of the same model at one twenty-fifth." |
| N14 | SHOULD | `pgg_tableau_arm_relations.v:170-173` | "it is **the sharpest** comparison of the input-indistinguishability arm with the proximity arm that does not need a model of one to be a model of the other" | A superlative over the space of possible comparisons, which nothing in the file establishes and no proof could. It is the same class as "key" or "headline": a reader cannot check it. The sentence before it already carries the content. | "This is the arm's number read on the carrier the input-indistinguishability arm states its own bound on, and it needs no model of one arm to be a model of the other." |
| N15 | SHOULD | `pgg_tableau_arm_relations.v:138-140` | "**The implication** is not empty for all that: idealproximity_ceiling holds it at two whatever the premise." | "The implication" has no antecedent in this comment. The statement it belongs to, `indistinguishability_prop_cert_free`, is an equality between two propositions and contains no implication; the implication meant is the one from the input-indistinguishability proposition to the proximity proposition, which only the file header names. | "An implication from this proposition to the proximity proposition is not empty for all that: idealproximity_prop_at2 gives the proximity proposition at two whatever the premise." (uses the N12 name; keep `idealproximity_ceiling` here if N12 is declined) |
| N16 | SHOULD | `five_card_proximity.v:347-348` | "This is the value a paper's table prints in the arm column for this row." | A claim about a document outside the development, unverifiable from the artifact, and a usage pointer of the kind the statement-comment rule excludes. The sentence before it already gives the position, and it gives it in mathematical terms. | Delete the sentence. What remains, "The arm the proximity row carries, at every real field and index: the distance to a private ideal model, and not the distance between two readings of one model", is the fact and the position. |
| N17 | SHOULD | `var_dist_joint_law.v:57-59` | "It is the **data processing inequality var_dist_fdistmap** at the map pairing the two readers, and it is the step by which …" | The clause names the lemma the proof applies. The proof is `exact: (le_trans (var_dist_fdistmap _ _ _) H)`, so the clause is the proof written in the docstring. The kind of fact is worth keeping; the dependency name belongs in the proof. | Docstring: "It is data processing along the map pairing the two readers, and it is the step by which the proximity arm's certificate is discharged: …". In the proof body, above the `exact:`, add `(* var_dist_fdistmap at (reading, secret), then transitivity. *)`. |
| N18 | SHOULD | `var_dist_joint_law.v:116-119` | "The second marginal of a product law is its second factor. infotheo's fdist_prod1 states this for the first marginal of a product with a channel, and the second marginal of such a product is a mixture, so the statement for a constant channel has no counterpart there." | The fact is right and the library claim is right: infotheo `probability/fdist.v:1071` defines ``P1 `x P2`` as ``P1 `X (fun _ => P2)``, `:1040` proves `fdist_prod1 : fdist_prod`1 = P` for the channel form, and the second marginal of ``P `X W`` is a mixture, with no counterpart lemma in the file. What the comment lacks is the position: the declaration is the only one of the five whose comment says nothing about the argument this file makes. It is the step at which `var_dist_own_marginals` (`:143`) identifies the ideal product's second marginal with the secret's own law, the mirror of the `fdist_prod1` step at `:142`. | "The second marginal of a product law is its second factor. It is the second half of the identification a comparison with an ideal makes: the ideal's joint law is a product, so each of its marginals is one of the two laws the ideal was built from, and var_dist_own_marginals needs both halves. infotheo's fdist_prod1 gives the first half for a product with a channel, where the second marginal is a mixture and has no counterpart." |
| N19 | SHOULD | `security/var_dist_joint_law.v` (the file name and header) | the module name against its directory | `security/` holds 14 `.v` files and every one is `pgg_`-prefixed; `manifest/` holds 5 and every one is `pgg_`-prefixed; `lib/` holds 6 and none is. The new file is the first unprefixed file in `security/`, and its five lemmas are stated at an arbitrary `realType` and arbitrary `finType`s with no PGG object in any of them, which is a `lib/` shape. It sits in `security/` for a dependency reason only: it consumes `var_dist_fdistmap` (`security/pgg_collusion_bound.v:126`) and `var_dist_triangle` (`:43`), and `lib/` carries no dependency on `security/`. Nothing in the file says so, so a reader meets an unexplained anomaly. | Keep the name, which states what the file holds and pairs it with `lib/var_dist_supp.v`, and add one sentence to the header, in the shape `five_card_mixing.v:29-31` already uses for a layering fact: "The file sits under security/ and not under lib/ because the two data-processing steps it uses, var_dist_fdistmap and var_dist_triangle, are stated in security/pgg_collusion_bound.v, and lib/ carries no dependency on security/." A rename to `pgg_var_dist_joint_law.v` would restore the directory convention but would claim a framework object the file does not have. |
| N20 | NOTE | `pgg_tableau_arm_relations.v`, `five_card_proximity.v`, passim | `idealproximity_*`, `IdealProximity*`, `ipc_*` | The owner's kept long form. Recorded, no action, per remit 4(d). | — |
| N21 | NOTE | `five_card_proximity.v:33` and `:265` | "one **per cent** of what a pair of laws … can reach" / "At one **percent** of the ceiling" | Two spellings of one word inside one file. Production spells it "percent": `five_card_mixing.v:479`, `five_card_rows.v:711`. | "percent" in both places. |
| N22 | NOTE | `pgg_tableau_arm_relations.v:70-81` against `five_card_proximity.v:51-80` | the `Recorded failures:` block | `pgg_tableau_arm_relations.v` indexes its three recorded `Fail`s; `five_card_proximity.v` indexes none of its six. Neither precedent file indexes any: `pgl27_rows.v` has 10 recorded `Fail`s and no entry for one of them, `five_card_rows.v` has 4 and likewise. So the batch is internally split and the tree's precedent is "do not index". Either rule is defensible; the two new files should not differ. | Either drop the `Recorded failures:` block from `pgg_tableau_arm_relations.v`, following the precedent, or add one to `five_card_proximity.v` for its six. The second is the better reading of a `Fail` as permanent text, but it is the owner's call. |
| N23 | NOTE | `var_dist_joint_law.v:89` and `:105` | `var_dist_prodR`, `var_dist_prodL` | Checked against the statements. `var_dist_prodR (P) (Q1 Q2) : var_dist (P `x Q1) (P `x Q2) = var_dist Q1 Q2` holds the LEFT factor fixed and varies the RIGHT, so `R` names the varying side; `var_dist_prodL (P1 P2) (Q) : var_dist (P1 `x Q) (P2 `x Q) = var_dist P1 P2` varies the LEFT, so `L` names the varying side. That is MathComp's own convention, where `mulrDl : (x + y) * z = …` puts the acted-on argument on the side the suffix names. Both comments agree with their statements: `:81` says "the same left factor … as far apart as their right factors", `:101` says "the same right factor … as far apart as their left factors". MathComp spells the side suffix lowercase (`mulrDl`, `big_distrr`); this tree's two existing `Local` copies already spell it `var_dist_prodR` with a capital. | Keep both names. |
| N24 | NOTE | `pgg_tableau_arm_relations.v:6` | "A Tableau row certifies one of **three** arms, and two of the three carry a number." | True, and the file's name promises "arm relations" while every statement in it relates the two numbered arms only. Nothing here relates the exact arm to either. | Optional: "…the statements here separate the two that carry a number", so the file name and the header agree on the scope. |
| N25 | NOTE | `five_card_proximity.v:67-68` and `:256` | header entry "kim_biased_proximity_eps_halfE == kim_biased_cert_exact's number is twice **it**" | Two small things. The header entry's "it" has no antecedent inside the entry. And the name says "half" while the statement is written as a doubling, `cert_eps (kim_biased_cert_exact R idx) = ipc_eps (…) + ipc_eps (…)`. The doubling form is the right one, since it is what the two-committed-pairs reading prices, and the rest of the tree writes the same shape (`five_card_rows.v:750`). | Header entry: "kim_biased_proximity_eps_halfE == the exact input-indistinguishability certificate's number is twice the proximity certificate's". Keep the lemma name. |
| N26 | NOTE | `five_card_proximity.v:224-225` | "the ideal a biased row is measured against is **the row** the manifest already carries and not a second description of it" | A model is not a row. The lemma at `:226` equates `ipc_ideal …` with `amf_sample (ab_f (published_at five_card_row_uniform_tableau)) R idx`, which is the model the uniform row publishes. | "…is the model the manifest's uniform row publishes and not a second description of it." |
| N27 | NOTE | `five_card_proximity.v:308-310` | "the transfer status is the one the input-indistinguishability row **earns**, since the same ideal cut is what both certificates compare against" | `IdealFinite` is written into the `publish` clause at `:314`; it is chosen, not derived. The sentence gives the reason for a choice, which is design rationale rather than a statement of what the object is. Harmless, and the reason is sound. | Optional: move it to a plain `(* … *)` comment above the `Definition`, or rewrite as a fact: "Its transfer status is IdealFinite, the same the input-indistinguishability row carries, and the two certificates compare against the same ideal cut." |
| N28 | NOTE | `five_card_proximity.v:65-66` | header entry "kim_biased_proximity_cert_idealE == the certificate's ideal is the uniform row" | The lemma is a conjunction. Its second half states that `ExactIndependence (ipc_witness …)` is `ab_port (published_at five_card_row_uniform_tableau)`, which the entry does not mention, and which the declaration comment does. | "kim_biased_proximity_cert_idealE == the certificate's ideal and witness are the uniform row's model and port". |
| N29 | NOTE | whole tree | collisions | A walk over every `.v` file outside `notes/`, `docs/`, `.claude/`, `_build` and the paper directories, matching every `Definition`, `Lemma`, `Theorem`, `Fact`, `Corollary`, `Notation`, `Record`, `Inductive`, `Axiom`, `Variable`, `Let`, `Example`, `Instance` and `Fixpoint` head against the 44 landed names, returns exactly two hits besides the moved lemma's own production home: `instances/pgl27/pgl27_mixing.v:1077` and `instances/psl211/psl211_mixing.v:577`, both `Local Lemma var_dist_prodR`, both invisible outside their file. `card_tnth_count` matches `lib/var_dist_supp.v:166`, which landing 2 removes. | Clean. No action. |
| N30 | NOTE | the five files | mechanical | No line over 80 bytes. No box-comment line whose closing `*)` is off column 80. No hit for the project's banned vocabulary list. No abbreviation of "indistinguishability", and no `_indist` segment. The first two lines of each of the three new files are the project's standard licence lines, as `security/`, `lib/` and `manifest/` all carry them. | Clean. No action. |
| N31 | NOTE | `five_card_proximity.v:289-290` | `(* exact: erefl and not by [], because done does not return on an equation between two rows' coordinates. *)` | Correctly a plain `(* *)` comment and not part of the docstring, which is what the rule asks. It sits between the docstring and the `Lemma` rather than inside the proof. The proof is one line, so the placement reads fine; recorded only so the convention is deliberate. | Optional: move it inside `Proof. … Qed.`. |

---

### N1, the 14 header entries, each checked against its declaration

For the `Key results:` block of `five_card_proximity.v`:

```
(*   five_card_uniform_pairE   == the uniform law on the committed pair is   *)
(*                                one law under either cardinality proof     *)
(*   five_card_reading_secretE == a coalition's reading and the secret       *)
(*                                factor through the pair of the committed   *)
(*                                bits and the cut                           *)
(*   five_card_arg_cut_prodE   == that pair's joint law is the uniform pair  *)
(*                                tensored with the model's cut law          *)
(*   kim_biased_proximity_cert_epsE                                          *)
(*                             == the certificate's number is one fiftieth   *)
(*   kim_biased_proximity_cert_eps_lt2                                       *)
(*                             == that number is under the ceiling a         *)
(*                                variation distance has                     *)
(*   five_card_row_biased_branch_indistinguishability_atE                    *)
(*                             == the branch and the program written out     *)
(*                                from the prefix hold one coordinate        *)
(*   five_card_row_biased_branch_indistinguishability_rowE                   *)
(*   five_card_row_biased_proximity_rowE                                     *)
(*                             == each of the two rows publishes the         *)
(*                                manifest's row for the biased path         *)
(*   five_card_row_biased_proximity_publishedE                               *)
(*                             == the three coordinates the proximity row    *)
(*                                publishes                                  *)
(*   five_card_row_biased_branch_indistinguishability_armE                   *)
(*                             == the branch carries the                     *)
(*                                input-indistinguishability arm             *)
(*   five_card_row_biased_proximity_armE                                     *)
(*                             == the proximity row carries the proximity    *)
(*                                arm                                        *)
(*   five_card_singleton_below_threshold                                     *)
(*                             == one seat is below the five-card privacy    *)
(*                                threshold                                  *)
(*   five_card_biased_proximity_prop_holds                                   *)
(*                             == the arm's proposition at the number the    *)
(*                                row publishes                              *)
(*   five_card_biased_indistinguishability_implies_proximity                 *)
(*                             == the input-indistinguishability proposition *)
(*                                implies it, its premise discarded          *)
```

Checks made before writing each line, all by reading the declaration:

- `five_card_uniform_pairE` (`:122`) is `fdist_uniform card_bool2 = fdist_uniform five_card_card_bool2 :> R.-fdist (bool * bool)`, two cardinality proofs of one pair.
- `five_card_reading_secretE` (`:131`) rewrites the pushforward of `(static_coalition_obs …, Secret)` as a pushforward through `(u.1, five_card_sample_cut u)`.
- `five_card_arg_cut_prodE` (`:152`) sends that pushforward of ``fdist_uniform five_card_card_bool2 `x W`` to ``fdist_uniform five_card_card_bool2 `x fdistmap (fun k => fc_sigma ^+ k) W``.
- `kim_biased_proximity_cert_epsE` (`:243`) is `ipc_eps … = 1 / 50`.
- `kim_biased_proximity_cert_eps_lt2` (`:266`) is `ipc_eps … < 2%:R`; the word "ceiling" here is the tree's settled prose, cf. the `kim_biased_cert_eps_lt2` entry in `five_card_rows.v`'s header, "the one-cut row's number is under the ceiling a variation distance has". N12 concerns the identifier only.
- `..._branch_indistinguishability_atE` (`:291`) equates the two `published_at` values.
- the two `_rowE` (`:297`, `:321`) both give `five_card_row_biased`, which is why one entry covers both.
- `..._publishedE` (`:326`) is the three-way conjunction on `apr_completion`, `apr_transfer`, `apr_assumptions`.
- the two `_armE` (`:336`, `:349`) give `InputIndistinguishabilityArm` and `IdealProximityArm`.
- `five_card_singleton_below_threshold` (`:444`) is `(#|[set i]| < profile_k (instance_profile five_card_algebra))%N`.
- `five_card_biased_proximity_prop_holds` (`:529`) is `IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 50)`, and `1 / 50` is the number `five_card_row_biased_proximity` publishes, per `kim_biased_proximity_cert_epsE`.
- `five_card_biased_indistinguishability_implies_proximity` (`:540`) takes `IndistinguishabilityPropAt (kim_biased_cert R tt) c` for any `c` and returns that same proposition; its proof discards the premise.

Whether the six recorded `Fail`s also get entries is N22, and is the owner's call.

---

## Coverage

**Remit 1, permanent-text read of the five files, comments included.** Every
comment of the three new files and of the two moved or edited declarations was
read in full. One sentence narrates history: N2, the word the remit names. No
comment in any of the five files speaks of a probe, a stage, a ledger row (P1,
P4, P7, P8, P9, T0, G2), an audit, a fix pass, "the spec", "this batch", "the
landing", or a date. The four narration removals and the two comment rewrites
STATUS records at E2 and E4 all landed: `five_card_biased_view_own_marginals`
no longer opens on a ledger row (its remaining defect is N9, which the rewrite
introduced), `kim_biased_conclude_below_false` no longer says "the probe",
`five_card_biased_proximity_prop_holds` no longer says "the spec's P8 row
wants", `five_card_biased_indistinguishability_implies_proximity` no longer
says "what the spec asks for", and the `_atE` source comment no longer cites
STATUS.md. `var_dist_prodR`'s R5 sentence is judged at N2, with a replacement
that keeps the three facts it carries and drops the order of writing.

**Remit 2, statement-comment discipline, every declaration.** Walked, one at a
time, against the declaration text: 5 in `var_dist_joint_law.v`, 6 in
`pgg_tableau_arm_relations.v`, 32 in `five_card_proximity.v`, and the moved
`card_tnth_count` at `five_card_mixing.v:248`. Defects: N2, N8, N9, N13, N14,
N15, N16, N17, N18, N26, N27. The rest state the fact and the position. Four
are worth naming as the standard the batch should be held to:
`kim_biased_proximity_close` (`:163-171`), which states the bound and then says
what it does not need, "The bound holds at every coalition and not only below
the threshold; the threshold enters the arm's proposition and not this
distance"; `five_card_biased_proximity_at_singleton` (`:448-452`), which says
why the coalition is not empty; `idealproximity_prop_cert_free` (`:146-151`),
which says what its own recorded failure does not show, "two logically
equivalent propositions would still be equal under propositional
extensionality"; and `five_card_row_biased_proximity_rowE` (`:316-320`), which
says why one manifest row carrying two claims says nothing about either.
`card_tnth_count`'s comment carries the file's leading-name convention and
gives the position ("the bridge from a law on card positions to the deck's
colour census"), and its header entry is present at `five_card_mixing.v:40-41`.
I could not compile, so every claim above rests on reading the declaration;
where a comment asserts a numeric fact I checked the arithmetic by hand
(`1 / 50` against the ceiling `2` is one percent; `3%:R * (1 / 50)` halves to
three hundredths; `kim_biased_epsE` at `five_card_rows.v:556` is
`Num.sqrt 5%:R * (1 / 80)`, so the "sqrt 5 over eighty" and "sqrt 5 over forty"
of `kim_biased_proximity_eps_halfE`'s comment are right). The one place I am
unsure is whether `ipc_secret`, `five_card_leakage.Secret R`, is literally the
`ew_secret` field of `five_card_exact_witness`: N8's replacement avoids the
question by not claiming it, but confirming it needs a compile.

**Remit 3, file headers of the three new files.** Every `Lemmas:`,
`Definitions:`, `Key results:` and `Recorded failures:` entry names an
identifier declared in that same file with that exact spelling: checked
mechanically, zero bad entries in all three. Coverage the other way is N1:
`var_dist_joint_law.v` 5 of 5, `pgg_tableau_arm_relations.v` 6 of 6 including
its `Fail`s, `five_card_proximity.v` 12 of 26. The precedent the remit asks
about: `instances/pgl27/pgl27_rows.v` indexes all 40 of its non-`Fail`
declarations and none of its 10 `Fail`s;
`instances/kim2025/five_card_rows.v` indexes all 58 of its non-`Fail`
declarations and none of its 4 `Fail`s. So the tree's rule is total coverage
of what is declared and silence on what is recorded as failing, which makes N1
a MUST and N22 a NOTE. Header prose anchored to nothing: true of
`five_card_proximity.v` and of `var_dist_joint_law.v`; false of
`pgg_tableau_arm_relations.v`, which is N3 and N4. The first two lines of all
three new files are the project's standard licence lines, confirmed and not
flagged.

**Remit 4, names and homes.** (a) `security/var_dist_joint_law.v`: N19.
(b) `manifest/pgg_tableau_arm_relations.v`: the name is `pgg_`-prefixed like
all five files of `manifest/`, sits in the `pgg_tableau*` family with the two
files it depends on, and states the content at the right grain. N24 is the only
qualification. (c) Each landed name against the conventions: the `E` suffix is
used for an equation in all twelve places it appears and nowhere else, two of
them a conjunction of equations, which is the `..._publishedE` shape
`five_card_rows.v` already uses; `_le`
and `_lt2` are used for an inequality; `_armE`, `_atE`, `_rowE`, `_publishedE`
follow `five_card_rows.v` and `pgl27_rows.v` exactly; the `var_dist_` and
`fdist_` prefixes match the carrier each lemma is stated on;
`five_card_reprice_inv100` follows `five_card_reprice_inv25` of
`five_card_rows.v:850`. `var_dist_prodR` and `var_dist_prodL` are N23, and the
answer to the remit's question is that each letter names the varying side, that
this is MathComp's convention, and that both comments agree with their
statements. The one name I would change is N12. (d) `idealproximity_*`,
`IdealProximity*` and `ipc_*` are recorded at N20 and nothing more.
(e) Collisions: N29, clean.

**Remit 5, one word per concept.** Drift that could make a reader suspect two
things: N10 ("reading" against "view", inside one comment, for
`sa_coalition_view`), N11 ("coordinate" in two senses inside one file) and N6
("variation distance" against "the sum", for one quantity, inside one file,
where the reader has just been handed a second quantity a factor of two away).
Checked and clean: "proximity arm" is used 8 times in `five_card_proximity.v`,
2 in `pgg_tableau_arm_relations.v`, 1 in `var_dist_joint_law.v` and 10 in
landing 1's staged `manifest/pgg_tableau.v`, and "ideal-proximity arm" appears
nowhere, so the prose word is settled and agrees with the `IdealProximityArm`
constructor. "Marginal bound" is used in the same sense in `five_card_mixing.v`
(5), `var_dist_supp.v` (1) and `kim_biased_proximity_eps_halfE`'s comment, and
agrees with `five_card_rows.v:153`. "The sum of absolute differences, twice the
total variation distance" appears once per file as the gloss of `var_dist`,
which is the project's own settled formula and matches `var_dist_supp.v`'s
existing header. "Observation" appears nowhere in the five files.

**Remit 6, mechanical.** N30, clean on all four counts. N21 is the only
spelling drift found.

**Not in remit, not audited.** The ten unchanged chain-consistency copies under
`staged/`; `landing_fidelity.v`; `verify.py`, `compile.py`, `restage.py`,
`_CoqProject`; the probe's own naming audit
`notes/probes/2026-09-19-tableau-extensions/naming-audit-stageB.md`, which was
not redone; everything in `five_card_mixing.v` and `var_dist_supp.v` other than
the moved `card_tnth_count`, the header edits and the rewritten section banner
at `five_card_mixing.v:505-507`, which carries no narration and is accurate to
what sits under it.
