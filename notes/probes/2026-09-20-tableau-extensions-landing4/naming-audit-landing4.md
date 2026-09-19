# Naming and style audit of landing 4 (PSL(2,11))

Frozen export
`/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc/493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad/land4_frozen/notes/probes/2026-09-20-tableau-extensions-landing4/`,
repository commit `833acaf`. Read-only on the repository except this file. No
compile was run; every finding that would need one says so.

Line numbers for the two new files are the staged files' own. Line numbers for
the four edited files are the staged files' own; the base each was diffed
against is `notes/probes/2026-09-20-tableau-extensions-landing3/staged/` for
the two manifest files and production for the two `psl211_` files.

## VERDICT: NO-GO

Twelve MUST, fourteen SHOULD, eleven NOTE (N1 to N37).

Six of the twelve MUSTs are exact recurrences of defects landing 2 or
landing 3 already found and whose fixed wording is sitting in the sibling file
this landing was asked to read alike: the false "read off the program" sentence
(landing-3 N2), the "a paper's table" sentence (landing-2 N16, landing-3 N4),
the `_idealE` witness-for-port slip (landing-2 N28, landing-3 N10), the
contentless `_view_proximity` header entry (landing-3 N13), the "in closed
form" header entry (landing-3 N14), and "the two rows differ in … alone"
(landing-3 N17, N18). Two more are mechanical: one box-comment line is 79 bytes
and one facade table column is off by two.

## Findings

| id | class | file:line | quoted text | problem with evidence | replacement |
|---|---|---|---|---|---|
| N1 | MUST | `psl211_word_proximity.v:299-303` | "Its five coordinates are the observed execution the program runs on, the completion level the publish terminal reaches, the model family the sample step named, and the two statuses the terminal was given, **so the manifest's description of this path is read off the program and not written beside it**." | False. `psl211_row_word` is a hand-written `Definition` in the manifest (`staged/manifest/pgg_analysis_manifest.v:1091-1093`), written out coordinate by coordinate in facade vocabulary; the lemma is an equation between that hand-written value and the program's projection, not a reading-off. This is the sentence landing-3 N1/N2 flagged at `pgl27_row_prior_exact_rowE` and the fix pass replaced; the fixed text is at `notes/probes/2026-09-20-tableau-extensions-landing3/staged/instances/pgl27/pgl27_proximity.v:189-197`. | "… and the two statuses the terminal was given. The manifest writes those coordinates in the facade's vocabulary and the program in this file's, and conversion decides the equation, so the manifest's row for this path is a claim this equation discharges rather than a table maintained beside the program. It differs from psl211_row_alldecks in the model family and in the transfer status, the all-decks row comparing no idealized model where this one replaces an idealized shuffle by a finite word." |
| N2 | MUST | `psl211_word_proximity.v:291-292` | "**This is the value a paper's table prints in the arm column for this row.**" | A claim about a document outside the development, unverifiable from the artifact, and a usage pointer the statement-comment rule excludes. Landing-2 N16 raised it at `five_card_row_biased_proximity_armE` and landing-3 N4 at both `pgl27_row_prior_exact_armE` and `pgl27_row_word_proximity_armE`; the fixed sibling `pgl27_proximity.v:409-411` no longer carries it, and neither does production `five_card_proximity.v`. | Delete the sentence. What remains, "The arm the row carries, at every real field and index: the distance to a private ideal model, and not the distance between two readings of one model.", is exactly the fixed sibling's docstring. |
| N3 | MUST | `psl211_word_proximity.v:49-51` | header entry "psl211_word_proximity_cert_idealE == the certificate's ideal is the all-decks row's model **and witness**" | The lemma's second conjunct (`:175-176`) is `ExactIndependence (ipc_witness (psl211_word_proximity_cert R idx)) = ab_port (published_at psl211_row_alldecks_tableau) R idx`. It equates the PORT BUILT FROM the witness with the row's port; no witness is equated with a witness. Landing-2 N28 and landing-3 N10(b) both raised this, and the fixed sibling `pgl27_proximity.v:70-73` reads "the certificate's ideal is the ideal row's model, and the port built from its witness is that row's port". | `(*   psl211_word_proximity_cert_idealE                                         *)` / `(*                              == the certificate's ideal is the all-decks   *)` / `(*                                 row's model, and the port built from its   *)` / `(*                                 witness is that row's port                 *)` |
| N4 | MUST | `psl211_word_proximity.v:168-169` | "The model the certificate calls ideal, **and the witness it carries for it, are the model and the witness of** the published all-decks row." | Same defect in the declaration comment. The second conjunct is about `ExactIndependence (ipc_witness …)`, a port, not about a witness. (Production `five_card_proximity.v:271-272` carries the same loose sentence; landing 2 fixed only the header entry there, so the owner may want the production docstring corrected in the same pass.) | "The model the certificate calls ideal is the model the published all-decks row carries, and the port built from the witness the certificate carries is that row's port. Conversion decides both, so the ideal a word row is measured against is the model psl211_rows.v publishes and not a second description of it." |
| N5 | MUST | `psl211_word_proximity.v:71` | header entry "psl211_word_view_proximity == **what the row states at this instance**" | Says nothing a reader can check and names neither the bound nor the number, where every other entry of the block does. Landing-3 N13 raised the identical entry at PGL(2,7) and the fixed sibling `pgl27_proximity.v:98-99` reads "== the proximity row's security statement, at 2^-39". The theorem (`:322-334`) concludes `… <= 2%:R^-40`. | `(*   psl211_word_view_proximity == the proximity row's security statement,    *)` / `(*                                 at 2^-40                                   *)` |
| N6 | MUST | `psl211_word_proximity.v:57-58` and `:206` | header entry "psl211_word_proximity_cert_epsE == the certificate's number **in closed form**" and docstring "The certificate's number **in closed form**: the 584-letter walk's number, 2^-40, …" | "In closed form" describes the shape of the statement rather than saying what the number is. Landing-3 N14 raised the identical entry; the fixed sibling reads "== the certificate's number is 2^-40" (`pgl27_proximity.v:74-75`) with docstring "The certificate's number is the two-hundred-letter walk's marginal number, 2^-40." (`:319-320`). The statement is `ipc_eps (psl211_word_proximity_cert R idx) = 2%:R^-40 :> R`. | header: "== the certificate's number is 2^-40"; docstring: "The certificate's number is the 584-letter walk's number, 2^-40." |
| N7 | MUST | `psl211_word_proximity.v:46-48` | header entry "psl211_word_proximity_close == the two models' joint laws of reading and chirality are within 2^-40" | The entry drops the statement's premise and its coalition. The declaration (`:121-136`) is `forall (C : {set seatT}), (#|C| < profile_k (instance_profile psl211_algebra))%N -> var_dist … <= 2%:R^-40`, so the joint laws are a coalition's, and the statement is premised on the threshold even though the proof discards the premise with `move=> _`. The fixed sibling `pgl27_proximity.v:66-69` reads "== below the four-seat threshold, the two models' joint laws of reading and secret are within 2^-40". The threshold value six is read from this file's own header (`:24`); not compiled. | `(*   psl211_word_proximity_close                                              *)` / `(*                              == below the six-seat threshold, the two      *)` / `(*                                 models' joint laws of a coalition's        *)` / `(*                                 reading and the chirality are within 2^-40 *)` |
| N8 | MUST | `staged/manifest/pgg_analysis_manifest.v:841-845` (Row 11 level justification, `:831-847`) | "Row 9 records the same instance and the same execution at the uniform cut, and the model of Row 9 is the ideal this row's certificate is measured against; **the two rows differ in the law of the cut alone** and carry different statements, …" | False, and contradicted by the manifest's own text 230 lines below. `psl211_row_alldecks` carries `PSL211Analysis.exact_family` and `StaticExecutedOnly`; `psl211_row_word` (`:1091-1093`) carries `PSL211Analysis.word_family` and `IdealFinite`. The two rows differ in two of their five coordinates, which the `psl211_row_word` docstring (`:1088-1089`) states correctly. Landing-3 N17 and N18 flagged this exact shape in Row 10's block and in `pgl27_row_prior_exact`'s docstring. | "…is the ideal this row's certificate is measured against. The two rows differ in the model family and in the transfer status, and they carry different statements, Row 9 exact independence and this row a bound on the distance to that independent model." |
| N9 | MUST | `psl211_word_proximity.v:238` | `Fail Definition psl211_word_law_tauto` | The name says the statement is a tautology. The statement is `var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2%:R^-40` (`:239`), the 2^-40 bound, which is the one non-tautological fact of the file; what is tautological is the rejected proof term `var_dist_le2 _ _`. The tree names a recorded `Fail` after the subject and the route attempted: `five_card_biased_proximity_by_computation`, `five_card_biased_proximity_by_done` (`five_card_proximity.v:514`, `:522`), `pgl27_word_proximity_cert_unit_ideal`, `pgl27_word_proximity_cert_uniform_ideal`. | `psl211_word_law_by_var_dist_le2`. The header does not index recorded `Fail`s, so the rename touches this line and `verify.py`'s `EXPECTED`/scan lists only; needs a compile. |
| N10 | MUST | `psl211_word_proximity.v:236-237` | "So the number psl211_word_lawE proves is carried by psl211_word_mixing **and by nothing that holds of an arbitrary pair of laws**." | A `Fail` guard shows that ONE named term does not typecheck at the ascribed type. It cannot establish that no fact true of an arbitrary pair of laws proves the bound, which is a universal claim over a class of facts. The quoted error itself is about `var_dist_le2` alone. | "So the bound `var_dist_le2` gives for an arbitrary pair of laws does not reach this number; what carries it is psl211_word_mixing." |
| N11 | MUST | `staged/manifest/pgg_analysis_client.v:7` | `(* eleven typed rows. The file has EXACTLY ONE Require of any kind, and      *)` | 79 bytes. The base line (`landing3/staged/manifest/pgg_analysis_client.v:7`) is 80, and every other box line of this header is 80; "ten" to "eleven" added three characters and five spaces were removed instead of three. | Add one space before `*)`, giving `…of any kind, and       *)` at 80 bytes. |
| N12 | MUST | `staged/instances/psl211/psl211_analysis.v:43` | `(*   584-letter word sample model           -> word_sample, word_family       *)` | The check table aligns `->` at column 46 in all thirteen other rows (`:34-42`, `:44-53`); this row puts it at column 44. The line is 80 bytes, so only the interior padding is wrong. | `(*   584-letter word sample model` + 13 spaces + `-> word_sample, word_family` + 5 spaces + `*)`, which is 80 bytes with `->` at column 46. |
| N13 | SHOULD | `psl211_word_model.v:137` (and header `:41`, Row 11's model-transfer cell, `landing_fidelity.v`) | `Lemma psl211_word_lawE` | The `E` suffix names an equation throughout this tree and throughout this file: `psl211_word_sampleP_E` (`:104`) and `psl211_word_cut_distE` (`:112`) are equalities, as are `psl211_alldecks_sampleP_E` and every other `…E` of `psl211_models.v`. `psl211_word_lawE`'s statement is `var_dist (psl211_wordP R) (psl211_alldecksP R) <= 2%:R^-40`, an inequality. The same file names the other inequality correctly, `psl211_word_law_le2`. The tree's shape for a bound at a power of two is `pgl27_word_proximity_le39` (`pgl27_proximity.v:352`). | `psl211_word_law_le40`. The rename touches this declaration, the `psl211_word_model.v` header entry, `psl211_word_law_tauto`'s comment (`:236`), the manifest's Row 11 model-transfer cell and `landing_fidelity.v`; needs a compile. |
| N14 | SHOULD | `psl211_word_proximity.v:281`, `staged/manifest/pgg_analysis_manifest.v:804` against `psl211_word_proximity.v:305-306`, `pgg_analysis_manifest.v:1087` | "an **idealised** shuffle being replaced here by a shuffle of 584 letters" / "an **idealised** uniform shuffle replaced by a word of 584 letters" against "the all-decks row comparing no **idealized** model" / "so an **idealized** shuffle is replaced by a finite one" | Two spellings of one word inside landing 4's own new text, twice each. Production spells it "idealized" in 34 places (for example `security/pgg_collusion_bound.v:8`, and Row 9's and Row 10's own missing-premise cells); "idealised" occurs 3 times, all in `instances/pgl27/pgl27_mixing.v`. | "idealised" to "idealized" in both places. |
| N15 | SHOULD | `psl211_word_proximity.v:9` against `psl211_word_model.v:94`, `psl211_word_proximity.v:193`, `:194`, `:250` | "the twelve-card chirality instance is the third **carrier** of that arm" | Three senses of one word across the two new files. At `psl211_word_model.v:94` and at `psl211_word_proximity.v:193`, `:194`, `:250` "carrier" is the underlying type, which is the mathcomp sense and the one the header entry at `:56` uses. At `psl211_word_model.v:12` it is the model. Here it is a protocol instance. | "…and the twelve-card chirality instance is the third instance to publish through that arm, beside Kim's one-cut five-card model and the eight-card orbit instance." |
| N16 | SHOULD | `psl211_word_model.v:22-25` | "Both models put a deck description and a cut in one sample point, so the model below is the all-decks **adapter** with the law of the cut coordinate replaced, and the chirality of one model is the chirality of the other as one term rather than two readings of one bit." | Says twice over what the header already says at `:11-14` ("The two models share the sample space, the deck description and the law it is drawn from, and differ in the law of the cut alone: this file is the all-decks **carrier** with that one coordinate's law replaced"), in different words for the same object, and its second clause is the `psl211_word_sample` docstring's last sentence (`:94-95`, "Its sample space is the carrier psl211_alldecks_sample uses, so the chirality is one random variable for the two models"). Landing-2 N4 is the same class. | Delete the paragraph. If the "one term rather than two readings of one bit" framing is wanted in the header, fold it into `:11-14` and drop it from the `psl211_word_sample` docstring, so the sentence is in one place. |
| N17 | SHOULD | `psl211_word_model.v:27-30` | "The deck description and the cut are independent in both models because each law is written as a product, which is **the dealer drawing the word without seeing the deck**: a premise about how the shuffle is performed and not a theorem about the execution." | The clause after "which is" is verbatim the `psl211_wordP` docstring at `:83-84` ("the two independent by construction, which is the dealer drawing the word without seeing the deck"). The header paragraph earns its place only for the second half, which is the part the declaration comment does not say. | "That both laws are written as products is a premise about how the shuffle is performed and not a theorem about the execution: it says the dealer draws the word without seeing the deck." Then drop the repeated clause from `:83-84`, leaving "the two independent by construction". |
| N18 | SHOULD | `psl211_word_model.v:130-131` | "The two models' laws are within 2^-40 of each other in **the sum of absolute differences, which is 9.094947017729282e-13**." | "Which" attaches to the nearest noun phrase, so the sentence reads as though the sum of absolute differences were a fixed number. The decimal is 2^-40. Landing-2 N15 and N25 are the ambiguous-antecedent class. | "The two models' laws are within 2^-40 of each other in the sum of absolute differences. That number is 9.094947017729282e-13." (See N27 on the decimal itself.) |
| N19 | SHOULD | `psl211_word_proximity.v:156-157` | "**The only inexact quantity is that number**: the ideal, its witness and the secret are the terms the all-decks row **already** publishes." | Two things. A model, a witness and a secret are not quantities, so "the only inexact quantity" compares things of different kinds; landing-2 N8 flagged the same sentence shape at `five_card_proximity.v`. And "already" narrates the order in which the two rows were written rather than stating a relation between them. | "The ideal, its witness and the secret are terms the all-decks row publishes; the number is this certificate's own." |
| N20 | SHOULD | `psl211_word_proximity.v:155` | "…the word walk's number 2^-40; and **the distance above**." | The fifth field is `(fun C HC => @psl211_word_proximity_close R C HC)`, a proof of a `<=`, not a distance. The manifest's own Row 11 cell names it correctly, "whose distance field is psl211_word_proximity_close" (`pgg_analysis_manifest.v:796-799`), and so does `psl211_word_proximity_close`'s own docstring at `:117` in the corrected form N26 asks for. | "…the word walk's number 2^-40; and the distance field above, which bounds that distance by that number." |
| N21 | SHOULD | `psl211_word_proximity.v:178-179` | "**Both projections close by exact: erefl in under 0.01 s.**" | A timing measurement in permanent text, and the sentence before it in the same comment already says the tactic is `exact: erefl`. `STATUS.md` records that this sentence replaced a dated one; what is left is the effort half of the same narration. The sibling's equivalent comment (`pgl27_proximity.v:404-405`) carries no number. Landing-3 N25 accepted in-proof timing numbers only where a number is the reason a line reads as it does, which is not the case for a tactic that costs nothing. | Delete the sentence. The comment then reads "exact: erefl and not by []: done does not return on an equation between two rows' coordinates, where exact: erefl decides it at once." |
| N22 | SHOULD | `psl211_word_proximity.v:177-180` against `:137-141` | the `(* … *)` comment placed between the statement and `Proof.` | The same file puts the other proof-strategy comment INSIDE the proof (`psl211_word_proximity_close`, `:138-140`), and the fixed sibling puts this very comment inside the proof too (`pgl27_proximity.v:403-407`). Landing-2 N31 and landing-3 N24 recorded the two placements; landing 3's fix pass settled on inside. The two placements now coexist in one new file. | Move it inside: `Proof.` / `(* exact: erefl and not by []: done does not return on an equation between two rows' coordinates, where exact: erefl decides it at once. *)` / `split; exact: erefl.` / `Qed.` |
| N23 | SHOULD | `psl211_word_proximity.v:61-66` | header entries "psl211_word_law_le2 == the two models' laws are within **the bound** every pair of laws on one sample space meets" and "psl211_word_proximity_cert_eps_lt2 == the certificate's number is below **that bound**" | Neither entry names the number. `psl211_word_law_le2` is `… <= 2%:R` (`:226`) and `psl211_word_proximity_cert_eps_lt2` is `… < 2%:R` (`:253`), and a reader of the index cannot tell what either bound is. "That bound" also takes its antecedent from the previous entry rather than from inside its own, which is landing-2 N25 and landing-3 N11. The fixed sibling reads "== that number is below the bound two var_dist_le2 gives" (`pgl27_proximity.v:83-85`). | "psl211_word_law_le2 == the two models' laws are within two, the bound var_dist_le2 gives for any pair of laws on one finite sample space" and "psl211_word_proximity_cert_eps_lt2 == the certificate's number is below that bound two". |
| N24 | SHOULD | `psl211_word_proximity.v:242-243` against `:37-39` | "the bound var_dist_le2 of lib/var_dist_supp.v gives for a **variation distance**" | The file's own header, two hundred lines above, has told the reader that "Every number below bounds **a sum of absolute differences**, which is twice the total variation distance of the literature". Naming the same quantity by the halved name inside the file is landing-2 N6 exactly, at the same lemma's sibling. | "…the bound var_dist_le2 of lib/var_dist_supp.v gives for a sum of absolute differences." |
| N25 | SHOULD | `staged/manifest/pgg_analysis_manifest.v:18-21` | "**A row records no security arm.** Which arm a published program carries is read off that program by security_arm_of of manifest/pgg_tableau.v, so **a row at the proximity arm** is told from one at the exact arm by the certificate its table names and not by a field of the record." | The paragraph's first sentence denies what its third sentence presupposes. The object that has an arm is the published program; the row is the record that does not. | "A row records no security arm. Which arm a published program carries is read off that program by security_arm_of of manifest/pgg_tableau.v, so which arm a path carries is told from the certificate its table names and not from a field of the record." |
| N26 | SHOULD | `psl211_word_proximity.v:114` | "It is **the certificate field** of the proximity arm at this instance" | Every record field of a certificate is a certificate field. The manifest and the rest of the tree name this one "the distance field" (`pgg_analysis_manifest.v:798-799`, `STATUS.md` passim). | "It is the distance field of this instance's proximity certificate" |

## Notes

| id | class | file:line | quoted text | problem with evidence | replacement |
|---|---|---|---|---|---|
| N27 | NOTE | `psl211_word_model.v:131`, `psl211_word_proximity.v:207` | "9.094947017729282e-13" (twice) | Landing-3 N26 recorded the same literal at PGL(2,7) as the only scientific-notation figure in a rendered comment of a tree that writes numbers in words, and the owner left it. Recorded for consistency of the record only, and the figure is right: 2^-40 = 9.0949470177292824e-13. | Owner's call. No action taken here. |
| N28 | NOTE | `psl211_word_model.v:77`, `:110`; and, in inherited text, `psl211_reading_constancy.v:16` | "2^-40, the bound psl211_word_mixing proves, is the whole **price** of the departure" / "the distance the proximity arm **spends** is a distance between the two cuts of one execution" / "this file is what the input-indistinguishability arm would **cost** it" | The complete inventory of economic-metaphor words in landing 4's landed text, as the remit asks for as one note. The first two are new text of `psl211_word_model.v`. The third is production's sentence, inside the passage E5(d) rewrote but not in the words it added. The open owner question from landing 3 (N1) governs all three. | Owner's call. If the question is settled against the metaphor: ":77 …is the whole information-theoretic cost of the departure" becomes "…is the whole distance between the two models"; ":110 the distance the proximity arm spends" becomes "the distance the proximity arm bounds". |
| N29 | NOTE | `psl211_word_proximity.v:104-105` | `Local Notation seatT` | Not indexed in the header's `Definitions:` or `Key results:` blocks, so the file indexes 14 of its 14 non-`Fail` `Definition`/`Lemma`/`Fact`/`Theorem` declarations and neither of its notations. That is the tree's precedent: `instances/psl211/psl211_rows.v` declares `seatT` and `cardT` at `:132` and `:136` and indexes neither. Clean, no action. | — |
| N30 | NOTE | both new files, naming | `psl211_word_sampleP_E`, `psl211_word_proximity_cert_secretTE`, and the sibling role shapes | Checked as the remit asks. `sampleP_E` with its underscore is production's own spelling: `psl211_alldecks_sampleP_E` is `instances/psl211/psl211_models.v:230`, so the new name matches its own file's sibling and not the bare `E` convention, which is the right call. `_secretTE` has no precedent, and it is the tree's `<field>E` convention applied to the field `ew_secretT`, so it parses. Same-role names match the PGL(2,7) sibling one for one: `_proximity_close`, `_proximity_cert`, `_proximity_cert_idealE`, `_proximity_cert_epsE`, `_proximity_cert_eps_lt2`, `_pow2_40_ge1`, `_pow2_40_gt0`, `_row_word_proximity`, `_rowE`, `_armE`, `_view_proximity`. No role is missing: `pgl27_word_proximity_le39` has no counterpart because this row has no `conclude`, and `_eps_halfE` and `_arm_neq` have none because this instance carries no input-indistinguishability certificate over the word model to relate a number or an arm to. | Clean. |
| N31 | NOTE | whole tree | collisions | A walk over every `.v` file outside `notes/`, `docs/`, `.claude/`, `.git/` and `_build/`, matching every `Definition`, `Lemma`, `Theorem`, `Fact`, `Corollary`, `Notation`, `Record`, `Inductive`, `Fixpoint`, `Axiom`, `Variable`, `Let`, `Remark` and `Example` head against the 25 landed names, returns zero hits. No landed name collides with a production identifier or with a landing-3 staged name. | Clean. |
| N32 | NOTE | the six files | mechanical scans | No line over 80 bytes in any landed or changed text. No hit for any word of the project's banned vocabulary list in the two new files or in the added text of the four edited ones. No abbreviation of "indistinguishability" and no `_indist` segment. No occurrence of the metaphor noun the campaign removed for a bound. Box-comment `*)` column: two defects, N11 and N12; every other added box line in the four edited files and every box line of the two new files closes at column 80. | Clean but for N11, N12. |
| N33 | NOTE | `psl211_word_proximity.v:281-282` | "Its transfer status is IdealFinite, an idealised shuffle being replaced here by a shuffle of 584 letters." | `IdealFinite` is written into the `publish` clause at `:287`; it is chosen, not derived. Landing-2 N27 and landing-3 N5 flagged the stronger form of this ("the status the input-indistinguishability row earns"); this one only gives the reason for a chosen constructor, which is design rationale rather than a statement of what the object is. Recorded, not raised, because the reason is also the mathematical difference between this row and Row 9 and is stated as such elsewhere. | Optional: "Its transfer status is IdealFinite: the cut is a shuffle of 584 letters where psl211_row_alldecks draws it uniformly from the group." |
| N34 | NOTE | `psl211_word_proximity.v:37-39`, `:269-270`; `staged/manifest/pgg_analysis_manifest.v:839-841` | "a distinguisher's advantage against the published row is at most half of 2^-40" / "a distinguisher's advantage is therefore at most half of it" / "a distinguisher's advantage against this row is at most 2^-41" | The half relation is stated three times in prose and proved nowhere, which is the tree's practice (`security/var_dist_joint_law.v`'s header states it and no lemma carries it). Two renderings of one number, "half of 2^-40" and "2^-41", in the two files that carry it. The currency labelling the owner's rule asks for is present and correct: `psl211_word_model.v:135-136` says the bound is unconditional and information-theoretic and names what it counts. | Optional: use "2^-41" in both places, or "half of 2^-40" in both. |
| N35 | NOTE | `psl211_word_proximity.v:302` | "the model family the sample step named, and the two statuses the terminal **was given**" | Passive past tense for a property of the program text. It reads as narration but describes the program's own syntax, and the phrase is the fixed sibling's verbatim (`pgl27_proximity.v:192-193`), so it is the settled wording. Recorded only. | — |
| N36 | NOTE | `psl211_word_proximity.v:16-22` against `psl211_word_model.v:16-20` | the "Word gloss of this instance" paragraph | Repeated verbatim in both new files, with one sentence added in the second. Header exposition anchored to nothing is what the rule asks for, and each file is read on its own, so a reader of either gets the gloss. Recorded because the two copies can now drift apart. | — |
| N37 | NOTE | vocabulary, both new files | "reading" / "view", "published at" / "concluded at", "word" / "walk", "chirality" | Checked as the remit asks. "View" appears in no prose of either new file; `sa_coalition_view` and `word_view_proximity` are identifiers, and the changed comment of `psl211_word_view_proximity` at `:317` now says "reading", which is landing-2 N10 applied. "Published at" appears at `:39` (index entry) and `:264` and "concluded at" nowhere, which is right for a row with no `conclude`; landing-3 N27 flagged the mixture at PGL(2,7) and this file does not repeat it. "584-letter word" and "584-letter walk" both appear, which is the sibling's practice too (`pgl27_proximity.v:319`, `:476`). "Chirality" is used throughout for the secret bit and never varied. "All-decks carrier" occurs once, at `psl211_word_model.v:12`; see N15 and N16 for the word "carrier". | Clean but for N15, N16. |

## Coverage

**Permanent-text read, remit 1.** Every line of the two new files and every
added or changed line of the four edited files was read against the list of
narration markers. Hits: "already" at `psl211_word_proximity.v:157` (N19), "was
given" at `:302` (N35, settled wording), the timing measurement at `:179`
(N21). No probe, stage, ledger, audit, fix pass, batch, landing, date, paper
table or measurement campaign is named anywhere in the landed text except the
"paper's table" sentence of N2. The dates the probe carried are gone.

**Statement-comment discipline, remit 2.** Walked, one at a time, against its
declaration:

- `psl211_word_model.v`, all seven: `psl211_word_cutP` (`:72-77`, fact and
  position both present; N28 on one word), `psl211_wordP` (`:81-86`; N17 on the
  duplicated clause), `psl211_word_sample` (`:91-95`; the "one random variable
  for the two models" clause is the file's load-bearing sentence and is correct
  against the `finType` argument at `:100`), `psl211_word_sampleP_E`
  (`:103`, one line for a conversion equation, which is the right length),
  `psl211_word_cut_distE` (`:108-111`; N28), `psl211_word_family` (`:118-121`,
  and it says the index types agree rather than that an index separates two
  models, which is landing-3 fix-1's MUST avoided), `psl211_word_lawE`
  (`:130-136`; N13 on the name, N18 on the antecedent; the currency labelling in
  the last sentence is the best in the landing).
- `psl211_word_proximity.v`, all fourteen statements and all three recorded
  `Fail`s: `psl211_word_proximity_close` (N26), `psl211_word_proximity_cert`
  (N19, N20), `_cert_idealE` (N4, N21, N22), `_cert_secretE` (`:182-186`,
  clean: it names what a mismatched pair of secrets would cost the arm's
  proposition), `_cert_secretTE` (`:193-197`, clean, and the vacuity boundary
  at a one-point carrier is exactly what the rule asks for), `_cert_epsE`
  (N6), `psl211_pow2_40_ge1` and `_gt0` (`:212`, `:216`, one line each, right
  length for a re-tupling fact), `psl211_word_law_le2` (`:220-224`, clean),
  `psl211_word_law_tauto` (N9, N10), `_cert_eps_lt2` (N23, N24),
  `psl211_row_word_proximity` (`:264-282`; the three refutations it cites and
  the arithmetic of the `_word584` side condition check out against
  `psl211_reading_constancy.v`'s own header, "eps < 1/1320 - 2^-40" being
  2*(eps + 2^-40) < 1/660; N14, N33), `_armE` (N2), `_rowE` (N1),
  `psl211_word_view_proximity` (`:315-321`, clean; the closing sentence is the
  fixed sibling's verbatim), `_cert_pgl27_ideal` (`:341-351`, clean: it says the
  field is rejected at its type and claims no impossibility beyond that),
  `_cert_ideal_self` (`:363-375`, clean).
- The two facade aliases: `word_sample` (`psl211_analysis.v:169-172`) and
  `word_family` (`:178-181`). Both follow the file's leading-name and em-dash
  convention, both say what the object is without restating the type, and
  `word_family`'s index-type sentence is correct. The section 4 banner rewrite
  (`:156-161`) is accurate. N12 is the only defect on this file.
- The Row 11 comment block (`pgg_analysis_manifest.v:769-847`): field order
  matches Row 9's and Row 10's, every cell was read against the declaration it
  names, and the capabilities table's three lines match
  `psl211_word_view_proximity`, `observed_recovers` and `secret_expectedE`.
  Naming raw declarations with their file paths in the bridges, certificate and
  final-bridge cells is Row 10's established practice, not a drift. N8 and N14
  are the defects; the level justification's Sampled and AnalysisBridged steps,
  the threshold sentence and the currency sentence are all correct.
- The `psl211_row_word` docstring (`:1080-1090`): correct, including the
  two-coordinate difference N8 gets wrong 230 lines above.
- The manifest header's new paragraph: N25. Row 9's missing-premise addition
  (`:668-671`): correct, and it is the wording landing 3 gave Row 10.
- The four changed passages of `psl211_reading_constancy.v` (`:14-16`,
  `:43-46`, `:72-74`, `:773-781`): all four read clean. Each states a relation
  between two propositions rather than narrating what changed; (a) and (b)
  replace clauses the word adapter makes false and the replacements are checked
  against `IdealProximityCert`'s five fields, which carry no constancy field,
  and against the lemma's own quantification over `ideal` and `eps`; (c) and
  (d) name the other arm and the file that carries it. No finding.

**Header index blocks, remit 3.** `psl211_word_model.v`: 4 `Definitions:` plus
3 `Key results:` = 7 of 7 non-`Fail` declarations, no `Fail` indexed, every
spelling exact, every description checked against its declaration, all seven
clean. `psl211_word_proximity.v`: 2 plus 12 = 14 of 14 non-`Fail`
declarations, no `Fail` indexed (which is the tree's precedent, landing-2 N22),
every spelling exact; four descriptions are wrong or empty, N3, N5, N6, N7, and
two under-specify, N23. Header prose of `psl211_word_proximity.v`: five
paragraphs, all exposition, none a copy of a declaration comment, and the fifth
carries the currency sentence; clean. Header prose of `psl211_word_model.v`:
N16 and N17.

**Shape against the two siblings, remit 3.** Section order matches
`pgl27_proximity.v` and `five_card_proximity.v` where the mathematics is shared:
distance, certificate and ideal, the number, the row, what the row states, what
the arm refuses. Divergences that are not forced: the file splits the refusals
into one section (`:337-339`) where `five_card_proximity.v` uses two banners and
`pgl27_proximity.v` one, which landing-3 N21 already recorded as accepted; and
the proof-comment placement of N22. Divergences that ARE forced and are correct:
no ideal-row section, because the ideal row is `psl211_rows.v`'s and is only
cited; no `conclude`, so no `Reprice`, no `_le39`-shaped obligation and no
`PublishedRowAt`; no second row over the model, so no `_arm_neq` and no
`_sampledE` pair; no input-indistinguishability certificate, so no `_eps_halfE`.
Banners, `Section` use (none, where `five_card_proximity.v` opens one for the
numbers) and the `Local Notation` preamble all read alike.

**Names, remit 4.** All 25 landed names checked against the tree's conventions
and against both siblings: N9 and N13 are the two defects, N30 records the
checks that came back clean, N31 the collision scan. `psl211_row_word` matches
`pgl27_row_word` and `psl211_row_alldecks`; the facade aliases `word_sample`
and `word_family` match `exact_sample` and `exact_family` in shape and drop the
`psl211_` prefix as the facade's contract requires.

**One word per concept, remit 5.** Checked across the two new files and against
`manifest/pgg_tableau.v`, `instances/psl211/psl211_rows.v`,
`instances/psl211/psl211_reading_constancy.v` and
`instances/kim2025/five_card_proximity.v`. Findings N14, N15, N24; clean
results recorded in N37. "Coordinate" is used in one sense only in the new text,
a field of an `AnalysisPathRow` (`:178`, `:301`), so landing-2 N11 and
landing-3 N20 do not recur.

**Mechanical, remit 6.** N11, N12; everything else in N32.

## What a fix pass must not lose

- The `psl211_word_law_le2` docstring's "A proximity certificate carrying two
  would be a certificate about nothing", and the `_cert_secretTE` docstring's
  one-point-carrier sentence. These two are the file's vacuity boundaries and
  are the best-written comments in the landing.
- `psl211_word_lawE`'s closing sentence, "The bound is unconditional and
  information-theoretic: it counts the 3^584 words and assumes nothing about an
  adversary's resources." N13 renames the lemma and must keep this.
- The arithmetic clause of `psl211_row_word_proximity`'s docstring, "once twice
  the sum of eps and 2^-40 stays below 1/660", which is the only place the
  landing states the side condition of the `_word584` refutation.
