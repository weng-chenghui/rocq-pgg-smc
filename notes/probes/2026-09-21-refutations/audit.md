# Audit of the refutations probe (2026-09-21)

Audit of `notes/20260921-refutations-probe-design.md` and
`notes/probes/2026-09-21-refutations/`, before a landing plan is written.
Two remits: adversarial soundness, and naming, style and placement. This
file is the only file the audit writes; its scratch compiles are under
`…/scratchpad/refute_audit/a_audit.v`.

Vocabulary of this report: a Tableau value is a PROGRAM, the manifest's
record is a PATH, a program certifies a SECURITY PROPERTY with SECURITY
EVIDENCE, and the evidence proves a PROPOSITION.

## Verdict

**GO for writing a landing plan**, with four MUST items settled inside the
plan before any file is touched. Nothing compiled in the probe is false.
Every theorem the probe states holds, `Print Assumptions` is the classical
trio throughout, and the six main files recompile. The four MUST items are
about what the statements *mean*, not about whether they hold:

1. the obstruction proposition takes a free law and is therefore satisfiable
   at every model, so a published obstruction is not by itself a statement
   about the model (D1);
2. N9 is stated under a certificate binder it does not use, so it is vacuous
   exactly when the certificate type is empty, and that type's inhabitation
   at this model is argued and not compiled (D2);
3. the ledger's account of how N3 and N9 relate is wrong in one direction
   (D3), and an existing theorem of the tree already covers part of N3 and is
   not named (D4);
4. the sentence that reconciles the obstruction with the instance's
   exact-independence program gives the wrong reason (D5).

All four are repairable by restatement, and the restatements are compiled in
the audit's scratch file (rc 0, classical trio only). None requires changing
an existing declaration.

### What was compiled for this audit

`…/scratchpad/refute_audit/a_audit.v`, one Rocq process, rc 0, all
`Print Assumptions` the classical trio and nothing else:

| tag | statement | why |
|---|---|---|
| A1 | `var_dist_xx : var_dist d d = 0` | the name the tree should use (D15) |
| A2 | `NoCertIdealCloseAnchored sa eps` (no free law) | the repair for D1 |
| A3 | reading gap `b` and `eps + eps < b` give the anchored obstruction | framework route, no constancy proposition |
| A4 | `1/#\|G\| <= var_dist (fdistmap (obs C (true,deal)) (sa_cut_dist sa)) (fdistmap (obs C (false,deal)) (sa_cut_dist sa))` | the certificate-free core, the repair for D2 |
| A5 | N9 from A4 | N9 is a corollary of the core |
| A6 | the anchored N3 from A3 and A4 | N3 is a corollary of the same core |
| A7 | the probe's N3 verbatim from A6 | the anchored form loses nothing at this model |
| A8 | `var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps -> IndistinguishabilityPropAt cert (eps + eps)` | generalises `indistinguishability_tail` |
| A9 | the probe's N3 verbatim from the probe's N9 verbatim, through A8 | refutes the ledger's claim (D3) |
| A10 | `indistinguishability_tail` from A8 | A8 subsumes the tree's own tail lemma |

## Findings

| id | grade | row | file:line | finding | rule, problem and evidence | what to change |
|---|---|---|---|---|---|---|
| D1 | MUST | N1, N5 | `n_framework.v:56` | `NoIndistinguishabilityCertNear sa U eps` leaves both payload coordinates unconstrained: the law `U` is not tied to the model, and `eps` is not constrained in sign. | The kind is what a published obstruction hands a reader, so whatever the kind does not constrain, the reader must check by hand. Two gaps. (i) Sign: `var_dist` is non-negative (infotheo `pos_var_dist`), so at any `eps < 0` the class is empty and the proposition holds at **every** model and every law. Nothing in `ObstructionKind`, in `refute` or in the path rejects such a value, and the probe itself hit this — `n_pgl27_nonvacuity.v:69` carries `0 <= eps` as a hypothesis for exactly this reason — without carrying the constraint back into the kind. (ii) The law: the proposition is the intended one only when `U` is the model's own cut law, since `ic_close` and `ic_Hd` place a certificate's ideal within its own marginal bound of `sa_cut_dist sa` and of nothing else. At psl211 the identification holds (`psl211_alldecks_cut_distE`), but the framework does not record it and `ObstructionProp` does not check it, so a reader of `obstruction_of` reads a statement whose domain meaning rests on an unrecorded fact. N4(a) tests one law at one other model and closes neither gap. | Anchor the law: `forall cert, var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps -> False`, with no law argument and the constructor carrying `eps` alone. Compiled as A2; the psl211 row goes through unchanged (A6) and the probe's own statement follows from it (A7). Then either require `0 <= eps` in the constructor, or say in the kind's comment that a number below zero makes the statement empty at every model. |
| D2 | MUST | N9 | `n_psl211_number.v:112` | `psl211_alldecks_indistinguishability_number_ge` quantifies over a certificate that its conclusion and its premise both ignore, so it is vacuous exactly when `IndistinguishabilityCert (amf_sample psl211_exact_family R tt)` is empty. | `IndistinguishabilityPropAt` does not mention its certificate; the tree says so itself at `manifest/pgg_tableau_security_property_relations.v:202`, `indistinguishability_prop_cert_free`. Whether that type is inhabited here is not compiled: `instances/psl211/psl211_reading_constancy.v` header, "That occupancy is argued and not compiled." A reader of the landed statement cannot tell a lower bound from an empty quantifier. | State the certificate-free core first (A4) and derive the certificate-shaped statement from it (A5). The core is a lower bound on the gap between two readings of the model's own cut law and needs no certificate to exist. |
| D3 | MUST | N3, N9 | `LEDGER.md:665` | "Neither implies the other as stated" is false in the N9 to N3 direction. | Compiled counter-evidence: A8 proves `IndistinguishabilityPropAt cert (eps+eps)` from `var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps` alone, and A9 then derives the probe's N3 **verbatim** from the probe's N9 **verbatim**. A8 also subsumes the tree's `indistinguishability_tail` (A10), which is A8 at the certificate's own marginal-bound epsilon. | Correct the ledger sentence. Present the core as the obstruction and N3 as its corollary. See the section "N3 against N9". |
| D4 | MUST | N3 | `n_psl211.v:96` against `instances/psl211/psl211_reading_constancy.v:713` | The tree already proves `psl211_alldecks_no_small_eps_cert`, and neither the probe nor the spec names it. | Two theorems about the same model, both saying that some certificate does not exist, differing in which quantity is constrained. Without a sentence relating them, a reader cannot tell whether the landing added anything. In fact the landed statement is the more general one, and the existing theorem is it at `eps := sw_bound_eps (ic_b cert)` through `psl211_alldecks_cert_ideal_close`. | The landed statement's comment names `psl211_alldecks_no_small_eps_cert` and says: the landed one constrains where the certificate's ideal sits, the existing one constrains the certificate's own marginal bound, and the second follows from the first at the certificate's own number. Do not edit the existing theorem. One thing the audit did not compile: the existing theorem is stated at `psl211_alldecks_sample R` and the probe at `amf_sample psl211_exact_family R tt`, so the landing's first step is one `Check` that the two adapters are convertible. |
| D5 | MUST | N8 | `n_psl211.v:152` | "the certificate's fifth field asking for constancy of a reading in the whole run argument, of which the chirality is one coordinate of four" is not the reason the obstruction and the exact-independence program do not conflict. | The witnessing pair is `(true, psl211_perdeck_deal)` and `(false, psl211_perdeck_deal)`: it differs in the chirality **alone**, so the extra coordinates are not what separates the two facts. The separation is the quantifier: exact independence is stated under the sample law, with the deck description drawn uniformly (`ExactWitness`'s `ew_indep` at `sa_sampleP sa`; `psl211_tableau_sampled.v`, "The deck description is drawn uniformly in both"), while constancy and the reading gap are stated at two fixed run arguments. A second, separate fact is that the chirality reindexes the laid deck (`psl211_reading_constancy.v:270` ff, "the chirality selecting the table the block line indexes"). | Rewrite the sentence around the quantifier difference: a coalition below the threshold learns nothing about the chirality when the deal is drawn, and still separates two named run arguments by at least the reciprocal of the group order. Say both, in that order. |
| D6 | SHOULD | N5 | `n_framework.v:252`; `m_reader_secrecy.v`, `m_reader_property.v` | "no security reader of `manifest/pgg_tableau.v` applies to it" is carried by two `Fail Check`s. | A `Fail` rejects the one term written under it and states no general impossibility; `instances/psl211/tableau/psl211_tableau_checks.v` says exactly this in its own header. The type argument given beside it is sound and sufficient on its own: the security readers project out of `PublishedAt`, and `PublishedObstruction` is a different inductive type. | State the type fact as the claim, and cite the two recorded rejections as the two spellings that were checked. |
| D7 | SHOULD | N8 | `n_psl211.v:113` | "the largest round fraction inside the range" is a judgement about roundness. | Statement comments state what the object is, not why a number looked tidy. The theorem holds at every `eps` with `eps + eps` below the reciprocal of the group order, an open range with no largest member. | Say the range and that the program names one member of it. Drop "round". |
| D8 | SHOULD | N1 | `n_framework.v:68` | "the sharpest statement is the one at the largest eps a model admits" names a largest element of an open range. | The psl211 range is `eps + eps < 1/#\|G\|`, strict, so no largest `eps` exists. | Say the family is downward closed in `eps`, and give the open bound. |
| D9 | NOTE | N5 | `n_framework.v:141` | `ObstructionPayload` lets the kind differ at each real field and each model index. | Same freedom `SecurityEvidence` has through `ExactPayload` and friends, so it is consistent, but the landed comment should say it, since a reader may assume one obstruction per program. | One clause in the payload's comment. |
| D10 | NOTE | N5, N6 | `n_framework.v:206`, `refute_completionE` | The level `AnalysisBridged` on a value whose data stops at `Sampled` is honest, and the comment cites the wrong authority. | `manifest/pgg_analysis_manifest.v` header: "AnalysisBridged + bridge alias to a named security, leakage, mixing or **limitation** theorem about the same distribution and the same observer". `manifest/pgg_analysis_status.v:13`: "which a negative mixing result also does." The level is fixed by the kind of theorem present, not by the stack position, and a limitation theorem is named in the definition. The probe's comment argues the point from first principles instead of quoting the two lines that settle it. | Quote the definition's own words ("limitation theorem", "the same distribution and the same observer") in the landed comment. |
| D11 | SHOULD | N7 | `n_syntax.v:30` | `s \|> refute a o by pf` puts the assumption status first, against the tree's stated surface order. | `manifest/pgg_tableau_syntax.v`, above `s \|> publish t a`: "The two statuses are written transfer first, against the argument order of publish itself, so that a program's last statement reads in the order the manifest column headings run." `s \|> publish Sampled t a` repeats it. At `refute` the transfer coordinate is fixed, and the payload occupying that column is the obstruction, so the obstruction leads and the assumption status trails. Neither order avoids two adjacent slots, so adjacency is not a reason to invert. | `s \|> refute o by pf a`. |
| D12 | NOTE | N7 | `pgg_tableau_syntax.v:64` | The keyword budget claim checks out. | The nineteen are dealt, functionality, execute, endpoints, recon, sample, certify, leaks, tied, ideal, mixing, invariant, encoded, supplied, layout, decoded_by, committed_by, expecting, fuel. `refute` follows the literal `\|>`, as `publish` and `conclude` do, and `by` is ssreflect's, measured on 2026-09-19. The count stays nineteen. | Nothing, unless the terminal is renamed (D27), in which case `Obstruction` follows the literal `publish` and joins `Observed` and `Sampled` in the header's caveat about that position. |
| D13 | MUST | all | `n_framework.v:46,84,114`; `n_psl211.v:48,83,110,182`; every file header | Section banners and headers carry ledger tokens. | Statement comments carry no plan or ledger tokens. Probe files may; landed files may not. | Strip at landing. A banner states the mathematics of the section. |
| D14 | SHOULD | N3, N8, N9 | `n_psl211.v:216`; `n_psl211_number.v:156` | `Print Assumptions` lines are probe instrumentation. | The landed form of that evidence is the assumption status on the path, `BaselineClassicalOnly`, whose meaning duty (1) of the manifest header defines. The two recorded rejections of N5 have a home: `instances/psl211/tableau/psl211_tableau_checks.v`, "one written term that the kernel rejects". | Drop the `Print Assumptions` lines; move the two `Fail` terms to the checks file. |
| D15 | MUST | N4 | `n_pgl27_nonvacuity.v:47` | `var_dist_self` is taken, and the name is not the MathComp one. | `legacy/security/pgg_uniform_security.v:86` declares `var_dist_self` under the same logical name `pgg_smc`. MathComp's published fragment for a relation at one argument twice is `xx` (`lexx`, `eqxx`). `var_dist_xx` has zero occurrences anywhere in the tree. | `var_dist_xx`, compiled as A1. |
| D16 | NOTE | N4 | `n_pgl27_nonvacuity.v:43` | The docstring's claim about infotheo is accurate. | `infotheo/variation_dist.v` carries `symmetric_var_dist`, `pos_var_dist`, `def_var_dist`, `leq_var_dist` and nothing at one argument twice. | Nothing. |
| D17 | SHOULD | N1, N2, N3 | `n_framework.v:56,71`; `n_psl211.v:71,96` | "Near" is a picture where the tree already has a word. | The relation is `var_dist _ _ <= eps`, and the tree spells it `close`: `ic_close`, `psl211_alldecks_cert_ideal_close`, `psl211_alldecks_constancy_false_close`. One word per concept tree-wide. | Rename the family to `close`. See "Proposed names". |
| D18 | SHOULD | N2 | `n_framework.v:96` | `no_indistinguishability_cert_nearP` uses the `P` suffix for a sufficient condition. | In MathComp `P` marks a characterization or a reflection; this lemma is one-directional. | Name it by where its hypothesis comes from, or drop it in favour of A8 (see the placement section). |
| D19 | SHOULD | N2 | `n_psl211.v:56` | `coalition_reading_constancy_unfoldE` narrates an implementation step. | "unfold" is a tactic, not a fact. MathComp's `E` alone is the suffix for "the definition equals its body". | `coalition_reading_constancyE`, if the lemma lands at all; the A8 route removes the need for it. |
| D20 | SHOULD | N6 | `n_psl211.v:191` | `psl211_alldecks_obstruction_pathE` drops the word the tree puts there. | The tree writes `psl211_alldecks_published_pathE` and `psl211_word_proximity_published_pathE`: the equation is named after the published value. | `psl211_alldecks_obstruction_published_pathE`, and the same for the two comparison lemmas below it. |
| D21 | NOTE | N8 | `n_psl211.v:146` | `psl211_alldecks_obstruction_proof` names a proof rather than a fact. | The record's own field is `published_obstruction_pf`. | `psl211_alldecks_obstruction_pf`, or a name stating the content. |
| D22 | NOTE | N5 | `n_framework.v:121` | `ObstructionKind` names a kind rather than a domain thing. | `TransferStatus`, `CompletionLevel`, `SecurityProperty` and `AssumptionStatus` are the tree's classifier nouns and each names something in the domain; `Kind` does not. It is the weakest of the five and the least costly to leave. | Optional. If it stays, the field `published_obstruction_kind` stays with it. |
| D23 | NOTE | N5, N6 | `manifest/pgg_analysis_status.v:68` | "obstruction" is the tree's own word, and it is not interchangeable with "limitation". | `NegativeTransfer` is "a theorem transporting an **obstruction** to the path's observer", so the thing carried is an obstruction. The manifest header and `legacy/instances/abelian/abelian_analysis.v:263` (`limitation_transfer_status`) use "limitation" for the theorem and the path kind. | Keep both words, each for its own concept. Use "limitation theorem" only where the level's own definition is being quoted. |
| D24 | SHOULD | N6 | `n_psl211.v:182`; spec line 72 | The ruling not to touch the manifest is consistent with the header, and the reason must be written down precisely. | The header records **paths**, not programs, and imposes duties on paths; nothing in it requires a published program to have a path. The path field vocabulary admits the theorem ("its security, leakage, mixing or limitation theorem"), the level admits it, the status admits it. The single blocker is duty (3): "A capability line uses the narrowest label the theorem statement supports, from the closed vocabulary correctness, exact privacy, approximate privacy, trace secrecy, conditional entropy, mutual information or endpoint marginal mixing" — and no label there fits a limitation. Extending the closed vocabulary is the owner's call. | See "What the landed comment must say" below. |
| D25 | SHOULD | N4(b) | `n_framework.v:52`; `n_psl211.v:86` | The spec's N4(b) sentence sits at the framework and not where a reader meets the claim. | A reader of the psl211 theorem is the one who may over-read it. | Put it at the instance theorem: a certificate whose ideal sits further away is untouched by this statement, and, once N9 lands, add that such a certificate still publishes a number of at least the reciprocal of the group order. |
| D26 | NOTE | N9 | `n_psl211_number.v:53,78` against `psl211_reading_constancy.v:643` | The two mass lemmas repeat the `Ut` and `Uf` steps that `psl211_alldecks_constancy_false_close` performs inline. | Naming them is a pure addition and the right move, since they are the inputs of the certificate-free core. A reader should be told they are the same two computations. | One clause in each comment naming the lemma that computes them inline. |
| D27 | NOTE | N5, N7 | `n_framework.v:194` | `refute` stands outside the terminal family's naming. | The three handover terminals are `publish`, `publish_observed`, `publish_sampled`; a fourth named `publish_obstruction` keeps the family readable and gives the surface `s \|> publish Obstruction o by pf a`, in which `Obstruction` follows a literal and reserves nothing. Against it: "refute" is a precise logical verb and the spec chose it. | Owner's call. The audit prefers `publish_obstruction`. |

## N3 against N9

**What each says.** N3 (`psl211_alldecks_no_certificate_near`) denies the
existence of an input-indistinguishability certificate over the all-decks
model whose ideal cut sits within `eps` of the group-uniform law, whenever
`eps` added to itself stays below the reciprocal of the group order. N9
(`psl211_alldecks_indistinguishability_number_ge`) says that any number at
which the input-indistinguishability proposition holds over that model is at
least that reciprocal. N3 constrains where a certificate's ideal may sit; N9
constrains the number a program may publish.

**They have one common source.** Both rest on a single fact with no
certificate in it: under the model's own cut law, the coalition
`psl211_perdeck_coalition` reads the two chiralities of `psl211_perdeck_deal`
at masses zero and the reciprocal of the group order, so the two readings are
at least that far apart in the sum of absolute differences. That fact is A4,
compiled. N9 is A4 instantiated at the coalition and the pair (A5). N3 is A4
plus the triangle inequality and the data-processing inequality for
`var_dist` (A3, A6, A7): moving from the model's cut to an ideal within `eps`
of it moves each of the two readings by at most `eps`, and the certificate's
fifth field makes the two readings of the ideal equal.

**N9 as stated does imply N3 as stated.** The ledger says it does not
(`LEDGER.md:665`). Compiled refutation: A8 proves
`IndistinguishabilityPropAt cert (eps + eps)` from
`var_dist (sa_cut_dist sa) (ic_ideal cert) <= eps` alone, using `ic_const`,
the data-processing inequality and the triangle inequality; A9 then feeds
that to N9 verbatim and obtains N3 verbatim. The direction N3 to N9 does not
hold: N3 says nothing about the readings of the model's own cut law.

**A8 is worth landing on its own account.** It generalises the tree's
`indistinguishability_tail`, which is A8 at
`eps := sw_bound_eps (ic_b cert)` through `ic_close` and `ic_Hd` (compiled as
A10). One framework lemma then serves `indistinguishability_tail`, N3, N9 and
the existing `psl211_alldecks_no_small_eps_cert`.

**Which the landing should present as the obstruction.** The certificate-free
core, A4, with N9 and N3 as its two corollaries. Reasons:

- A4 is the only one of the three that is non-vacuous without an inhabitation
  premise (D2). N9 quantifies over a certificate the tree has not exhibited
  at this model, and N3 is an emptiness claim, so both can be true of an
  empty type. A4 is a numeric lower bound about the model's own law and holds
  regardless.
- A4 is the statement a domain reader wants: below the privacy threshold,
  three of the twelve seats separate two named run arguments by at least
  1/660 in the sum of absolute differences, so a distinguisher's advantage is
  at least 1/1320 at those two arguments.
- N9 is the sharper of the two published consequences, since it bounds what
  any input-indistinguishability program over this model can publish, whereas
  N3 rules out one construction route.

**What the `ObstructionKind` family should hold.** The probe kept N9 out of
the enumeration, the spec fixing one member. Once N3 is a corollary of the
core, the honest single member is the one that names the model's own
obstruction. Two shapes are available:

- one constructor carrying `eps`, the anchored N3 (D1): a program publishes
  "no certificate has its ideal within `eps` of my cut law";
- one constructor carrying `c`, N9: a program publishes "no
  input-indistinguishability program over me publishes below `c`".

The audit recommends landing the second as the single first member and the
first beside it only if the owner wants both, because N9 is the stronger of
the two (it implies N3) and it is the one whose statement names a quantity a
paper cites. If only one lands, the family is still a closed `Variant` and
not a free proposition: a free `Prop` payload is `restate`, and a reader of a
free payload cannot tell what kind of fact was published. A one-constructor
closed enumeration is therefore right even though a second member exists,
and adding the second later is a pure addition.

## Proposed names

Every replacement below was checked for collisions across the tracked tree
outside `notes/`, legacy included; each has zero occurrences unless said
otherwise.

| probe | proposed | why |
|---|---|---|
| `NoIndistinguishabilityCertNear sa U eps` | `NoIndistinguishabilityCertIdealClose sa eps` | "Near" is a picture; `close` is the tree's word for `var_dist _ _ <= eps` (`ic_close`, `psl211_alldecks_cert_ideal_close`). The law argument goes (D1). |
| `no_indistinguishability_cert_near_le` | `no_indistinguishability_cert_ideal_close_le` | tracks the above; `_le` is the MathComp suffix for the smaller-epsilon instance. |
| `no_indistinguishability_cert_nearP` | drop, or `indistinguishability_prop_of_ideal_close` | the `P` suffix is for a characterization. If the A8 route is taken this lemma is replaced by A8, which is the general fact and also gives `indistinguishability_tail`. |
| `no_certificate_near_of_constancy_false` | drop, or `no_indistinguishability_cert_ideal_close_of_constancy_false` | `_of_` is published; "certificate" becomes `cert`, the tree's spelling. Dropped entirely if A8 is taken. |
| `coalition_reading_constancy_unfoldE` | `coalition_reading_constancyE`, or drop | `E` alone is the MathComp suffix; "unfold" narrates a tactic. Not needed on the A8 route. |
| `ObstructionKind` | keep | a classifier noun beside `TransferStatus`, `CompletionLevel`, `SecurityProperty`; the weakest of the four but not wrong, and the record's field name depends on it. |
| constructor `NoCertificateNear U eps` | `NoIndistinguishabilityCertIdealCloseObstruction eps`, or, if the standalone proposition is dropped and `ObstructionProp` is the only writer, `NoIndistinguishabilityCertIdealClose eps` | the tree disambiguates a constructor from its proposition by a suffix (`InputIndistinguishabilityProperty` beside `InputIndistinguishability`). "Certificate" becomes `cert`. |
| `ObstructionProp` | keep | parallels `EvidenceProp`. |
| `ObstructionPayload` | keep | parallels `ExactPayload`, `IndistinguishabilityPayload`, `IdealProximityPayload`. |
| `ObstructionPropOf` | `ObstructionPayloadProp` | parallels `BridgedProp`, which is the tree's name for "the proposition a payload asserts at every field and index". |
| `RefutePayload` | keep, or `PublishObstructionPayload` if the terminal is renamed | `ConcludePayload` and `RestatePayload` are the precedent for naming a payload after its terminal. |
| `mk_obstruction` | keep | parallels `mk_indistinguishability`, and belongs in the same file as it (see placement). |
| `PublishedObstruction` and `published_obstruction_at/_path/_kind/_thm/_pf` | keep | parallels `PublishedSampled` and `published_sampled_at/_path/_thm` exactly, with two fields added. |
| `refute` | `publish_obstruction` preferred, `refute` acceptable | the other three handover terminals are `publish`, `publish_observed`, `publish_sampled`. |
| `refute_completionE`, `_transferE`, `_modelE`, `_observedE`, `_assumptionsE`, `_kindE` | `publish_obstruction_completionE`, … | track the terminal's name. The existing sets prove three of the five coordinates; proving all five plus the kind is a pure addition and is an improvement. |
| `obstruction_of` | keep | parallels `run_correct_of`, `view_secrecy_of`, `view_indistinguishability_of`. |
| `psl211_alldecks_no_certificate_near` | `psl211_alldecks_no_indistinguishability_cert_ideal_close` | tracks the proposition; distinguishes it from the existing `psl211_alldecks_no_small_eps_cert` in the name, not only in the statement. |
| (new, D2) | `psl211_alldecks_perdeck_reading_ge` | the certificate-free core: the two readings of the model's own cut law are at least `1/#\|G\|` apart. `_ge` is the MathComp suffix. |
| `psl211_alldecks_indistinguishability_number_ge` | keep, as a corollary of the core | the name is right; the proof route changes. |
| `psl211_alldecks_obstruction_published` | keep | parallels `psl211_alldecks_published`, `psl211_word_proximity_published`. |
| `psl211_alldecks_obstruction_proof` | `psl211_alldecks_obstruction_pf` | matches the record field it fills. |
| `psl211_alldecks_obstruction_eps_lt` | keep | parallels `psl211_word_proximity_cert_eps_lt2`; the comment carries the bound. |
| `psl211_alldecks_obstruction_pathE` | `psl211_alldecks_obstruction_published_pathE` | parallels `psl211_alldecks_published_pathE`. Same for `_path_observedE` and `_path_transfer_neq`. |
| `pgl27_word_no_certificate_near_false` | `pgl27_word_no_indistinguishability_cert_ideal_close_false` | tracks the proposition; `_false` is the tree's suffix for a refuted proposition (`psl211_alldecks_constancy_false`). |
| `var_dist_self` | `var_dist_xx` | `var_dist_self` is taken by `legacy/security/pgg_uniform_security.v:86` under the same logical name; `xx` is MathComp's fragment for one argument twice. |
| `pgl27_word_cert_ideal_uniform` | keep | states what the ideal is. |

## Placement

| piece | home | why |
|---|---|---|
| `NoIndistinguishabilityCertIdealClose`, its `_le`, `ObstructionKind`, `ObstructionProp`, `ObstructionPayload`, `ObstructionPayloadProp`, `RefutePayload`, `PublishedObstruction`, the terminal, the six path and kind equations, `obstruction_of`, `run_correct_of_obstruction`, `view_identification_of_obstruction` | `manifest/pgg_tableau.v`, a new section after "Handing a program over below AnalysisBridged" | The record is the fourth handover record and the terminal the fourth handover terminal; the other three live there, the placement rule of step 4.3 lives there, and the file's "Definitions:" index is the tree's map of the framework. About 130 lines onto 1293. The alternative, a new `manifest/pgg_tableau_refutation.v`, would have to be inserted **between** `pgg_tableau.v` and `pgg_tableau_syntax.v`, because the surface rule must stay in the file that carries the keyword accounting; that is a shape the tree does not yet have, since the two leaves landing today (`manifest/pgg_tableau_reading.v`, `manifest/pgg_tableau_marginal_bounds.v`) both sit above the syntax file. Take the leaf only when a second obstruction constructor makes the family a layer of its own. |
| A8, `indistinguishability_prop_of_ideal_close` | `manifest/pgg_tableau.v`, beside `indistinguishability_tail` | It is the general form of that lemma and its proof is the same argument with the number left free. Landing it beside its special case is a pure addition; `indistinguishability_tail` is not touched. |
| `mk_obstruction` and the surface rule | `manifest/pgg_tableau_syntax.v` | `mk_indistinguishability` and `obs_payload` are there, and that file's header is where the keyword count is measured. |
| N2, the general route | not needed, if A8 lands | A8 needs no constancy proposition: it uses `ic_const` directly. This dissolves the question of whether `coalition_reading_constancy` should move down. If the owner keeps the constancy route instead, the pure-addition alternative is the probe's own: the framework lemma writes the hypothesis out, and `instances/psl211/psl211_reading_constancy.v` gains the one-line identity (`coalition_reading_constancyE`) that catches later drift between the written-out form and the named one. Moving `coalition_reading_constancy` down beside `IndistinguishabilityCert` is the cleaner end state and is **not** a pure addition, so it is a separate unit, not part of this landing. |
| `psl211_alldecks_perdeck_reading_ge` (the core) and the two mass lemmas | `instances/psl211/psl211_reading_constancy.v`, appended | The two masses are the ones that file already computes inline inside `psl211_alldecks_constancy_false_close`, and the core is the quantitative form of the fact that file exists to record. Its header already argues the 1/660 consequence in prose; the core makes it a theorem in the same file. Appending is a pure addition. |
| `psl211_alldecks_indistinguishability_number_ge` | `instances/psl211/psl211_reading_constancy.v`, beside `psl211_alldecks_no_small_eps_cert` | The header of that file already states this result in prose ("every program over this model that publishes its certificate's own number publishes at least 1/660"), and it belongs with the existing certificate exclusions. |
| the obstruction payload, its proof, the published program, the path equations | `instances/psl211/tableau/psl211_tableau_analysis_bridged.v` | The path the program publishes is at `AnalysisBridged`, and the phase file is named by the level the path records. That file's header already says "No input-indistinguishability program is published over either model" and gives the reason; the obstruction program turns that reason into a published value, and the header sentence extends to name it. A new phase file would have to name a phase, and there is none between Sampled and AnalysisBridged. |
| the two recorded reader rejections | `instances/psl211/tableau/psl211_tableau_checks.v` | Its header: "Each entry below is one written term that the kernel rejects, recorded so that the rejection is compiled rather than described." |
| `pgl27_word_no_indistinguishability_cert_ideal_close_false` and `pgl27_word_cert_ideal_uniform` | land, in `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` | Non-vacuity is not probe bookkeeping: it is the only compiled evidence that the obstruction is a statement about the twelve-card model and not about the shape of the proposition. It belongs where `pgl27_word_cert` is built. Note that with the law anchored (D1) the statement changes shape: the PGL(2,7) certificate's ideal is its model's own cut law at distance zero, so the anchored obstruction is false there at every non-negative number, which is the same evidence and a shorter statement. |
| `var_dist_xx` | `lib/var_dist_supp.v` | The tree's support file for `var_dist` facts (`var_dist_le2` is there). It now has a user, the PGL(2,7) non-vacuity lemma, which is why the tree's earlier deletion of it no longer applies. Cost: the file is low in the build order, so landing it there rebuilds much of the tree; landing it local to the PGL(2,7) file avoids that and is acceptable as long as the name is `var_dist_xx` and not the taken `var_dist_self`. |

### What the landed comment must say about the manifest (D24)

At the published program, in the instance's phase file, and nowhere else:

- the path this program carries is honest on all five coordinates. Its level
  is `AnalysisBridged` because the manifest's own definition of that level
  admits a **limitation** theorem about the same distribution and the same
  observer as the sample, and the obstruction is one; its transfer status is
  `NegativeTransfer` because that status is defined as a theorem transporting
  an obstruction to the path's observer, and the program's own proposition is
  that theorem;
- the manifest gains no twelfth path in this batch. The manifest records
  paths and imposes its duties on paths, and no duty requires a published
  program to have one. The single coordinate that has no honest value is the
  capability line, whose closed vocabulary is correctness, exact privacy,
  approximate privacy, trace secrecy, conditional entropy, mutual information
  and endpoint marginal mixing, none of which labels a limitation. Extending
  that vocabulary is the owner's call;
- were the path recorded, it would be a twelfth path and not a second
  description of `psl211_alldecks_path`: the two agree on the observed
  execution, the level, the model family and the assumption status, and
  differ in the transfer status, and the manifest's rule is that two paths
  over one model and one pair of statuses are one path;
- the obstruction and the instance's exact-independence program are two facts
  about one model and do not conflict, for the reason D5 gives.
