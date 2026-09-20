# Adversarial soundness audit: a proposition stated at a reader, and one-seat marginal bounds

Audit of the spec `notes/20260920-readers-and-marginal-bounds-probe-design.md`
and the probe `notes/probes/2026-09-20-readers-and-marginal-bounds/`, before a
landing plan is written. No repository file was edited except this one.

Vocabulary as fixed for this audit: a Tableau value is a PROGRAM, the
manifest's record is a PATH, a program certifies a SECURITY PROPERTY with
SECURITY EVIDENCE, and the evidence proves a PROPOSITION.

## Verdict

**GO for a landing plan, with the plan's scope cut.** Every compiled claim in
the probe is true, each restatement is faithful to the theorem it cites, and
the four main files add no assumption beyond what those theorems already carry.
Nothing here is unsound.

The cut is on scope. The reader generalisation is motivated in the probe by the
eight-card content trace, and that reader is the canonical reader under a
second name: the two are pointwise equal, and the trace theorem was already
derived from the reading theorem by the very equality the probe uses to derive
the reading theorem back from it. A generalisation with one non-canonical
instance that equals the canonical one has no use.

A genuinely different reader with a proved theorem does exist, and the probe
did not look at it: the PSL(2,11) colour view, strictly coarser than the
card-identity reading, independent of the chirality at every coalition of at
most five of the twelve positions, with the sharpness at six also proved. That
is the instance a reader generalisation should be built for, and it carries one
real obstacle, the absence of a sample adapter over its model.

So: write a landing plan for the two marginal-bound propositions, their two
instances, the vacuity lemmas, and the eight-card identification of the two
readers as one lemma. Send the reader-generalised propositions back for one
more probe row at PSL(2,11) first.

## Findings

| id | class | ledger row | file:line | finding with the statement quoted and the evidence | what to change |
|---|---|---|---|---|---|
| P1 | NOTE | R2 | `manifest/pgg_tableau.v:478-486`, `notes/probes/2026-09-20-readers-and-marginal-bounds/r_framework.v:125-141` | TRUE and it is what the spec wanted. `IndistinguishabilityPropAt` is `forall (C) (x x' : ex_inputT E), (#\|C\| < profile_k (instance_profile A))%N -> var_dist (fdistmap (static_coalition_obs C x) (sa_cut_dist sa)) (fdistmap (static_coalition_obs C x') (sa_cut_dist sa)) <= c`, and `ReaderIndistinguishabilityPropAt r c` is the same term with `sr_read r C` in place of `static_coalition_obs C`. Same three binders in the same order, same threshold `#\|C\| < profile_k`, same cut law `sa_cut_dist sa`, same `var_dist`, same `<= c`. `sr_read (coalition_reading_reader E) C` reduces to `static_coalition_obs C` by iota, so `erefl` is a real conversion and not a coincidence of notation. The `cert` argument is ignored in the framework body, which is why the reader form carries no certificate. Nothing the framework states today changes. | nothing |
| P2 | NOTE | R3 | `security/pgg_collusion_bound.v:126-127`, `r_framework.v:149-174` | TRUE. `var_dist_fdistmap : var_dist (fdistmap f P) (fdistmap f Q) <= var_dist P Q` is the data processing inequality for the sum of absolute differences, so the conclusion's number is unchanged for the right reason and not by an accident of the script. The factorisation hypothesis `Hf : forall C x g, sr_read r' C x g = f C (sr_read r C x g)` is the right strength: the proof needs it at the two compared run arguments and at every cut, the `forall g` is consumed by `boolp.funext`, and the `forall C` and `forall x` match the binders the conclusion itself quantifies. | nothing |
| P3 | SHOULD | R3 | `r_framework.v:337-343` | The R3 mutation is a SCRIPT mutation, not a statement mutation. `Fail Definition postprocessing_without_factorisation` drops both `f` and `Hf` and reruns the same tactic script, which fails with `Cannot apply lemma (Order.POrderTheory.le_trans (var_dist_fdistmap _ _ _))`. A failed script does not show the statement is unprovable. The statement without `Hf` is in fact false, and a countermodel is cheap: a reader that returns a finite encoding of the run argument itself puts the two pushforwards at distance 2 while the canonical reader satisfies a small bound. | in the landing plan, either build that countermodel as a proved negative or state in the plan that R3's mutation is evidence about the proof route only |
| P4 | MUST | R4, R5, finding (1) | `instances/pgl27/pgl27_trace.v:410-423`, `instances/pgl27/pgl27_proximity.v:101-109`, `r_pgl27.v:97-106` | Finding (1) is confirmed, and it is stronger than the probe reports. `pgl27_coalition_trace C = pgl27_view R C` (`pgl27_coalition_trace_E`, an equality of random variables) and `static_coalition_obs C s g = pgl27_view R C (s, g)` (`pgl27_static_obsE`). The two readers therefore read into ONE finite type `{ffun 'I_8 -> 'I_8}` and are pointwise equal, which `pgl27_reading_of_trace` compiles with `f := id`. So `pgl27_trace_reader` is the canonical reader under a second name, and the generalisation over readers has, at this instance, one non-canonical instance that is equal to the canonical one. | do not land `StaticReader`, `ReaderIndistinguishabilityPropAt` or `ReaderExactPropAt` on the strength of this instance |
| P5 | MUST | R4, R5 | `instances/pgl27/pgl27_word_privacy.v:190-219` | The round trip. `pgl27_word_trace_indistinguishability` is proved by `by rewrite (pgl27_coalition_trace_E R C); exact: pgl27_word_view_indistinguishability.` — it IS `pgl27_word_view_indistinguishability` rewritten along the same equality the probe's R5 uses. The probe then derives the reading's proposition back from the trace theorem through R3 at `f = id`. The derived `pgl27_word_reading_indistinguishability_by_postprocessing` is therefore the upstream theorem recovered by undoing a rewrite, and the data processing step with the identity map is the trivial inequality. The ledger's flow line `derive P(canonical, 2^-39) (var_dist_fdistmap) -- 2^-39 (R3, number unchanged)` is true but prices a step that costs nothing. | say in the landing plan that the two published 2^-39 were one number in the tree before this probe, and that the trace theorem was already derived from the reading theorem |
| P6 | MUST | R6 | `manifest/pgg_tableau.v:186-194` and `450-470`, `r_framework.v:186-215` | The spec's R6 wording is wrong and the probe's is right. `ReaderExactPropAt` at the canonical reader is convertible to the `ew_indep` FIELD of the `ExactWitness` record, whose body reads `sa_sampleP sa \|= (fun u => static_coalition_obs C (sa.(sa_arg) u) (sa.(sa_cut) u)) _\|_ ew_secret`. It is NOT the independence conjunct of `ExactProp`, whose body reads `sa_sampleP sa \|= (@sa_coalition_view R (instance_profile A) (instance_exec E) sa 0 C) _\|_ (ew_secret w)`. The two differ by the link lemma of the `Sampled` level, which is exactly the hypothesis `Hview` of the probe's `reader_exact_executed`. The probe is honest; the spec's ledger row R6 ("canonical instance equals the framework's exact-independence proposition's independence conjunct") over-claims. | the landing plan must use the probe's wording, naming the link lemma as the step between the witness field and the framework's proposition |
| P7 | SHOULD | R6 | `r_framework.v:14-19` | The file header says "the framework's own propositions are their values at the canonical reader". True of `IndistinguishabilityPropAt` (P1). False of `ExactProp`, which is a four-conjunct statement about `sa_coalition_view` and is not the value of `ReaderExactPropAt` at any reader (P6). | restrict the header sentence to the input-indistinguishability proposition, and say of the exact case that the reader form is the witness's independence field and reaches the framework's proposition along the link lemma |
| P8 | NOTE | R6, finding (2) | `instances/pgl27/pgl27_trace.v:429-439` | Finding (2) is confirmed. `pgl27_coalition_trace_secrecy` is proved by `apply: (trace_secrecy_of_view (view := pgl27_view R C) ...)` with third obligation `exact: pgl27_view_indep R C HC`, so independence is upstream of the entropy equality. The probe's `pgl27_trace_exact_at_reader` takes the upstream fact `pgl27_view_indep` directly, which is correct and not a shortcut. The missing converse (conditional entropy equality to independence) is genuinely absent and is correctly recorded as a comment, not as an `Admitted`. | nothing; keep the recorded absence in whatever lands |
| P9 | NOTE | R8 | `manifest/pgg_analysis_manifest.v:2251-2257`, `r_framework.v:228-233`, `r_marginals.v:56-62` | TRUE with no change of meaning. The manifest pins `S5Analysis.exec_endpoint_bound` at `var_dist (sa_seat_dist (S5Analysis.word_sample secretP L) 0 i) (S5Analysis.ideal_reading secretP) <= Num.sqrt 5%:R * (s5_mixing.s5_alpha_R R) ^+ L`, and `SeatMarginalPropAt sa i ideal c := var_dist (sa_seat_dist sa 0 i) ideal <= c` instantiates it argument for argument, including the hard-coded round index `0`. The proof is `exact:`, with no coercion. | nothing |
| P10 | SHOULD | R8 | `instances/kim2025/tableau/five_card_tableau_sampled.v:233-238`, `r_marginals.v:68-82` | The five-card instance is cited at `< 2%:R ^- 40` and restated at `<= 2%:R^-40` through `Order.POrderTheory.ltW`. The lost strictness is not information a reader of the manifest needs at this magnitude, but the file that carries the restatement does not say the widening happened: `r_marginals.v`'s docstring says only "sits within 2^-40 of the uniform law". The LEDGER records it; the source does not. | add the widening to the statement comment of `five_card_repeated_endpoint_as_marginal` wherever it lands |
| P11 | NOTE | R8 | `r_marginals.v:93-97`, `r_framework.v:241-244` | Two definitions really are needed, and for the reason given. `SeatMarginalPropAt` compares `sa_seat_dist`, a pushforward of the SAMPLE law along the executed seat reader into the card carrier; `CutMarginalPropAt` compares `fdistmap read (sa_cut_dist sa)`, a pushforward of the CUT law along a function of the shuffle alone. Different source law and different carrier, so no substitution of arguments turns one into the other, and the `Fail Check` confirms it. | nothing |
| P12 | MUST | R9 | `r_framework.v:293-307`, precedent at `manifest/pgg_tableau_security_property_relations.v:387-396` | The two type-level refusals show only that two definitions have different types, which is true of any two definitions, and NOT that no security property follows from a marginal bound. The spec's R9 asked for a recorded type-level fact and the probe delivered exactly that, so the probe met the spec; the spec asked for too little. The statement that WOULD express "no security property follows" is a proved negative, and this repository already has the shape: `indistinguishability_prop_idealproximity_lt2_false : c < 2%:R -> ~ (IndistinguishabilityPropAt ic (cert_eps ic) -> forall cert : IdealProximityCert sa, IdealProximityPropAt cert c)`, refuted from a degenerate certificate built for the purpose. The countermodel candidate is in the tree: `manifest/pgg_analysis_manifest.v:626-627` says the S_5 encoder-image ideal "is neither uniform nor secret-independent", and `S5Analysis.ideal_reading` takes `secretP` as an argument, so a small seat-marginal number there is compatible with the reading depending on the secret. | before landing R9's claim, either prove a negative of the form `c < 2%:R -> ~ (forall ..., SeatMarginalPropAt sa i ideal 0 -> IndistinguishabilityPropAt cert c)` from a purpose-built adapter, on the model of the cited precedent, or downgrade the claim to what the refusals actually show |
| P13 | NOTE | R6 | `r_framework.v:118-124` | The docstring of `ReaderIndistinguishabilityPropAt` ends "A finer reader makes the statement stronger: the same number bounds a larger distance." The claim is true in the direction R3 proves, but "finer" is never defined in the file, and the ordering it refers to is exactly R3's factorisation hypothesis. The spec's own invariant asks that comments say which reader is finer only where R5 compiled it, and this sentence is generic. | replace "a finer reader" with the relation the file proves: a reader the other factors through |
| P14 | NOTE | R10 | `notes/probes/2026-09-20-readers-and-marginal-bounds/a1_assumptions.v`, LEDGER R10 | The axiom footprint is what the ledger reports and the main session recompiled it: the three classical assumptions on ten of twelve, plus `rigidity_s5_instance.s5_group_order_eq` on `s5_exec_endpoint_bound_as_marginal` and on its cited theorem, identically. No restatement adds an assumption. | nothing |
| P15 | MUST | R1, R4 | `instances/pgl27/pgl27_trace.v:316-319`, `r_framework.v:64-70`, `r_pgl27.v:61-64` | The record does not enforce what its statement comment claims. `StaticReader`'s comment says "What a reader omits is the interpreter state: a static reader sees the run argument and the shuffle and nothing of the messages the run exchanged, which is why a statement made at a reader is a statement about a group action." The probe's own second instance breaks that: `pgl27_trace_reader`'s reading is `fun C x g => pgl27_coalition_trace R C (x, g)`, and `pgl27_coalition_trace` is built from `pgl27_player_trace i := fun u => content_of (nth [::] (run_interp pgl27_fuel (pgl27_procs u.1 u.2)).2 (2 + i))`, which reads the interpreter's message queue. The record types a function of the run argument and the cut and nothing more; whether the body consults the run is not something the type refuses. Only `pgl27_player_trace_E` makes the reading a group action, and that is a theorem, not the record's content. | rewrite the record's statement comment to say what the type actually constrains, and name `pgl27_player_trace_E` as the fact that makes this instance a group action |
| P16 | SHOULD | R9, invariant "var_dist is twice the literature's total variation" | `r_framework.v:118-124` against `manifest/pgg_tableau.v:499-513` | The production `IdealProximityPropAt` comment carries the factor-two caveat in full ("a distinguisher's advantage is at most half of c, the sum of the absolute differences being twice the total variation distance of the literature"). The probe's `ReaderIndistinguishabilityPropAt` comment says only "within variation distance c" and never states the factor. `r_pgl27.v:70` does the halving correctly at the instance ("A distinguisher's advantage against the trace is therefore at most 2^-40" from 2^-39), so the probe is type-honest where it publishes a number and silent where it defines the proposition. | carry the factor-two sentence into whichever reader-form or marginal-form definition lands |
| P17 | NOTE | R6 (spec's item 2), manifest level | `manifest/pgg_analysis_status.v:55-61`, `manifest/pgg_analysis_manifest.v:622-632` and `890-898` | The level is CONSISTENT with the manifest's own definition of it. `AnalysisBridged` is defined as the level that "adds a theorem about that distribution and that observer" — it does not require a security theorem. The path's own level justification says `exec_endpoint_bound` "is a mixing theorem at the path's own executed observer, giving AnalysisBridged. It bounds ONE seat's endpoint marginal against the encoder-image ideal, which is neither uniform nor secret-independent; it quantifies over no coalition, mentions no second secret and has neither the shape of an indistinguishability statement nor that of a leakage statement." The header's "no endpoint marginal bound is recorded as a privacy or security capability" is about the capability slot, a different field. The row at line 590 is a four-way slot labelled "security, leakage, mixing or limitation theorem" whose value reads "endpoint marginal mixing at the executed observer", so it names which of the four and asserts no security. No contradiction to repair. | nothing in the manifest |
| P18 | MUST | R8, R9, spec's landing instruction for the S_5 phase files | `instances/s5/tableau/s5_tableau_sampled.v:18-35` | The record the spec asks a landing to add to the S_5 phase files is ALREADY THERE, and is stronger than what the spec asks for. That header says the word model "is not named at this level", that "the manifest's path over it, s5_word_path, is justified by a mixing theorem and by no program", that two of the five parts of an input-indistinguishability certificate over that model are out of reach, and that one of them is out of reach "for a reason no proof can remove: under every cut exactly one seat holds the card carrying the whole secret, so that seat's reading law moves with the secret". It closes: "What the manifest names for that path is an endpoint marginal bound against the encoder-image ideal, with no claim about a coalition." | drop the S_5 recording work item from the landing plan, or reduce it to a cross-reference from the marginal-bound definition to this header |
| P20 | MUST | R1, R2, R6, and the spec's list of readers | `instances/psl211/psl211_secrecy.v:241-244`, `307-313`, `328-331`, `instances/psl211/psl211_exec.v:126-132` | The probe looked at the wrong instance. A reader that IS genuinely different from the coalition's card-identity reading, and that has a proved exact-independence theorem today, exists: `psl211_colour_view (C : {set 'I_12}) : {RV psl211P -> {ffun 'I_12 -> bool}}`, "the colour, heart or club, of the card dealt to each position of C, and false at every position outside C. It records the colour pattern on C and no card identity." Its theorem is `psl211_colour_view_indep : (#\|C\| <= 5)%N -> psl211P \|= psl211_colour_view C _\|_ psl211_secret`, `Qed`. The threshold matches the framework's exactly: `profile_k_psl211_algebra` gives six, so `#\|C\| < profile_k` is `#\|C\| <= 5`. The sample is `psl211P := secretP \`x (\`U psl211_G_pos)`, a pair of the dealt bit and the cut, which is the shape `sr_read C x g` wants. It is strictly coarser than the canonical reading, being its image under the colour map `psl211_is_heart (c : 'I_12) : bool := (val c < 6)%N` (`instances/psl211/psl211_orbit.v:84`), a six-to-one collapse of the twelve card values onto two colours, and its theorem is NOT derivable from a canonical-reader proposition: the file header states "The all-decks code view, in which the dealt deck is redrawn uniformly over the valid decks of its class and the coalition reads card identities, is not proved here", and the tree's card-identity independence `PSL211Analysis.exact_view_indep` is at the all-decks model, a different sample. The instance also proves the sharpness, `psl211_colour_view_dep_k6 : secretP true != 0 -> secretP false != 0 -> (#\|psl211_leak_coalition\| = 6)%N /\ ~ psl211P \|= psl211_colour_view psl211_leak_coalition _\|_ psl211_secret`. | make this the motivating instance of any reader generalisation, and probe it before a landing plan fixes the framework's shape |
| P21 | SHOULD | R1, out-of-scope item 3 | `instances/psl211/psl211_secrecy.v` (no adapter), grep of `psl211P` across `instances/` | The obstacle at P20's instance, so a landing plan does not discover it late. `psl211P` occurs in no file but `psl211_secrecy.v`: the fixed-dealer colour model has NO `SampleAdapter` in the tree. `ReaderExactPropAt` is stated at an adapter, so a landing needs a new adapter over `psl211P` with sample type `bool * pgg_gT psl211_M`, `sa_arg := fst` and `sa_cut := snd`, of the same shape as the eight-card exact family's. That is construction, not restatement, and it is the row the probe should have carried instead of the eight-card trace. A second, smaller step: the generic `colour_view` of `reconstruct/design_privacy.v:122-125` reads `colour (tnth (encode u.1) (rho u.2 i))`, indexing the shuffle at `i`, while `static_coalition_obs` indexes at `tnth (pi_starts (mp_PI (instance_profile A))) i`; the eight-card instance needed `pgl27_static_obsE` to reconcile the two and the twelve-card instance will need its counterpart. The colour map itself factors cleanly, `f C v := [ffun i => if i \in C then colour (v i) else false]` discarding the coordinates outside the coalition, so R3 applies in the direction from card identity to colour with no side condition. | add it as the first row of the next probe, ahead of any framework definition |
| P22 | NOTE | R1, the spec's second and third readers | `protocol/pgg_instance.v:481-489`, `instances/kim2025/five_card_models.v:292-296` and `368-373` | The spec's other two candidate readers do not supply a use either. "One seat's content, `ex_content_obs` directly" is not a second reader: `static_coalition_obs` is DEFINED as `[ffun i => if i \in C then ex_content_obs E x (g, tnth (pi_starts ...) i) else ord0]`, so `ex_content_obs` is the field the canonical reader is built from and a singleton coalition is the canonical reader at a singleton. The five-card colour reader `five_card_exec_colour_view` IS genuinely coarser, reading `(size A).-tuple bool` at a list of positions with multiplicity rather than a coalition of seats, but its only theorem is `five_card_colour_view_leak_bound`, a `cond_mutual_info ... <= kim_leak_bound eps`, which is the leakage measure the spec puts out of scope, and its index is a `seq nat` and not a `{set seats}`, so it does not fit `StaticReader` without changing the record. | record both as checked and not usable, so the landing plan does not relitigate them |
| P24 | NOTE | R1 | `instances/denboer1989/five_card_leakage.v:69-83`, `instances/denboer1989/denboer_secrecy.v:32-33`, `instances/psl211/psl211_models.v:502-511` | Two further readers checked, neither of which changes the recommendation. The den Boer instance has a genuinely coarser reader, `ViewA (A : seq nat) : {RV P -> (size A).-tuple bool}` reading card colours off `arr`, with a proved independence theorem `denboer_indep : dbP \|= ViewA R [:: 0%N] _\|_ Secret R`, `Qed`. It does not fit `StaticReader`: it is indexed by a `seq nat` rather than a `{set seats}`, it holds at one position rather than at every coalition below a threshold, and the den Boer development builds no algebra, no execution parameters and no adapter, so the proposition cannot be stated over it without building that stack first. Separately, the twelve-card card-identity independence `psl211_alldecks_static_indep : (#\|C\| <= 5)%N -> psl211_alldecksP R \|= (fun u => static_coalition_obs C u.1 u.2) _\|_ psl211_alldecks_secret R` is at `psl211_alldecksP`, confirming that it is a different sample from the colour view's `psl211P` and that P20's claim of non-derivability holds. | none; recorded so the landing plan does not search again |
| P23 | SHOULD | R9 | `instances/s5/tableau/s5_tableau_sampled.v:27-35` | The countermodel P12 asks for is already identified in prose at the S_5 word model: one seat's reading law moves with the secret there, while `exec_endpoint_bound` gives that seat a small marginal bound. That is precisely "a marginal bound holds and no security property follows". It is an argument in a comment, not a theorem. | if R9's claim is to land as more than a type mismatch, formalize this S_5 observation, which is the cheapest countermodel in the tree, rather than building a synthetic adapter |

(There is no P19; the row that carried that id was renumbered P23 when the
PSL(2,11) rows were inserted ahead of it.)

## What is worth landing

### Land now

1. **The two marginal-bound propositions and their two instances.**
   `SeatMarginalPropAt` and `CutMarginalPropAt`, with
   `s5_exec_endpoint_bound_as_marginal` and
   `five_card_repeated_endpoint_as_marginal`. This is the part of the probe
   that pays. The tree has two published numbers that are not about any
   coalition and the Tableau has had no name for what they are; these two
   definitions give them one, they are faithful to the cited theorems argument
   for argument (P9, P11), and they add no assumption (P14). They carry no
   constructor of the evidence type, which is the spec's decision and the
   manifest's own position. Fix P10 on the way in: the statement comment of the
   five-card instance must say that the cited theorem is strict and the
   restatement widens it.

2. **The vacuity lemmas.** `seat_marginal_at_two` and `cut_marginal_at_two`.
   They are one line each and they tell a reader that a marginal bound says
   nothing at or above two, which is the honest reading of any number the
   propositions publish.

3. **The PGL(2,7) identification of the two readers, as ONE lemma.** The tree
   proves `static_coalition_obs C x g = pgl27_view R C (x, g)`
   (`pgl27_static_obsE`) and `pgl27_coalition_trace C = pgl27_view R C`
   (`pgl27_coalition_trace_E`) and never composes them. The composite, that at
   this instance a coalition's content trace and its endpoint reading are one
   finite function, is the fact that explains why two theorems of this instance
   publish 2^-39. It belongs in the eight-card analysis-bridged file as a
   corollary with a statement comment saying which two published numbers it
   identifies. One lemma, two lines, and it removes an apparent duplication
   from the published results.

### Do not land yet

4. **`StaticReader`, `ReaderIndistinguishabilityPropAt`, `ReaderExactPropAt`
   and `reader_indistinguishability_postprocessing`.** The probe's evidence for
   these is the eight-card trace reader, and that reader is the canonical
   reader under a second name (P4). A generalisation whose only non-canonical
   instance is equal to the canonical one is a framework with no use, and the
   round trip through the identity map (P5) makes the point sharper: the tree
   derived the trace theorem FROM the reading theorem by the same equality the
   probe uses to derive the reading theorem back from the trace theorem. Nothing
   is gained and a new vocabulary is spent.

   These definitions are not wrong. R2's conversion is real (P1) and the
   post-processing law is the data processing inequality correctly applied
   (P2). What is missing is a reader that makes them say something.

5. **What would earn them.** The PSL(2,11) colour view (P20). It is strictly
   coarser than the canonical reading, it is indexed by a coalition of the
   right type, its threshold is `profile_k` on the nose, its independence
   theorem is proved, and the instance even proves the sharpness at six. It is
   not derivable from any canonical-reader proposition at that model, because
   the card-identity result at the fixed dealer is exactly what the instance's
   own header says is not proved. If a reader generalisation is to exist in
   this development, that is its first customer and the eight-card trace is a
   footnote.

   The next probe should therefore run, in this order: build a sample adapter
   over `psl211P` (P21, the one real obstacle, and it is construction rather
   than restatement); state `ReaderExactPropAt` at a colour reader over it;
   discharge it with `psl211_colour_view_indep`; record `psl211_colour_view_dep_k6`
   beside it as the statement that the threshold is sharp; and only then fix
   the record's shape. Doing it in the other order fixes `StaticReader` to the
   eight-card instance's needs and then discovers that the reader with a real
   theorem does not fit.

   Ranking of the candidates, so the plan does not pick the wrong one again.
   PSL(2,11) colour is first and is the only one that fits the record's shape,
   needing one adapter. Den Boer colour is second and needs an algebra, an
   execution plug, an observed execution and an adapter before its proposition
   can even be typed (P24). Five-card colour is third and its only theorem is
   the leakage measure the spec rules out (P22). The eight-card trace is not a
   candidate (P4).

### Rewrite before anything lands

6. **P15, the record's statement comment.** `StaticReader` claims to omit the
   interpreter state and the probe's own second instance reads the interpreter's
   message queue. Whatever lands must say what the type constrains, which is a
   function of the run argument and the cut, and name the theorem that makes a
   given instance a group action.

7. **P6 and P7, the exact case.** The spec's R6 row is wrong and the probe's
   ledger is right. Any landing text must say that the reader form at the
   canonical reader is the witness's independence field, and that the framework's
   exact-independence proposition is reached from it along the link lemma of the
   `Sampled` level.

8. **P12, R9's claim.** Two `Fail Check`s show two definitions have different
   types, which is true of any two definitions. Either prove a negative on the
   model of `indistinguishability_prop_idealproximity_lt2_false`, using the S_5
   word model whose seat reading law moves with the secret (P23), or say in the
   landing text only what the refusals show.

### Not to be touched

9. **The manifest.** `s5_word_path` at `AnalysisBridged` is consistent with the
   manifest's own definition of that level, which is a theorem at the path's own
   distribution and observer and not a security claim (P17), and the S_5 phase
   file already records everything the spec wanted recorded, in stronger terms
   (P18).

## How this audit was done

Every finding above is a direct read of the cited source in this working tree.
Nothing was recompiled: another agent is landing code into
`manifest/pgg_tableau.v` through the same lock, so production `.vo` files above
it are stale and an "inconsistent assumptions" failure would say nothing about
the probe. The probe's own four main files were recompiled by the main session
before this audit, exit code 0.

A retrieval agent was run in parallel to inventory the tree's observation
functions. Its three substantive claims were re-verified here against the
source before being used: `psl211_colour_view` and its two theorems,
`five_card_exec_colour_view` and its single leakage theorem, and the den Boer
`ViewA` with `denboer_indep`. The P24 row records the two it added.

Mechanical checks run over the probe directory: no `Admitted`, no `Axiom`, no
`Hypothesis` in the four main files; the only `Variable`s are section
parameters.
