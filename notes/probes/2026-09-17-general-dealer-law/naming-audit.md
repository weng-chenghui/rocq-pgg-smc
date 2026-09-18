# C10 naming and style audit, round 1

Date: 2026-09-18

Independent read-only audit at HEAD c9634fd. VERDICT of this round: NO-GO.
Line numbers refer to the probe files before the C9 milestones and the rename
pass.

---

Read-only. No file was edited, nothing was compiled, no Rocq process was
started. All evidence is `grep`/`awk`/`Read` over the working tree at HEAD
`c9634fd`; the design note is tracked and unmodified since commit `9f54a3a`,
the probe directory is untracked.

Files audited (all under
`/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/notes/probes/2026-09-17-general-dealer-law/`):
`dealer_kernel_probe.v`, `carrier_transport_probe.v`,
`pgl27_deterministic_bridge.v`, `psl211_alldecks_bridge.v`,
`psl211_per_deck_counter.v`.

Design note:
`/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/notes/20260917-general-dealer-law-feasibility-design.md`.

---

## Summary table

| ID | Sev | file:line | Rule | Evidence | Pasteable alternative |
|---|---|---|---|---|---|
| N001 | PASS | — | C10 literal half | Zero hits for all 11 identifiers across `lib protocol groups security smc reconstruct instances manifest legacy` and `_opam/.../user-contrib/{infotheo,mathcomp}` | none needed |
| A001 | BLOCKING | `psl211_alldecks_bridge.v:127` | no duplicate lemma | `uniform_fdistmap_sectionsT` IS `uniform_fdistmap_fiberE` (`reconstruct/design_privacy.v:51`) at `A := [set: D]`; its own proof line 138 is `apply: uniform_fdistmap_fiberE` | §Alt-1 `uniform_fdistmap_fiberTE` in `design_privacy.v` |
| A002 | BLOCKING | `pgl27_deterministic_bridge.v:50,61`; `carrier_transport_probe.v:23`; `psl211_alldecks_bridge.v:58` | one fact, one lemma | 4 declarations of one fact; lines 55-59 and 66-70 are byte-identical proof scripts of converse statements | §Alt-2 one iff `inde_RV_fdistmap` |
| A003 | BLOCKING | `pgl27_deterministic_bridge.v:318-325` | same statement, another name | verbatim `pgl27_view_indep_alldecks`, `instances/pgl27/pgl27_secrecy.v:215-219` | §Alt-4 `pgl27_view_indep_alldecks_via_dealer` |
| A004 | BLOCKING | `psl211_alldecks_bridge.v:264-268` | same statement, another name | verbatim `psl211_alldecks_view_indep`, `instances/psl211/psl211_models.v:427-430` | §Alt-4 `psl211_alldecks_view_indep_via_dealer` |
| A005 | BLOCKING | `pgl27_deterministic_bridge.v:208-209` | same statement, another name | verbatim `pgl27_view_indep_via_profile`, `instances/pgl27/pgl27_profile_privacy.v:82-83`; equals `pgl27_view_indep` (`pgl27_secrecy.v:82-83`) modulo section form | §Alt-4 `pgl27_view_indep_via_dealer` |
| A006 | SHOULD-FIX | design note:88 / `dealer_kernel_probe.v:27` | one word per concept | `dealer_secret := fun u => u.1` re-words `dealt_secret` (`transitivity_privacy.v:499`, same body, used in 6 files) | §Alt-3 `dealer_shuffle_secret` |
| A007 | PASS | `carrier_transport_probe.v:23` | not in infotheo | `probability/proba.v` has only `inde_RV_comp:2399` and `Pr_fdistmap:440`; no fdistmap pullback of independence | — |
| A008 | PASS | `psl211_alldecks_bridge.v:85` | not a special case | `fdistmap_prod_const:216` / `_snd_const:241` conclude a **constant** law; this concludes an equality of two pushforwards with a law varying in `g` | — |
| B001 | PASS (precedent CONFIRMED) | — | `P` = law on a `Definition` | `pgl27P` (`pgl27_secrecy.v:66`), `alldecksP` (`transitivity_privacy.v:771`), `psl211P:230`, `psl211_alldecksP:138`, `uniform_deckP:883`, `s5_rand_sampleP`, `pgl27_word_sampleP`; reflection `P` only on `Lemma`s (`inde_rv_cprP`, `stype_eqP`, `prescribedP`) | keep `dealer_shuffleP` |
| B002 | BLOCKING | `dealer_kernel_probe.v:27,30` | reader prefix = law name minus `P` | `alldecksP`→`alldecks_secret:777`/`alldecks_view:782`; `psl211_alldecksP`→`psl211_alldecks_secret:145`/`_view:678`; `pgl27P`→`pgl27_secret:71`/`pgl27_view:75`; `uniform_deckP`→`uniform_deck_view:890` | §Alt-3 `dealer_shuffle_secret`, `dealer_shuffle_view` |
| B003 | SHOULD-FIX | `dealer_kernel_probe.v:30` | no misreadable name | `protocol/` owns a `dealer_*` **party** namespace: `dealer_idx` (`card_exchange_pismc.v:132`), `exchange_dealer:221`, `dealer_with_input_encoding` (`pgg_run.v:45`), `dealer_hand_env:185`. `dealer_view` reads as the dealer party's view; it is the coalition's reading | fixed by §Alt-3 |
| B004 | NOTE | note:99; `pgl27_deterministic_bridge.v:254`; `psl211_alldecks_bridge.v:171` | one `E` spelling | `^Lemma .*PE` has zero repo hits, but the rule is mechanical (`fdist_prodE`, `fdistmapE`); repo has 250 names in `E` vs 12 in `_E` (incl. `psl211_alldecks_sampleP_E`). Probe uses three spellings: `dealer_shufflePE`, `pgl_all_dealerP_E`, `psl_law_E` | keep `PE`; rename `pgl_all_dealerP_E`→`pgl27_alldecks_dealerPE`, `psl_law_E`→`psl211_dealerPE` |
| B005 | SHOULD-FIX | `pgl27_deterministic_bridge.v:81-…`; `psl211_*:*` | project instance prefixes | every instance declaration uses `pgl27_`/`psl211_` (`pgl27_secret`, `psl211_alldecks_view`, …). `pgl_`/`psl_`/`psl_counter_` drop the group parameter | §Alt-5 full rename table |
| B006 | SHOULD-FIX | `pgl27:118,124`; `psl211:192,199` | `E` for an equation, not a diagram word | `_square` is a commuting-diagram metaphor; the statements are equations | `pgl27_dealer_viewE`, `pgl27_dealer_secretE`, `psl211_dealer_viewE`, `psl211_dealer_secretE` |
| B007 | SHOULD-FIX | `pgl27:113,181,208,318`; `psl211:188,247,264` | no development words | "generic" describes the development, not the mathematics. `_via_` IS repo precedent (`pgl27_view_indep_via_profile`, `word_view_indist_via_transfer`) — objection is to `generic`, not to `via` | replace `generic`→`dealer` throughout; see §Alt-4/5 |
| B008 | SHOULD-FIX (offer both) | `psl211_per_deck_counter.v:100-101` | `P` = reflect/view, `E` = boolean identity | conclusion is `(raw_view sq t == counter_view) = test sq t`, a bool equality | (a) rename `psl211_counter_testE`; **or** (b) restate `reflect (psl_counter_raw_view sq t = psl_counter_view) (psl_counter_test sq t)` and keep `P` |
| B009 | NOTE | `psl211_per_deck_counter.v:233` | no verbs in names | `psl_per_deck_fibers_differ`; the statement is `#|…| != #|…|` | `psl211_per_deck_fiber_card_neq` |
| B010 | NOTE | `psl211_per_deck_counter.v:30-233` | one word per concept | `counter` is ambiguous between counterexample and counting; the same file has `psl_counter_raw_count:119` | `psl211_perdeck_*` (or `psl211_witness_*`) |
| B011 | NOTE | `psl211_alldecks_bridge.v:85` | `E` for the equality concluded | joins the `fdistmap_prod_const` family | `fdistmap_prod_sectionE` |
| B012 | NOTE | `psl211_alldecks_bridge.v:76` | no ad-hoc `_eq` suffix | subsumed by A002: with the iff, the use site rewrites, as `pgl27_deterministic_bridge.v:222` already does | drop, or `inde_RV_fdistmap_pullback_of` |
| B013 | PASS | proofs throughout | hypothesis names | `Htrue/Hfalse/Heq/H1/H0/Ht/Hf` break no stated project rule; local and readable | — |
| C000 | PASS | all five files | banned vocabulary | the banned-vocabulary scan returns nothing; `cap` as a noun for a bound absent. Independently confirms STATUS.md | — |
| C001 | SHOULD-FIX | `psl211_alldecks_bridge.v:85` vs `:127` | one word per concept | "sections" names sections at 85-91 (`fun d => f d g`) and **fibers** at 127-131 (`[set d \| f d == v]`); its own comment at 121-123 says "fibers" twice | `uniform_fdistmap_fiberTE` (§Alt-1) |
| C002 | SHOULD-FIX | `psl211_per_deck_counter.v:29,41,50,118,123,125` vs `:124,228` | one word per concept | the same `b : bool` is "class" 6× and "chirality" 2×; lines 125 and 229 are the same sentence with different words. `psl211_models.v:421` says "chirality" | pick **chirality** file-wide |
| C003 | SHOULD-FIX | `psl211_alldecks_bridge.v:72` vs `:75`; `psl211_per_deck_counter.v:26,36,84,91,98,126,156,229` | one word per concept | "reading" and "view" alternate inside one comment block (72 vs 75). Both are established repo prose (`pgl27_rows.v:182`, `s5_exec.v:462`, `design_privacy.v:248`), so either is allowed — one per file | pick **reading** in PSL files, **view** in the generic file, never both |
| C004 | SHOULD-FIX | note:44; `dealer_kernel_probe.v:21`; `psl211_per_deck_counter.v:26,85,117,131` vs `psl211_alldecks_bridge.v:125,219` | generic home's word | the type is `cutT`, the public name is `dealer_shuffleP`, the prose says both. `reconstruct/transitivity_privacy.v` = 38 "shuffle", 0 "cut"; `psl211_models.v` = 15 "cut", 2 "shuffle" | rename the generic carrier `cutT`→`shuffleT`; keep `cutT` inside `psl211_*` only |
| C005 | NOTE | `psl211_per_deck_counter.v:125` vs `:126`; `:228` vs `:231`; `psl211_alldecks_bridge.v:220` vs `:221` | one word per concept | "deck description" and "deal" name `psl211_deal` in adjacent sentences | pick **deal** (matches the carrier `psl211_deal`) |
| C006 | NOTE | `pgl27:28-70`; `psl211:35-83` | no metaphor prefixes | `bridge_*`, `psl_bridge_*` carry no mathematics | never promote; see A002 |
| D001 | BLOCKING | `dealer_kernel_probe.v` (0 comments, 6 decls); `carrier_transport_probe.v` (0, 1); `pgl27_deterministic_bridge.v` (0, 25) | every declaration carries a statement comment | **all seven proposed public identifiers are uncommented**: `:23,27,30,35,40,53` and `carrier_transport_probe.v:23`. Also `fdistmap_prod_sections:85` and `bridge_pushforward:61`. 9 of the 11 C10 identifiers have no statement comment | §Alt-3 (writes them) |
| D002 | NOTE (rule PASS) | `psl211_alldecks_bridge.v:18-25` | measurements out of statement comments | this is a `(* *)` source comment justifying the `Local Opaque` at line 26, **not** a statement comment, so the rule permits the rationale. Two caveats: the raw timing log was not retained (STATUS.md: diagnostics "live in the session scratchpad"), and STATUS.md already carries the same 30 s / 0.01 s figures | drop the numerals from the `.v`, keep the reason; cite STATUS.md |
| D003 | PASS | `psl211_per_deck_counter.v:66-69,163-165,186-187,191-192,236-238`; `psl211_alldecks_bridge.v:133-134` | in-proof rationale allowed | each is inside a proof and states why a tactic is chosen and what the alternative does wrong | keep |
| D004 | SHOULD-FIX | `psl211_alldecks_bridge.v:69-75` | fact + domain position | the comment states development rationale (why equations rather than composites), not the mathematical fact and its place in the privacy argument | rewrite: fact = independence is invariant under a reindexing of the sample space; position = the PSL carrier reassociation is such a reindexing |
| D005 | PASS | `psl211_alldecks_bridge.v:121-126,219-223`; all 19 of `psl211_per_deck_counter.v` | exemplars | `psl_section_law`'s "it is the only place where the instance's laid deck enters the bridge" is exactly the position sentence; `psl211_per_deck_counter.v` has 19 `(**` for 19 declarations | use as the template |
| E001 | BLOCKING | `carrier_transport_probe.v:8`; `dealer_kernel_probe.v:9`; `psl211_per_deck_counter.v:10`; `psl211_alldecks_bridge.v:11`; `pgl27_deterministic_bridge.v:14` | repo header convention | all five keep `Import Prenex Implicits.` and drop `Set Implicit Arguments.` / `Unset Strict Implicit.`. 122 of 127 permanent `.v` files have all three; infotheo always pairs them (`ecc_modern/ldpc_algo.v:23-25`); `transitivity_privacy.v:69-71`. Consequence: discharged section variables are **explicit** in the probe and would become **implicit** in a permanent home, so every proposed statement and every mutation was elaborated in a regime the permanent file will not have | §Alt-6: add the three lines to all five files and recompile |
| E002 | BLOCKING | `dealer_kernel_probe.v:80,84`; `carrier_transport_probe.v:41`; `pgl27:229,310`; `psl211:114,209` | "each mutation must fail for the intended reason" (note:256) | `grep -B2 '^Fail '` shows **no comment above any of the seven mutations**. Per-mutation reading verdict below | §Alt-7 (comments + positive controls) |
| E003 | NOTE | `carrier_transport_probe.v:29`; `psl211:66`; `pgl27:58,69,178,307` | `by` closes the sentence | six lone `by [].` lines | fold into the preceding `rewrite`: `by rewrite -!dist_of_RVE /dist_of_RV !fdistmap_comp.` |
| E004 | NOTE | `psl211_alldecks_bridge.v:26`; `psl211_per_deck_counter.v:199` | `Local Opaque` pairing | neither seal is lifted; `Opaque`/`Transparent` are not section-scoped, so in a permanent file the seal governs every later declaration | add `Local Transparent psl211_alldecks_view.` (and `psl211_elem_table`) after the last step that needs the seal |
| E005 | NOTE | `pgl27_deterministic_bridge.v:234-236` (End at 238), `:359-360` (End at 362) vs `dealer_kernel_probe.v:92-94`, `carrier_transport_probe.v:48` | one placement | the pgl27 `Print Assumptions` run **inside** their sections, so they report the section-local constant, not the discharged one | move all after the enclosing `End` |
| E006 | PASS | all five files | line length, bullets, ssreflect vocabulary | `awk 'length>80'` returns nothing (confirms STATUS.md independently); bullets `-`/`+` consistent; no `pose proof`, `assert`, `f_equal`, or bare `auto`; `have`/`exact:`/`apply:`/`under eq_bigr` used idiomatically | — |
| E007 | SHOULD-FIX | `psl211_alldecks_bridge.v:87-89` | match the target file's discipline | premise quantifies over **all** `g`; both siblings in the target file restrict to positive mass (`fdistmap_prod_const` `:217` `forall a, P a != 0 ->`; `_snd_const` `:243`) | `(forall g, PG g != 0 -> fdistmap (fun d => f d g) PD = fdistmap (fun d => h d g) PD)` |
| E008 | NOTE | `pgl27_deterministic_bridge.v:137-179` and `:268-308` | no duplicated proof | the same 40-line script with `orbit_encode s` replaced by `d`; the second subsumes the first at `d := orbit_encode s` with `uniq` from `orbit_encode_deck` | keep `pgl_deck_view_law` only; derive the fixed-deck case |
| F001 | BLOCKING | note:181,194,156 vs `reconstruct/transitivity_privacy.v:788` | note cites a reachable object | `alldecks_view_law` is declared **`Local Lemma`**, so no other file can name it. C6's evidence line ("reuse of `alldecks_view_law`") is unsatisfiable as written, and `pgl27_deterministic_bridge.v:268-308` re-proves the counting — which note:156-157 forbade | drop `Local` at `transitivity_privacy.v:788` |
| F002 | SHOULD-FIX | note:238 | note names a file that exists | `pgl27_alldecks_bridge.v` does not exist; C6 is `pgl27_deterministic_bridge.v` Section `PGLAllDecks` (240-362) | edit note:238 |
| F003 | SHOULD-FIX | note:240,241,244 | ditto | `concrete_instances.v`, `headline_decomposition.v`, `soundness-audit.md`, `naming-audit.md` do not exist | edit note; add `STATUS.md`, which exists and is not listed |
| F004 | SHOULD-FIX | note:239 | artifact list complete | note folds C8 into `psl211_alldecks_bridge.v`; C8 is a sixth file, `psl211_per_deck_counter.v` | add as item 6 |
| F005 | BLOCKING (scope) | note:80-129 | C10 audits the full public set | four generic objects the note's "Proposed generic declarations" never mentions: `fdistmap_prod_sections:85`, `uniform_fdistmap_sectionsT:127`, `psl_bridge_pullback_eq:76`, `bridge_pushforward` (pgl27:61). The ledger row audits a smaller set than the probe produced | widen note §"Proposed generic declarations" before re-running C10 |
| F006 | SHOULD-FIX | note:181 | note matches the file | note says C6 derives `ttrans_view_indep_alldecks` (generic in `N', t, gT`); the file proves the PGL(2,7) **instantiation**, verbatim `pgl27_view_indep_alldecks` | edit note:181 to name `pgl27_view_indep_alldecks` |
| F007 | NOTE | note:182 | ditto | C7 satisfied in substance; only the name objects (A004) | — |
| F008 | NOTE | note:243 vs STATUS.md "How to rerun one file" | ditto | note lists `Makefile.rocq` "for the project build"; STATUS.md says "Do not run `make` here" and gives a bare `rocq compile` recipe | edit note:243 |
| F009 | NOTE | note:144-149 vs `carrier_transport_probe.v:17-23` | note quotes the compiled spelling | note writes the carriers as lemma binders; the file declares them as Section Variables, so the compiled constant is `R A B TA TB P f X Y`, all explicit (E001) | align after §Alt-6 |

**Caveat on the task brief's item F.** I could not evidence the quoted C8
respelling. The design note on disk (tracked, unmodified since `9f54a3a`)
contains no C8 code at all: its C8 row (line 183) says only "Either a compiled
per-deck theorem or a compiled concrete counterexample", and
`grep -rn 'inord 0; inord 1; inord 2' notes/` returns nothing. So the note does
not contradict `psl211_per_deck_counter.v:33-34,38-39`; it simply never
recorded a spelling. I am not reporting a drift I cannot see.

---

## Per-mutation reading verdict (E002)

| Mutation | file:line | Intended reason | From reading alone |
|---|---|---|---|
| `dealer_shuffleP_missing_cut` | `dealer_kernel_probe.v:80` | ascribed `R.-fdist (secretT*(deckT*cutT))` vs `secretP \`X delta : R.-fdist (secretT*deckT)` | plausible, low risk |
| `dealer_view_indep_without_common_law` | `:84` | unapplied mixed-law premise | plausible, **but** 23 explicit arguments across three `@`-applications; an arity or order slip yields the same error class. Needs a positive control |
| `inde_RV_fdistmap_bad_reader` | `carrier_transport_probe.v:41` | `Ybad : A -> TB` will not unify with `Y \o f` | plausible, low risk |
| `pgl_bad_view_square` | `pgl27:229` | `erefl` on the negated secret | **best of the seven** — positively controlled by `pgl_view_square:118-122`, proved `by []` with the identical spelling |
| `pgl_deck_view_law_without_validity` | `pgl27:310` | `HC : (#\|C\| <= 3)%N` supplied in the `uniq d` slot | plausible, low risk |
| `fdistmap_prod_sections_without_sections` | `psl211:114` | missing section-equality premise | **HIGH RISK of an unrelated error.** The application `fdistmap_prod_sections PD PG f h` omits the lemma's own `(D G V : finType)` binders, which are **explicit** in this file because `Set Implicit Arguments` is absent (E001). The elaborator would then place `PD : R0.-fdist D` in `D : finType`'s slot and fail on an argument type, not on the missing premise. From reading alone this mutation may certify nothing. Confidence: medium-high — it must be decided by compiling §Alt-7c |
| `psl_bad_secret_square` | `psl211:209` | `erefl` on the negated first coordinate | positively controlled by `psl_secret_square:199-203` (`by []`). Intended |

---

## Compiled alternatives

### Alt-1 — replaces `uniform_fdistmap_sectionsT` (A001, C001). Append to `reconstruct/design_privacy.v`, after `End fibers.`

```coq
Section fibersT.
Variables (R : realType) (X : finType) (HT : (0 < #|[set: X]|)%N).
Variable T : finType.

(** uniform_fdistmap_fiberTE — the whole-type case of uniform_fdistmap_fiberE:
    two maps out of a finite type whose fibers over every value are
    equinumerous push the uniform law on that type to the same law.  This is
    the comprehension shape a per-cut count of the deals producing one reading
    takes, so a design instance's counting certificate becomes an equality of
    the two secrets' reading laws without first rewriting its set shapes. *)
Lemma uniform_fdistmap_fiberTE (f0 f1 : X -> T) :
  (forall v, #|[set x : X | f0 x == v]| = #|[set x : X | f1 x == v]|) ->
  fdistmap f0 ((`U HT) : R.-fdist X) = fdistmap f1 (`U HT).
Proof.
have Hfull : forall (k : X -> T) (w : T),
    [set x in [set: X] | k x == w] = [set x : X | k x == w].
  by move=> k w; apply/setP => x; rewrite !inE.
move=> Hfib; apply: uniform_fdistmap_fiberE => v.
rewrite (Hfull f0 v) (Hfull f1 v); exact: Hfib v.
Qed.

End fibersT.
```

### Alt-2 — replaces `inde_RV_fdistmap_pullback`, `bridge_pullback`, `bridge_pushforward`, `psl_bridge_pullback` (A002). Append to `reconstruct/transitivity_privacy.v`

```coq
Section inde_RV_reindex.
Variables (R : realType) (A B TA TB : finType).
Variables (P : R.-fdist A) (f : A -> B) (X : B -> TA) (Y : B -> TB).

(** inde_RV_fdistmap — two readers of a pushforward law are independent
    exactly when the readers composed with the reindexing are independent
    under the original law.  A privacy statement is therefore a property of
    the sample it reads and not of the product association the model happens
    to be written in, which is what lets one dealer law serve instances whose
    carriers associate the secret, the deck and the shuffle differently. *)
Lemma inde_RV_fdistmap :
  fdistmap f P |= X _|_ Y <-> P |= (X \o f) _|_ (Y \o f).
Proof.
by split => H x y; move: (H x y);
   rewrite -!dist_of_RVE /dist_of_RV !fdistmap_comp.
Qed.

End inde_RV_reindex.
```

`psl_bridge_pullback_eq`'s use site (`psl211_alldecks_bridge.v:272-281`) then
becomes what `pgl27_deterministic_bridge.v:222` already does:

```coq
by rewrite -(psl_view_square C) -psl_secret_square; apply/inde_RV_fdistmap.
```

### Alt-3 — replaces `dealer_kernel_probe.v:23-33` (A006, B002, B003, C004, D001)

```coq
(** dealer_shuffleP — the joint law of a secret, the deck the dealer deals for
    that secret, and an independent shuffle.  The paper's dealer model, with
    the protocol's quantifier order fixed in the kernel: average over secrets
    under secretP, then conditional on the secret over decks under delta, then
    independently over shuffles under nu.  Information-theoretic and exact:
    no computational premise enters the equality of laws. *)
Definition dealer_shuffleP :
    R.-fdist (secretT * (deckT * shuffleT)) :=
  secretP `X (fun s => (delta s) `x nu).

(** dealer_shuffle_secret — the secret coordinate of a dealer sample.  The
    quantity every privacy claim in this development asks a coalition's
    reading to be independent of; the generic counterpart of dealt_secret,
    which reads the same coordinate of the single-deck product law. *)
Definition dealer_shuffle_secret : {RV dealer_shuffleP -> secretT} :=
  fun u => u.1.

(** dealer_shuffle_view view — what an observer reading a dealer sample
    through view sees.  The reader is an argument rather than a fixed
    coalition observable so that one law serves each instance's own reading,
    and it is given the secret as well as the deck and the shuffle because an
    instance may write its reading in terms of the secret it was dealt. *)
Definition dealer_shuffle_view
    (view : secretT -> deckT -> shuffleT -> viewT) :
    {RV dealer_shuffleP -> viewT} :=
  fun u => view u.1 u.2.1 u.2.2.
```

with `Variable nu : R.-fdist shuffleT.` at line 21 and `shuffleT` replacing
`cutT` in the `Variables` line 18. `dealer_view_indep` /
`dealer_view_indep_of_deck` keep their names (B001 and the `_of_` suffix are
both sanctioned) and gain statement comments; every occurrence of
`dealer_view`/`dealer_secret` in their statements becomes
`dealer_shuffle_view`/`dealer_shuffle_secret`.

### Alt-4 — the three verbatim duplicates (A003, A004, A005, B007)

Either replace the existing proofs, or keep both routes under the repo's own
`_via_` convention, whose comment shape is already set by
`pgl27_profile_privacy.v:79-82`:

```coq
(** pgl27_view_indep_via_dealer — the eight-card deterministic row through the
    general dealer law.  The statement is pgl27_view_indep verbatim; only the
    route differs, so the general law costs the instance nothing. *)
Lemma pgl27_view_indep_via_dealer (C : {set 'I_8}) :
  (#|C| <= 3)%N -> pgl27P R |= pgl27_view R C _|_ pgl27_secret R.
```

```coq
Lemma pgl27_view_indep_alldecks_via_dealer (C : {set 'I_8}) : ...
Lemma psl211_alldecks_view_indep_via_dealer (C : {set seatT}) : ...
```

### Alt-5 — instance prefix repair (B005, B006, B007, B009, B010)

`pgl27_deterministic_bridge.v`: `pgl_delta`→`pgl27_dealer_delta`,
`pgl_nu`→`pgl27_dealer_nu`, `pgl_dealerP`→`pgl27_dealerP`,
`pgl_embed`→`pgl27_dealer_embed`, `pgl_dealerP_map`→`pgl27_dealerPE`,
`pgl_generic_view`→`pgl27_dealer_view`, `pgl_view_square`→`pgl27_dealer_viewE`,
`pgl_secret_square`→`pgl27_dealer_secretE`, `pgl_common_mu`→`pgl27_dealer_mu`,
`pgl_fixed_view_law`→`pgl27_dealer_view_law` (E008: keep only the deck form),
`pgl_generic_indep`→`pgl27_dealer_view_indep`,
`pgl_indep_via_generic`→`pgl27_view_indep_via_dealer`,
`pgl_bad_embed`→`pgl27_dealer_bad_embed`,
`pgl_all_delta`→`pgl27_alldecks_dealer_delta`,
`pgl_all_dealerP`→`pgl27_alldecks_dealerP`,
`pgl_all_dealerP_E`→`pgl27_alldecks_dealerPE`,
`pgl_all_viewE`→`pgl27_alldecks_dealer_viewE`,
`pgl_deck_view_law`→`pgl27_alldecks_dealer_view_law`,
`pgl_all_indep_via_generic`→`pgl27_view_indep_alldecks_via_dealer`.

`psl211_alldecks_bridge.v`: `psl_deal_pos`→`psl211_deal_pos`,
`psl_delta`→`psl211_dealer_delta`, `psl_nu`→`psl211_dealer_nu`,
`psl_genericP`→`psl211_dealerP`, `psl_assoc`→`psl211_dealer_assoc`,
`psl_law_E`→`psl211_dealerPE`, `psl_generic_view`→`psl211_dealer_view`,
`psl_view_square`→`psl211_dealer_viewE`,
`psl_secret_square`→`psl211_dealer_secretE`,
`psl_bad_assoc`→`psl211_dealer_bad_assoc`,
`psl_mixed_law`→`psl211_dealer_mixed_law`,
`psl_mixed_lawE`→`psl211_dealer_mixed_lawE`,
`psl_section_law`→`psl211_dealer_sectionE`,
`psl_generic_indep`→`psl211_dealer_view_indep`,
`psl_indep_via_generic`→`psl211_alldecks_view_indep_via_dealer`.

`psl211_per_deck_counter.v`: `psl_counter_*`→`psl211_perdeck_*`
(`psl211_perdeck_deal`, `_coalition`, `_view`, `_seq`, `_row_size`,
`_corow_size`, `_seqE`, `_raw_view`, `_test`, `_testE` (B008a), `_raw_count`,
`_raw_countE`, `_ptbl_nth`, `_raw_viewE`, `_ptbl_enum`, `_fiber`, `_fiberE`),
`psl_entry_perm_enum`→`psl211_entry_perm_enum`,
`psl_per_deck_fibers_differ`→`psl211_perdeck_fiber_card_neq`.

All 12 candidate names I checked (`dealer_shuffle_secret`,
`dealer_shuffle_view`, `psl211_ptbl_nth`, `psl211_dealerP`, `pgl27_dealerP`,
`pgl27_dealer_view`, `psl211_dealer_view`, `inde_RV_fdistmap`,
`uniform_fdistmap_fiberTE`, `fdistmap_prod_sectionE`, `psl211_counter_testE`,
`pgl27_alldecks_dealerP`) return **zero** hits across the repo — the
alternatives do not themselves collide.

### Alt-6 — header repair, all five files (E001)

Replace the bare `Import Prenex Implicits.` with the repo's three lines,
exactly as `reconstruct/transitivity_privacy.v:69-71`:

```coq
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
```

This changes the elaboration of every `@`-application in
`pgl27_deterministic_bridge.v` and `psl211_alldecks_bridge.v` and of every
`Fail` mutation. **Recompiling under this header is the single most important
compiled check C10 needs**, because until it runs, none of the proposed
statements has been elaborated in the regime its permanent home will have.

### Alt-7 — mutation repair (E002)

(a) `dealer_kernel_probe.v`, after line 78:

```coq
Variable Hmix : forall s, secretP s != 0 ->
  fdistmap (fun dg => view s dg.1 dg.2) ((delta s) `x nu) = fdist1 x.

(* Positive control: the same explicit spelling with the mixed-law premise
   supplied must elaborate, so the Fail below isolates the missing premise
   and not an argument order or arity slip. *)
Definition dealer_view_indep_with_common_law :
  @dealer_shuffleP R secretT deckT cutT secretP delta nu
  |= @dealer_view R secretT deckT cutT viewT secretP delta nu view
     _|_ @dealer_secret R secretT deckT cutT secretP delta nu :=
  dealer_view_indep (view := view) (mu := fdist1 x) Hmix.

(* Expected failure: without Hmix the term still carries an unapplied
   hypothesis, so its type is a function type where an independence claim
   is expected. *)
```

(b) `dealer_kernel_probe.v:79`, above the first mutation:

```coq
(* Expected failure: secretP `X delta has type R.-fdist (secretT * deckT),
   which does not match the ascribed R.-fdist (secretT * (deckT * cutT)). *)
```

(c) `psl211_alldecks_bridge.v:113`, the high-risk one — positive control plus
an `@`-spelling that is robust under either implicit regime:

```coq
(* Positive control: with the section premise the term is well typed under
   this file's implicit-argument regime, so the Fail below isolates the
   missing premise and not an argument type. *)
Definition fdistmap_prod_sections_control
    (D G V : finType) (PD : R0.-fdist D) (PG : R0.-fdist G)
    (f h : D -> G -> V)
    (Hs : forall g, fdistmap (fun d => f d g) PD =
                    fdistmap (fun d => h d g) PD) :
  fdistmap (fun dg => f dg.1 dg.2) (PD `x PG) =
  fdistmap (fun dg => h dg.1 dg.2) (PD `x PG) :=
  @fdistmap_prod_sections D G V PD PG f h Hs.

(* Expected failure: the section-equality premise is absent, so the term has
   type (forall g, _ = _) -> _ where an equality of pushforwards is
   expected. *)
Fail Definition fdistmap_prod_sections_without_sections
    (D G V : finType) (PD : R0.-fdist D) (PG : R0.-fdist G)
    (f h : D -> G -> V) :
  fdistmap (fun dg => f dg.1 dg.2) (PD `x PG) =
  fdistmap (fun dg => h dg.1 dg.2) (PD `x PG) :=
  @fdistmap_prod_sections D G V PD PG f h.
```

(d) one-line expected-reason comments above `carrier_transport_probe.v:41`,
`pgl27:229`, `pgl27:310`, `psl211:209`.

### Alt-8 — `reconstruct/transitivity_privacy.v:788` (F001)

```coq
Lemma alldecks_view_law (C : {set 'I_N'.+1}) (s : bool)
```

(drop `Local`), so C6's evidence line becomes satisfiable and
`pgl27_deterministic_bridge.v:268-308` can stop re-proving the counting.

---

## VERDICT: NO-GO

C10 fails on both halves as it stands.

On "do not collide": the exact-name half passes cleanly (N001). The
same-statement half does not. Three of the probe's headline lemmas are
character-for-character restatements of theorems the repository already proves
(A003, A004, A005), one generic lemma is an existing generic lemma specialized
(A001), and one fact is declared four times (A002).

On "match project and MathComp conventions": `dealer_secret` and `dealer_view`
break the repo's own law-to-reader prefix rule, which holds without exception
across four law/reader families (B002), and `dealer_view` additionally
misreads against the `dealer_*` party namespace `protocol/` already owns
(B003). The `P`-suffix precedent the brief asked me to test is **confirmed**,
not refuted (B001), and `_via_` turned out to be repo precedent too (B007) —
those two objections I expected to raise, I withdraw.

On the evidence clause ("compiled alternatives for every objection"): nothing
has been compiled, and E001 means nothing *can* be compiled honestly until the
header regime is fixed, because the probe elaborated every proposed statement
with `Set Implicit Arguments` off while 122 of 127 permanent files have it on.

### Objections that need a compiled alternative before C10 can be GO

1. **Alt-6 first** (E001) — the three-line header on all five files,
   recompiled. Everything below is measured in the wrong regime until this
   lands.
2. **Alt-7c** (E002, `fdistmap_prod_sections_without_sections`) — this
   mutation may currently certify nothing; the control must compile and the
   `Fail` must still fail.
3. **Alt-7a** (E002, `dealer_view_indep_without_common_law`) — control must
   compile.
4. **Alt-1** (A001, C001) — `uniform_fdistmap_fiberTE` in `design_privacy.v`,
   with `psl211_dealer_sectionE` re-proved through it.
5. **Alt-2** (A002) — the single iff `inde_RV_fdistmap`, with all four copies
   deleted and both bridges re-proved through it.
6. **Alt-3** (A006, B002, B003, C004, D001) — the renamed and commented public
   block, with `shuffleT` for `cutT`.
7. **Alt-4** (A003, A004, A005, B007) — the three `_via_dealer` names, or a
   decision to replace the existing proofs instead.
8. **Alt-8** (F001) — dropping `Local` from `alldecks_view_law`, without which
   C6's evidence line cannot be met and E008's duplicated 40-line proof cannot
   be removed.

Alt-5 (the prefix table), E003, E004, E005, E007, C002-C005, D004 and the
F-series note edits are SHOULD-FIX or NOTE: they do not need a compiled
alternative to be judged, but Alt-5 and E007 do need a compile to be *landed*.
