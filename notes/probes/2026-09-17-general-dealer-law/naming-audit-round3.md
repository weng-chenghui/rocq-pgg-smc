# C10 naming and style audit, round 3 (final)

Date: 2026-09-18

Independent read-only audit of the probe directory as it stands after the round-2
fixes. VERDICT of this round: GO. Rounds 1 and 2 are `naming-audit.md` and
`naming-audit-round2.md` in this directory; their line numbers do not hold
against the current files.

Nothing was edited, nothing was compiled, no Rocq process was started. All
word-boundary scans were run in Python with `\b`, per STATUS.md's measurement
that this machine's `grep -E` silently matches nothing for `[[:<:]]`/`[[:>:]]`.

Scope: the seven `.v` files in `_CoqProject`, now 79 declarations, 1511 lines.

---

## 1. The round-2 blocking item and the three adjudications

### R2-B014 — RESOLVED

`dealer_kernel_probe.v:66` is now `dealer_shuffle_view_indep` and `:86` is
`dealer_shuffle_view_indep_of_deck`. A Python `\b` scan for `dealer_view_indep`
across all seven `.v` files returns **zero** hits. The only two occurrences left
in the directory are `STATUS.md:107-108`, which are the *Old* column of the
rename table and are supposed to hold the superseded spelling.

The stem is now a declared reader in every case, matching the four repository
precedents the finding rested on (`colour_view` → `colour_view_indep_laws`,
`psl211_alldecks_view` → `psl211_alldecks_view_indep`, `pgl27_view` →
`pgl27_view_indep`, `alldecks_view` → `ttrans_view_indep_alldecks`). The file's
internal contradiction is gone: the control at `:127` and the theorem it controls
now share the stem. Round-1 B003 is fully closed with it — no identifier anywhere
in the probe now reads as the dealer party's own view.

Call sites confirmed updated: `dealer_kernel_probe.v` 8 + 3, and
`pgl27_deterministic_bridge.v` 2 + 3, `psl211_alldecks_bridge.v` 2,
`psl211_per_deck_law_counter.v` 2 + 3.

### R2-C007 — RESOLVED, with one word left elsewhere

`pgl27_deterministic_bridge.v` now declares `Local Notation shuffleT` at `:29`
and `:285`, and measures **shuffleT 28, shuffle 5, cut 0**. The file agrees with
its own instance (`pgl27_secrecy.v` 7 shuffle / 0 cut, `pgl27_orbit.v` 20 / 0)
and with the generic home (`transitivity_privacy.v` 25 / 0).

One residue, NOTE only: `concrete_instances.v:30`, inside the comment of the PGL
wrapper `pgl27_view_indep_at_R`, still says "a view of the **cut** deck". The
other two "cut" occurrences in that file (`:67-68`) are in the PSL wrapper and
are correct. One word, one line.

### R2-E008 — RESOLVED

`pgl27_alldecks_dealer_view_law` is now the single general per-deck law at
`pgl27_deterministic_bridge.v:126-165`, inside Section `PGLDeterministic`, and
`pgl27_dealer_view_law` at `:171-180` is

```coq
move=> HC; rewrite /pgl27_dealer_nu.
exact: (@pgl27_alldecks_dealer_view_law C s (orbit_encode s) Hdt HC
  (orbit_encode_deck s)).
```

exactly the derivation round 2 proposed, using `orbit_encode_deck s` for the
validity premise. The 35 duplicated lines are gone and the counting is done once.

NOTE, not a defect: now that the general law serves both rows and lives in the
deterministic section, the `alldecks` component of its name no longer
discriminates — it reads as "the law for all decks", which is true but is not
what the name meant when the lemma belonged to the all-decks row.
`pgl27_dealer_anydeck_view_law` would be unambiguous. Non-blocking; the current
name is not wrong, only less sharp than it was.

### The mutation adjudication — RESOLVED, and better than asked

Round 2 asked for a positive control. What landed is stronger: the premises of
`pgl27_alldecks_dealer_view_law` are now coalition size first, validity last
(`:128`, `(#|C| <= 3)%N -> uniq d ->`), so dropping validity leaves an arrow
instead of shifting an argument. Control and mutation sit in a dedicated
`Section PGLDeckLawMutation` (`:253-279`) and differ by exactly the final
`Huniq`: `:267` ends `... Hdt HC Huniq`, `:277` ends `... Hdt HC`. The recaptured
error in the STATUS.md table is `has type "uniq d -> fdistmap ... = ..." while it
is expected to have type "fdistmap ... = ..."` — a leftover arrow.

My round-2 objection is fully answered. All seven mutations now fail on a
leftover arrow or a non-convertible `erefl`, neither of which a vacuous premise
can produce.

Deleting the uncompiled sentence about a repeated-card deck is the right call,
and STATUS.md's replacement framing — validity is shown needed for typing, not
for truth — is the accurate one. The stronger claim is correctly carried to the
implementation plan (STATUS.md:587-589).

**But one paragraph of STATUS.md was not updated with it.** See R3-S001 below.

---

## 2. The five new declarations

### Collisions — clean

Re-ran the scan over **582 files** (the nine repository trees plus the installed
`infotheo` and `mathcomp`) for all 79 probe declarations: **zero** hits. The
seven names added or renamed since round 2 were also checked individually:
`psl211_dealer_valid_forced`, `psl211_dealer_view_indep_of_deck_unsat`,
`psl211_fixed_deal_delta`, `psl211_fixed_dealP`, `psl211_fixed_deal_view_dep`,
`pgl27_alldecks_dealer_secretE`, `pgl27_alldecks_dealer_view_law_with_validity`,
plus `dealer_shuffle_view_indep` and `dealer_shuffle_view_indep_of_deck` — all
zero.

### `psl211_fixed_deal_view_dep` — ACCEPTED, and my prior lean was wrong

You asked whether this should follow a repo precedent for non-independence. It
already follows the best one there is. `instances/pgl27/pgl27_profile_privacy.v:224`
declares

```coq
Lemma constant_deck_view_dep :
  ~ pgl27P R |= coalition_view ... [set ord0] _|_ dealt_secret ...
```

with the comment "under constant_deck_profile a single position already has a
view depending on the dealt secret". That is the same statement shape (`~ ... |=
... _|_ ...`), the same situation (a degenerate deck-laying rule breaking
privacy), in the same instance family, under the same `_view_dep` suffix. The
probe's name is the PSL(2,11) sibling of it.

I had been ready to push the repository's `no_` family here
(`s5_no_secret_dim3`, `s5_no_secret_dim4` in `reconstruct/s5_nogo.v`,
`partial_sum_no_info`, `perm_module_no_dim23`, `no_walk`). The precedent refutes
that: `no_` is used for "this quantity does not exist / carries nothing",
`_view_dep` for "this independence fails". Keep `_view_dep`.

### `psl211_fixed_dealP` and `psl211_fixed_deal_delta` — CONFORM to B002

B002's rule is that a law is `<stem>P` and everything hanging off it is
`<stem>_...`. Checking every law/kernel pair in the probe:

| Law | Stem | Kernel |
|---|---|---|
| `pgl27_dealerP` | `pgl27_dealer` | `pgl27_dealer_delta` |
| `pgl27_alldecks_dealerP` | `pgl27_alldecks_dealer` | `pgl27_alldecks_dealer_delta` |
| `psl211_dealerP` | `psl211_dealer` | `psl211_dealer_delta` |
| `psl211_fixed_dealP` | `psl211_fixed_deal` | `psl211_fixed_deal_delta` |

The fourth row is the same shape as the first three. It has no readers of its own
because `psl211_fixed_deal_view_dep` applies the generic `dealer_shuffle_view`
and `dealer_shuffle_secret` at this kernel, so there is nothing that could
violate the reader half of the rule. Conforms.

One thing worth noticing and accepting: `psl211_fixed_dealP` parses as "the fixed
deal law", not "the fixed-deal dealer law". The dealer component is dropped
where the other three keep it. Since the stem must also carry `_delta`, adding it
back would give `psl211_fixed_deal_dealerP` / `psl211_fixed_deal_dealer_delta`,
which is worse to read. The short form is the better trade. NOTE only.

### `_unsat` — ACCEPTED, and it should not be replaced by `no_`

You asked whether `_unsat` is decodable or should be spelled out. Two facts.

It has no precedent: zero `_unsat` names in the repository, in `infotheo` or in
`mathcomp`, and it is SAT-solver vocabulary rather than MathComp vocabulary. On
its face that argues for spelling it out.

But it is carrying a distinction that the obvious replacement would destroy.
`psl211_dealer_view_indep_of_deck_unsat` does **not** say that PSL privacy fails
— `psl211_alldecks_view_indep_via_dealer` proves PSL privacy. It says that *the
premises of one route* have no common solution. Renaming it into the `no_`
family, as `psl211_dealer_no_view_indep_of_deck`, would assert the negation of
the conclusion, which is false. So `_unsat` is the discriminating word and the
repo's negative-result family is the wrong one to join here.

Its own statement comment decodes it in the first sentence: "the two premises of
`dealer_shuffle_view_indep_of_deck` have no common solution, for every validity
predicate and every candidate reading law" (`psl211_per_deck_law_counter.v:143-145`).
A reader who does not know the suffix learns it before the statement. Keep it.

Related: I checked whether the four negation spellings now in that one file are a
one-word-per-concept violation, and they are not. `_neq` (two lemmas) is for
genuine `!=` statements and has three repo precedents; `no_common_law` is for
"no such object exists"; `_unsat` is for "these premises are jointly
unsatisfiable"; `_view_dep` is for "this independence fails". Four spellings for
four different statement shapes is discrimination, not drift.

### `psl211_dealer_valid_forced` — ACCEPTED

The stem `psl211_dealer_valid` is not a declaration, and `valid` is a bound
predicate argument rather than a constant, which is the one thing that gave me
pause after B014. It is a different situation: B014's `dealer_view` was a name
that had been a declaration and had been renamed away, leaving a stem that also
misread against another namespace. Here `valid` is the role word the repository
already uses for this argument (`deck_ok`, and the `valid` binder of
`dealer_shuffle_view_indep_of_deck` itself at `dealer_kernel_probe.v:87`), and
nothing else in the project claims the name. Fine.

### The five statement comments — all pass, and one is exemplary

Fact plus position in every case. Specifically:

- `:127-132` names what it stops: "This is what stops the per-deck route from
  being repaired by a narrower notion of validity." That is the position, and it
  answers the obvious objection to the refutation before it is raised.
- `:143-148` states the fact, then the position: "the average over deal
  descriptions that `dealer_shuffle_view_indep` asks for is the only route that
  remains."
- `:164-167` says why the degenerate kernel is named at all: "so that the general
  model can be asked whether it claims privacy for it."
- `:178-186` is the strongest comment in the probe. It gives the fact, the domain
  position ("this is what entitles the paper to say that privacy is a property of
  the dealer law and not of the protocol alone: the shuffle group, the design and
  the coalition are the ones PSL(2,11) uses, only the dealer changed"), the
  reading against its sibling theorem, and then the scope limit: "What is NOT
  shown here is that a hidden uniform deal leaks: the deal is public in this
  refutation, being a point mass." A domain expert reading only that comment can
  tell exactly what has and has not been established. This is the standard the
  rest of the development should be held to.

A scan of all 79 `(** ... *)` blocks for status markers, effort estimates, "key
lemma" meta, proof strategy and measurements returns **zero** hits.

### Vocabulary in the new material

"chirality" is used throughout and "class" does not appear — clean.
"reading" is used throughout and "view" does not appear in prose — clean.

One residue, NOTE: the object `psl211_deal` is called "deal description" six
times across `psl211_alldecks_bridge.v` and `psl211_per_deck_law_counter.v`,
"deal" twenty-four times, and **"deck description" twice** in
`psl211_per_deck_counter.v` (`:128`, `:234`). The new file is internally
consistent; the residue is the round-2 C005 finding, unchanged. `psl211_per_deck_law_counter.v:127`
also uses both spellings in one sentence ("every deal description positive mass,
so ... cannot exclude any deal"), which is harmless but is the same pattern.

---

## 3. Hygiene, re-verified cold

| Check | Result |
|---|---|
| Declarations | 79, all seven files |
| Statement comments | 79 of 79 present; zero missing |
| Forbidden content in `(** *)` | zero |
| Collisions, 582 files | zero |
| Residual round-1 / round-2 identifiers | zero |
| Banned vocabulary (`\b`, Python) | zero |
| Lines over 80 characters | zero |
| Lone `by [].` lines | zero |
| `Admitted` / `Abort` / `Axiom` / `Time` / `Timeout` / `Show` | zero |
| `Print Assumptions` inside a `Section` | zero |
| `Local Opaque` / `Local Transparent` | four seals, all paired (`psl211_alldecks_bridge.v:29/313`, `psl211_per_deck_counter.v:204/258`, `psl211_per_deck_law_counter.v:27,33/251`) |

I also verified the F001 fact independently rather than taking it on trust.
`reconstruct/transitivity_privacy.v:788-795` states

```coq
fdistmap (fun dg => alldecks_view C (s, dg))
  ((`U (card_class_decks_gt0 s)) `x ((`U card_G_gt0) : R.-fdist gT)) = ...
```

The pushforward is of the **product of the deck law and the shuffle law**, which
is C2's mixed-law premise shape, not C3's per-deck shape `fdistmap (fun g =>
view C s d g) (`U G) = mu` at a fixed deck. The prover's finding is correct:
`alldecks_view_law` cannot discharge the premise the probe's C6 route needs, so
dropping `Local` would not have enabled the reuse round 1 asked for. F001 changes
character — it is no longer a production edit, it is a design-note row that names
the wrong object. That belongs with F006 in the note, which is the user's.

---

## 4. What blocks C10, and what is implementation-plan only

### Blocking: none.

### Non-blocking, should be fixed before the implementation plan is written

**R3-S001 — a stale paragraph in STATUS.md contradicts its own table.** The final
three lines of §Mutations still read: "`pgl27_alldecks_dealer_view_law_without_validity`
is the one mutation whose error is an argument-position mismatch rather than a
leftover arrow. That is still the intended reason, since the coalition-size
argument only lands in the `uniq d` slot because `uniq d` was dropped." The
premise reorder made that false, and the table three rows above it now shows the
leftover-arrow error. A reader of STATUS.md would conclude the probe's mutation
evidence is weaker than it is. Delete the paragraph; the "Three positive
controls" paragraph above it already covers the mutation correctly.

**R2-D006 — still open.** None of `pgl27_view_indep_via_dealer` (`:214`),
`pgl27_view_indep_alldecks_via_dealer` (`:330`) or
`psl211_alldecks_view_indep_via_dealer` (`psl211_alldecks_bridge.v:288`) names
the existing theorem whose statement it restates verbatim. One clause each, on
the model of `instances/pgl27/pgl27_profile_privacy.v:79-82`.

**Minor, one line each.** `concrete_instances.v:30` "cut deck" in a PGL comment.
"deck description" at `psl211_per_deck_counter.v:128,234`. The clause "Validity
is the last premise so that dropping it leaves an arrow rather than shifting an
argument" at `pgl27_deterministic_bridge.v:124-125` is apparatus rationale inside
a statement comment; it belongs in the `(* *)` note at `:269-273`, where it
already effectively is. `psl211_per_deck_law_counter.v` prose mixes "cut" (2) and
"shuffle" (6) while its notation is `cutT`. The `alldecks` component of
`pgl27_alldecks_dealer_view_law` no longer discriminates.

### Implementation-plan items, and whether STATUS.md specifies them precisely

STATUS.md:336-347 now tabulates all ten generic declarations with name, one-line
statement and proposed home. Judging each against your criterion:

| Item | Precise enough? |
|---|---|
| `dealer_shuffleP`, `dealer_shufflePE`, the two readers, the two independence theorems → `reconstruct/transitivity_privacy.v` | **Yes.** Name, statement and home for all six |
| `inde_RV_fdistmap` → `transitivity_privacy.v` (Alt-2) | **Yes.** Row 344 |
| `uniform_fdistmap_fiberTE` → `design_privacy.v` (Alt-1) | **Yes.** Row 346 |
| `uniform_fdistmap_pointE` → `design_privacy.v` (R2-A009) | **Yes**, and better than asked: `:349-351` adds that it should land first and that `uniform_fdistmap_fiberE` should be re-proved through it, naming the internal `have key` |
| `fdistmap_prod_sectionE` → `design_privacy.v` | **Yes**, with a NOTE: round 1 proposed `transitivity_privacy.v` beside `fdistmap_prod_const`, its own family. Splitting the family is defensible but is a change of plan; say which file wins and why, so the implementation does not rediscover the question |
| The four `Arguments` directives (R2-E009) | **Yes.** `:583-586`, with the target shape and the reference at `pgl27_secrecy.v:216-219` |
| Proving validity is needed for truth, not only for typing | **Yes.** `:587-589`, correctly scoped and honestly labelled as not attempted |
| Restating C6's ledger row (supersedes F001/Alt-8) | **Yes.** `:590` plus §"C6: which route, and what it reuses". The design-note half is the user's |

Two disclosures STATUS.md now makes that no reviewer asked for, and that I would
have had to raise otherwise: §"Two premises that are never exercised" (`:357-362`)
records that the `secretP s != 0` guard of C2 and C3 is never non-trivially
tested, since all three instances use `fdist_uniform card_bool`; and §"What
validity is shown to do, and what it is not" separates the typing claim from the
truth claim. Both are the right kind of self-report.

### Owned elsewhere

The design-note rows F002, F003 (remainder), F004, F006 and F008; the production
vocabulary behind C002; and the file names still containing "bridge" and
"counter", which STATUS.md:120-122 reports rather than changes.

---

## VERDICT: GO

C10 reads: "Proposed public identifiers do not collide and match project and
MathComp conventions. Evidence: repository search plus an independent naming
audit with compiled alternatives for every objection."

On collisions: 79 declarations checked with word-boundary matching against 582
files across the nine repository trees, `infotheo` and `mathcomp` — zero. The
three statements that round 1 found restated verbatim under new names now carry
`_via_dealer`, which is repository precedent, so no statement is offered twice as
if it were new.

On conventions: every naming objection raised across three rounds is closed. The
law-and-reader rule holds for all four dealer laws in the probe; the instance
prefixes are `pgl27_` and `psl211_` without exception; the `E`, `P`, `PE`, `_of_`,
`_neq`, `no_`, `_via_` and `_view_dep` suffixes are each used for the statement
shape the repository uses them for, with the one unprecedented suffix, `_unsat`,
carrying a distinction its alternatives would destroy and decoded in the first
sentence of its own comment. Every one of the 79 declarations has a statement
comment giving the fact and its position, with no status, strategy or measurement
content anywhere in them.

On the evidence clause: every objection I raised that could be closed inside the
probe has been applied and compiled, including round 2's single blocking item.
The objections that can only be closed by editing a production file are carried
with name, statement and home stated precisely for all ten generic declarations,
which meets the bar set for an implementation-plan item.

Nothing blocks C10. The seven items in §4 are worth an hour before the
implementation plan is written, and the first of them — the stale STATUS.md
paragraph — should be fixed regardless, because it understates evidence the probe
actually has.
