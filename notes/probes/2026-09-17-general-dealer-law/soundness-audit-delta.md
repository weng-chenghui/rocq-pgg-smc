# General dealer law probe: independent soundness audit, delta round

Date: 2026-09-18

Independent audit; delta round, against the files as of the two-audit fix pass.
This document audits only what changed since `soundness-audit.md`. The auditor
wrote none of the probe files. Files changed since the first round:
`dealer_kernel_probe.v`, `pgl27_deterministic_bridge.v`,
`psl211_alldecks_bridge.v`, `psl211_per_deck_law_counter.v` and `STATUS.md`.
`carrier_transport_probe.v`, `psl211_per_deck_counter.v` and
`concrete_instances.v` are byte-identical to the versions audited in round one.

Every compile below was run by the auditor from the probe directory with the
single-file command in STATUS.md, one Rocq process at a time, with `-o`
directing output into a session scratch directory. No `.vo` in the probe
directory and no production file was rebuilt or touched. `make` was not run.
No checksum or inconsistent-assumptions error appeared. Nothing ran long enough
to need killing; the longest single compile was 27.5 s.

## Findings

| id | severity | file:line | claim | evidence |
|---|---|---|---|---|
| G1 | SHOULD-FIX | `psl211_per_deck_law_counter.v:146-148` | The comment on `psl211_dealer_view_indep_of_deck_unsat` ends "the average over deal descriptions that `dealer_shuffle_view_indep` asks for is the only route that remains". Two overreaches. `dealer_shuffle_view_indep` does not ask for an average over deal descriptions; it asks for a common mixed view law, a condition on `delta` that the uniform deal law meets and that other laws could also meet. And "the only route that remains" is not proved: the probe states two sufficient conditions and shows one of them unsatisfiable, which is not the same as showing there is no third. Weaker wording in D3. | D3, plus the compiled premise shapes in D1. |
| G2 | SHOULD-FIX | `psl211_per_deck_law_counter.v:183-185`, and the same sentence in `STATUS.md:319-320` | "Read together with `psl211_alldecks_view_indep_via_dealer` it says that for PSL(2,11) privacy is a property of the uniform average over deal descriptions." What the pair shows is that privacy depends on which deal law the dealer uses: the uniform one delivers it, and one point-mass law does not. Necessity of the uniform law is not shown, and the refutation is at one deal description, not at all of them. Weaker wording in D3. | D2, D3. |
| G3 | NOTE | `psl211_per_deck_law_counter.v:164-169`, `:180-182` | The refuting dealer is secret-INDEPENDENT, `fun _ => fdist1 psl211_perdeck_deal`, unlike pgl27's `fun s => fdist1 (orbit_encode s)`. The refutation works because at a fixed deal description the two chiralities still lay different decks, through the class table inside `psl211_alldecks_view`. The comment's "only the dealer changed" is correct but silent on this, and a reader may infer that a secret-independent dealer makes the laid deck secret-independent. | `audit_deck_depends_on_chirality` compiled, D2. |
| G4 | NOTE | paper-level, not a file | "Deterministic dealer: private at PGL(2,7), not private at PSL(2,11)" is fair as a report of the two compiled facts, but it must not be offered as the explanation. The explanatory variable is the transitivity degree, and the repository already carries both facts: `instances/pgl27/pgl27_group.v:303` proves `pgl27_3transitive` and `instances/psl211/psl211_group.v:321` proves `psl211_2transitive`, with no 3-transitivity stated anywhere for PSL(2,11). | Repository grep, D2. |
| G5 | NOTE | `STATUS.md:503-505` | "no proof sentence exceeds 0.7 s" for `psl211_per_deck_law_counter.v`. Measured with `rocq compile -time`, the tightest true bound is 0.055 s for a proof sentence and 0.138 s for a `Print Assumptions`; 0.702 s belongs to a third `Require Import` line. True but loose enough to read as if a proof sentence approached 0.7 s. | D6. |
| G6 | NOTE | `STATUS.md:486`, `:506` | "A fourth hang shape" is placed before "A third hang shape". Ordering slip only; both sections are accurate. | Section headings. |

No BLOCKING finding.

### Round-one findings, current state

| round-one id | state |
|---|---|
| F1 validity mutation | RESOLVED. It is now a leftover-arrow test with a declared control. See D5. |
| F2 C6 evidence and in-probe duplication | RESOLVED, and more than asked: the auditor compiled the C2 route, so STATUS.md's two-route account is now checked in both legs. See D4. |
| F3 the C3 step carried in prose | RESOLVED by three new lemmas. Machine-checked in D1. |
| F5 missing secret-reader equation | RESOLVED. `pgl27_alldecks_dealer_secretE` at `pgl27_deterministic_bridge.v:323`, used at `:370`. |
| F6 unnamed implicit mutation controls | RESOLVED in STATUS.md, which now names them and explains which two need none. |
| F8 unproved claims in a statement comment | RESOLVED. The injectivity and support sentences are gone from `pgl27_dealer_embed`'s comment. |
| F9 generic surface larger than proposed | RESOLVED in STATUS.md, which tabulates all ten with proposed homes. Verified: each of the ten is defined in a probe file, and the three extras are still absent from the production tree. |
| F4 untested `secretP s != 0` guard | OPEN by design, now documented in STATUS.md under "Two premises that are never exercised". |
| F7 design-note artifact list | OPEN. Not in the changed set. STATUS.md's own "Carried to the implementation plan" keeps the C6 ledger row as an item. |
| F10 `make -n` claim | OPEN in the same sense: `make` is still forbidden here, and the static equivalent still holds. |

## Recompiles and assumption reports

All seven files, exit 0. Wall time and peak resident set from `/usr/bin/time -l`:

| file | exit | wall | peak RSS | STATUS.md |
|---|---|---|---|---|
| `dealer_kernel_probe.v` | 0 | 3.69 s | 1.643 GB | 4 s, 1.65 GB |
| `carrier_transport_probe.v` | 0 | 3.59 s | 1.619 GB | 3 s, 1.62 GB |
| `pgl27_deterministic_bridge.v` | 0 | 4.63 s | 1.692 GB | 5 s, 1.69 GB |
| `psl211_alldecks_bridge.v` | 0 | 5.29 s | 1.742 GB | 6 s, 1.74 GB |
| `psl211_per_deck_counter.v` | 0 | 27.50 s | 1.849 GB | 27 s, 1.85 GB |
| `psl211_per_deck_law_counter.v` | 0 | 4.89 s | 1.730 GB | 5 s, 1.73 GB |
| `concrete_instances.v` | 0 | 5.27 s | 1.776 GB | 5 s, 1.78 GB |

The table matches within rounding. `psl211_per_deck_law_counter.v` at 4.89 s
and 1.730 GB confirms the near-hang is gone; it stood at 4.76 s and 1.702 GB
before the three new lemmas were added, so the three lemmas cost about 0.1 s.

Assumption reports. `Print Assumptions` block counts against the number of
commands per file: 3/3, 1/1, 8/8, 7/7, 0/8, 7/7, 4/4.
`psl211_per_deck_counter.v` printed `Closed under the global context` eight
times. Every block of the five abstract-R files, including all seven of
`psl211_per_deck_law_counter.v`, is verbatim and identical:

```text
Axioms:
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

So the three new lemmas, `psl211_dealer_valid_forced`,
`psl211_dealer_view_indep_of_deck_unsat` and `psl211_fixed_deal_view_dep`, each
report the three `boolp` axioms and nothing else, as D2 requires.
`concrete_instances.v` still reports exactly the seven-entry real-number list.

The two renamed files were checked to have changed in name only: `diff` against
`history/*.2026-09-18-before-m8.v` shows, for `dealer_kernel_probe.v`, only
`dealer_view_indep` becoming `dealer_shuffle_view_indep` and
`dealer_view_indep_of_deck` becoming `dealer_shuffle_view_indep_of_deck` in the
two `Lemma` heads, one `apply:`, two `Print Assumptions` and the comments; and
for `psl211_alldecks_bridge.v`, one `apply:` and one comment line. No statement
and no proof changed.

## D1 The unsat lemma is about C3

Two hypotheses were written in the unsat lemma's own spelling and fed to the
generic lemma. Both definitions elaborated:

```coq
Hypothesis H1 : forall (b : bool) (d : psl211_deal),
  psl211_dealer_delta R b d != 0 -> valid b d.
Hypothesis H2 : forall (b : bool) (d : psl211_deal),
  (fdist_uniform card_bool : R.-fdist bool) b != 0 -> valid b d ->
  fdistmap (psl211_dealer_view psl211_perdeck_coalition b d)
    (psl211_dealer_nu R) = mu.

Definition audit_unsat_premises_are_c3 : <C3's conclusion at the PSL data> :=
  @dealer_shuffle_view_indep_of_deck R bool psl211_deal (pgg_gT psl211_M)
    {ffun 'I_12 -> 'I_12} (fdist_uniform card_bool)
    (@psl211_dealer_delta R) (@psl211_dealer_nu R) valid
    (psl211_dealer_view psl211_perdeck_coalition) mu H1 H2.

Definition audit_unsat_gives_false : False :=
  @psl211_dealer_view_indep_of_deck_unsat R valid mu H1 H2.
```

The first accepts H1 and H2 in C3's two premise slots, so they are C3's
premises at `(fdist_uniform card_bool, psl211_dealer_delta, psl211_dealer_nu,
psl211_dealer_view psl211_perdeck_coalition)` and not something adjacent. The
second consumes the same two and returns `False`. So
`psl211_dealer_view_indep_of_deck_unsat` says exactly "C3 cannot be applied to
PSL(2,11) under its own dealer law", for every validity predicate and every
candidate law. D1 passes.

`psl211_dealer_valid_forced` is the reason it holds for every validity
predicate: the uniform deal law gives every description positive mass, so C3's
first premise cannot exclude the counterexample deal. That lemma's own proof is
two lines and reports the three `boolp` axioms.

## D2 The fixed-deal refutation

### It negates C2's conclusion at a genuine dealer kernel

Compiled by the auditor:

```coq
Definition audit_fixed_is_c2_conclusion (mu) (Hmix : <C2's premise here>) :
  psl211_fixed_dealP R |=
    @dealer_shuffle_view R bool psl211_deal (pgg_gT psl211_M)
      ({ffun 'I_12 -> 'I_12}) (fdist_uniform card_bool)
      (@psl211_fixed_deal_delta R) (`U psl211_G_pos)
      (psl211_dealer_view psl211_perdeck_coalition)
  _|_ @dealer_shuffle_secret R bool psl211_deal (pgg_gT psl211_M)
      (fdist_uniform card_bool) (@psl211_fixed_deal_delta R)
      (`U psl211_G_pos) :=
  @dealer_shuffle_view_indep R bool psl211_deal (pgg_gT psl211_M)
    ({ffun 'I_12 -> 'I_12}) (fdist_uniform card_bool)
    (@psl211_fixed_deal_delta R) (`U psl211_G_pos)
    (psl211_dealer_view psl211_perdeck_coalition) mu Hmix.
```

The ascribed type is the body that `psl211_fixed_deal_view_dep` negates,
character for character, and the term is `dealer_shuffle_view_indep` applied at
the fixed-deal kernel. So the negated statement is C2's conclusion with nothing
altered. A corollary follows in one line and was compiled:

```coq
Definition audit_fixed_no_mixed_law (mu) (Hmix : <C2's premise>) : False :=
  @psl211_fixed_deal_view_dep R (@audit_fixed_is_c2_conclusion mu Hmix).
```

No candidate law satisfies C2's premise at that kernel either. Reported with
the three `boolp` axioms.

### The refutation is non-degenerate

- Both secrets carry positive mass. The prior is `fdist_uniform card_bool`;
  `audit_prior_both_positive` compiles `(fdist_uniform card_bool : R.-fdist
  bool) b != 0` for every `b`, which is also what the probe's own proof uses
  through `card_bool`.
- The coalition is three of the twelve seats, under the privacy threshold of
  five. `audit_coalition_card : #|psl211_perdeck_coalition| = 3` compiles and
  reports `Closed under the global context`.
- The shuffle law is the production one and is shared with the private model.
  `audit_fixed_nu_is_production : @psl211_dealer_nu R = (`U psl211_G_pos) :=
  erefl` compiles, and `psl211_fixed_dealP` is `dealer_shuffleP (fdist_uniform
  card_bool) psl211_fixed_deal_delta (`U psl211_G_pos)` against
  `psl211_dealerP`'s `dealer_shuffleP (fdist_uniform card_bool)
  psl211_dealer_delta psl211_dealer_nu`. The two differ in the `delta`
  argument and in nothing else.
- The view is the production one. `psl211_dealer_view C b d g` is
  `psl211_alldecks_view C (b, d) g` by definition, the same reading
  `psl211_alldecks_view_indep` is stated about.

### The deck still depends on the chirality

`psl211_fixed_deal_delta` ignores its secret argument, so the DEAL DESCRIPTION
is constant. The laid deck is not. Compiled:

```coq
Lemma audit_deck_depends_on_chirality :
  psl211_alldecks_seq (true, psl211_perdeck_deal)
  != psl211_alldecks_seq (false, psl211_perdeck_deal).
Proof. by rewrite !psl211_perdeck_seqE; vm_compute. Qed.
```

reported `Closed under the global context`. The dependence runs through
`psl211_alldecks_row`, which reads `psl211_class_tbl x.1`, a different Steiner
table per chirality. So this dealer is the PSL analogue of pgl27's
`fdist1 (orbit_encode s)` in the sense that matters, namely that the laid deck
is a deterministic function of the secret with no randomness of its own. It is
not the analogue in the sense that the kernel depends on the secret: pgl27's
does, this one does not. That asymmetry makes the PSL result the stronger of
the two, and finding G3 asks for one clause saying so.

### Is "deterministic dealer: private at PGL(2,7), not private at PSL(2,11)" fair?

As a report of the two compiled facts, yes:
`pgl27_view_indep_via_dealer` is privacy at `#|C| <= 3` of eight positions
under a dealer whose laid deck is a function of the secret, and
`psl211_fixed_deal_view_dep` is its failure at a three-seat coalition of twelve
under a dealer whose laid deck is also a function of the secret. The coalition
sizes are the same, both are under their instance's threshold, and both are
stated at every `realType`.

As an explanation, no, and the sentence should not be offered as one. Nothing
compiled says the determinism causes the difference. The repository states what
does: `pgl27_3transitive` at `instances/pgl27/pgl27_group.v:303` and
`psl211_2transitive` at `instances/psl211/psl211_group.v:321`, with no
3-transitivity claimed for PSL(2,11) anywhere. A three-position reading is
covered uniformly from any repetition-free deck when the group is 3-transitive,
which is what `ktuple_encode_uniform` turns into the per-deck law for pgl27; at
PSL(2,11) that step is unavailable. The fiber sizes 0 and 1 are consistent with
this, since the group has order 660 and 12 · 11 · 10 = 1320, so the ordered
triples of seats fall into two orbits on each of which the group is sharply
transitive. That last remark is an observation, not something the repository
proves, and the paper should cite the two transitivity lemmas rather than the
arithmetic.

### The proof matches its comment

Read line by line. The comment says the true fiber is empty and the false
fiber has one element, and that is exactly the proof's structure.

- `Hcard0` and `Hcard1` pin the two cardinalities to 0 and 1 in term mode from
  `psl211_perdeck_fiberE` and `psl211_perdeck_raw_countE`, then `Hemp` turns
  the first into `psl211_perdeck_fiber true = set0`.
- The joint at `(psl211_perdeck_view, true)` is shown to vanish by `big1` over
  the event. For a sample `(b, (d, g))` in it: off the fixed deal the point
  mass gives 0 by `fdist10`; off the group the uniform shuffle gives 0 by
  `fdist_uniform_supp_notin`; and on both, the sample's shuffle would lie in
  `psl211_perdeck_fiber b` with `b = true`, which `Hemp` empties. So the empty
  true fiber is what kills the joint.
- The two marginals are then shown nonzero by `pfwd1_neq0` with explicit
  witnesses. The view marginal at `psl211_perdeck_view` uses
  `(false, (psl211_perdeck_deal, g0))` with `g0` drawn from the false fiber by
  `card_gt0P` on `Hcard1`, so the non-empty false fiber is what keeps it alive.
  The secret marginal at `true` uses `(true, (psl211_perdeck_deal, g0))`, alive
  because the prior is uniform on `bool`.
- `Hmass` supplies positivity of both witnesses and splits the two positivity
  goals rather than leaving `#|pgg_G psl211_M|` to a trailing `//`, which is
  the discipline STATUS.md's third hang-shape section records.

The comment and the proof agree, and `Print Assumptions` gives the three
`boolp` axioms.

## D3 The paper-level sentences in the new comments

Sentence by sentence.

`psl211_dealer_valid_forced`, lines 127-132. "The all-decks dealer gives every
deal description positive mass, so the first premise of
`dealer_shuffle_view_indep_of_deck` cannot exclude any deal: a validity
predicate satisfying it accepts `psl211_perdeck_deal` at both chiralities."
BACKED by the lemma itself. "This is what stops the per-deck route from being
repaired by a narrower notion of validity." BACKED, and it is the right reading
of why the unsat lemma may quantify over every `valid`.

`psl211_dealer_view_indep_of_deck_unsat`, lines 143-148. "At PSL(2,11) under
its own dealer law the two premises of `dealer_shuffle_view_indep_of_deck` have
no common solution, for every validity predicate and every candidate reading
law." BACKED, and machine-checked to be about C3 in D1. "The per-deck route to
privacy is closed for this instance." BACKED, under the reading "the per-deck
sufficient condition is unavailable". "And the average over deal descriptions
that `dealer_shuffle_view_indep` asks for is the only route that remains."
OVERREACH, twice. `dealer_shuffle_view_indep` asks for a common mixed view law,
not for an average over deal descriptions; the uniform deal law is one law that
meets that condition, and the condition does not name it. And nothing proves
C2 and C3 exhaust the routes. Suggested replacement for the last clause:

> so of the model's two conditions only the mixed-law condition of
> `dealer_shuffle_view_indep` is available to this instance, and the uniform
> deal law is the law that meets it.

`psl211_fixed_deal_view_dep`, lines 178-186. "Under that dealer law the reading
of three seats is NOT independent of the chirality." BACKED. "This is what
entitles the paper to say that privacy is a property of the dealer law and not
of the protocol alone: the shuffle group, the design and the coalition are the
ones PSL(2,11) uses, only the dealer changed, and the conclusion fails."
BACKED, and each clause was checked separately in D2. "Read together with
`psl211_alldecks_view_indep_via_dealer` it says that for PSL(2,11) privacy is a
property of the uniform average over deal descriptions." OVERREACH. The pair
shows that privacy depends on the deal law, the uniform one delivering it and
one point-mass law not. Necessity of the uniform law is not shown, and the
failure is exhibited at one deal description rather than at every one.
Suggested replacement:

> Read together with `psl211_alldecks_view_indep_via_dealer` it says that for
> PSL(2,11) privacy depends on which deal law the dealer uses: the uniform one
> delivers it, and the point mass at `psl211_perdeck_deal` does not.

"What is NOT shown here is that a hidden uniform deal leaks: the deal is public
in this refutation, being a point mass." BACKED and correctly self-limiting.
The formal content is that the kernel is a point mass, so the deal coordinate
carries no entropy; reading that as "public" is an interpretation, and it is
the conservative one.

STATUS.md carries the second overreaching sentence a second time, at its C8
section, so both carriers need the change.

## D4 The C2 route

The prover's reading of `alldecks_view_law` is correct. Its conclusion, printed
in full by the auditor, is

```text
fdistmap
  (fun dg => alldecks_view rho secretP card_G_gt0 card_class_decks_gt0 C (s, dg))
  (`U (card_class_decks_gt0 s)) `x (`U card_G_gt0) =
fdistmap
  (fun r : (size (enum C)).-tuple 'I_N'.+1 =>
   [ffun i => nth ord0 (\val r) (index i (enum C))])
  (`U Hdt)
```

The pushforward is along the PAIR of deck and shuffle at one fixed secret. That
is the mixed law and it is exactly C2's premise shape. C3's second premise
needs the deck fixed and only the shuffle averaged. A constant average does not
force each term of the average to be constant, so the mixed law cannot
discharge C3's second premise. Confirmed, not refuted.

STATUS.md's two-route account is accurate, and the auditor compiled the leg it
only described. The C2 route exists and reuses the repository lemma directly:

```coq
Lemma audit_c2_route_exists (R : realType) (C : {set 'I_8}) :
  (#|C| <= 3)%N ->
  alldecksP (fdist_uniform card_bool) pgl27_G_pos
    (R := R) pgl27_class_decks_pos
  |= alldecks_view (@pgg_rho pgl27_M) (fdist_uniform card_bool)
       pgl27_G_pos pgl27_class_decks_pos C
  _|_ alldecks_secret (fdist_uniform card_bool) pgl27_G_pos
       pgl27_class_decks_pos.
```

proved by the three transport equations, one `apply:` of
`dealer_shuffle_view_indep`, and a single `refine` of
`transitivity_privacy.alldecks_view_law`. No counting is redone. Its type is
convertible with the probe's C3-route headline:

```text
audit_same_type audit_c2_route_exists pgl27_view_indep_alldecks_via_dealer
     : Type
```

and it reports the three `boolp` axioms. So both routes reach the same
statement, the C2 one reusing the existing lemma and the C3 one instantiating
the per-deck condition. Shipping the C3 route is what keeps soundness invariant
8 true, since otherwise no bridge would instantiate C3 at all; STATUS.md says
this and it is correct.

The in-probe duplication is gone. `pgl27_dealer_view_law`
(`pgl27_deterministic_bridge.v:171-180`) is now three lines: the general
per-deck law at `d := orbit_encode s` with `orbit_encode_deck s` supplying
repetition-freeness. The 88 per cent textual overlap reported in round one no
longer exists.

## D5 The validity mutation

Re-captured with `rocq repl -q <flags> < pgl27_deterministic_bridge.v`. The
control is reported defined before the mutation is reached, and the mutation
fails with a leftover arrow:

```text
pgl27_alldecks_dealer_view_law_with_validity is defined
The command has indeed failed with message:
In environment
R : realType
C : {set 'I_8}
s : bool
d : 8.-tuple 'I_8
Hdt : (0 < #|(size (enum C)).-dtuple([set: 'I_8])|)%N
HC : (#|C| <= 3)%N
Huniq : uniq d
The term "pgl27_alldecks_dealer_view_law R s Hdt HC" has type
 "uniq d ->
  fdistmap [eta pgl27_dealer_view C s d] (`U pgl27_G_pos) =
  pgl27_dealer_mu R Hdt"
while it is expected to have type
 "fdistmap [eta pgl27_dealer_view C s d] (`U pgl27_G_pos) =
  pgl27_dealer_mu R Hdt".
```

This is now the same failure mode as the other leftover-arrow mutations, and
the control and the mutation differ by exactly the final `Huniq`. The premise
order at `:128` is `(#|C| <= 3)%N -> uniq d ->`, coalition size first and
validity last, so the argument-position coincidence that made the old mutation
fragile cannot recur. Round-one finding F1 is resolved.

STATUS.md's description of what remains is accurate. It says validity is shown
needed for the term to typecheck and not shown to be needed for the statement
to be true, it records that the earlier comment asserting a repeated-card deck
lacks the common view law was deleted rather than left standing, and it carries
the falsity proof to the implementation plan with a reason (the point-mass
lemma it needs sits downstream). The auditor confirms the comment is gone from
`pgl27_alldecks_dealer_view_law` and that no probe file asserts falsity
anywhere. This is the honest state: a typing test plus an explicit statement
that the truth question is open.

All seven mutations still fail. The other six were re-captured too and their
first `The term` lines match STATUS.md's table, including the two the rename
touched:

```text
dealer_kernel_probe #1: The term "secretP `X delta" has type
dealer_kernel_probe #2: The term "dealer_shuffle_view_indep (mu:=fdist1 x)" has type
carrier_transport_probe #1: The term "proj1 (inde_RV_fdistmap P f X Y)" has type
pgl27_deterministic_bridge #1: The term "erefl" has type
pgl27_deterministic_bridge #2: The term "pgl27_alldecks_dealer_view_law R s Hdt HC" has type
psl211_alldecks_bridge #1: The term "fdistmap_prod_sectionE (h:=h)" has type
psl211_alldecks_bridge #2: The term "erefl" has type
```

Three declared positive controls now, as STATUS.md says.

## D6 Re-checks

Statement fidelity survived the rename and the restructuring. All six
directions of the conversion test on the three bridge headlines elaborated, and
so did the four `_at_R` wrappers against the production theorems at
`Rdefinitions.R`:

```text
audit_same_type pgl27_view_indep_via_dealer pgl27_view_indep          : Type
audit_same_type pgl27_view_indep pgl27_view_indep_via_dealer          : Type
audit_same_type pgl27_view_indep_alldecks_via_dealer
  pgl27_view_indep_alldecks                                           : Type
audit_same_type pgl27_view_indep_alldecks
  pgl27_view_indep_alldecks_via_dealer                                : Type
audit_same_type psl211_alldecks_view_indep_via_dealer
  psl211_alldecks_view_indep                                          : Type
audit_same_type psl211_alldecks_view_indep
  psl211_alldecks_view_indep_via_dealer                               : Type
audit_same_type pgl27_view_indep_at_R
  (pgl27_view_indep Rdefinitions.RbaseSymbolsImpl.R)                  : Type
audit_same_type (pgl27_view_indep Rdefinitions.RbaseSymbolsImpl.R)
  pgl27_view_indep_at_R                                               : Type
audit_same_type pgl27_view_indep_alldecks_at_R
  (pgl27_view_indep_alldecks Rdefinitions.RbaseSymbolsImpl.R)         : Type
audit_same_type psl211_alldecks_view_indep_at_R
  (psl211_alldecks_view_indep Rdefinitions.RbaseSymbolsImpl.R)        : Type
```

STATUS.md's tables. The compile-cost table matches, as tabulated above. The
mutation table matches all seven texts. The ten-declaration table is accurate:
each of the ten is defined in a probe file, six in `dealer_kernel_probe.v`, one
in `carrier_transport_probe.v`, two in `psl211_alldecks_bridge.v` and
`uniform_fdistmap_pointE` in `psl211_per_deck_law_counter.v`, and a recursive
search of `lib protocol groups security smc reconstruct instances manifest`
finds none of the ten names in the production tree. Four hang shapes are
documented and each is a distinct shape: the ordinal structures that do not
reduce, the rewrite that unfolds both chirality tables, `done` on a group
cardinality, and `exact:` re-evaluating a count by conversion. Findings G5 and
G6 are the two small inaccuracies in that part of the document.

`rocq compile -time` on `psl211_per_deck_law_counter.v`, measured by the
auditor, slowest sentences:

```text
1.356  From~mathcomp~Require~Import~a...
1.265  From~infotheo~Require~Import~r...
0.702  From~mathcomp~Require~Import~b...
0.138  Print~Assumptions~psl211_fixed...
0.125  Print~Assumptions~psl211_deale...
0.055  Qed.
```

The three slowest are `Require Import` lines. No proof sentence exceeds 0.055 s
and no `Print Assumptions` exceeds 0.138 s. The near-hang is gone, the
coordinator's "every proof sentence under 0.2 s" is correct, and STATUS.md's
0.7 s bound is true but loose, which is finding G5.

Mechanical checks on the four changed files: no line over 80 characters, no
banned vocabulary, no `Admitted`, `Abort`, `Axiom`, `Time`, `Timeout` or
`Show`, and every `Definition`, `Lemma` and `Corollary` carries a `(** *)`
statement comment. Both `Local Opaque` in
`psl211_per_deck_law_counter.v` (lines 27 and 33) are released by the
`Local Transparent` at line 251, before the `Print Assumptions` block; the new
`Local Opaque psl211_perdeck_raw_count` is the seal the fourth hang shape calls
for.

Integrity. `shasum -a 256 -c` reports OK for all seven `.v` files, the four
`.md` files and `_CoqProject`; the probe's `.vo` timestamps are unchanged at
21:59 to 22:07; `git status --porcelain --untracked-files=no` is empty; and no
production source imports `general_dealer_law_probe`.

## What the paper may claim, and what it may not

May claim. One dealer law, `secretP `X (fun s => delta s `x nu)`, represents
all three concrete models, and all three of the development's existing privacy
statements are recovered through it with types convertible with the originals,
at an arbitrary real field and at the standard real line, on the three `boolp`
axioms alone. Privacy follows from the model when every positive-mass secret
induces the same mixed observation law, and, as a stronger sufficient
condition, when every positive-mass deck is valid and every valid deck induces
the same observation law under the shuffle alone. The PGL(2,7) all-decks row
satisfies both conditions, and the paper may say so: the mixed-law route reuses
`transitivity_privacy.alldecks_view_law` unchanged and the per-deck route
follows from 3-transitivity, and both reach the same statement.

The PSL(2,11) row satisfies the mixed-law condition and cannot satisfy the
per-deck one. That last is now a theorem rather than a failure to find a proof:
under the instance's own uniform deal law, the two premises of the per-deck
condition have no common solution, for every validity predicate and every
candidate observation law, because the uniform deal law leaves no deal for a
validity predicate to exclude and the counterexample deal admits no common
observation law.

Privacy is a property of the dealer law and not of the protocol alone. Holding
the PSL(2,11) shuffle group, the Steiner design, the reading and a three-seat
coalition fixed, and replacing only the dealer by the one that always lays the
same deal description, independence of the chirality fails. That coalition is
under the instance's privacy threshold of five, both chiralities carry positive
prior mass, and the laid deck still depends on the chirality through the class
table, so the failure is not an artefact of a collapsed instance.

May not claim. That any dealer law preserves privacy; the premise-free
conclusion is not derivable and the mutation at `dealer_kernel_probe.v:137`
shows the model's own lemma does not yield it. That the uniform deal law is
NECESSARY for PSL(2,11) privacy, or that privacy is a property of the uniform
average: what is shown is that the uniform law suffices and that one point-mass
law fails, which leaves every other deal law undecided. That the mixed-law
condition and the per-deck condition are the only routes to privacy; they are
the only two the probe states. That the PSL(2,11) instance leaks under its own
model: the refuting dealer publishes the deal by making it deterministic, and
no statement here concerns a hidden uniform deal. That determinism of the
dealer explains the PGL and PSL difference: the compiled facts are that one
deterministic dealer is private at PGL(2,7) and another is not at PSL(2,11),
and the explanatory difference the repository actually states is
`pgl27_3transitive` against `psl211_2transitive`, with no 3-transitivity proved
for PSL(2,11). That a deck with a repeated card fails the common view law: only
the typing dependence on repetition-freeness is checked, and the truth question
is open and recorded as an implementation-plan item.

VERDICT: GO
