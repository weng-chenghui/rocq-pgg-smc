# Can a PSL(2,11) row be certified by the Tableau's SpectralDecay arm?

Probe, 2026-09-19, branch `feat/kim-spectral-probe`. Two fix passes applied the
same day, the first after the round 1 soundness audit, `soundness-audit.md`,
the second after the round 2 audit, `soundness-audit-round2.md`. The second
pass changed comments and this document only. No permanent file edited, no
`make` run. Logical path `psl211_sc_const_probe`, directory
`notes/probes/2026-09-19-psl211-sc-const/`. The four `.v` files and this
document are in `history/` twice, as they stood before each pass, with
`.2026-09-19-before-fix` and `.2026-09-19-before-fix2` inserted before the
extension.

Answer: **no at any number equal to a certificate's own bound.** A row
publishes `odflt (cert_eps cert) (c R)` at its reprice coordinate `c`
(`PortProp`, `manifest/pgg_tableau.v:363-369`), and the obligation of
`conclude` is today the equality `cert_eps cert = c R` (`RepricePayload`,
`:610-614`), with
`cert_eps cert = sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert)`
(`:345-347`). Over the all-decks model no certificate carries
`cert_eps < 1/660`, equivalently no certificate carries a shuffle bound
epsilon below `1/1320`, so a spectral row written for this dealer would publish
at least `1/660` against a shuffle whose single-card marginal error this
instance proves to be exactly zero. The constancy field is false at the
group-uniform ideal, at every ideal that vanishes off the shuffle group and is
nonzero at every element of it, and at every ideal within variation distance
`1/1320` of the group-uniform law. The dealt mode fails too, at the record's
own field type, at one named ideal. What is excluded is that range of epsilon
and nothing wider. Argued and not compiled: the range above it is occupied, so
the spectral arm is not unavailable at this instance. Argued and not compiled
as well: a `conclude` whose obligation were weakened from the equality to
`cert_eps cert <= c R` could only publish a number larger than `cert_eps`, so
the exclusion would carry over to it.

## Ledger

| ID | Verdict | Evidence |
|---|---|---|
| Q1 | GO | `psl211_alldecks_sc_const_false` ends in `Qed` |
| Q2 | NO-GO as briefed, GO corrected | `psl211_alldecks_sc_const_false_supp` |
| Q3 | GO, and GO corrected | `fdist_uniform_close_supp`, `psl211_alldecks_sc_const_false_close`, `psl211_alldecks_no_spectral_cert` |
| Q4 | GO | `psl211_dealt_sc_const_false` |
| Q5 | GO | `psl211_alldecks_sc_const_set0` |
| Q6 | done | below |
| Q7 (round 1) | GO | `psl211_alldecks_sc_const_false_word`, `psl211_alldecks_sc_const_false_word584` |
| Q8 (round 1) | GO | `psl211_samechir_law_neq` |

Every headline carries exactly the three boolp axioms
(`propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`), the two new word lemmas and the new
same-chirality lemma included.
`psl211_dealt_raw_countE` is `Closed under the global context`. No `Admitted`,
`Abort`, `Axiom`, `Parameter` or `admit` anywhere in the four files.

## Compile table

Wall times re-measured in the round 1 fix pass, under the machine-wide single-Rocq
lock. Peak `rocqworker` RSS was not re-measured; the figures of the first pass
were 1.76, 1.59, 1.69 and 1.45 GB in the same order.

| file | wall | slowest sentence | exit |
|---|---|---|---|
| `psl211_sc_const_probe.v` | 16.4 s | 6.1 s | 0 |
| `psl211_sc_const_bound_probe.v` | 5.8 s | 1.5 s | 0 |
| `psl211_dealt_sc_const_probe.v` | 15.7 s | 6.1 s | 0 |
| `psl211_deck_diag.v` (diagnostic) | 3.9 s | 1.5 s | 0 |

No sentence exceeds 20 s under `-time`. The first file grew from 5.5 s to
16.4 s because the round 1 fix pass added a second 660-cut count to it, the Q8 block;
its two slowest sentences are the `perm_filter` step of
`psl211_samechir_fiberE` at 6.1 s and the `vm_compute` of
`psl211_samechir_raw_countE` at 5.1 s. The slowest sentence of the third file
is the `perm_filter` step of `psl211_dealt_fiberE` at 6.1 s. The thirteen
`Print Assumptions` of the four files report the three boolp axioms twelve
times and `Closed under the global context` once, for
`psl211_dealt_raw_countE`. The thirteen are four in
`psl211_sc_const_probe.v`, seven in `psl211_sc_const_bound_probe.v`, two in
`psl211_dealt_sc_const_probe.v` and none in `psl211_deck_diag.v`, counted from
the sources and cross-checked against the compile logs, which hold twelve
`Axioms:` blocks each listing exactly `propositional_extensionality`,
`functional_extensionality_dep` and `constructive_indefinite_description`.

## Q1

`sc_const_prop E ideal` restates `sc_const`, the fifth field of `SpectralCert`
(`manifest/pgg_tableau.v:138-142`; the fourth is `sc_close` at `:137`), and
`sc_const_prop_field` proves it is that field read at a certificate's own
ideal, by `exact: sc_const cert`.

    Lemma psl211_alldecks_sc_const_false (R : realType) :
      ~ sc_const_prop psl211_alldecks_params
          ((`U psl211_G_pos) : R.-fdist cutT).

The threshold premise is `psl211_perdeck_coalition_le3`, which puts the three
seats inside a three-point superset and counts that superset with `cardsU1`;
no enumeration of the twelve seats is taken.

## Q2

The brief's premise is wrong at this instance. `pgg_gT psl211_M` is
`{perm 'I_12}` and `pgg_G psl211_M` is a 660-element subgroup of it, so a law
with full support on the carrier puts mass outside the group, the true-side
fiber over `psl211_perdeck_view` is then not empty, and the argument by an
empty fiber does not run. The audit note
`notes/probes/2026-09-15-psl211-planb/AUDIT-SOUNDNESS-2.md` row 18 already
records, argued and not compiled, that at the uniform law on the whole of
`{perm 'I_12}` the reading of any twelve-distinct-card deck is a uniform
injective tuple and `sc_const` holds there. What is proved instead:

    Lemma psl211_alldecks_sc_const_false_supp (R : realType)
        (ideal : R.-fdist cutT) :
      (forall g : cutT, g \notin pgg_G psl211_M -> ideal g = 0) ->
      (forall g : cutT, g \in pgg_G psl211_M -> ideal g != 0) ->
      ~ sc_const_prop psl211_alldecks_params ideal.

Both hypotheses are load-bearing and both must be carried in any paraphrase.
The ideal has to vanish off the shuffle group **and** to be nonzero at every
element of it, so what the lemma covers is exactly the ideals whose support is
the whole shuffle group. An ideal supported on a proper subset of the group is
not covered.

## Q3

The generic lemma the brief asked for, at a finType and the ambient uniform
law:

    Lemma fdist_uniform_close_supp (R : realType) (T : finType) (n : nat)
        (HT : #|T| = n.+1) (Q : R.-fdist T) :
      var_dist (fdist_uniform HT) Q < (#|T|%:R)^-1 -> forall t, Q t != 0.

It does not compose with Q2 here, for the reason in the Q2 row: the ideal that
matters is close to the uniform law on the group and not to the uniform law on
the carrier, and closeness to the group-uniform law does not give support
inside the group. The quantitative form is what carries the argument:

    Lemma psl211_alldecks_sc_const_false_close (R : realType)
        (ideal : R.-fdist cutT) (eps : R) :
      var_dist ((`U psl211_G_pos) : R.-fdist cutT) ideal <= eps ->
      eps + eps < (#|pgg_G psl211_M|%:R)^-1 ->
      ~ sc_const_prop psl211_alldecks_params ideal.

    Theorem psl211_alldecks_no_spectral_cert (R : realType)
      (cert : SpectralCert (psl211_alldecks_sample R)) :
      sw_bound_eps (sc_b cert) + sw_bound_eps (sc_b cert)
        < (#|pgg_G psl211_M|%:R)^-1 -> False.

    Corollary psl211_alldecks_no_spectral_cert0 (R : realType)
      (cert : SpectralCert (psl211_alldecks_sample R)) :
      sw_bound_eps (sc_b cert) = 0 -> False.

The threshold is `1/1320` because infotheo's `var_dist` is the full L1 sum and
not half of it. Excluded: every certificate whose shuffle bound epsilon is
below `1/1320`, that is every certificate whose published `cert_eps`, twice
that epsilon, is below `1/660`.

Not excluded: an ideal at variation distance `1/1320` or more from the
group-uniform law, whose certificate publishes `1/660` or more. Argued and not
compiled, from
`notes/probes/2026-09-15-psl211-planb/AUDIT-SOUNDNESS-2.md` row 18: that range
is not merely unvisited, it is occupied. The uniform law on the whole of
`{perm 'I_12}` satisfies the constancy field, and under infotheo's full-L1
convention its distance from `` `U psl211_G_pos `` is `2 * (1 - 660/12!)`,
essentially 2, which is the L1 ceiling. A certificate at that ideal therefore
exists, with an epsilon near 2, and `sc_close` prices it at that distance. So
a different ideal cut does repair the field; what it cannot repair is the
number the row would then have to publish. Nothing in this paragraph is
compiled, here or anywhere in the tree.

## Q4

The Plan B evidence is
`notes/probes/2026-09-15-psl211-planb/probe_p2_codeview.v:126-131`:

    Lemma psl211_codeview_neq3 :
      psl211_multvec true psl211_seats3 1728
      != psl211_multvec false psl211_seats3 1728.

a multiplicity-vector inequality over raw nat tables, with the witness printed
in `log-probe_p2_codeview.txt:9` as `(18, (0, 1, 6), (0, 1))`. The same file at
`:198-211` states `psl211_sc_const_demand` at the dealt parameters and `Check`s
it against `sc_const`, but never refutes it. The passage to the field type is
new here:

    Lemma psl211_dealt_sc_const_false (R : realType) :
      ~ sc_const_prop psl211_dealt_params ((`U psl211_G_pos) : R.-fdist cutT).

This rules out one named ideal and no certificate. There is no dealt-mode
sample adapter in this tree: `grep MkSampleAdapter instances/psl211/` returns
only `psl211_alldecks_sample` at `psl211_models.v:223`. Without an adapter
there is no `sc_Hd` to pin a dealt certificate's ideal to
`` `U psl211_G_pos ``, so the dealt statement has no certificate-level
consequence of the kind `psl211_alldecks_no_spectral_cert` has.

The cheap route was tried first and does not exist: block line zero of either
chirality's table is `[0;1;2;3;4;10]` and `[0;1;2;3;4;11]` while the encoder
deals its heart codes on `[2;3;5;7;8;9]` and `[0;1;3;7;10;11]`, so the encoder
deck is not the deck the all-decks dealer lays at `psl211_perdeck_deal` and the
all-decks refutation does not transport. `psl211_deck_diag.v` records that
computation. The fiber count is therefore redone for the encoder decks, along
the bridges of `psl211_models.v`.

## Q5

    Lemma psl211_alldecks_sc_const_set0 (R : realType)
        (ideal : R.-fdist cutT) (x x' : ex_inputT psl211_alldecks_params) :
      fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
          set0 x) ideal
      = fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
          set0 x') ideal.

At the empty coalition the reading is the constant map to card zero, so the
constancy statement holds for every law on cuts and the refutations do spend a
nonempty coalition.

## Q7, the word model

The round 1 fix pass added two lemmas, in `psl211_sc_const_bound_probe.v`.

    Lemma psl211_alldecks_sc_const_false_word (R : realType)
        (W ideal : R.-fdist cutT) (d eps : R) :
      var_dist ((`U psl211_G_pos) : R.-fdist cutT) W <= d ->
      var_dist W ideal <= eps ->
      (d + eps) + (d + eps) < (#|pgg_G psl211_M|%:R)^-1 ->
      ~ sc_const_prop psl211_alldecks_params ideal.

    Lemma psl211_alldecks_sc_const_false_word584 (R : realType)
        (ideal : R.-fdist cutT) (eps : R) :
      var_dist (@rho_from_words_weighted R 10 2 584 psl211_moves
          (psl211_Wuni R)) ideal <= eps ->
      (2%:R^-40 + eps) + (2%:R^-40 + eps) < (#|pgg_G psl211_M|%:R)^-1 ->
      ~ sc_const_prop psl211_alldecks_params ideal.

The second is the statement about the word model a paper would want a row for:
the dealer performs a finite 584-letter word and not an exact uniform draw, and
`2^-40` is the whole information-theoretic price of that replacement,
`psl211_word_mixing` at `instances/psl211/psl211_mixing.v:545`. It is stated on
the cut law and not on a certificate, because no weighted-word `SampleAdapter`
exists in this tree and so no `sc_Hd` pins a certificate's ideal to that law.
`psl211_word_mixing` states the distance with the word law on the left, so the
instance goes through infotheo's `symmetric_var_dist`.

The audit proposed these under the names `audit_var_dist_tri` and
`audit_sc_const_false_word` and asked that the triangle inequality be checked
against the libraries first. It is already in the tree:

- `var_dist_triangle` at `security/pgg_collusion_bound.v:43`, in section
  `var_dist_extra`, with exactly the statement wanted, `var_dist P M <=
  var_dist P Q + var_dist Q M`. The probe already imported that file, so no
  copy was made and the new lemma uses it directly. The audit's remark that
  infotheo does not state a triangle inequality is correct; the tree does.
- `leq_var_dist` in infotheo's `probability/variation_dist.v:51` states
  `` `| p x - q x | <= d(p, q) ``, which is the probe's own `var_dist_point_le`
  statement for statement, with the same proof shape. The local copy was left
  in place rather than removing it and reworking the proofs that use it, and a
  source comment on it says so.

  Landing note, confirmed in the round 2 audit. `Set Implicit Arguments` is on
  in the infotheo file and the finType is determined by `p`, so
  `leq_var_dist P Q t` is a drop-in for `var_dist_point_le P Q t` at both call
  sites in this probe, inside `fdist_uniform_close_supp` and inside
  `psl211_alldecks_sc_const_false_close`. A landing drops the local copy and
  keeps `From infotheo Require Import variation_dist`, which the file already
  has. This probe makes no such code change.

## Q8, two deck descriptions of one chirality

The round 1 fix pass added, in `psl211_sc_const_probe.v`:

    Lemma psl211_samechir_law_neq (R : realType) :
      fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
          psl211_perdeck_coalition (true, psl211_perdeck_deal))
        ((`U psl211_G_pos) : R.-fdist cutT)
      != fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
          psl211_perdeck_coalition (true, psl211_samechir_deal))
        ((`U psl211_G_pos) : R.-fdist cutT).

`psl211_samechir_deal` is `(@Ordinal 132 1 isT, 1%g, 1%g)`, which differs from
`psl211_perdeck_deal = (ord0, 1%g, 1%g)` (`psl211_models.v:789`) in the block
line alone. Both run arguments carry chirality `true`. The statement is
literally the equation the constancy field asserts, read at a pair of run
arguments carrying the same secret, and it is false. The field's failure under
the all-decks parameters therefore does not need the secret to move.

The route is the fiber-count route of `psl211_models.v`, at the reading that
gives cards 3, 2 and 4 to seats 0, 1 and 2. That reading has fiber cardinal 1
at the deck of `psl211_perdeck_deal` and 0 at the deck of
`psl211_samechir_deal`, by `psl211_samechir_raw_countE`, a `vm_compute` over
the 660-row closure table costing 5.1 s. The witness was found by a search
outside the repository, which also reported 300 readings reachable at the first
deck and not the second and 300 the other way round, consistent with the
auditor's L1 gap of 600 of 660.

Two lemmas of `psl211_models.v` had to be restated. `psl211_perdeck_raw_viewE`
is restated here as `psl211_alldecks_raw_viewE`, with the deck description left
free instead of fixed to `psl211_perdeck_deal` and the same proof, so that one
is a generalisation in place. `psl211_samechir_fiberE` is not a one-argument
generalisation of `psl211_perdeck_fiberE`: besides freeing the deck
description it changes the target reading, from `psl211_perdeck_view` to
`psl211_samechir_view`, and with it the raw test and the `testE` lemma. A
landing that generalises `psl211_perdeck_fiberE` in place has to abstract the
reading and its raw test as well, for instance as one lemma taking
`v : viewT`, `test : seq nat -> seq nat -> bool` and the hypothesis
`forall sq t, (psl211_perdeck_raw_view sq t == v) = test sq t`. The landing is
not sized as a one-argument generalisation.

## What the result means

The two modes give two different results and a paper must not merge them.

**All-decks mode.** `ex_inputT psl211_alldecks_params` is
`bool * ('I_132 * {perm 'I_6} * {perm 'I_6})`, a whole deck description, whose
first coordinate is the chirality and whose other three are public. The
constancy field quantifies over every pair of deck descriptions, so it asks for
constancy of a coalition's reading in the block line and in the two labellings
as well as in the chirality. The obstruction is therefore what the field
quantifies over and not leakage. The field already fails between two deck
descriptions of one chirality, so its failure does not need the secret to move.
No pair of run arguments varies the secret without varying the laid deck
either, because the chirality selects the table the block line indexes
(`instances/psl211/psl211_alldecks.v:116-123`). Under
the all-decks law three seats read nothing about the chirality: that is
`psl211_alldecks_static_indep`, exact, at every real field, for coalitions of
at most five of the twelve seats, and it is the row that is published. A paper
must not read the all-decks refutation as leakage.

The same-chirality failure is Q8, `psl211_samechir_law_neq`: the field's own
equation refuted at one pair of run arguments, and not a `~ sc_const_prop`
statement. The artifact a paper would cite for this claim is a corollary
refuting `sc_const_prop psl211_alldecks_params` at the group-uniform ideal
from that same-secret pair, four lines along the route of
`psl211_alldecks_sc_const_false`, and the probe does not carry it. How wide the
failure is remains measured only. The auditor's
`audit-soundness/audit_diag.v`, with its output in
`audit-soundness/audit_diag.log.txt`, `vm_compute`s the reading multiplicity
vectors over `psl211_elem_table` and reports an L1 gap of 600 of 660 cuts
between block line 0 and block line 1 at chirality `true`, against 360 of 660
between the two chiralities at block line 0, and 660 distinct readings at
seats 0, 1 and 2 under one deck description. Those three numbers are a
`vm_compute` diagnostic and not Rocq theorems. The same source gives the
diagnostic consequence that any certificate would need `cert_eps >= 10/11`,
about 600 times the proved floor; that too is a diagnostic and not a theorem.
Proving it needs the mass of a 300-reading event rather than of one reading,
which is a fiber count over an explicit reading predicate and was not
attempted.

**Dealt mode.** `ex_inputT psl211_dealt_params` is `pga_secretT psl211_algebra`,
which is `bool`, because `psl211_dealt_params` is
`dealt_secret_params psl211_algebra psl211_fuel`
(`protocol/pgg_instance.v:398-401`). The field's two run arguments are the two
secrets and nothing else, so here the field is exactly constancy in the secret,
and it still fails. That is a fact about the group and the design. PGL(2,7)
certifies the same field through `pgl27_word_view_const`
(`instances/pgl27/pgl27_rows.v`), which is three-transitivity read as a privacy
statement for coalitions below four. PSL(2,11) is 2-transitive and not
3-transitive, so three seats see a reading, cards 0, 1 and 6 at seats 0, 1 and
2, that one chirality's encoder deck reaches under exactly one cut and the
other reaches under none.

## Q6. Homes

Reverse-dependency closures recomputed in the round 1 fix pass from
`.Makefile.rocq.d` with `audit-soundness/revdeps.py`, which expands line
continuations, keeps only `.vo` nodes and takes the transitive closure of the
reversed edge set.

| file | reverse-dependants | `psl211_endpoints.vo` in closure |
|---|---|---|
| `security/pgg_collusion_bound.v` | 105 | **yes** |
| `reconstruct/design_privacy.v` | 11 | no |
| `instances/psl211/psl211_models.v` | 9 | no |
| `instances/psl211/psl211_rows.v` | 0 | no |
| `instances/psl211/psl211_mixing.v` | 0 | no |

`security/pgg_collusion_bound.v` is **not** an allowed home. Its reverse
closure contains `instances/psl211/psl211_endpoints.vo`, and the project rule
is that no file whose reverse closure contains `psl211_endpoints` may be
edited. The first pass of this probe proposed it for two generic lemmas; that
proposal is withdrawn.

`reconstruct/design_privacy.v` has 11 reverse-dependants and `psl211_endpoints`
is not among them: `instances/kim2025/five_card_rows.vo`,
`instances/pgl27/pgl27_rows.vo`, `instances/psl211/psl211_analysis.vo`,
`instances/psl211/psl211_models.vo`, `instances/psl211/psl211_rows.vo`,
`instances/psl211/psl211_secrecy.vo`, `instances/s5/s5_rows.vo`,
`manifest/pgg_analysis_client.vo`, `manifest/pgg_analysis_manifest.vo`,
`manifest/pgg_tableau.vo`, `manifest/pgg_tableau_syntax.vo`.

The sibling Kim probe, `notes/probes/2026-09-19-kim-spectral-arm/`, proposes a
new `lib/var_dist_supp.v` for generic variation-distance facts, on the grounds
that `lib/` is where this tree puts extensions to the underlying libraries and
that its files carry no `pgg_` prefix. `fdist_uniform_close_supp` belongs
there, beside that probe's inhabitants. A new file has an empty reverse closure
wherever it is put, so the `psl211_endpoints` rule does not constrain it; it
does need one line in `_CoqProject`, which enumerates the built files by name,
as that probe's round 2 soundness audit established.

| item | proposed name | proposed home |
|---|---|---|
| generic point bound | — | dropped, infotheo's `leq_var_dist` |
| generic triangle inequality | — | dropped, the tree's `var_dist_triangle` |
| generic uniform support | `fdist_uniform_close_supp` | new `lib/var_dist_supp.v` |
| generic pushforward point mass | `fdistmap_point_condE` | `reconstruct/design_privacy.v`, section `fibers` |
| Q1 and its coalition lemmas | `psl211_perdeck_coalition_le3`, `psl211_perdeck_coalition_below_k`, `psl211_perdeck_ideal_lawE`, `psl211_perdeck_fiber_true0` | `instances/psl211/psl211_models.v` |
| Q2, Q3, Q7, the headline | `psl211_alldecks_sc_const_false`, `psl211_alldecks_sc_const_false_supp`, `psl211_alldecks_sc_const_false_close`, `psl211_alldecks_sc_const_false_word`, `psl211_alldecks_sc_const_false_word584`, `psl211_alldecks_cert_ideal_close`, `psl211_alldecks_no_spectral_cert`, `psl211_alldecks_no_spectral_cert0`, `psl211_alldecks_sc_const_set0` | `instances/psl211/psl211_rows.v` |
| Q4 | the `psl211_dealt_*` block | `instances/psl211/psl211_rows.v` |
| Q8 | the `psl211_samechir_*` block, with `psl211_perdeck_raw_viewE` generalised in place and `psl211_perdeck_fiberE` generalised over the target reading and its raw test as well | `instances/psl211/psl211_models.v` |

`fdistmap_point_condE` goes to `design_privacy.v` because that file is already
this probe's and the tree's home for fiber and pushforward lemmas, which is its
subject matter; it is not sent to `lib/var_dist_supp.v`, which is about
variation distance.

The `sc_const` statements name `SpectralCert`, which lives in the manifest
layer, so they cannot go in `psl211_models.v`: that file deliberately imports
nothing from the manifest, and `psl211_rows.v` is where this instance's other
manifest-typed statements already live. Landing the word lemmas in
`psl211_rows.v` adds `From infotheo Require Import variation_dist` and
`From pgg_smc Require Import pgg_collusion_bound psl211_mixing
pgg_weighted_words` to that file, none of which it has today, and
`psl211_rows.v` has zero reverse-dependants. Anything landing in
`psl211_rows.v` also carries the `sc_const_prop` restatement itself, which
today lives only in this probe.

Whole-word scan of the new names with Python `\b`: zero hits for the 31 names
of the first pass, over 583 files. The seventeen names added in the round 1 fix pass,
`psl211_alldecks_sc_const_false_word`,
`psl211_alldecks_sc_const_false_word584`, `psl211_alldecks_raw_viewE` and the
fourteen `psl211_samechir_*`, were rescanned the same way over 1129 files, the
production tree plus the installed infotheo and mathcomp trees, excluding this
probe's own directory: zero hits.

The header sentence of `psl211_rows.v` a landing would have to rewrite is the
one at lines 40-45:

> Not claimed. There is no spectral arm for this dealer: a certificate's
> constancy field asks that a coalition's reading of the ideal cut not vary
> with the run argument, which fails at three seats under the dealt mode at
> the group-uniform ideal, and under the all-decks dealer it is a different
> statement nobody has measured.

Only the last clause is out of date. The all-decks statement has been measured
and is false at the group-uniform ideal, at every ideal whose support is
exactly the shuffle group, and at every ideal within `1/1320` of the
group-uniform law. The first clause is not out of date: the dealt-mode failure
at three seats at the group-uniform ideal was true before and is now carried at
the record's own field type rather than at the raw count, which is a
strengthening. The opening sentence, "There is no spectral arm for this
dealer", does overstate and must be rewritten with the number in it. A landing
replaces the passage with something of this shape:

> Not claimed. The spectral arm is not available to this dealer at any number
> equal to a certificate's own bound. A certificate's constancy field asks
> that a coalition below the threshold read the ideal cut the same way at
> every run argument. Under the dealer-dealt parameters, where the run
> argument is the secret, it fails at three seats at the group-uniform ideal.
> Under the all-decks parameters, where the run argument is the deck
> description, it fails at the group-uniform ideal, at every ideal whose
> support is exactly the shuffle group and at every ideal within `1/1320` of
> the group-uniform law, so a row over this model that publishes its
> certificate's own bound publishes at least `1/660` against a shuffle whose
> single-card marginal error is zero. It fails at two deck descriptions of
> one chirality as well, so the field is stronger than the
> secret-independence this row claims and its failure is not leakage.

## What a paper may and may not say

- May say: at PSL(2,11) under the all-decks dealer, a coalition of at most five
  of the twelve seats reads nothing about the chirality, exactly, at every real
  field. That is `psl211_alldecks_static_indep`.
- May say: no spectral certificate over that model carries a shuffle bound
  below `1/1320`, so a spectral row there that publishes its certificate's own
  bound publishes at least `1/660`, while the exact arm closes with no number
  at all. That is `psl211_alldecks_no_spectral_cert`, at its own hypothesis.
- May say: under the dealer-dealt parameters, where the run argument is the
  secret itself, the constancy field fails at three seats at the group-uniform
  ideal, and the reason is that PSL(2,11) is 2-transitive and not
  3-transitive, which is the contrast with PGL(2,7)'s certified spectral row.
- May say: under the all-decks parameters the constancy field fails at two deck
  descriptions of one chirality, so its failure does not need the secret to
  move. That is `psl211_samechir_law_neq`, at the block lines 0 and 1 with both
  labellings the identity, and it is the field's equation refuted at that pair
  rather than a refutation of `sc_const_prop`.
- May not say: that the failure is unrelated to the secret, or that it is not a
  failure of constancy in the chirality. The field fails between the two
  chiralities of `psl211_perdeck_deal` too, which is
  `psl211_alldecks_sc_const_false` through `psl211_perdeck_law_neq`, and no
  pair of run arguments moves the secret without moving the laid deck.
- May not say: that no spectral certificate exists at this instance. What is
  excluded is a range of epsilon, and the range above it is occupied by the
  ambient uniform ideal. That occupancy is argued and not compiled.
- May not say: that the failure of the constancy field is leakage, or that
  three seats learn the chirality. Under the all-decks law they do not, and the
  field fails at two deck descriptions of one chirality as well,
  `psl211_samechir_law_neq`.
- May not say: that the word row is excluded outright.
  `psl211_alldecks_sc_const_false_word584` reaches only
  `eps < 1/1320 - 2^-40`, and no weighted-word adapter exists for PSL(2,11).

## Code changes of the round 1 fix pass that are not pure renames

Nothing was renamed, so there is no `rename_map.tsv`. No existing proof was
reordered or restructured. Every change below is either a comment or an
addition. The round 2 pass that followed changed no `.v` line outside a
comment at all.

1. `psl211_sc_const_probe.v`, header banner. Reflowed to 79 bytes a line,
   fixing the fourteen 81-byte lines, and one paragraph added about what the
   all-decks run argument is. The round 2 pass rewrote that paragraph; see
   "Round 2 audit and what changed".
2. `psl211_sc_const_probe.v`, statement comments of `sc_const_prop`,
   `psl211_alldecks_sc_const_false` and `psl211_alldecks_sc_const_set0`
   rewritten. A source comment under `psl211_alldecks_sc_const_false` names
   `psl211_samechir_law_neq` and says that the width of the same-chirality
   failure is a diagnostic and not a theorem. No statement changed.
3. `psl211_sc_const_bound_probe.v`, header banner: three 78-byte lines padded
   to 79 and one paragraph added about the word model.
4. `psl211_sc_const_bound_probe.v`, two `Require Import` lines changed:
   `psl211_mixing` added to the `psl211_blocks psl211_closure` line, and a new
   line `From pgg_smc Require Import pgg_weighted_words.` These are what
   `psl211_word_mixing`, `rho_from_words_weighted` and `psl211_Wuni` need.
5. `psl211_sc_const_bound_probe.v`, statement comments of
   `psl211_perdeck_ideal_lawE`, `psl211_alldecks_no_spectral_cert` and
   `psl211_alldecks_no_spectral_cert0` rewritten; a source comment added
   under each of `var_dist_point_le` and `psl211_alldecks_no_spectral_cert`.
6. `psl211_sc_const_bound_probe.v`, new final section with the two new lemmas
   `psl211_alldecks_sc_const_false_word` and
   `psl211_alldecks_sc_const_false_word584`, and two new
   `Print Assumptions` lines for them. Nothing above that section was touched
   apart from the comments listed here.
7. `psl211_dealt_sc_const_probe.v`, statement comment of
   `psl211_dealt_sc_const_false` rewritten.
8. `psl211_sc_const_probe.v`, two additions carrying Q8: a
   `From pgg_smc Require Import psl211_blocks psl211_closure.` line, a
   `Local Notation viewT`, and a new final section holding
   `psl211_samechir_deal`, `psl211_samechir_view`, `psl211_samechir_test`,
   `psl211_samechir_testE`, `psl211_alldecks_raw_viewE`,
   `psl211_samechir_seq`, `psl211_samechir_row_size`,
   `psl211_samechir_corow_size`, `psl211_samechir_seqE`,
   `psl211_samechir_raw_count`, `psl211_samechir_raw_countE`,
   `psl211_samechir_fiber`, `psl211_samechir_fiberE`,
   `psl211_samechir_massE` and `psl211_samechir_law_neq`, two `Local Opaque`
   lines inside that section and one new `Print Assumptions`. Nothing above
   that section was touched apart from the comments listed here.
9. `psl211_sc_const_probe.v`, the four pre-existing section banners padded
   from 80 bytes to 79, so that all four files now carry one banner width.
   Whitespace only.
10. `psl211_deck_diag.v`: unchanged.

The list was checked mechanically, not by eye: each file was diffed against
its `history/` copy after both had every `(* ... *)` block removed, nesting
respected. `psl211_dealt_sc_const_probe.v` shows no non-comment change at all,
`psl211_sc_const_bound_probe.v` shows exactly the two import lines, the two new
lemmas and the two new `Print Assumptions`, and `psl211_sc_const_probe.v` shows
exactly the one import line, the `viewT` notation, the Q8 block and its one new
`Print Assumptions`.

Every line of every `.v` file is at most 80 bytes, and every banner rule is
79, both checked byte by byte in Python rather than with `awk`, whose
`length` counts characters and not bytes on the em-dashes these comments
carry.

## Items of the round 1 audit not applied

- S3(b), a same-chirality refutation, was applied: it is Q8,
  `psl211_samechir_law_neq`, closed on the first attempt, as the field's own
  equation refuted at one pair of run arguments. What remains measured and not
  proved is the width of the failure, the 600-of-660 L1 gap, and the
  `cert_eps >= 10/11` floor that follows from it.
- S8 and S10 are the audit's own NOTEs with recommendation "harmless" and
  "none". Nothing to apply.
- S9 asks that `fdist_uniform_close_supp` be kept only if a later statement
  needs it. It is kept: it is the generic lemma the brief's Q3 asked for, and
  the Q3 row explains why it does not compose at this instance. A landing
  decides whether it survives.

## Round 2 audit and what changed

`soundness-audit-round2.md`, verdict NO-GO on the English, with every compiled
statement found true, correctly typed and carrying only the three boolp
axioms. The pass below changed comments and this document only. After comment
stripping each of the four `.v` files is identical to its
`.2026-09-19-before-fix2` copy, checked with a nesting- and string-aware
stripper.

**B1, the field ordinal.** `sc_const` is the fifth field of `SpectralCert`
(`manifest/pgg_tableau.v:138-142`, after `sc_b`, `sc_Hd`, `sc_ideal` and
`sc_close`; the record's own comment says "Five fields"). The statement comment
of `sc_const_prop_field` called it the fourth, which is `sc_close`, a
materially different claim. Replaced with the audit's text, which also drops
the two positional pointers and the maintenance remark. The error was
pre-existing and round 1 missed it. The Q1 row of this document now names the
field's position and its line range as well, which fixes N1.

**B2, three sentences denying a proved failure.** The constancy field fails
between the two chiralities at `psl211_perdeck_deal`, which is
`psl211_alldecks_sc_const_false` through `psl211_perdeck_law_neq`
(`instances/psl211/psl211_models.v:1036-1042`), and it fails between two block
lines at chirality `true`, which is `psl211_samechir_law_neq`. Calling the
failure "not constancy in the secret", "not of constancy in the chirality" or
"not a statement about the secret" therefore denies what the probe proves. What
is true is that the failure does not need the secret to move, that it is
already a failure of constancy in the public block line, and that a change of
secret is always also a change of the laid deck, because the chirality selects
the table the block line indexes (`instances/psl211/psl211_alldecks.v:116-123`,
`psl211_alldecks_row x = nth [::] (psl211_class_tbl x.1) (val x.2.1.1)`).

Sentences changed, all of them:

| where | what it said | what it says now |
|---|---|---|
| `psl211_sc_const_probe.v`, header | "the refutation in this file is not a statement about the secret and is not a statement of leakage" | its failure does not need the secret to move; a change of secret is always also a change of the laid deck; the no-leakage clause is kept and tied to `psl211_alldecks_static_indep` |
| `psl211_sc_const_probe.v`, header | "by a wider margin than between the two chiralities of one deck description" | dropped, the comparative inherited its numbers from the auditor's `vm_compute` diagnostic |
| `psl211_sc_const_probe.v`, `psl211_alldecks_sc_const_false` | "what fails here is constancy in a public coordinate and not constancy in the secret" | the audit's B2a block: the field fails at a pair of one chirality too, `psl211_samechir_law_neq`, and a change of secret is always also a change of the laid deck |
| `psl211_sc_const_probe.v`, `psl211_samechir_law_neq` | "is a failure of constancy in the public block line and not of constancy in the chirality" | the audit's B2b block: the failure does not need the chirality to move, it is already a failure of constancy in the public block line |
| `STATUS.md`, "What the result means" | "so the refutation is not a statement about the secret at all" | the audit's B2c text, with the table-selection reason and its source citation |
| `STATUS.md`, Q8 | "The field's failure under the all-decks parameters is therefore not a statement about the secret." | "therefore does not need the secret to move" |
| `STATUS.md`, "May say" | "so it is not a statement about the secret" | "so its failure does not need the secret to move", plus a new "May not say" bullet against the two denials |
| `STATUS.md`, round 1 change log | described the added paragraph as saying "the refutation is not a statement about the secret or about leakage" | describes it neutrally and points here |

The phrase "states no leakage" survives in two places, at the header and at
`psl211_alldecks_sc_const_false`, in both tied to
`psl211_alldecks_static_indep`: three seats read nothing about the chirality
under the all-decks law, and a refutation of the field is not a proof of
leakage. Neither says that the two chiralities give the same law at a fixed
deck description, which is false.

**SHOULD-FIX, all twelve dispositioned.** Eleven are applied in full. SF12 is
applied as its wording half; its alternative, a new corollary, is a code change
and is listed below as not applied.

| id | disposition |
|---|---|
| SF1 | `psl211_alldecks_sc_const_false_supp`: the loose "any law that sees the group at all" replaced by the audit's text, which carries both hypotheses, vanishing off `pgg_G` and nonzero at every element of it |
| SF2 | `psl211_perdeck_fiber_true0`: "which is the whole of the per-deck asymmetry" replaced, 360 of the 660 cuts separate the two chiralities at this deck description, so one reading is the whole of what the refutation spends, not the whole of the asymmetry |
| SF3 | `psl211_samechir_view`: the 660-distinct-readings claim moved out of the rendered comment into a source comment labelled "measured once and not proved", citing `audit-soundness/audit_diag.v` line 62 and its log |
| SF4 | header of `psl211_sc_const_probe.v`: "Everything mathematical is already in psl211_models.v" replaced by the audit's text naming the second count |
| SF5 | "the public deck description" replaced at all three surviving sites, `psl211_sc_const_probe.v` header, `psl211_perdeck_ideal_lawE` and this document's "All-decks mode"; the fourth site was inside B2a |
| SF6 | the `Print Assumptions` count corrected from twelve to thirteen, with the true split and the per-file breakdown, recounted from the sources and cross-checked against the compile logs |
| SF7 | the Q8 landing instruction and the homes table now say that `psl211_samechir_fiberE` also changes the target reading and its raw test, and give the shape a real generalisation takes |
| SF8 | the answer paragraph and `psl211_alldecks_no_spectral_cert` now name the reprice coordinate, say the obligation of `conclude` is today an equality, and state that what is excluded is every published number equal to `cert_eps`, hence at least `1/660` |
| SF9 | "the refutations take the instance through the one consequence whose fiber counts psl211_models.v carries" moved from the rendered comment of `psl211_perdeck_ideal_lawE` to a source comment |
| SF10 | the reduction warning moved out of the rendered comment of `psl211_perdeck_coalition_le3` into a source comment above the statement, which is where this file puts its other reduction warnings |
| SF11 | the occupancy of the unexcluded range now carries "argued and not compiled" in the answer paragraph, in Q3 and in the "May not say" list, matching the source comment at `psl211_alldecks_no_spectral_cert` |
| SF12 | the same-chirality result is no longer called "proved at the field type": it is the field's own equation refuted at one pair of run arguments, and the corollary a paper would cite is named as absent |

**NOTE items.**

| id | disposition |
|---|---|
| N1 | applied, the `sc_const` citation is now `:138-142` and names `:137` as `sc_close` |
| N2 | applied, "block index one of the chirality's table" is now "block line one, both labellings the identity" |
| N3 | applied, `fdist_uniform_close_supp` now says nothing here spends it and why |
| N4 | recorded and not changed, per the audit's own ruling: the 2-transitivity sentence in `psl211_dealt_sc_const_probe.v` is a sound domain reading and not the file's proof, which is a count |
| N5 | applied, the first sentence of `psl211_dealt_sc_const_false` now names the two levels, the named ideal and the certificate, so it no longer reads against the closing sentence |
| N6 | applied, "the statement about the word model a paper would want a row for" dropped from `psl211_alldecks_sc_const_false_word584`; the currencies stay labelled |
| N7 | recorded in Q7 as a landing note, see below |

**The reprice argument, argued and not compiled.** `PortProp`
(`manifest/pgg_tableau.v:363-369`) publishes `odflt (cert_eps cert) (c R)`, and
`RepricePayload` (`:610-614`) obliges a `conclude` to prove
`cert_eps cert = odflt (cert_eps cert) (c R)`, an equality. So today's excluded
set is exactly the published numbers equal to `cert_eps`. A row carries
`SpectralPropAt cert c`, a variation distance bounded above by `c`, so an
obligation weakened to `cert_eps cert <= c R` could only let a row publish a
number larger than `cert_eps` and the exclusion would carry over. That second
half is argued here and compiled nowhere.

**N7, the duplicate lemma.** The probe's `var_dist_point_le` duplicates
infotheo's `leq_var_dist` (`probability/variation_dist.v:51`) statement for
statement. Both take three explicit arguments, the real field and the finType
being implicit and determined by the first, so `leq_var_dist P Q t` is a
drop-in at both of this probe's call sites, inside `fdist_uniform_close_supp`
and inside `psl211_alldecks_sc_const_false_close`. A landing drops the local
copy. The Q7 row carries this note; no `.v` code was changed for it.

**Found by re-reading, beyond the audit's list.** Every comment of the four
files and every paragraph of this document were read again after the edits
above, on the expectation that this pass introduced errors of its own, as the
round 1 pass did. Five were found and fixed.

- "block index" for the first coordinate of a deck description, at
  `psl211_dealt_sc_const_probe.v:23` and at three places here, against the
  file-wide word "block line". N2 had caught only one of the five.
- `psl211_samechir_view` said the reading is reached by "the deck of
  psl211_perdeck_deal" and not by "the deck of psl211_samechir_deal", with no
  chirality named, while `psl211_samechir_raw_countE` decides both at chirality
  `true` only. Both are now written as the deck laid at
  `(true, psl211_perdeck_deal)` and at `(true, psl211_samechir_deal)`.
- The source comment under `psl211_alldecks_sc_const_false` still said
  `psl211_samechir_law_neq` "proves the same-chirality failure at the field
  type", which is SF12's error at a second site the audit did not list. It now
  says the lemma refutes the field's own equation at one pair of run arguments.
  The same phrase is corrected in the round 1 items-not-applied list.
- The argued source comment under `psl211_alldecks_no_spectral_cert` ended "the
  spectral arm is available at this instance; what it is not is available at a
  number worth publishing", a value judgement inside an argued block. It now
  says the arm is not unavailable and that the theorem excludes a range of
  epsilon and not the arm.
- The replacement text proposed for `psl211_rows.v` said "a certificate over
  this model publishes at least 1/660" without SF8's reprice caveat. It now
  says a row that publishes its certificate's own bound.

Checked and found clean: nothing in the four files or here says the spectral
arm cannot be closed at all; 360/660, 600/660 and 10/11 are labelled
`vm_compute` diagnostics at every occurrence; the unexcluded range reads
`1/1320` in epsilon and `1/660` in the published number everywhere.

## Round 2 findings not applied

- **SF12, second half.** The audit offers either a wording fix or a four-line
  corollary refuting `sc_const_prop psl211_alldecks_params` at the group-uniform
  ideal from the same-secret pair. The wording fix is applied. The corollary is
  a code change, which this pass may not make; it is named in Q8 as the
  artifact a paper would cite, and it is a landing item.
- **N7.** Replacing `var_dist_point_le` by `leq_var_dist` is a code change. The
  Q7 row records it as a landing item with both call sites named.
- **The 300-reading event.** Proving the 600-of-660 L1 gap, and with it the
  `cert_eps >= 10/11` diagnostic, needs the mass of a 300-reading event rather
  than of one reading. That was already out of scope in round 1 and stays out
  of scope here.
