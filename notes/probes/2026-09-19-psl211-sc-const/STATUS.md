# Can a PSL(2,11) row be certified by the Tableau's SpectralDecay arm?

Probe, 2026-09-19, branch `feat/kim-spectral-probe`. No permanent file edited,
no `make` run. Logical path `psl211_sc_const_probe`, directory
`notes/probes/2026-09-19-psl211-sc-const/`.

Answer: **no**, at the all-decks model, and not for a reason that a different
ideal cut can repair. The constancy field fails at the group-uniform ideal, it
fails at every ideal supported on the shuffle group, and it fails at every
ideal within variation distance `1/(2*660)` of the group-uniform law. The
certificate's own identification field pins its shuffle law to the adapter's
cut, which this model draws uniformly on the group, so a certificate would
have to quote a shuffle bound of at least `1/1320` against a shuffle whose
marginal error this instance proves to be zero. The dealt mode fails too, at
the record's own field type.

## Ledger

| ID | Verdict | Evidence |
|---|---|---|
| Q1 | GO | `psl211_alldecks_sc_const_false` ends in `Qed` |
| Q2 | NO-GO as briefed, GO corrected | `psl211_alldecks_sc_const_false_supp` |
| Q3 | GO, and GO corrected | `fdist_uniform_close_supp`, `psl211_alldecks_sc_const_false_close`, `psl211_alldecks_no_spectral_cert` |
| Q4 | GO | `psl211_dealt_sc_const_false` |
| Q5 | GO | `psl211_alldecks_sc_const_set0` |
| Q6 | done | below |

Every headline carries exactly the three boolp axioms
(`propositional_extensionality`, `functional_extensionality_dep`,
`constructive_indefinite_description`). `psl211_dealt_raw_countE` is `Closed
under the global context`. No `Admitted`, `Abort`, `Axiom`, `Parameter` or
`admit` anywhere in the three files.

## Compile table

| file | wall | peak rocqworker RSS | exit |
|---|---|---|---|
| `psl211_sc_const_probe.v` | 5.1 s | 1.76 GB | 0 |
| `psl211_sc_const_bound_probe.v` | 5.0 s | 1.59 GB | 0 |
| `psl211_dealt_sc_const_probe.v` | 15.7 s | 1.69 GB | 0 |
| `psl211_deck_diag.v` (diagnostic) | 3.7 s | 1.45 GB | 0 |

No sentence exceeds 20 s under `-time`; the slowest is the `vm_compute` of
`psl211_dealt_raw_countE` at 6.9 s.

## Q1

`sc_const_prop E ideal` restates the `sc_const` field of `SpectralCert`
(`manifest/pgg_tableau.v:137-142`), and `sc_const_prop_field` proves it is
that field read at a certificate's own ideal, by `exact: sc_const cert`.

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
not half of it. Not excluded: an ideal at variation distance `1/660` or more
from the group-uniform law, which is where the ambient uniform law sits, and
which `sc_close` then prices at that distance or worse.

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

The cheap route was tried first and does not exist: block index zero of either
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
constancy statement holds for every law on cuts and the refutations above do
spend their coalition.

## Q6

Reverse-dependency closure from `.Makefile.rocq.d`.

`instances/psl211/psl211_models.vo` has nine transitive importers:
`instances/kim2025/five_card_rows.vo`, `instances/pgl27/pgl27_rows.vo`,
`instances/psl211/psl211_analysis.vo`, `instances/psl211/psl211_rows.vo`,
`instances/s5/s5_rows.vo`, `manifest/pgg_analysis_client.vo`,
`manifest/pgg_analysis_manifest.vo`, `manifest/pgg_tableau.vo`,
`manifest/pgg_tableau_syntax.vo`. `psl211_endpoints` is **not** in that
closure: it is a dependency of `psl211_models`, not a dependent of it, so
landing in `psl211_models.v` does not rebuild it.

`instances/psl211/psl211_rows.vo` has zero importers.

| item | proposed name | proposed home |
|---|---|---|
| generic point bound | `var_dist_point_le` | `security/pgg_collusion_bound.v`, section `var_dist_extra` |
| generic uniform support | `fdist_uniform_close_supp` | `security/pgg_collusion_bound.v`, section `var_dist_extra` |
| generic pushforward point mass | `fdistmap_point_condE` | `reconstruct/design_privacy.v`, section `fibers` |
| Q1 and its coalition lemmas | `psl211_perdeck_coalition_le3`, `psl211_perdeck_coalition_below_k`, `psl211_perdeck_ideal_lawE`, `psl211_perdeck_fiber_true0` | `instances/psl211/psl211_models.v` |
| Q2, Q3, the headline | `psl211_alldecks_sc_const_false`, `psl211_alldecks_sc_const_false_supp`, `psl211_alldecks_sc_const_false_close`, `psl211_alldecks_cert_ideal_close`, `psl211_alldecks_no_spectral_cert`, `psl211_alldecks_no_spectral_cert0`, `psl211_alldecks_sc_const_set0` | `instances/psl211/psl211_rows.v` |
| Q4 | the `psl211_dealt_*` block | `instances/psl211/psl211_rows.v` |

The `sc_const` statements name `SpectralCert`, which lives in the manifest
layer, so they cannot go in `psl211_models.v`: that file deliberately imports
nothing from the manifest, and `psl211_rows.v` is where this instance's other
manifest-typed statements already live. The three generic lemmas are below
`psl211_endpoints` in the build order and must not name it; none of them does.

Whole-word scan of the 31 new names over 583 files, the production tree plus
the installed infotheo and mathcomp trees, with Python `\b`: zero hits.

The header sentence of `psl211_rows.v` a landing would have to rewrite is the
one at lines 40-45:

> Not claimed. There is no spectral arm for this dealer: a certificate's
> constancy field asks that a coalition's reading of the ideal cut not vary
> with the run argument, which fails at three seats under the dealt mode at
> the group-uniform ideal, and under the all-decks dealer it is a different
> statement nobody has measured.

Both of its clauses are now out of date: the dealt-mode failure is proved at
the field type rather than at the raw count, and the all-decks statement has
been measured and is false.

## Known cosmetic defect

Fourteen header lines of `psl211_sc_const_probe.v` are 81 characters wide.
Correcting them would restamp the `.vo` the other two files load, so they are
left as they are and corrected at a landing.
