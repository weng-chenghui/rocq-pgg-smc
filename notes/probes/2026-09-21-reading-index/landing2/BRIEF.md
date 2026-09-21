# Landing commit 2: the reading as an index of the security claim (brief)

Authority, in this order: `../RULINGS.md` (with its addendum), the spec
`notes/20260921-reading-index-and-surface-prepositions-probe-design.md`
sections 3, 5, 8, 9, this brief. Sources: `../index2/staged1/` (the one-record
framework, compiled), `../index2/staged/` (the two-record variant, green end to
end, for the instance annotation sites), `../index2/k12_k14_psl211.v`,
`../index2/k15a_distinguishable.v`, `../index2/k15b_obstruction.v`,
`../index2/m6_dealt_endpoints_home.v`, `../audit-soundness/s_monotone.v`,
`../audit-soundness/s_vacuity.v`. Landing commit 1 (the surface) is in
production: every program is written with `by`, `conclude at`, `assuming` and
the inline obstruction rule. The staged trees were taken BEFORE commit 1, so
their instance files carry the OLD surface: take the TERMS and annotations
from them, never the surface text.

## What lands

1. `manifest/pgg_tableau.v`: record `CoalitionReading A` (fields `cr_readT`,
   `cr_read`), default `coalition_endpoint_reading`; the index on
   `ExactWitness`, `IndistinguishabilityCert`, `IdealProximityCert` (the
   ideal's witness of a proximity certificate at the same reading); each
   constructor of `SecurityEvidence` packs its reading; `evidence_reading`,
   `ab_reading`, `reading_of`; ONE free-reading proposition
   `ReadingIndistinguishabilityPropAt sa r c`; `ExactProp`,
   `IndistinguishabilityPropAt`, `IdealProximityPropAt` at the reading of
   their evidence, the other two bodies inlined; the three tails at a free
   reading; two statements per property: `certify_exact`,
   `certify_indistinguishability`, `certify_idealproximity` with production's
   payload types and bodies (default reading), and the twins
   `certify_reading_exact`, `certify_reading_indistinguishability`,
   `certify_reading_idealproximity`; the `_readingE` lemmas beside the
   `_propertyE` ones, each quantified over the real field AND the index;
   `InputDistinguishabilityPropAt sa r c`, the obstruction constructor with
   its reading, the number bound and the exclusion lemma at one reading;
   `ReadingExactIndependence` and `exact_independence_of_witness` if they move
   here in the staged tree.
2. `manifest/pgg_tableau_reading.v`: reduced to lemmas about readings:
   `reading_factors`, `reading_factors_coalition_endpoint_reading`,
   `reading_indistinguishability_postprocessing` (one lemma),
   `input_distinguishability_prop_finer`,
   `input_distinguishability_prop_coalition_endpoint_reading`,
   `indistinguishability_number_ge_across_readings`, and what of
   `exact_independence_*` the colour file still uses. `StaticReading`,
   `static_coalition_reading` and their lemmas are retired. The file header
   is rewritten for what the file now is.
3. `manifest/pgg_tableau_syntax.v`: `s certify ExactIndependence of r by w`,
   `s certify InputIndistinguishability of r by c`,
   `s certify IdealProximity of r by c`; the obstruction terminal gains its
   reading: `s |> publish Obstruction InputDistinguishability of r at c by pf
   assuming a` (and the form without `of r` stays, at the default reading, if
   and only if both factor without an ambiguity warning; otherwise every
   obstruction program names its reading, and the all-decks program names
   `coalition_endpoint_reading psl211_algebra`). The header's keyword
   paragraph gains the sentence about `of`: what is read; it follows the
   literal naming the security property (and `InputDistinguishability`), it is
   a keyword of Rocq already, the count stays twenty. The two-kinds paragraph
   gains `of` what is read. The five-clause rule is at the default reading and
   its comment says so.
4. `manifest/pgg_tableau_security_property_relations.v`: the 14 sites, and
   beside the constant-secret records the constant-reading one: at the reading
   whose value type is `unit` at every coalition, exact independence holds of
   every model and every secret (`inde_RV_cst`), so a program certified at it
   says nothing about the model; name it after what it states (pattern of
   `exact_witness_cst_true`).
5. The annotation sites of the instance files (43 in the two-record count;
   recount), no proof script changed. `instances/psl211/psl211_reading_constancy.v`
   and `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v`: the narrowed
   statements get comments that NAME the reading (the coalition's endpoint
   reading, the finest) and say what is left open: a certificate at a coarser
   reading is not covered; `pgl27_word_input_distinguishability_false` cites
   `input_distinguishability_prop_coalition_endpoint_reading` for why "at no
   reading" follows from "not at the endpoint reading".
6. `instances/psl211/psl211_models.v`: `psl211_dealt_endpoints :=
   profile_endpointsE psl211_profile_endpoints`, `psl211_dealt_observed`,
   beside the all-decks twins. CHECK FIRST that `psl211_models.v` is not in
   the frozen list and that editing it does not put `psl211_endpoints.v` in
   the closure (`closure.py` must print "frozen files met: none"); its
   reverse closure is large (the manifest is above it), that is expected.
7. `instances/psl211/psl211_colour_reading.v`: the hand pass.
   `psl211_colour_reading : CoalitionReading psl211_algebra` is the single
   name; the seat reconciliation lemma moves above `psl211_colour_readingE`
   and the two proofs merge, named once; use sites of the two-argument
   `sr_read` change shape. The header sentence that says the dealer-dealt
   parameters carry no endpoints statement, no Observed and no Sampled level,
   no program and no path is corrected: they do, through `profile_endpointsE`
   as `psl211_endpoints.v` already says, and the programs are in the new file
   below. Count what changed.
8. NEW `instances/psl211/tableau/psl211_tableau_dealt.v` (add to
   `_CoqProject` in dependency order): `psl211_dealt_family`, the Sampled
   program `psl211_dealt_sampled`, `psl211_colour_exact_witness`,
   `psl211_colour_exact_published` (surface: `certify ExactIndependence of
   psl211_colour_reading by psl211_colour_exact_witness |> publish
   StaticExecutedOnly assuming BaselineClassicalOnly`), its `_readingE`,
   `_propertyE`, `_pathE`; `psl211_dealt_input_distinguishable` (K15, at the
   coalition's endpoint reading, 1/660, `psl211_perdeck_coalition`), the
   obstruction program over the dealt model in the inline surface with
   `0 < c`, its `_kindE`/`_pathE`. File header per the template
   `notes/probes/2026-09-20-tableau-directories-s5/staged/TEMPLATE.md`. The
   header states the pair in domain terms (RULINGS design ruling 8): two
   DIFFERENT properties, exact independence of the chirality at the colour
   reading below six seats, input distinguishability between two run
   arguments at the endpoint reading at three seats; over the dealer-dealt
   parameters the run argument is the chirality, which is why the second is a
   privacy statement at this model, and that does not generalise. It also
   says the paths these two programs publish are not among the manifest's
   twelve.

## Traps

- At PSL(2,11) never let the reading wrapper be removed by the conversion that
  closes a goal holding BOTH chiralities (two runs lost, 423 s). Discharge it
  first in a `have` naming one chirality (`exact: erefl`), then rewrite. Never
  `rewrite` with the two mass lemmas when both chiralities are in the goal.
- Measure the dealt obstruction program's `_pathE` and its
  `Print Assumptions` ONE AT A TIME, each under `Timeout 300`; probe B lost a
  combined file to a hang and could not attribute it.
- Implicit arguments of a constructor are not omitted in a `match` pattern in
  Rocq 9.0.0. `by []` on equations between programs may not return: `exact:
  erefl`. `Fail` cannot hold a parser rejection.
- The PGL(2,7) program file must stay near its baseline: time it (production
  before this commit about 7 s); over 15 s means the payload mechanism is not
  the round-2 one.

## Comments

Every statement comment of an object that gained a reading is restated as
what the object IS and its position in the domain argument (attack model: a
static coalition of fewer than `profile_k` seats; a reading is what that
coalition is granted to see of its endpoints, never who it is). `var_dist` is
the sum of absolute differences, twice the total variation distance of the
literature. No history words, no plan or finding ids, no probe tokens, no
"observer" for the party (the manifest's observer column holds random
variables; for a coalition's capability it holds a reading). A comment never
says a reading or a model "is secure": it names the property AND the reading.
The default reading's comment: "The identity at every coalition. A program
that names no reading is a program at this one."
