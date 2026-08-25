# pgg-smc architecture diagram (suggested completion)

Date: 2026-05-17

## Context

Starting from a rough hand-drawn tree of the pgg-smc work, this note
fills the `(text ...)` placeholders with names actually present in the
codebase (as of commit `751d18b`), and flags two layers that are
load-bearing but were missing from the rough draft.

## Suggested diagram

```
Secret Sharing Protocol:
  card-based MPC (pi-SMC session-typed; dealer/verifier/player roles)
  protocol/card_protocol.v           - CardShuffle model + cs_decode_encode_correct
  protocol/card_exchange_pismc.v     - session-typed Reveal/Deal/Announce/Observe/Receive
|
|--> Plug-able group instance (protocol/pgg_interface.v):
       HB-structured interface; an instance populates
         PGGTypes        (pgg_gT, pgg_N', pgg_G)
         isMonodromyRepr (pgg_rho : G >-> {perm 'I_(N'.+1)})
         hasGenerators   (pgg_sigmas, pgg_sigmas_gen)
         hasWeights R    (pgg_gen_weights : fdist of generator choice)
       Same protocol shell; security and recoverability profiles
       come from which structures the instance instantiates.
|
|--> Group instances (in scope):
       instances/denboer1989  - Z/5Z, single 5-cycle generator sigma=(0 1 2 3 4)
       instances/kim2025      - Z/5Z, 5 cyclic-rotation generators, biased weights 1/5 +/- eps
       instances/s5           - S_5 as Coxeter A_4 with 4 adjacent transpositions
       instances/s5x5         - S_5 x S_5 in S_10, two disjoint 5-piles, |G|=14400
|
|--> Security analysis (security/):
      |
      |--> Random-walk uniformity / mixing
      |      pgg_uniform_security.v   - uniform_security_witness, exact eps=0 (regular transitive)
      |      pgg_mixing.v             - symm_ds_TV_bound: TV <= sqrt(N) * alpha^L
      |      pgg_schreier.v           - SchreierCertificate; security_witness_schreier
      |      pgg_schreier_weighted.v  - WeightedSchreierCertificate; unif_offdiag_var_dist
      |--> Abelian limitation
      |      pgg_abelian_collapse.v   - search_space M L <= C(L + ngens', ngens')
      |                                  (polynomial collapse, justifies needing non-abelian groups)
      |--> Entropy / asymptotic
      |      pgg_entropy_security.v   - EntropyWitness; Pinsker route eps = sqrt(2*(log N - H_min))
      |      pgg_weighted_entropy.v   - var_dist_from_weighted_entropy (fiber-entropy -> TV)
      |      pgg_word_analysis.v      - RAAG trace combinatorics for word-eval fiber sizes
      |--> SecurityWitness
             reconstruct/algebraic_rigidity.v
               record (sw_L, sw_bound_eps, sw_rho_dist, sw_bound)
               with optional sw_exact (closed-form equality) and
               sw_asymptotic (spectral-gap envelope);
               common interface every security route exports into.

|--> Recoverability analysis (reconstruct/):
     |
     |--> Recovery schemes
     |      pgg_sum_mod.v        - sum-mod-N (reconstruct_sum, preserves_sum_mod)
     |      product_threshold.v  - product-mod-N for s5x5 (split_secret/combine_secret)
     |      pgg_threshold.v      - RampConfig + ramp_threshold (recoverable bits per covered edges)
     |
     |--> Classifier for algebraic curves (organised by genus):
            covering_scheme.v    - CoveringData (Riemann-Hurwitz) + CoveringScheme
                                   with cs_gap : ts_T <= ts_k + 2 * cd_genus
            curve_realisation.v  - realised_by_curve predicate, RealisedCoveringData wrapper
            multi_covering.v     - intransitive aggregator (sum/max genus over components)
            cover_genus0.v       - genus-0 = Reed-Solomon / Shamir slice (shamir_exact)
            cover_genus1.v       - elliptic_gap; generic higher_genus_gap_bound
            cover_genus2.v       - hyperelliptic slice (genus2_gap, genus2_vs_genus1)
            ag_code.v            - algebraic-geometry code; ag_min_dist_lb: n - (k+g-1) <= d_min
            hyperelliptic_code.v - hyp_goppa_wt, dual_min_dist, hyp_priv_surj
            rs_code_5sheets.v    - concrete GF(5) RS pieces; RS5_witness_trivial
            pgl_bound.v          - pgl_card q = q*(q^2-1); pgl_card_5 = 120; pgl2_5_eq_s5

|--> AlgebraicRigidity (reconstruct/algebraic_rigidity.v, cover_tradeoff.v):
       AlgebraicRigidity record = (ar_security : SecurityWitness, ar_threshold : ThresholdWitness),
       where ThresholdWitness carries cs : CoveringScheme M and
       genus-0 -> |G| <= pgl_bound M.
       Trade-off theorem (cover_tradeoff.v, security_threshold_tradeoff):
         either  cd_genus = 0  /\  |G| <= pgl_bound M  /\  ts_T <= ts_k
         or      0 < cd_genus  /\  ts_T <= ts_k + 2 * cd_genus.
       Companions: large_group_forces_gap (contrapositive), search_gap_tradeoff.
```

## Changes from the rough draft

- `SecurityWitness` is a real record but it lives in
  `reconstruct/algebraic_rigidity.v`, not under `security/`. The arrow
  should cross the security/reconstruct boundary, because that record
  is exactly what couples the two halves.
- The recoverability classifier is organised by *genus*, not by code
  family, with `covering_scheme.v` as the shared abstraction and
  `cover_genus{0,1,2}.v` as the slices. Shamir and Reed-Solomon are
  the genus-0 corner of that classification, not a separate category.
- The trade-off theorem is not only "big group vs recovery"; the
  precise statement is a disjunction: genus 0 with PGL-bounded group
  and exact threshold, or positive genus with gap `2g`. The diagram
  should hint at the two-branch shape so the meaning of "trade-off"
  is unambiguous.
- The session-typed protocol shell (`card_exchange_pismc.v`) and the
  `multi_covering.v` intransitive aggregator are missing from the
  rough draft but both are load-bearing, the latter especially for
  s5x5.

## Slide-fit horizontal version (4-column, 16:9)

The vertical tree above does not fit a 16:9 slide. The horizontal
4-column form below sacrifices a little structural accuracy (security
and recoverability are siblings, not in series) for slide-fit. Each
column's contents are described by meaning rather than by Rocq
identifier name, so a reader who does not know the codebase can still
follow.

```
┌────────────────────────────┐    ┌─────────────────────────────┐    ┌─────────────────────────────┐    ┌────────────────────────────┐
│ PROTOCOL + INTERFACE       │    │ SECURITY                    │    │ RECOVERABILITY              │    │ ALGEBRAIC RIGIDITY         │
│                            │    │                             │    │                             │    │                            │
│ Card-game-based MPC flow,  │    │ Shuffle becomes             │    │ How a qualified subset of   │    │ Once the algebraic choice  │
│ session-typed:             │    │ indistinguishable from      │    │ players recovers the secret │    │ (group, permutation rep,   │
│ dealer / verifier / player │ ──▶│ uniform after enough        │ ──▶│ from their cards:           │ ──▶│ generator set) is fixed,   │
│                            │    │ rounds:                     │    │  · combine shares by        │    │ the security ceiling AND   │
│ Plug-able instance =       │    │  pgg_uniform_security       │    │    addition mod N           │    │ the reconstruction gap     │
│                            │    │  pgg_mixing                 │    │  · combine shares by group  │    │ are JOINTLY determined.    │
│  · ambient group, deck     │    │  pgg_schreier(_weighted)    │    │    multiplication in        │    │ No free parameter to       │
│    size, acting subgroup   │    │                             │    │    S_5 x S_5                │    │ trade one against the      │
│  · how group elements      │    │ Abelian groups hide only    │    │  · graded recovery between  │    │ other after the fact.      │
│    permute card positions  │    │ poly-many shuffle words,    │    │    k and T (partial leak    │    │                            │
│  · which shuffles are      │    │ so need non-abelian:        │    │    before full recovery)    │    │ Trade-off, in observables: │
│    available (group        │    │  pgg_abelian_collapse       │    │                             │    │                            │
│    presentation by chosen  │    │                             │    │ Recovery as evaluation on   │    │   T = k       ⇒            │
│    generators)             │    │ Long-run min-entropy and    │    │ a branched cover of the     │    │     |G| ≤ Klein cap        │
│  · biased mixing (prob.    │    │ spectral-gap estimates      │    │ projective line; genus from │    │                            │
│    of choosing each        │    │ bound total variation (TV)  │    │ Riemann-Hurwitz:            │    │   |G| > Klein cap  ⇒       │
│    shuffle)                │    │ distance:                   │    │   genus 0  Reed-Solomon /   │    │     T > k                  │
│                            │    │  pgg_entropy_security       │    │           Shamir            │    │                            │
│ In-scope instances:        │    │  pgg_weighted_entropy       │    │   genus 1  elliptic         │    │ Klein cap = order of A_5   │
│  denboer1989  Z/5Z, 1-cyc  │    │  pgg_word_analysis          │    │   genus 2  hyperelliptic    │    │ (= 60), the largest        │
│  kim2025      Z/5Z, biased │    │                             │    │   higher   general          │    │ exceptional finite         │
│  s5           Coxeter A_4  │    │ → SecurityWitness           │    │           algebraic-        │    │ subgroup of PSL_2 in       │
│  s5x5         |G| = 14400  │    │                             │    │           geometry code     │    │ Klein's 1884               │
│                            │    │                             │    │ → CoveringScheme +          │    │ classification.            │
│                            │    │                             │    │   ThresholdWitness          │    │                            │
└────────────────────────────┘    └─────────────────────────────┘    └─────────────────────────────┘    └────────────────────────────┘
```

Reading caveats for the slide:

- The L-to-R arrows are narrative, not strict dependency. Security and
  recoverability are siblings; both depend on the leftmost column and
  both feed AlgebraicRigidity.
- "Klein cap" lives only on the AlgebraicRigidity side. It bounds `|G|`
  when the cover has genus 0, via Klein's 1884 classification of
  finite subgroups of PSL_2 (the largest exceptional case is A_5 with
  order 60). It is unrelated to Riemann-Hurwitz, which lives on the
  recoverability side and gives the genus from the ramification data
  of the cover.
- The trade-off block uses only `|G|`, `T`, `k`, and the Klein cap.
  Genus quantifies the size of the gap when `|G| > Klein cap` (the gap
  is `2g`), but the slide does not need to surface that constant.
