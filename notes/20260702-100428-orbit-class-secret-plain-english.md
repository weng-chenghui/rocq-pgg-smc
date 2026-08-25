# What "orbit-class secret" means, in plain English and card terms

Date: 2026-07-02

Plain-language definition of the orbit-class-secret mechanism, the Item-1 novel
contribution of the shuffle-matters ladder. Companion to the ladder report
[[20260701-175221-report-shuffle-matters-group-ladder]] and the verification
template [[20260701-173005-shuffle-matters-verification-template]]. Written after
two deep-research passes (the second adversarial); the novelty verdicts are at the
bottom.

## The one-sentence answer

The secret is not printed on any card and is not "where the hearts are." It is
which FAMILY the whole heart-layout belongs to, a property the shuffle can never
change.

## The card picture

Deal N face-down cards on N spots, with a fixed count of hearts and clubs, say 4
hearts and 4 clubs. Which spots hold the hearts is the "layout". Before anyone
looks, apply one shuffle picked at random from a fixed rulebook of allowed moves.

The rulebook can rearrange the hearts, but it cannot turn every heart-layout into
every other one. The layouts split into a few FAMILIES: two layouts are in the
same family when some allowed move carries one to the other. "Orbit" is the math
word for one such family. The secret is which family your layout is in.

Two consequences make it a good secret:

- No shuffle ever leaks it, because the allowed moves keep you inside your family.
- You cannot read it off a single card. You must flip enough cards to reconstruct
  the shape of the heart-set before you can tell which family it is.

## The two concrete schemes, in card terms

- A5 on 6 spots (chirality). 3 hearts among 6 spots. The 20 possible heart-triples
  fall into exactly two families of 10, mirror images of each other, like a
  necklace that is either left-handed or right-handed. The secret is the
  handedness. Rotating or flipping the necklace (the allowed moves) never changes
  the handedness, and two beads tell you nothing about it. Privacy threshold k=2.

- PGL(2,7) on 8 spots (cross-ratio). 4 hearts among 8 spots laid out as a
  projective line, shuffled by "Möbius moves". The 70 possible heart-quadruples
  split into two families of sizes 42 and 28, told apart by a geometric property
  of the four heart-spots called their cross-ratio, roughly whether the four
  points sit in a special harmonic configuration or a generic one. The secret is
  which family, the 42 or the 28. Privacy threshold k=3.

## Why this is the novel piece

Every other card protocol hides a number or a bit written on a card. Den Boer
hides an AND-bit; Shinagawa hides a Z/nZ value via a card's rotation angle. Here
nothing is written down. The secret is a class of the entire arrangement that only
a rich enough shuffle group can define, and it stays hidden until enough cards are
flipped to determine the shape. The "secret = which orbit of a subset under a
group action" mechanism is what the literature audit found nobody has used in a
card or physical protocol.

## Novelty verdicts (two deep-research passes, corpus-bounded)

- Orbit-class secret (this note): NOVEL. Near-neighbours all hide a scalar, not a
  subset's family (Shinagawa polygon/dihedral cards, the invariant-based
  cross-ratio scheme arXiv:2505.08115, Pieprzyk-Zhang permutation secret sharing).
- The deck-colour hypergeometric bridge lemma: NOVEL as a named lemma, though it
  is a corollary of already-cited classical facts.
- The machine-checked formalization in a proof assistant: NOVEL. Closest is
  Koch-Schrempp-Kirsten (ASIACRYPT 2019, SAT bounded model checking) and
  Mizuki-Shizuya 2014 (pen-and-paper abstract machine).
- The transitivity ladder itself: PARTIALLY PREEMPTED. The mechanism and the exact
  ladder are published (Kaplan-Naor-Reingold 2005/2009; Finucane-Peled-Yaari
  2015), but only as pseudorandomness or design results. The coalition-privacy
  framing is the surviving novel piece; scope any claim to that.

Bound: all verdicts are corpus-bounded. Not fully reached: 2023-2026 card-crypto
follow-ups (Ruangwises, Toyoda, Miyahara, Abe, Nishida), the
cryptographic-group-actions / isogeny secret-sharing line, and
t-design-as-access-structure secret sharing. Sources saved in
~/.claude/research-kb.

## PGG framework fit (mapped against live code, 2026-07-02)

The orbit-class secret and a PGL(2,7) shuffle fit the current PGG flow and records
with NO record-shape change. It is an s5-style secret-sharing family (no input
prologue) with a den Boer-style bool secret, shuffled by ONE uniform draw from the
whole group (den Boer word-length-1 mode, not an s5 random walk).

- Fits unchanged: the monodromy slot `pgg_rho : {morphism G >-> {perm 'I_N}}`
  (s5 already plugs full S_5 there); `PGGInterface` (T=8, starts=ord_tuple 8);
  `MonodromyProfile`; `SecurityWitness`; `rp_recon_invariant` (the orbit-class
  secret IS a monodromy-invariant, the cleanest fit); the `trace_secrecy_of_view`
  keystone.
- New content in existing slots: the PGL action + 3-transitivity; `ts_recon` =
  cross-ratio orbit classifier; `ts_encode` = canonical representative per orbit;
  security with epsilon = 0 exact (uniform over a transitive group makes the
  single-card marginal exactly uniform, axiom-free, cleaner than s5's Schreier
  walk).
- The one real extension: a THIRD privacy mechanism beyond additive one-time-pad
  (s5) and concrete enumeration (den Boer), namely "t-transitive shuffle => any
  <=t coalition view is hypergeometric and secret-independent => ts_private".
- Not involved: the Klein / Riemann-Hurwitz / pgl_bound rigidity machinery is a
  DIFFERENT role of PGL (the genus-0 automorphism ceiling on the AG-recovery side);
  the orbit-class scheme uses reveal-all recovery, no AG cover. No gray-zone
  (size 4-6) leakage witness: prove only the k=3 security direction plus recovery.

## Shape probe verdict (rocq-prover, 2026-07-02)

All three risky shapes were drafted in `.local/wip/pgl_shape_probe.v` and the file
COMPILES with real coqc against the live framework. The instance is FEASIBLE with
zero framework plumbing. Two findings revise the plan.

1. Do NOT build pgl2's quotient action (several hundred lines). Use the framework
   template `@Gen_PGGTypes 1 6 sigmas`: pgg_gT = {perm 'I_8}, pgg_N' = 7,
   pgg_rho = the identity inclusion G into S_8. PGL(2,7) as a subgroup of S_8, via
   its two Möbius generators z -> z+1 and z -> -1/z, carries the monodromy for
   free. pgl2 stays only for the Klein cardinality check |pgl2 F_7| = 336.
   3-transitivity: `ntransitive 3 (@pgg_rho M @* pgg_G M) [set: 'I_8] 'P`.
2. Soundness correction: PGL(2,7) is SHARPLY 3-transitive, so the pointwise
   stabiliser of any 3 points is trivial. Privacy therefore CANNOT be witnessed by
   permuting shares with a group element fixing the coalition (it would be the
   identity, unable to flip the orbit bit), UNLIKE the sum-mod scheme. The
   ts_private witness must be a genuine RE-DEALING (a different heart 4-subset in
   the other orbit matching colours on the <=3 revealed cards), sound because
   ts_private only asserts such a sharing EXISTS. So rp_monodromy powers
   correctness only; privacy comes purely from "both orbits survive fixing <=3
   colours".

Remaining work is mathematics, not plumbing: the `pgl_3transitive` proof, the
cross-ratio PGL-invariance (`orbit_recon_invariant`), and the combinatorial
`ts_private` bridge. Detailed formalization plan:
[[20260702-114631-pgl27-orbit-class-ROCQ-formalization-spec]].
