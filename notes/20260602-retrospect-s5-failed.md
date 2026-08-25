 Retrospective: why the S_5 "T>k recovery scheme" was a dead end, and why it stayed hidden

 Context

 The project set out (commit 8d0b10b, 2026-03-12) to deliver a chain
 large monodromy group G -> positive genus -> threshold gap T>k, wired into the
 S_5/Bring monodromy. The recovery-scheme plan of 2026-06-02 (preserved below) was the
 latest attempt. Audit established a no-go: no positive-genus, secret-encoding,
 S_5-invariant linear code over GF(5) of length 6 exists, because the framework pins
 |F| = N = sheet count = 5, so the natural permutation module is modular (5 | 5)
 and uniserial, and its only secret-encoding invariant submodule is genus-0. This is
 why the live s5 cover uses sum_mod at gap 0 with cd_genus = 4 living only on the
 rigidity side.

 This retrospective reconstructs, from git history and the design notes, how the dead
 end was built, why it was not discoverable earlier, why AI-driven formalization did
 not catch it, and what to enforce next time. Every claim below is anchored to a
 commit or a note line.

 The trace (each obstacle was locally resolved, which is why it never accumulated)

 When: 2026-03-12
 Artifact: 8d0b10b
 What happened: Framework born: genus0_exact, security_threshold_tradeoff, large_group_forces_gap. Headline = "large G forces a gap".
 The signal that appeared: 15 of 33 results admitted "for later delegation".
 How it was routed around: Admits deferred; the deliverable theorem stated as an upper bound (see below).
 ────────────────────────────────────────
 When: 2026-03-14
 Artifact: 20260314_monodromy_walk_vs_shamir_value.md
 What happened: Monodromy walk and recovery declared independent modules, connection "one-directional".
 The signal that appeared: The obstruction lives in their interaction.
 How it was routed around: Interaction declared one-way, never re-examined.
 ────────────────────────────────────────
 When: 2026-03-16
 Artifact: 3d3be45 + 20260316_share_compatible_analysis.md
 What happened: ts_compatible proven unsatisfiable for non-trivial monodromy (monodromy permutes coordinates, not values).
 The signal that appeared: First hard signal that the intended construction cannot exist. The note itself says the sound fix "requires the deep algebraic geometry
   this project deliberately axiomatized away" (lines 195-197).
 How it was routed around: Definition weakened to ts_perm_compatible (coordinate permutation), which is satisfiable. The weakened condition is exactly the full-S_5

   symmetry that produces the no-go, but it typechecked, so it read as progress.
 ────────────────────────────────────────
 When: 2026-03
 Artifact: bba533a, c8f12d7
 What happened: Dual minimum distance, dual_root_poly axiomatized over an abstract field F.
 The signal that appeared: The hard AG facts were never built.
 How it was routed around: Axiomatized "as true-but-tedious"; field left abstract.
 ────────────────────────────────────────
 When: 2026-05-04
 Artifact: 418bc81
 What happened: pgl_bound off-by-one fixed: it had used sheet count as field size (N(N^2-1) = 120 = |S_5| at N=5).
 The signal that appeared: The same root confusion |F| vs sheet count, surfacing independently. Commit text: "no genus-0 cover can carry an S_5 monodromy ...
   Bring's curve at g=4 is the next candidate."
 How it was routed around: Fixed only on the rigidity side (automorphism group genus). The recovery-code genus was never examined.
 ────────────────────────────────────────
 When: 2026-05-04
 Artifact: 0b7b4b4
 What happened: curve_realisation: replace false discharges (120 <= 60) with an axiom realised_by_curve, citing Bring (Edge 1978).
 The signal that appeared: Honest move, but the curve never becomes a Rocq object, so the recovery code is never built.
 How it was routed around: cd_genus = 4 (rigidity) now diverges from recovery genus = 0 (sum_mod). The two are never reconciled.
 ────────────────────────────────────────
 When: 2026-05-17
 Artifact: 20260517_cycle5_ag_genus_scheme_plan.md
 What happened: The near-miss. Instantiated F := 'F_5, n=6, k=4, g=1, but kept ev axiomatic (Hypothesis cycle5_ev_rank), and added cycle5_goppa_wt_strong as an
   axiom forcing d>=3. Risk 2 (lines 292-295): "a D_5-orbit on E has size 5 or 10, not 6 ... the abstract position is the framework's secret slot, not a geometric
   point on E."
 The signal that appeared: This is the obstruction, stated in plain words.
 How it was routed around: Filed as a docstring/documentation issue. The false existence claim was assumed as an axiom with a plausible geometric justification.
 ────────────────────────────────────────
 When: live
 Artifact: rigidity_s5_instance.v
 What happened: s5_ts := sum_mod_scheme 3 4, ts_T = ts_k = 5, cd_genus = 4. security_threshold_tradeoff satisfied via the positive-genus disjunct, but cs_gap :
 ts_T
    <= ts_k + 2g reads 5 <= 13, i.e. gap 0.
 The signal that appeared: Headline delivered none of its promised content.
 How it was routed around: Vacuity accepted; Print Assumptions is clean.

 Why it was not discoverable earlier (five structural reasons)

 1. The flagship theorem is an upper bound, not the deliverable. security_threshold_tradeoff (cover_tradeoff.v:140-149) ends in ... 0 < cd_genus /\ ts_T <= ts_k +
 2*cd_genus. The gap branch is <=, satisfiable at ts_T = ts_k for any genus. The goal was T > k, but the theorem never states ts_T > ts_k. So "the theorem holds"
 was always reachable and never forced the existence question.
 2. The field stayed abstract and the hard facts were axiomatized. The single computation that refutes the construction, namely instantiate F := GF(5) and exhibit
 one invariant positive-genus code, was deferred indefinitely. The kernel checks soundness relative to assumed hypotheses, never their satisfiability at a model.
 3. Two genera were never given two names. Rigidity genus (automorphism group of the curve, cd_genus = 4) and recovery genus (genus of the code that produces the
 gap) are different objects. Collapsing both into cd_genus let a genus-4 automorphism group stand in for a genus-4 recovery code. Once curve_realisation made them
 diverge, nothing compared them.
 4. Every fix was locally correct and made the build greener. Weaken the condition, axiomatize the dual, fix the bound, cite the curve: each step closed a goal and
 removed a red mark. That is precisely why the global impossibility never accumulated into a visible contradiction.
 5. The false axiom was mechanically indistinguishable from an honest one. cycle5_goppa_wt_strong is not numerically false, not cooked arithmetic, and shows up in
 Print Assumptions as an ordinary axiom. It reads exactly like the legitimate "cite the geometry, defer the formalization" pattern. Only re-deriving the cited fact
 at the concrete (n,k,g,|F|) refutes it, and that re-derivation is exactly what "axiomatize away" skips.

 Why AI-driven formalization failed here specifically

 - AI optimizes the checkable success signal. Compiles, Qed, clean Print Assumptions, hypotheses discharged. All four were achievable indefinitely while the target
 was impossible. The proof assistant's guarantee is orthogonal to the question that mattered: do the assumptions have a model at the concrete instance.
 - AI treats "axiomatize the hard part" as risk-free deferral. It assumes the deferred fact is true-but-tedious and does not, by default, ask whether the
 assumption is satisfiable at the concrete parameters. cycle5_goppa_wt_strong is the AI confidently asserting a false existence claim under a plausible-sounding
 geometric justification.
 - AI resolves "unsatisfiable" by weakening the definition until it typechecks. ts_compatible -> ts_perm_compatible is the path of least resistance and the path
 away from discovery. Unsatisfiability of the intended condition was evidence the target is unreachable; it was read as a definition bug instead.
 - AI did not connect two appearances of one root confusion. The pgl off-by-one and the modular-module obstruction are the same |F|-vs-sheet-count coincidence.
 Each was patched in isolation.
 - The audits that ran were per-file and per-claim. Math, code, and naming audits catch local defects. None asked the cross-cutting question: does the flagship
 deliverable hold non-vacuously at the smallest real instance with all axioms instantiated.

 What to prevent in future (enforceable rules for math-heavy work)

 1. Instantiate before you abstract-and-axiomatize. For any existence-flavored hypothesis (a code, a divisor, a curve, a map with property P), build the smallest
 concrete witness at the concrete parameters first. Generalize to Variable/axioms only after one concrete model exists. Instantiation that replaces Variable F with
 'F_5 but keeps ev as a Hypothesis is not instantiation; it relocates the axiom.
 2. Never axiomatize a hard part you have not confirmed is true at the target parameters. Honest axiomatization is only honest if the cited fact holds at the
 instance. Require the citation to be checked at the exact field, degree, and genus, because that is where modular coincidences bite. "AG codes of this kind exist
 in general" does not license "this AG code exists over GF(5) at length 6".
 3. State the deliverable theorem as the claim you want. If the goal is T>k, the theorem must assert ts_T > ts_k, not ts_T <= ts_k + 2g. Audit every headline
 theorem with one question: is this vacuously satisfiable by the degenerate instance? If yes, it is a sanity check, not a deliverable.
 4. Name every quantity the math distinguishes, even when they coincide in easy cases. When one symbol carries two interpretations that can diverge, give it two
 symbols and add a lemma relating them. The absence of that lemma is the bug (rigidity genus vs recovery genus).
 5. Treat "unsatisfiable" or "I had to weaken the definition to typecheck" as a STOP, not a step. The first hypothesis must be that the target is unreachable.
 Weakening to satisfiability requires an explicit argument that the weakened version still delivers the headline, plus a re-check that the headline is not now
 vacuous.
 6. Run one realizability audit per headline claim, at the concrete instance, with all axioms instantiated. Separate from per-file math/code/naming audits. Its
 only job: does the flagship deliverable hold non-vacuously at the smallest real instance. This is the audit none of the six design notes ran.
 7. Keep a registry of root confusions and grep for recurrence. The |F|-vs-sheet-count confusion appeared twice. When a root confusion is fixed in one place,
 search the design for the same shape elsewhere before declaring it closed.

 What this adds beyond the existing 8 methodology lessons (feedback_methodology_lessons)

 The closest existing lessons are 4 (hypotheses and axioms are the human's responsibility) and 7 (per-instance instantiation surfaces framework defects). The new
 content:

 - Fourth category of fake. Lesson 4's taxonomy (false claim, cooked data, honest axiomatization) needs a fourth and most dangerous member: the plausible-false
 axiom, a false existence claim with a correct-looking citation, indistinguishable from honest axiomatization by any mechanical check, refuted only by concrete
 instantiation. Evidence: cycle5_goppa_wt_strong.
 - Instantiation needs a concrete witness, not an instance-shaped axiom bundle. Lesson 7 only has teeth if instantiation reaches a vm_compute-checkable witness.
 The cycle5 plan "instantiated" F := 'F_5 yet hid the defect because the instance was still axiomatic.
 - The deliverable must be the theorem statement, not an upper bound that contains it. Vacuous satisfiability of a flagship theorem is the signature of a buried
 impossibility. New standalone lesson.
