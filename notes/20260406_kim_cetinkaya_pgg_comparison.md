# Kim & Cetinkaya 2025 vs. PGG: Concept Mapping

**Date:** 2026-04-06  
**Paper:** "Confidentiality in a Card-Based Protocol Under Repeated Biased Shuffles" (Kim & Cetinkaya, arXiv:2511.05111, November 2025)

## Concept Mapping Table

| Concept | Kim & Cetinkaya 2025 | PGG (Weng et al.) | Mapping |
|---|---|---|---|
| **Group** | Z_5 (cyclic, implicit — never named as such) | Arbitrary finGroupType; instances include cyclic, S_5, RAAGs, free groups | PGG generalizes; Z_5 is one abelian instance in `pgg_abelian.v` |
| **Shuffle** | Random cyclic cut on 5 cards (rotation by s positions) | Generator application `tnth sigmas i` composed via word evaluation | Direct — a cyclic cut is a single generator of Z_5 |
| **Repeated shuffles** | T independent biased cuts, modeled as Markov chain P^T | L-length word `pgg_word L` = L.-tuple of generator indices, evaluated as product | Direct — word of length L = T repeated shuffles |
| **Bias / non-uniformity** | Explicit: P(s=0) = 1/5 − ε, P(s≠0) = 1/5 + ε/4 | Implicit via fibers: `fiber_at(x) = \|{w : word_eval(w) = x}\|`; uniform over words, non-uniform over group elements | Different mechanism — Kim puts bias on step distribution; PGG gets non-uniformity from word-to-element non-injectivity |
| **Transition matrix** | 5×5 doubly-stochastic matrix with entries a, b | Schreier transition matrix `schreier_transition` ∈ M_(N×N) | Direct generalization — Kim's matrix is the Schreier matrix of Z_5 acting on 5 points |
| **Eigenstructure** | λ₁=1, λ₂=…=λ₅=a−b; closed-form P^T | Spectral gap `sc_lambda_gap`; convergence bound √N·(1−gap)^L | PGG abstracts to spectral gap certificate; Kim computes exact eigenvalues for Z_5 |
| **Convergence / mixing** | Exponential decay \|a−b\|^T → 0 | `var_dist ≤ √N · (1 − λ_gap)^L` | Same exponential mixing, PGG gives general bound vs. Kim's exact formula |
| **Security definition** | \|P(c_I = I \| c_F = F) − 1/2\| (posterior bias on Alice's bit) | `var_dist(adversary_marginal, uniform)` (statistical distance) + entropy via Pinsker | Related but different — Kim uses posterior probability deviation; PGG uses variation distance and KL divergence |
| **Confidentiality threshold** | T ≥ ln(…)/ln\|a−b\| shuffles needed for bound C | Collusion bound: `var_dist ≤ ε + 2(T−1)/N` | Both give concrete shuffle-count bounds; PGG's is multi-party |
| **Protocol** | Five Card Trick (den Boer 1990), AND gate only | General card protocol with split/compute/outcome phases | PGG generalizes; Five Card Trick is one instance |
| **Number of parties** | 2 (Alice & Bob) | T parties with collusion bound | PGG generalizes to multi-party |
| **Card encoding** | rB/Br encodes 0/1 positionally | `encode_bit g b s` using involution g on sheet pair | PGG abstracts the encoding via group involution |
| **Decode correctness** | Pattern-matching on revealed face-up cards | `cs_decode (σ p.1) (σ p.2) = b` proved for commuting σ | PGG proves equivariance algebraically |
| **Generator weights** | Non-uniform: each cut value has explicit probability | Uniform: each generator chosen with prob 1/Tg | **No mapping** — PGG assumes uniform generator sampling; Kim's core contribution (biased step dist) has no PGG counterpart |
| **Parity oscillation** | When a < b, leakage oscillates by parity of T | No counterpart | **No mapping** — artifact of biased step distribution |
| **Fiber analysis** | Not present (single generator, bijective action) | `fiber_at(x)` counting words mapping to same element | **No mapping in Kim** — fibers are trivial for Z_5 with one generator |
| **RAAG / trace equivalence** | Not present | Commutation graph on generators; trace-equivalent words | **No mapping** — Kim has only one generator |
| **Collusion (multi-party)** | Not present (2-party only) | Collusion bound with T−1 observed endpoints | **No mapping in Kim** |
| **Formal verification** | Pen-and-paper proofs | Machine-checked in Rocq/Coq with MathComp + Infotheo | Different methodology |
| **Information measure** | \|posterior − 1/2\| (raw bias) | Shannon entropy H, KL divergence D, Pinsker inequality | PGG richer; Kim's measure is a special case |

## Key Takeaway

The two works address the **same mathematical phenomenon** (random walks on groups governing card-shuffle security) from complementary angles:

- **Kim & Cetinkaya**: Deep, exact analysis of one specific protocol (Five Card Trick) with **biased step distributions** — their unique contribution with no PGG counterpart.
- **PGG**: Broad, abstract framework for **arbitrary groups and multi-party protocols** with uniform generator sampling — fibers, RAAGs, collusion bounds, and spectral certificates have no counterpart in Kim.

The most natural extension would be to add **weighted generator sampling** to PGG (replacing uniform 1/Tg with arbitrary weights), which would subsume Kim's bias model as a special case.
