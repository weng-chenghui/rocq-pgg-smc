# The literature's constant for the upper bound lemma (looked up 2026-09-21)

Retrieval by a Sonnet agent through the research knowledge base (slices
`Diaconis1988-ch3-upper-bound-lemma`, `LevinPeresWilmer2017-ch12-eigenvalues`);
AUDITED by the main session against the sources, as recorded below.

1. Persi Diaconis, "Group Representations in Probability and Statistics", IMS
   Lecture Notes-Monograph Series vol. 11, 1988, Chapter 3 "Random Walks on
   Groups", Section B, page 24 (page header "24 Chapter 3B"). The label as
   printed is "LEMMA 1. (Upper bound lemma)", not "Proposition 2". The
   variation distance of the book is `||P - Q|| = max_A |P(A) - Q(A)| =
   (1/2) sum_s |P(s) - Q(s)|` (p. 21). The proof's first line reads
   `4 ||Q - U||^2 = { sum_s |Q(s) - U(s)| }^2 <= |G| sum_s |Q(s) - U(s)|^2 =
   sum* d_rho Tr(Q^(rho) Q^(rho)*)`.
   https://projecteuclid.org/ebook/download?urlId=10.1214/lnms/1215467412&isFullBook=false
   Main session's check: the label, the page header and the shape of the
   proof line (the constant 4 on the left, the squared sum of absolute
   differences) were read in the OCR text of the fetched chapter. The Project
   Euclid copy is an OCR scan whose text layer garbles symbols; the agent read
   the formulas off page images. Provenance in the knowledge base: ocr.
2. David A. Levin, Yuval Peres, Elizabeth L. Wilmer, "Markov Chains and Mixing
   Times", 2nd ed., AMS 2017, Chapter 12, Lemma 12.18, pp. 172-173: for a
   reversible chain, (i) `4 ||P^t(x,.) - pi||_TV^2 <= sum_{j>=2} f_j(x)^2
   lambda_j^{2t}`, and (ii) if the chain is transitive,
   `4 ||P^t(x,.) - pi||_TV^2 <= sum_{j>=2} lambda_j^{2t}`.
   https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf
   Main session's check: read directly in the text layer of the authors' PDF.
3. Consequence (one line of algebra, not a printed corollary of either book):
   if every non-trivial eigenvalue has modulus at most beta, then
   `2 ||P^t(x,.) - pi||_TV <= sqrt(N - 1) beta^t <= sqrt(N) beta^t`. The left
   side is infotheo's `var_dist`, so the tree's field
   `var_dist ... <= sqrt(N) * (1 - lambda_gap)^L` is the literature's bound
   with no factor lost, and a display `d_TV <= sqrt(N) * rate^L` states HALF of
   what the field needs on its left side.
4. Not obtained: Diaconis and Shahshahani 1981 (paywalled).
