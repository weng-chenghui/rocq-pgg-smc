(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Algebraic Rigidity: One Algebraic Choice Determines Security + Threshold  *)
(*                                                                            *)
(* Given a monodromy representation with generators M, the algebraic          *)
(* structure determines:                                                      *)
(*   1. Complexity — search_space L <= |G| (from pgg_interface.v)            *)
(*   2. Security — var_dist(endpoint, uniform) <= epsilon (endpoint bound)   *)
(*   3. Threshold — gap <= 2*genus, with genus-0 -> gap=0 (covering_scheme)  *)
(*                                                                            *)
(* The key insight: all three are consequences of the single algebraic        *)
(* choice (G, rho, sigmas). No further degrees of freedom exist.             *)
(*                                                                            *)
(* Galois-theoretic interpretation:                                           *)
(*   The fiber at a branch point consists of roots of the minimal polynomial *)
(*   of K(C) over K(X). The monodromy group G permutes these roots,         *)
(*   making G the Galois group of the Galois closure. This connects PGG     *)
(*   to Galois theory of function fields: the algebraic choice (G, rho,     *)
(*   sigmas) determines the field extension K(C)/K(X) up to isomorphism.    *)
(*   Note: this is conceptual — field arithmetic on roots is irrelevant     *)
(*   to the permutation action that PGG uses.                                *)
(*                                                                            *)
(* The endpoint-level security guarantee is packed in two layers. The bound   *)
(* layer is always present. The certificate layer attaches optional exact     *)
(* and asymptotic evidence for the same shuffle distribution, leaving the     *)
(* bound unchanged.                                                          *)
(*                                                                            *)
(* Records:                                                                   *)
(*   SecurityExact rho == optional exact-equality carrier:                   *)
(*                         var_dist(rho, uniform) = se_eps                   *)
(*   SecurityAsymptotic == optional geometric-convergence certificate         *)
(*   ShuffleMarginalBound R M == the bound layer: sw_L, sw_bound_eps,         *)
(*                          sw_rho_dist and the per-position sw_bound         *)
(*   ShuffleCertificateBundle R M == the certificate layer: scb_bound with    *)
(*                          the optional scb_exact and scb_asymptotic         *)
(*   ThresholdWitness M  == packages the covering scheme + PGL hypothesis     *)
(*   AlgebraicRigidity R M == combines a bundle and a threshold witness       *)
(*                                                                            *)
(*   See dropout_witness.v for [DropoutWitness], the capability-side          *)
(*   record that complements the structural ThresholdWitness here.            *)
(*                                                                            *)
(* Constructors:                                                              *)
(*   shuffle_bundle_of_bound == a bound with neither certificate attached     *)
(*   security_witness_fiber == bound from fiber-counted epsilon               *)
(*     Accepts any epsilon + proof; instances use vm_compute/case analysis.   *)
(*     Applicable to: OC (eps=1), S5 (eps=6/5), Star (eps=2(m+1)/(m+3))   *)
(*   security_witness_endpoint_inj == for perm_endpoint-injective groups             *)
(*     Epsilon = 2*(N - Tg^L)/N. Applicable to: NCycle, Abelian, Monster     *)
(*   security_witness_from_bound == bound from an arbitrary epsilon proof     *)
(*   security_witness_with_exact == bundle with the exact certificate         *)
(*                                                                            *)
(* Derived properties:                                                        *)
(*   ar_complexity      == search space bounded by |G|                        *)
(*   ar_genus_gap_dichotomy        == genus-0/bounded or genus>0/gap tradeoff           *)
(*   ar_search_gap_dichotomy == search space vs threshold gap                 *)
(*   ar_large_group_forces_gap == |G| > PGL -> genus > 0                    *)
(*   ar_gap_bound       == threshold gap <= 2*genus                          *)
(*   ar_protocol_correct == end-to-end protocol correctness                  *)
(*                                                                            *)
(* RAAG-specific derived properties:                                          *)
(*   ar_search_space_chain == search_space <= n_traces <= Tg^L               *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import perm_uniform pgg_interface pgg_weval_inj pgg_raag.
From pgg_smc Require Import pgg_collusion_bound pgg_security_solver.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.

(******************************************************************************)
(*     Record Definitions                                                     *)
(******************************************************************************)

Section algebraic_rigidity_records.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.
Let N' := pgg_N' M.
Let G := pgg_G M.

(** SecurityExact: an optional exact-equality carrier. Parameterised by the
    distribution rho so the exact-value proof is pinned to the same
    distribution a ShuffleCertificateBundle's marginal bound is stated at.
    Present exactly when a random walk's stationary marginal is known in
    closed form rather than only bounded, e.g. structured group orbits;
    absent for a fiber-counted or reducible-walk bound. *)
Record SecurityExact (rho : R.-fdist {perm 'I_N'.+1}) := MkSecurityExact {
  se_eps : R;
  se_exact :
    forall s : 'I_N'.+1,
    var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) rho)
             (fdist_uniform (card_ord N'.+1)) = se_eps
}.

(** SecurityAsymptotic: optional asymptotic convergence certificate.           *)
(* For group settings with a valid random walk (connected Schreier graph),     *)
(* the variational distance converges to 0 geometrically in L.                *)
(*                                                                             *)
(* This is None for:                                                           *)
(*   - Uniform dealing (no random walk, e.g., den Boer five-card)             *)
(*   - Disconnected Schreier graphs (e.g., cyclic/1-gen, abelian/disjoint)    *)
(*   - Instances where the spectral gap has not yet been formalized           *)
(*                                                                             *)
(* Mirrors SchreierCertificate (pgg_schreier.v) at the bundle level.          *)
(* Cannot reuse SchreierCertificate directly due to circular dependency:       *)
(*   pgg_schreier.v imports algebraic_rigidity.v.                              *)
(*                                                                             *)
(* sa_rho_L maps word length L to the endpoint distribution — typically        *)
(* instantiated as rho_from_words L sigmas, but kept abstract here to          *)
(* avoid requiring {perm 'I_N} typed generators (which Gen_PGGTypes has        *)
(* but general MonodromyReprType may not).                                     *)
(* sa_eps_inf is the constant variation-distance floor: the bound is        *)
(*   var_dist (sigma s) uniform <= sa_eps_inf + sqrt(N) * (1 - gap)^L      *)
(* For irreducible Schreier walks (e.g. S_5) sa_eps_inf = 0 and the bound  *)
(* decays to 0. For reducible walks (e.g. S_5 x S_5 with pile-disjoint     *)
(* generators) the actual stationary distribution is uniform on the orbit, *)
(* and the gap to fdist_uniform is the constant sa_eps_inf (1 in infotheo's *)
(* un-halved L^1 var_dist convention; 1/2 in standard TV).                  *)
Record SecurityAsymptotic := MkSecurityAsymptotic {
  sa_spectral_gap : R;
  sa_eps_inf : R;
  sa_gap_pos : (0 < sa_spectral_gap)%R;
  sa_gap_le1 : (sa_spectral_gap <= 1)%R;
  sa_eps_inf_ge0 : (0 <= sa_eps_inf)%R;
  sa_rho_L : nat -> R.-fdist {perm 'I_N'.+1};
  sa_convergence : forall (L : nat) (s : 'I_N'.+1),
    (var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s)
                       (sa_rho_L L))
             (fdist_uniform (card_ord N'.+1))
    <= sa_eps_inf + Num.sqrt N'.+1%:R * (1 - sa_spectral_gap) ^+ L)%R
}.

(** ShuffleMarginalBound — the single-position marginal bound of a shuffle
    distribution against the uniform distribution on card positions. A
    constructor
    supplies a finite-word length, a stated epsilon, the analyzed
    distribution on permutation images, and the per-position proof that the
    one-card pushforward of that distribution is within epsilon of uniform.
    This is the always-present bound layer of the endpoint-security
    guarantee; ShuffleCertificateBundle below attaches optional exact and
    asymptotic evidence on top of it without changing this bound. *)
Record ShuffleMarginalBound := MkShuffleMarginalBound {
  (* sw_L is the finite-word length the distribution is read at. It is the
     length consumed by the dealer bridge (pgg_dealer_bridge.v) and by the
     SecurityParams of a CertifiedSolution. *)
  sw_L : nat;
  (* sw_bound_eps is the stated full-L1 upper bound on one endpoint marginal.
     It is a per-position quantity, not a coalition-view distance. *)
  sw_bound_eps : R;
  (* sw_rho_dist is the analyzed distribution on permutation images. *)
  sw_rho_dist : R.-fdist {perm 'I_N'.+1};
  (* sw_bound proves the bound separately for each starting position s. The
     guarantee is the endpoint marginal at one position; it is neither
     coalition-view privacy nor protocol security. *)
  sw_bound :
    forall (s : 'I_N'.+1),
    (var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) sw_rho_dist)
              (fdist_uniform (card_ord N'.+1)) <= sw_bound_eps)%O
}.

(** ShuffleCertificateBundle — a marginal bound together with the optional
    exact-equality and asymptotic-convergence certificates of the same shuffle
    distribution.
    A constructor supplies a ShuffleMarginalBound and, indexed on that bound's
    own sw_rho_dist, an optional SecurityExact and an optional
    SecurityAsymptotic.
    The two optional slots record the mechanism of the bound: both Some for a
    random walk with exact counting, exact only for uniform dealing, and both
    None for a fiber-counted bound. *)
Record ShuffleCertificateBundle := MkShuffleCertificateBundle {
  (* scb_bound is the marginal bound the bundle is built on. It is the only
     always-present component; the two fields below are attachments. *)
  scb_bound : ShuffleMarginalBound;
  (* scb_exact is an optional closed-form equality var_dist ... = se_eps at
     sw_rho_dist scb_bound. Attaching or emptying it leaves scb_bound and its
     epsilon unchanged. *)
  scb_exact : option (SecurityExact (sw_rho_dist scb_bound));
  (* scb_asymptotic is an optional geometric-convergence certificate for the
     same group. Attaching or emptying it leaves scb_bound and its epsilon
     unchanged. *)
  scb_asymptotic : option SecurityAsymptotic
}.

(* The cs_gap field of [tw_covering] (ts_T <= ts_k + 2 * cd_genus,
   from cover_tradeoff.v:gap_bound) is a privacy-vs-reveal gap, not
   a dropout-tolerance budget. Reconstruction in every concrete
   threshold scheme used here consumes the FULL share tuple:
   - rs_massey_exact (rs_massey_bridge.v:194): RS gives ts_T = ts_k
     at genus 0, so the gap is zero;
   - shamir_exact (cover_genus0.v:179): same statement at the
     transported covering scheme;
   - ag_massey_gap (ag_massey_bridge.v:85): AG-Massey gives
     ts_T <= ts_k + 2g for genus g > 0 codes, but its ts_recon
     (massey_recon_tuple, massey.v:369) still takes a full tuple.
   Operationalising T - k as "any T - k missing shares can be
   tolerated" requires a partial-erasure decoder, which is left
   as future work; see [reconstruct/dropout_witness.v] for the
   [DropoutWitness] record that records such a decoder when one
   is constructed.

   ThresholdWitness is purely structural: it says the covering's
   parameters fit together legally. DropoutWitness is a capability
   claim: a specific decoder exists meeting a specific bound.
   Different kinds of obligations, even though both attach to the
   same CoveringScheme. *)
Record ThresholdWitness := MkThresholdWitness {
  tw_covering : CoveringScheme M;
  tw_genus0_klein :
    cd_genus (cs_data tw_covering) = 0 -> #|G| <= klein_genus0_bound M
}.

(** AlgebraicRigidity: the single object pairing a security certificate
    bundle (ar_security) with a structural threshold witness (ar_threshold),
    both derived from the same monodromy representation M. Every derived
    property below, complexity, security, and threshold gap, reads off one
    of these two fields; the record exists so that one algebraic choice
    (G, rho, sigmas) is the single input all three guarantees share. *)
Record AlgebraicRigidity := MkAlgebraicRigidity {
  ar_security : ShuffleCertificateBundle;
  ar_threshold : ThresholdWitness
}.

End algebraic_rigidity_records.

Arguments SecurityExact {R} {M} rho.
Arguments SecurityAsymptotic {R} {M}.
(* Under Set Implicit Arguments the field scb_bound occurs in the type of
   scb_exact, so the bundle constructor would take it implicitly. The two
   constructor directives below restore the three- and four-explicit-argument
   shapes; the two record directives keep R and M explicit at the type. *)
Arguments MkShuffleMarginalBound {R M} _ _ _ _.
Arguments MkShuffleCertificateBundle {R M} _ _ _.
Arguments ShuffleMarginalBound R M : clear implicits.
Arguments ShuffleCertificateBundle R M : clear implicits.
Arguments ThresholdWitness M : clear implicits.
Arguments AlgebraicRigidity R M : clear implicits.

(** The certificate bundle carrying a marginal bound with neither optional
    certificate attached: the mechanism-agnostic case, used when the bound
    comes from fiber counting rather than from a random walk with known
    exact or asymptotic behavior. *)
Definition shuffle_bundle_of_bound R M (b : ShuffleMarginalBound R M)
  : ShuffleCertificateBundle R M := MkShuffleCertificateBundle b None None.

(******************************************************************************)
(*     Fiber-Counted ShuffleMarginalBound Constructor                         *)
(*                                                                            *)
(* For groups where perm_endpoint is NOT injective on achievable(L), the direct      *)
(* endpoint bound is invalid. Instead, each instance proves its own           *)
(* var_dist bound by fiber counting (case analysis, vm_compute, or            *)
(* parametric algebra). The constructor accepts epsilon + proof directly.      *)
(*                                                                            *)
(* Applicable to: OC (eps=1), S5 (eps=6/5), Star (eps=2(m+1)/(m+3))       *)
(******************************************************************************)

Section fiber_security.

Variable R : realType.
Variable m n' : nat.
Variable sigmas : m.+1.-tuple {perm 'I_n'.+2}.
Let M := Gen_PGGTypes sigmas.

(** The ShuffleMarginalBound assembled directly from a caller-supplied
    epsilon and its per-position var_dist proof, independent of how that
    proof was derived. Groups where perm_endpoint fails to be injective on
    achievable(L) have no uniform closed-form epsilon and must fall back to
    fiber counting (case analysis, vm_compute, parametric algebra); this
    constructor is the common landing point for whatever proof that fiber
    count produces. *)
Definition security_witness_fiber (L : nat)
    (Hlfree : @weval_inj M L)
    (epsilon : R)
    (Hbound : forall s : 'I_n'.+2,
      (var_dist (fdistmap (fun sigma : {perm 'I_n'.+2} => sigma s)
                         (rho_from_words L sigmas))
               (fdist_uniform (card_ord n'.+2)) <= epsilon)%O)
    : ShuffleMarginalBound R M :=
  @MkShuffleMarginalBound R M L epsilon
    (rho_from_words L sigmas) Hbound.

End fiber_security.

(******************************************************************************)
(*     Direct Endpoint ShuffleMarginalBound Constructor                       *)
(*                                                                            *)
(* When perm_endpoint is injective on achievable(L) for each starting card   *)
(* position s,                                                               *)
(* the endpoint distribution is closer to uniform than the DPI bound gives.  *)
(* Epsilon = 2*(N - Tg^L)/N (denominator N, not N!).                         *)
(*                                                                            *)
(* Applicable to: Cyclic (Tg=1, perm_endpoint trivially injective),                 *)
(*                Abelian (Tg=2, N=4, perm_endpoint injective on achievable(1))     *)
(* NOT applicable to: Star, S5, OC, Monster (perm_endpoint not injective on  *)
(*                    achievable for all card positions)                     *)
(******************************************************************************)

Section direct_endpoint_security.

Variable R : realType.
Variable m n' : nat.
Variable sigmas : m.+1.-tuple {perm 'I_n'.+2}.
Let M := Gen_PGGTypes sigmas.

(** The ShuffleMarginalBound built when perm_endpoint is injective on
    achievable(L): the epsilon improves from a generic fiber estimate to the
    closed form 2*(N - Tg^L)/N (denominator N, not N!), since injectivity
    lets the endpoint distribution be counted exactly rather than merely
    bounded. *)
Definition security_witness_endpoint_inj (L : nat)
    (Hlfree : @weval_inj M L)
    (Hinj_s : forall s : 'I_n'.+2,
      {in @achievable M L &,
       injective (fun sigma : {perm 'I_n'.+2} => sigma s)})
    : ShuffleMarginalBound R M :=
  @MkShuffleMarginalBound R M L _
    (rho_from_words L sigmas)
    (var_dist_endpoint_direct Hlfree Hinj_s).

End direct_endpoint_security.

(******************************************************************************)
(*     Convenience Constructors                                               *)
(*                                                                            *)
(* security_witness_from_bound: build a ShuffleMarginalBound from a bound.    *)
(*   Use this when only an upper bound on var_dist is available (e.g.,        *)
(*   spectral / Pinsker / DPI estimates).                                     *)
(*                                                                            *)
(* security_witness_with_exact: build a ShuffleCertificateBundle from a bound *)
(*   and an exact-equality proof (scb_exact := Some ...). Use this when a     *)
(*   closed-form var_dist equality is known alongside the bound.              *)
(******************************************************************************)

Section security_witness_constructors.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.
Let N' := pgg_N' M.

(** The ShuffleMarginalBound built from an arbitrary epsilon and its
    per-position var_dist proof, with no assumption on how that bound was
    derived. This is the entry point for spectral-gap, Pinsker, or DPI
    estimates, none of which come from fiber counting or endpoint
    injectivity. *)
Definition security_witness_from_bound (L : nat)
    (eps : R)
    (rho_dist : R.-fdist {perm 'I_N'.+1})
    (Hbound : forall s : 'I_N'.+1,
      (var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) rho_dist)
                (fdist_uniform (card_ord N'.+1)) <= eps)%O)
    : ShuffleMarginalBound R M :=
  @MkShuffleMarginalBound R M L eps rho_dist Hbound.

(** The ShuffleCertificateBundle built from a marginal bound together with a
    closed-form var_dist equality at the same distribution, filling
    scb_exact with that equality and leaving scb_asymptotic empty. Use when
    the exact stationary marginal is known, e.g. for structured group
    orbits, rather than only bounded. *)
Definition security_witness_with_exact (L : nat)
    (bound_eps : R)
    (rho_dist : R.-fdist {perm 'I_N'.+1})
    (Hbound : forall s : 'I_N'.+1,
      (var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) rho_dist)
                (fdist_uniform (card_ord N'.+1)) <= bound_eps)%O)
    (exact_eps : R)
    (Hexact : forall s : 'I_N'.+1,
      var_dist (fdistmap (fun sigma : {perm 'I_N'.+1} => sigma s) rho_dist)
               (fdist_uniform (card_ord N'.+1)) = exact_eps)
    : ShuffleCertificateBundle R M :=
  @MkShuffleCertificateBundle R M
    (@MkShuffleMarginalBound R M L bound_eps rho_dist Hbound)
    (Some (@MkSecurityExact R M rho_dist exact_eps Hexact))
    None.

End security_witness_constructors.

(******************************************************************************)
(*     Derived Properties                                                     *)
(******************************************************************************)

Section derived_properties.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.
Variable ar : AlgebraicRigidity R M.

Let G := pgg_G M.
Let N := (pgg_N' M).+1.

(** The adversary's search space at word length L is bounded by the group
    order: search_space M L <= #|G|. This is the complexity leg of
    algebraic rigidity: the same monodromy group G that fixes security and
    threshold below also caps how large the brute-force search ever
    gets. *)
Lemma ar_complexity (L : nat) : @search_space M L <= #|G|.
Proof. exact: search_space_leG. Qed.

(** Every AlgebraicRigidity instance falls into exactly one of two regimes:
    genus 0, where the group order stays under the Klein bound and the
    reconstruction threshold ts_T equals the privacy threshold ts_k, or
    positive genus, where the gap ts_T - ts_k is only bounded, by twice the
    genus. This is the threshold leg of algebraic rigidity: the same genus
    that classifies the covering scheme also determines whether
    reconstruction is exact or merely bounded. *)
Lemma ar_genus_gap_dichotomy :
  let cs := tw_covering (ar_threshold ar) in
  (cd_genus (cs_data cs) = 0 /\
   #|G| <= klein_genus0_bound M /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))
  \/
  (0 < cd_genus (cs_data cs) /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs)).
Proof.
move=> /=.
exact (@security_threshold_tradeoff M
  (tw_covering (ar_threshold ar))
  (@tw_genus0_klein M (ar_threshold ar))).
Qed.

(** The same genus-0/positive-genus dichotomy as ar_genus_gap_dichotomy,
    restated with the complexity bound in terms of the adversary's search
    space at length L rather than the raw group order #|G|. This ties the
    complexity leg directly to the threshold leg: bounded search space and
    exact reconstruction come together, and so do unbounded search space
    and a genus-dependent gap. *)
Lemma ar_search_gap_dichotomy (L : nat) :
  let cs := tw_covering (ar_threshold ar) in
  (@search_space M L <= klein_genus0_bound M /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))
  \/
  (0 < cd_genus (cs_data cs) /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs)).
Proof.
move=> /=.
exact (@search_gap_tradeoff M
  (tw_covering (ar_threshold ar))
  (@tw_genus0_klein M (ar_threshold ar)) L).
Qed.

(** A monodromy group larger than the Klein genus-0 bound forces positive
    genus: klein_genus0_bound M < #|G| implies 0 < cd_genus. This is the
    contrapositive reading of the genus-0 branch of the tradeoff dichotomy:
    once the group is too large to fit a genus-0 covering, the
    reconstruction gap becomes unavoidable, not merely possible. *)
Lemma ar_large_group_forces_gap :
  let cs := tw_covering (ar_threshold ar) in
  klein_genus0_bound M < #|G| ->
  0 < cd_genus (cs_data cs).
Proof.
move=> /=.
exact (@large_group_forces_gap M
  (tw_covering (ar_threshold ar))
  (@tw_genus0_klein M (ar_threshold ar))).
Qed.

(** The reconstruction/privacy gap ts_T - ts_k is at most twice the genus,
    unconditionally, whichever regime ar_genus_gap_dichotomy places the
    scheme in. This is the numeric form of the threshold leg of algebraic
    rigidity: genus is not just a classification but a literal price cap on
    the gap. *)
Lemma ar_gap_bound :
  let cs := tw_covering (ar_threshold ar) in
  ts_T (cs_scheme cs) - ts_k (cs_scheme cs) <= 2 * cd_genus (cs_data cs).
Proof. move=> /=. exact: gap_bound. Qed.

(** End-to-end protocol correctness: given a PGGInterface PI whose share
    count matches the covering scheme's ts_T' (HT), and a G_stable
    hypothesis that the scheme's per-position content reading of the group
    action agrees with the monodromy structure at every coordinate, a valid
    share tuple built by reading PI's starting positions through the plug
    reconstructs, via pgg_recon_endpoints, exactly the secret s that
    produced it. This closes the loop from algebraic rigidity's structural
    threshold witness back to the dealer's original secret: the covering
    scheme is not merely a legal parameter tuple, it actually
    reconstructs. *)
Lemma ar_protocol_correct (PI : PGGInterface M)
    (HT : ts_T' (cs_scheme (tw_covering (ar_threshold ar))) = pi_T' PI)
    (s : 'I_N) (P : pgg_gT M)
    (G_stable : forall g, g \in pgg_G M ->
       forall i : 'I_(ts_T' (cs_scheme (tw_covering (ar_threshold ar)))).+1,
         rp_content (cs_plug (tw_covering (ar_threshold ar)))
           (@pgg_rho M g (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) i)) =
         tnth [tuple rp_content (cs_plug (tw_covering (ar_threshold ar)))
                 (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) j)
              | j < (ts_T' (cs_scheme (tw_covering (ar_threshold ar)))).+1]
              (rp_monodromy (cs_plug (tw_covering (ar_threshold ar))) g i)) :
  P \in pgg_G M ->
  ts_valid (cs_scheme (tw_covering (ar_threshold ar))) s
          [tuple rp_content (cs_plug (tw_covering (ar_threshold ar)))
             (tnth (cast_tuple (esym (congr1 S HT)) (pi_starts PI)) j)
          | j < (ts_T' (cs_scheme (tw_covering (ar_threshold ar)))).+1] ->
  pgg_recon_endpoints HT
    (rp_content (cs_plug (tw_covering (ar_threshold ar)))) P = s.
Proof.
move=> PG Hvalid.
apply: (pgg_recon_monodromy_correct
          (perm := rp_monodromy (cs_plug (tw_covering (ar_threshold ar)))));
  [exact: subxx | exact: G_stable | exact: PG | exact: Hvalid
  | exact: rp_recon_invariant].
Qed.

End derived_properties.

(******************************************************************************)
(*     RAAG-Specific Derived Properties                                       *)
(******************************************************************************)

Section raag_derived_properties.

Variable R : realType.
Variable M : RAAGType.
Variable ar : AlgebraicRigidity R M.

Let Tg := (@pgg_ngens' M).+1.

(** For RAAG-typed monodromy representations, the search space is sandwiched
    between the number of distinct traces reachable at length L and the
    trivial exponential bound Tg^L, where Tg is the number of generators.
    This refines the generic complexity bound ar_complexity with a
    RAAG-specific intermediate quantity, n_traces, that can be computed
    directly rather than only bounded by #|G|. *)
Lemma ar_search_space_chain (L : nat) :
  (@search_space M L <= @n_traces M L) && (@n_traces M L <= Tg ^ L).
Proof. exact: search_space_chain. Qed.

End raag_derived_properties.

(******************************************************************************)
(*     SecurityProfile: ShuffleMarginalBound + L* + nontriviality             *)
(*                                                                            *)
(* A SecurityProfile bundles a ShuffleMarginalBound with a specific word      *)
(* length sp_Lstar, the turning point at which the bound was established,    *)
(* and a nontriviality witness sp_nontrivial that epsilon < 2, strictly       *)
(* better than the trivial full-variation-distance bound.                    *)
(*                                                                            *)
(* The threshold is 2 rather than 1 because the DPI epsilon is always < 2    *)
(* once Tg^L >= 1, which holds trivially, while epsilon < 1 needs the        *)
(* direct endpoint bound that only some instances can supply; fixing the     *)
(* threshold at 2 lets every existing instance build a SecurityProfile       *)
(* immediately.                                                              *)
(*                                                                            *)
(* The bound is required only at L*, not at every length, because weval_inj  *)
(* is not monotone in L: OC satisfies weval_inj(2) but not weval_inj(3),     *)
(* since its generator cubes collide there.                                  *)
(******************************************************************************)

Section security_profile.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.

Local Open Scope ring_scope.

Let eps_bound := (2%:R : R).

(** A ShuffleMarginalBound at a distinguished word length sp_Lstar, together
    with a proof that its epsilon is strictly below the trivial bound of 2.
    Existence at one length is deliberate: weval_inj need not hold beyond
    sp_Lstar, so the profile makes no monotonicity claim about longer
    words. *)
Record SecurityProfile := MkSecurityProfile {
  sp_Lstar : nat ;
  sp_witness : ShuffleMarginalBound R M ;
  sp_at_Lstar : sw_L sp_witness = sp_Lstar ;
  sp_nontrivial : is_true (Num.lt (sw_bound_eps sp_witness) eps_bound)
}.

(* Builds a SecurityProfile from an AlgebraicRigidity instance once its
   security bound's epsilon is shown below 2: the profile's word length is
   read off the bound's own sw_L, so no new length choice is introduced. *)
Definition ar_security_profile (ar : AlgebraicRigidity R M)
    (Hlt2 : is_true
      (Num.lt (sw_bound_eps (scb_bound (ar_security ar))) eps_bound))
    : SecurityProfile :=
  @MkSecurityProfile
    (sw_L (scb_bound (ar_security ar)))
    (scb_bound (ar_security ar))
    erefl
    Hlt2.

End security_profile.

Arguments SecurityProfile R M : clear implicits.

(******************************************************************************)
(*     CertifiedSolution: Bridge from computable solver to proof witness     *)
(*                                                                           *)
(*     Connects the nat-level SecurityParams (from dealer_solve/raag_template *)
(*     via vm_compute) to the proof-level ShuffleMarginalBound.              *)
(*                                                                           *)
(*     Since the solver uses raag_fiber_eps_nat (same formula as the witness *)
(*     fiber counting), cs_eps_le is typically lexx (reflexivity) for all    *)
(*     RAAG instances.                                                       *)
(******************************************************************************)

Section certified_solution.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.

Local Open Scope ring_scope.

(** A nat-level SecurityParams (a rational epsilon at word length sp_L,
    typically produced by vm_compute on the dealer solver) paired with a
    proof-level ShuffleMarginalBound at the same length, and a proof that
    the bound's epsilon does not exceed the rational one claimed by the
    params. This is the bridge that turns a solver's numeric output into a
    machine-checked security certificate rather than an unverified
    assertion. *)
Record CertifiedSolution := MkCertifiedSolution {
  cs_params    : SecurityParams ;
  cs_witness   : ShuffleMarginalBound R M ;
  cs_L_eq      : sw_L cs_witness = sp_L cs_params ;
  cs_denom_pos : (0 < (sp_eps cs_params).2)%N ;
  cs_eps_le    : (sw_bound_eps cs_witness <=
                  (sp_eps cs_params).1%:R / (sp_eps cs_params).2%:R)%O
}.

End certified_solution.

Arguments CertifiedSolution R M : clear implicits.

(******************************************************************************)
(*     Generic CertifiedSolution Constructor                                  *)
(*                                                                            *)
(* Any ShuffleMarginalBound with known rational epsilon gives a               *)
(* CertifiedSolution.                                                         *)
(* Works for ALL groups — RAAG and non-RAAG alike (Monster, Star, S5, etc.). *)
(*                                                                            *)
(* Architecture layers:                                                       *)
(*   Layer 1 (Computable — RAAG only):                                       *)
(*     RAAGDesc -> dealer_solve -> SecurityParams (uses vm_compute)           *)
(*   Layer 2 (Proof-level — ANY MonodromyReprWithGeneratorType):                  *)
(*     ShuffleMarginalBound -> certified_from_bound -> CertifiedSolution      *)
(*     AlgebraicRigidity + PGGInterface + G_stable -> ar_protocol_correct     *)
(******************************************************************************)

Section certified_from_bound.

Variable R : realType.
Variable M : MonodromyReprWithGeneratorType.

Local Open Scope ring_scope.

(* R and M are inferable from the bound argument, so section discharge demotes
   them to implicit arguments; callers that pin the group write
   @certified_from_bound R M b .... *)

(** Assembles a CertifiedSolution from any ShuffleMarginalBound together with
    a rational epsilon bound eps_n / eps_d that dominates it: the
    SecurityParams are read off the group's own generator count, card
    position count, and the bound's length, so the only new input is the
    rational
    certificate itself. This is the generic route from a proof-level bound
    to a certified security parameter tuple, independent of whether the
    bound came from a RAAG solver or was proved by hand. *)
Definition certified_from_bound
    (b : ShuffleMarginalBound R M)
    (eps_n eps_d : nat) (Hd : (0 < eps_d)%N)
    (Hle : (sw_bound_eps b <= eps_n%:R / eps_d%:R)%O)
    : CertifiedSolution R M :=
  @MkCertifiedSolution R M
    (MkSP (@pgg_ngens' M).+1 (pgg_N' M).+1 (sw_L b) (eps_n, eps_d))
    b erefl Hd Hle.

End certified_from_bound.

(* Exact-equality evidence is carried by ShuffleCertificateBundle above,      *)
(* whose scb_exact field is an optional SecurityExact at the bound's own      *)
(* distribution. Build a ShuffleMarginalBound with                            *)
(* `security_witness_from_bound` and a ShuffleCertificateBundle with          *)
(* `security_witness_with_exact`.                                             *)
