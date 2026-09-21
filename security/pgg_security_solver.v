(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG Security Solver: Computable Parameter Relationships                    *)
(*                                                                            *)
(* Given the endpoint-level security formula:                                 *)
(*   epsilon = 2 * (N - Tg^L) / N                                            *)
(*                                                                            *)
(* this file provides:                                                        *)
(*   - SecurityParams record: fully determined {Tg, N, L, epsilon} set        *)
(*   - epsilon_endpoint_rat: computable epsilon as rational (numerator/denom)  *)
(*   - Constraint/solve: given partial parameters, solve for the rest         *)
(*   - solve_L_aux: search for smallest L achieving target epsilon            *)
(*   - StarParams/star_solve: star-graph specific solver (m -> Tg=m+1, N=m+3)*)
(*   - vm_compute demonstrations for all group families                       *)
(*                                                                            *)
(* Key design: two epsilon formulas:                                          *)
(*   - Injective groups: 2*(N-Tg^L)/N (direct endpoint bound)                *)
(*   - Non-injective groups: fiber-counted (per-group; see star/oc/s5_fiber)  *)
(* DPI-based formula 2*(N!-Tg^L)/N! has been REMOVED as too loose.           *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     SecurityParams: fully determined parameter set                         *)
(******************************************************************************)

Record SecurityParams := MkSP {
  sp_Tg : nat ;
  sp_N : nat ;
  sp_L : nat ;
  sp_eps : nat * nat   (* epsilon as numerator/denominator rational *)
}.

(* Consistency: the epsilon matches the endpoint formula 2*(N-Tg^L)/N *)
Definition sp_consistent (p : SecurityParams) : bool :=
  let (en, ed) := sp_eps p in
  (2 * (sp_N p - sp_Tg p ^ sp_L p) * ed == en * sp_N p)%N.

(******************************************************************************)
(*     Epsilon computation                                                    *)
(******************************************************************************)

(* Endpoint-level epsilon as rational: 2*(N - Tg^L) / N *)
Definition epsilon_endpoint_rat (Tg N L : nat) : nat * nat :=
  let tl := Tg ^ L in
  if (tl <= N)%N then (2 * (N - tl), N) else (0, 1).

(******************************************************************************)
(*     L* search: smallest L achieving target epsilon                         *)
(******************************************************************************)

(* Search for smallest L such that epsilon(L) <= eps_n/eps_d.
   i.e., 2*(N - Tg^L)/N <= eps_n/eps_d
   i.e., 2*(N - Tg^L) * eps_d <= eps_n * N *)
Fixpoint solve_L_aux (Tg N eps_n eps_d fuel L : nat) : option nat :=
  match fuel with
  | 0 => None
  | fuel'.+1 =>
    let er := epsilon_endpoint_rat Tg N L in
    if (er.1 * eps_d <= eps_n * er.2)%N then Some L
    else solve_L_aux Tg N eps_n eps_d fuel' L.+1
  end.

(* Wraps solve_L_aux with a fixed fuel of 100: the smallest L such
   that epsilon_endpoint_rat Tg N L <= eps_n/eps_d, or None if no such L
   is found within 100 steps.  The search that solve's FixEps branch
   performs to turn a dealer's target epsilon into a concrete word length,
   starting at L = 1. *)
Definition solve_L (Tg N eps_n eps_d : nat) : option nat :=
  solve_L_aux Tg N eps_n eps_d 100 1.

(******************************************************************************)
(*     Constraint types and solver                                            *)
(******************************************************************************)

Inductive Constraint :=
| FixEps  (eps_n eps_d : nat) (Tg N : nat)  (* given epsilon, Tg, N -> solve L *)
| FixL    (L Tg N : nat)                     (* given L, Tg, N -> solve epsilon *)
| FixEpsTg (eps_n eps_d : nat) (Tg : nat)   (* given epsilon, Tg -> solve L, N *)
| FixEpsL  (eps_n eps_d : nat) (L N : nat)  (* given epsilon, L, N -> solve Tg *)
.

(* Single entry point *)
Definition solve (c : Constraint) : option SecurityParams :=
  match c with
  | FixL L Tg N =>
    let eps := epsilon_endpoint_rat Tg N L in
    Some (MkSP Tg N L eps)
  | FixEps eps_n eps_d Tg N =>
    match solve_L Tg N eps_n eps_d with
    | Some L => Some (MkSP Tg N L (epsilon_endpoint_rat Tg N L))
    | None => None
    end
  | _ => None  (* FixEpsTg, FixEpsL: under-determined without additional constraints *)
  end.

(******************************************************************************)
(*     Consistency proof                                                      *)
(******************************************************************************)

(* When Tg^L <= N, epsilon_endpoint_rat Tg N L reduces to its defining
   pair (2 * (N - Tg^L), N): the guard fires and the (0,1) fallback never
   triggers.  Lets later SecurityParams reasoning rewrite by the nominal
   endpoint formula without repeating the case split. *)
Lemma epsilon_endpoint_rat_consistent (Tg N L : nat) :
  let er := epsilon_endpoint_rat Tg N L in
  (Tg ^ L <= N)%N -> er = (2 * (N - Tg ^ L), N).
Proof. by rewrite /epsilon_endpoint_rat; move=> ->. Qed.

(* The rational pair er = epsilon_endpoint_rat Tg N L represents the
   fraction 2 * (N - Tg^L) / N as a cross-multiplied equality:
   2 * (N - Tg^L) * er.2 = er.1 * N.  This holds even past the Tg^L > N
   fallback, since nat subtraction truncates N - Tg^L to 0 there too.
   The raw numeric identity sp_consistent_endpoint packages onto a
   SecurityParams record. *)
Lemma epsilon_endpoint_rat_sp_consistent Tg N L :
  let er := epsilon_endpoint_rat Tg N L in
  (2 * (N - Tg ^ L) * er.2 == er.1 * N)%N.
Proof.
rewrite /= /epsilon_endpoint_rat.
case: ifP => HtlN.
  by rewrite /= mulnC.
rewrite /=.
have /eqP -> : (N - Tg ^ L == 0)%N.
  by rewrite subn_eq0 ltnW // ltnNge HtlN.
by rewrite muln0 mul0n.
Qed.

(* MkSP Tg N L (epsilon_endpoint_rat Tg N L) satisfies sp_consistent: the
   SecurityParams built directly from the endpoint-rational formula is a
   valid encoding.  solve_consistent reduces to exactly this fact for
   both producing branches of solve. *)
Lemma sp_consistent_endpoint Tg N L :
  sp_consistent (MkSP Tg N L (epsilon_endpoint_rat Tg N L)).
Proof.
rewrite /sp_consistent /= /epsilon_endpoint_rat.
case: ifP => HtlN.
  by rewrite /= mulnC.
rewrite /=.
have /eqP -> : (N - Tg ^ L == 0)%N.
  by rewrite subn_eq0 ltnW // ltnNge HtlN.
by rewrite muln0 mul0n.
Qed.

(* solve c = Some p implies sp_consistent p, for every Constraint c: the
   solver never emits a SecurityParams record whose stated epsilon
   disagrees with the endpoint formula on the parameters it also states.
   The file's top-level correctness result for the generic solver. *)
Lemma solve_consistent c p : solve c = Some p -> sp_consistent p.
Proof.
case: c => [eps_n eps_d Tg N | L Tg N | eps_n eps_d Tg | eps_n eps_d L N] //=.
- (* FixEps *)
  case Heq : (solve_L Tg N eps_n eps_d) => [L|] //=.
  by case=> <-; exact: sp_consistent_endpoint.
- (* FixL *)
  by case=> <-; exact: sp_consistent_endpoint.
Qed.

(******************************************************************************)
(*     Star-graph specific solver                                             *)
(******************************************************************************)

(* Star-specific: m determines Tg = m+1, N = m+3 *)
Record StarParams := MkStarP {
  star_m : nat ;
  star_L : nat ;
  star_eps : nat * nat
}.

(* Lifts a StarParams into a SecurityParams by instantiating the star
   family's fixed relation Tg = star_m + 1, N = star_m + 3.  Lets
   star-specific solver output be consumed anywhere a generic
   SecurityParams is expected, without a star-specific consumer. *)
Definition star_to_generic (sp : StarParams) : SecurityParams :=
  MkSP (star_m sp + 1) (star_m sp + 3) (star_L sp) (star_eps sp).

Inductive StarConstraint :=
| Star_FixM  (m : nat)        (* given m -> default L=1, compute eps *)
| Star_FixML (m L : nat)      (* given m, L -> compute eps *)
.

(* Computes the star family's epsilon via epsilon_endpoint_rat at
   Tg = m+1, N = m+3 and returns it as StarParams; total, since Tg and N
   are forced functions of m and no search is needed.  Specializes the
   generic Constraint/solve machinery to the one-parameter star family. *)
Definition star_solve (c : StarConstraint) : option StarParams :=
  match c with
  | Star_FixML m L =>
    let eps := epsilon_endpoint_rat (m + 1) (m + 3) L in
    Some (MkStarP m L eps)
  | Star_FixM m =>
    let eps := epsilon_endpoint_rat (m + 1) (m + 3) 1 in
    Some (MkStarP m 1 eps)
  end.

(******************************************************************************)
(*     vm_compute demonstrations                                              *)
(******************************************************************************)

(* S5: L=1, Tg=4, N=5 -> eps = 2*(5-4)/5 = (2,5) *)
Eval vm_compute in solve (FixL 1 4 5).

(* Abelian: L=1, Tg=2, N=4 -> eps = 2*(4-2)/4 = (4,4) = 1 *)
Eval vm_compute in solve (FixL 1 2 4).

(* OC: L=2, Tg=2, N=4 -> eps = 2*(4-4)/4 = (0,4) = 0 *)
Eval vm_compute in solve (FixL 2 2 4).

(* Cyclic n=2: L=1, Tg=1, N=4 -> eps = 2*(4-1)/4 = (6,4) *)
Eval vm_compute in solve (FixL 1 1 4).

(* Cyclic n=3: L=1, Tg=1, N=5 -> eps = 2*(5-1)/5 = (8,5) *)
Eval vm_compute in solve (FixL 1 1 5).

(* S5: eps <= 1/2, Tg=4, N=5 -> L=? *)
Eval vm_compute in solve (FixEps 1 2 4 5).

(* Abelian: eps <= 1/2, Tg=2, N=4 -> L=? *)
Eval vm_compute in solve (FixEps 1 2 2 4).

(* Tg=1 degenerate: eps <= 1/2, Tg=1, N=4 -> None (1^L = 1 never helps) *)
Eval vm_compute in solve (FixEps 1 2 1 4).

(* Star-specific *)
Eval vm_compute in star_solve (Star_FixML 2 1).   (* m=2, L=1 -> eps *)
Eval vm_compute in star_solve (Star_FixML 2 2).   (* m=2, L=2 -> eps *)
Eval vm_compute in star_solve (Star_FixM 2).       (* m=2 default *)

(* Star m=10: Tg=11, N=13 *)
Eval vm_compute in star_solve (Star_FixML 10 1).

(******************************************************************************)
(*     Fiber-counted epsilon (TRUE endpoint epsilon for non-injective groups) *)
(******************************************************************************)

(* For groups where perm_endpoint is NOT injective on achievable(L), the formula
   2*(N-Tg^L)/N is WRONG (underestimates). The true epsilon comes from
   the worst-case fiber distribution over all starting card positions. *)

(* Star(m) at L=1: true epsilon = 2(m+1)/(m+3) *)
Definition star_fiber_eps (m : nat) : nat * nat := (2 * (m + 1), m + 3).

(* OC at L=2: true epsilon = 1 (worst-case s=1; other card positions have
   1/2) *)
Definition oc_fiber_eps : nat * nat := (1, 1).

(* S5 at L=1: true epsilon = 6/5 *)
Definition s5_fiber_eps : nat * nat := (6, 5).

(* Comparison: formula-based (wrong for non-injective) vs fiber-counted *)
Eval vm_compute in (epsilon_endpoint_rat 2 4 2, oc_fiber_eps).
(* = ((0,4), (1,1)) — formula says 0, fiber says 1. Formula is WRONG. *)

Eval vm_compute in (epsilon_endpoint_rat 4 5 1, s5_fiber_eps).
(* = ((2,5), (6,5)) — formula says 2/5, fiber says 6/5. Formula is WRONG. *)

Eval vm_compute in (epsilon_endpoint_rat 3 5 1, star_fiber_eps 2).
(* = ((4,5), (6,5)) — formula says 4/5, fiber says 6/5. Formula is WRONG. *)

Eval vm_compute in star_fiber_eps 5.   (* m=5: (12,8) = 3/2 *)
Eval vm_compute in star_fiber_eps 10.  (* m=10: (22,13) *)

(******************************************************************************)
(*     Epsilon comparison utilities                                           *)
(******************************************************************************)

(* Is epsilon < 2? (i.e., strictly better than trivial) *)
Definition eps_lt2 (er : nat * nat) : bool :=
  (er.1 < 2 * er.2)%N.

(* Is epsilon < 1? (i.e., d_TV < 1/2) *)
Definition eps_lt1 (er : nat * nat) : bool :=
  (er.1 < er.2)%N.

(* Is epsilon = 0? (perfect security) *)
Definition eps_eq0 (er : nat * nat) : bool :=
  (er.1 == 0)%N.

(* Demonstrations *)
Eval vm_compute in eps_lt2 (epsilon_endpoint_rat 4 5 1).   (* S5 L=1: true *)
Eval vm_compute in eps_lt1 (epsilon_endpoint_rat 4 5 1).   (* S5 L=1: true (2/5 < 1) *)
Eval vm_compute in eps_lt1 (epsilon_endpoint_rat 2 4 1).   (* Abelian L=1: false (4/4 = 1) *)
Eval vm_compute in eps_lt1 (epsilon_endpoint_rat 2 4 2).   (* OC L=2: true (0 < 1) *)
Eval vm_compute in eps_eq0 (epsilon_endpoint_rat 2 4 2).   (* OC L=2: true *)
Eval vm_compute in eps_lt2 (epsilon_endpoint_rat 1 4 1).   (* Cyclic N=4: true (6/4 < 2) *)
Eval vm_compute in eps_lt1 (epsilon_endpoint_rat 1 4 1).   (* Cyclic N=4: false *)

(******************************************************************************)
(*     Nat-level word enumeration and fingerprinting                         *)
(*     (duplicated from legacy/groups/pgg_weval_inj.v, solver-independent)   *)
(******************************************************************************)

(* Enumerates every length-L word over the alphabet {0, ..., Tg-1} as a
   seq of seqs of nat.  The nat-level counterpart of the pgg_word finType
   enumeration in legacy/groups/pgg_weval_inj.v, duplicated here to keep
   this file's
   vm_compute demos free of the finType/tuple dependency. *)
Fixpoint enum_words (Tg L : nat) : seq (seq nat) :=
  match L with
  | 0 => [:: [::]]
  | L'.+1 =>
    flatten [seq map (cons i) (enum_words Tg L') | i <- iota 0 Tg]
  end.

(* Left-folds the generators of word w over starting card position x: the
   card position reached by applying w's generators in order.  The numeric
   word
   evaluator every solver check in this file, fingerprinting,
   injectivity, fiber epsilon, is built from; kept purely on nat so
   vm_compute stays fast. *)
Definition eval_word (gens : nat -> nat -> nat) (w : seq nat) (x : nat)
    : nat :=
  foldl (fun acc i => gens i acc) x w.

(* The full action of word w on every card position, reified as a seq:
   mapping eval_word gens w over 0, ..., N-1.  Two words act identically
   on every card position iff their fingerprints are equal, so comparing
   fingerprints is
   how check_weval_inj decides word-evaluation injectivity at the nat
   level. *)
Definition word_fingerprint (N : nat) (gens : nat -> nat -> nat)
    (w : seq nat) : seq nat :=
  map (eval_word gens w) (iota 0 N).

(* Decides whether the length-L word fingerprints over Tg generators on N
   card positions are pairwise distinct: whether word evaluation is
   injective at
   length L.  group_template checks this before trusting the generic
   endpoint formula 2*(N-Tg^L)/N, which assumes distinct words reach
   distinct achievable permutations and underestimates epsilon when that
   fails (Section "Fiber-counted epsilon" below). *)
Definition check_weval_inj (N Tg L : nat) (gens : nat -> nat -> nat)
    : bool :=
  uniq (map (word_fingerprint N gens) (enum_words Tg L)).

(******************************************************************************)
(*     GroupDesc: Nat-level description of a group by generators             *)
(*                                                                           *)
(*     Captures a group's generator structure at the nat level for           *)
(*     vm_compute.  Works for ANY group family (RAAG, cyclic, Monster, ...). *)
(*     The rd_comm field records commutativity relations between generators;  *)
(*     it is used only by RAAG-specific analyses (trace counting) and is     *)
(*     ignored by generic computations (achievable_fps, endpoint_count,      *)
(*     fiber_entropy_summary). Non-RAAG groups can set rd_comm to            *)
(*     fun _ _ => false (as cyclic_desc does).                               *)
(******************************************************************************)

Record GroupDesc := MkGroupDesc {
  gd_Tg   : nat ;                        (* number of generators *)
  gd_N    : nat ;                        (* number of card positions *)
  gd_comm : nat -> nat -> bool ;         (* commutativity relation *)
  gd_gens : nat -> nat -> nat ;          (* generator action: gens(i, x) *)
}.

Notation RAAGDesc := GroupDesc (only parsing).
Notation MkRAAGDesc := MkGroupDesc (only parsing).
Notation rd_Tg := gd_Tg (only parsing).
Notation rd_N := gd_N (only parsing).
Notation rd_comm := gd_comm (only parsing).
Notation rd_gens := gd_gens (only parsing).

(******************************************************************************)
(*     Known RAAG family descriptors                                         *)
(******************************************************************************)

(* Star(m): center (gen 0) + m leaves, Tg = m+1, N = m+3
   gen 0: swap(0, 1), gen i (i>0): swap(2, i+2) *)
Definition star_gens (i x : nat) : nat :=
  if i == 0 then
    if x == 0 then 1 else if x == 1 then 0 else x
  else
    if x == 2 then i + 2 else if x == i + 2 then 2 else x.

(* Commutation relation for Star(m) at the nat level: true exactly when
   one of i, j is the central generator 0 and i != j.  The central
   generator swaps {0,1} and leaf generator i > 0 swaps {2, i+2},
   disjoint supports, so center and leaf commute; two distinct leaves
   share the point 2 and do not commute.  Feeds star_desc. *)
Definition star_comm' (m i j : nat) : bool :=
  ((i == 0) || (j == 0)) && (i != j).

(* GroupDesc for Star(m): Tg = m+1 generators, gen 0 the central
   swap(0, 1) and gen i > 0 the leaf swap(2, i+2), on N = m+3 card
   positions,
   with commutation star_comm'.  A worked instance where word evaluation
   is not injective, so the naive endpoint formula 2*(N-Tg^L)/N
   underestimates epsilon and the fiber-counted computation further down
   this file is needed (star_fiber_eps, the "Formula is WRONG"
   comparisons). *)
Definition star_desc (m : nat) : GroupDesc :=
  MkGroupDesc m.+1 (m + 3) (star_comm' m) star_gens.

(* Path(n): adjacent transpositions, Tg = n+1, N = n+2
   gen i: swap(i, i+1) *)
Definition path_gens (i x : nat) : nat :=
  if x == i then i.+1 else if x == i.+1 then i else x.

(* Two adjacent transpositions gen i, gen j of Path(n) commute iff their
   indices differ by at least 2 (disjoint supports); the nat-level
   encoding fed into path_desc. *)
Definition path_comm' (i j : nat) : bool :=
  (2 <= (maxn i j - minn i j)) && (i != j).

(* GroupDesc for Path(n): Tg = n+1 adjacent transpositions gen i =
   swap(i, i+1) on N = n+2 card positions, with commutation path_comm'.
   The
   adjacent transpositions generate the full symmetric group S_{n+2}, so
   this is the file's transitive test case, whose achievable set can
   reach every permutation as L grows (contrasted with Star's stuck
   orbits in legacy/security/pgg_security_demo.v). *)
Definition path_desc (n : nat) : GroupDesc :=
  MkGroupDesc n.+1 (n + 2) path_comm' path_gens.

(* Disjoint(k): k disjoint transpositions, Tg = k, N = 2*k
   gen i: swap(2*i, 2*i+1), all generators commute *)
Definition disjoint_gens (i x : nat) : nat :=
  let a := 2 * i in
  if x == a then a.+1 else if x == a.+1 then a else x.

(* GroupDesc for Disjoint(k): Tg = k pairwise-disjoint transpositions
   gen i = swap(2i, 2i+1) on N = 2k card positions; every pair of distinct
   generators commutes, since their supports never overlap.  The
   fully-commuting extreme, a stress test for the solver's
   commutation-relation handling and a sanity ceiling for the
   trace-counting code path. *)
Definition disjoint_desc (k : nat) : GroupDesc :=
  MkGroupDesc k (2 * k) (fun i j : nat => i != j) disjoint_gens.

(* OC(k,p): k overlapping p-cycles, Tg = k, N = k + p - 1
   gen i: p-cycle on {i, ..., i+p-1} *)
Definition oc_gens (p i x : nat) : nat :=
  if (i <= x) && (x < i + p) then
    if x == i + p - 1 then i else x.+1
  else x.

(* Two p-cycles gen i, gen j of OC(k, p) commute iff their offsets differ
   by at least p (disjoint supports); the nat-level encoding fed into
   oc_desc. *)
Definition oc_comm' (p i j : nat) : bool :=
  (p <= maxn i j - minn i j) && (i != j).

(* GroupDesc for OC(k, p): Tg = k overlapping p-cycles gen i, a p-cycle
   on {i, ..., i+p-1}, on N = k+p-1 card positions, with commutation
   oc_comm'. Each generator moves more card positions than one of Path's
   adjacent transpositions does, so OC converges to eps -> 0 faster; the
   eps-progression
   demos in legacy/security/pgg_security_demo.v compare the two families on
   this basis. *)
Definition oc_desc (k p : nat) : GroupDesc :=
  MkGroupDesc k (k + p - 1) (oc_comm' p) (oc_gens p).

(* Cyclic(n): single n-cycle generator, Tg = 1, N = n
   gen 0: x -> (x+1) mod n *)
Definition cyclic_gens (n i x : nat) : nat :=
  if (i == 0) && (x < n) then
    if x.+1 < n then x.+1 else 0
  else x.

(* GroupDesc for Cyclic(n): a single generator (Tg = 1) rotating
   x -> x+1 mod n on N = n card positions; the commutation relation is
   vacuously
   false, since there is no pair of distinct generators to commute.  The
   degenerate one-generator case, checking that the generic solver
   pipeline degrades correctly when Tg = 1. *)
Definition cyclic_desc (n : nat) : GroupDesc :=
  MkGroupDesc 1 n (fun _ _ => false) (cyclic_gens n).

(******************************************************************************)
(*     Fiber-counted epsilon computation (fiber_eps_nat)                *)
(*                                                                           *)
(*     Computes worst-case var_dist(endpoint distribution, uniform)          *)
(*     over all starting card positions, using achievable set fingerprints.          *)
(*     var_dist convention: sum |P(x) - Q(x)| (range 0..2, no 1/2 factor). *)
(*                                                                           *)
(*     This single function replaces per-instance epsilon formulas           *)
(*     (star_fiber_eps, s5_fiber_eps, oc_fiber_eps) with a generic           *)
(*     computation applicable to any GroupDesc.                              *)
(******************************************************************************)

(* Achievable fingerprints: distinct word evaluations *)
Definition achievable_fps (desc : GroupDesc) (L : nat) : seq (seq nat) :=
  undup (map (word_fingerprint (rd_N desc) (rd_gens desc))
             (enum_words (rd_Tg desc) L)).

(* Count how many achievable elements map card position s to endpoint x *)
Definition endpoint_count (fps : seq (seq nat)) (s x : nat) : nat :=
  count (fun fp => nth 0 fp s == x) fps.

(* Var_dist numerator for card position s:
   sum_{x=0}^{N-1} |N * count(x) - total|
   where |a - b| = (a - b) + (b - a) in nat arithmetic *)
Definition vardist_num (fps : seq (seq nat)) (N s : nat) : nat :=
  let total := size fps in
  sumn [seq let c := endpoint_count fps s x in
            (N * c - total) + (total - N * c)
       | x <- iota 0 N].

(* Worst-case vardist numerator over all card positions *)
Definition worst_vardist (fps : seq (seq nat)) (N : nat) : nat :=
  foldr maxn 0 [seq vardist_num fps N s | s <- iota 0 N].

(* Reduce a fraction by GCD *)
Definition reduce_frac (n d : nat) : nat * nat :=
  match gcdn n d with
  | 0 => (0, 1)
  | g => (n %/ g, d %/ g)
  end.

(* fiber_eps_nat: worst-case endpoint var_dist as (numerator, denominator)
   Input: GroupDesc + L -> Output: worst-case (eps_num, eps_den) *)
Definition fiber_eps_nat (desc : GroupDesc) (L : nat) : nat * nat :=
  let fps := achievable_fps desc L in
  let N := rd_N desc in
  let total := size fps in
  if total == 0 then (0, 1)
  else reduce_frac (worst_vardist fps N) (N * total).

Notation raag_fiber_eps_nat := fiber_eps_nat (only parsing).

(******************************************************************************)
(*     SecuritySpec and GroupTemplate                                         *)
(*                                                                           *)
(*     SecuritySpec: dealer's partial specification (target epsilon, fix L).  *)
(*     GroupTemplate: a group family's solver (parameterized by desc).        *)
(*     group_template: generic template — star, path, disjoint, oc, cyclic   *)
(*       are all just different GroupDescs fed to the same solver logic.     *)
(******************************************************************************)

Record SecuritySpec := MkSecuritySpec {
  ss_target_eps : option (nat * nat) ;  (* upper bound on epsilon *)
  ss_L          : option nat ;          (* fix word length *)
}.

Record GroupTemplate := MkGroupTemplate {
  gt_Tg : nat ;
  gt_N  : nat ;
  gt_solve : SecuritySpec -> option SecurityParams ;
}.

(* Builds a GroupTemplate from a GroupDesc and a default word length: at
   the spec's L (or the default), checks word-eval injectivity
   (check_weval_inj), computes the fiber-counted epsilon fiber_eps_nat,
   the true worst-case endpoint epsilon, and returns SecurityParams only
   if injectivity holds and any target epsilon in the spec is met.
   Every named family below, star_template through cyclic_template, is a
   one-line specialization of this single generic logic; using
   fiber_eps_nat rather than the naive 2*(N-Tg^L)/N formula is what keeps
   it correct for non-injective families such as Star. *)
Definition group_template (desc : GroupDesc) (default_L : nat)
    : GroupTemplate :=
  MkGroupTemplate (rd_Tg desc) (rd_N desc)
    (fun spec =>
      let L := match ss_L spec with
               | Some l => l
               | None => default_L
               end in
      if check_weval_inj (rd_N desc) (rd_Tg desc) L (rd_gens desc) then
        let eps := fiber_eps_nat desc L in
        match ss_target_eps spec with
        | Some target =>
            if (eps.1 * target.2 <= target.1 * eps.2)%N then
              Some (MkSP (rd_Tg desc) (rd_N desc) L eps)
            else None
        | None => Some (MkSP (rd_Tg desc) (rd_N desc) L eps)
        end
      else None).

Notation raag_template := group_template (only parsing).

(******************************************************************************)
(*     Named templates for known families                                    *)
(******************************************************************************)

(* Star(m) specialized from group_template with default word length 1. *)
Definition star_template (m : nat) := group_template (star_desc m) 1.
(* Path(n) specialized from group_template with default word length 1. *)
Definition path_template (n : nat) := group_template (path_desc n) 1.
(* Disjoint(k) specialized from group_template with default word length 1. *)
Definition disjoint_template (k : nat) := group_template (disjoint_desc k) 1.
(* OC(k, p) specialized from group_template with default word length p - 1. *)
Definition oc_template (k p : nat) := group_template (oc_desc k p) (p - 1).
(* Cyclic(n) specialized from group_template with default word length 1. *)
Definition cyclic_template (n : nat) := group_template (cyclic_desc n) 1.

(* Top-level dealer entry point *)
Definition dealer_solve (spec : SecuritySpec) (tmpl : GroupTemplate)
    : option SecurityParams := gt_solve tmpl spec.

(******************************************************************************)
(*     vm_compute demonstrations: dealer_solve                               *)
(******************************************************************************)

(* Star m=2: Tg=3, N=5, L=1, eps=6/5 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec None None) (star_template 2).

(* Path n=3 (= S5): Tg=4, N=5, L=1, eps=6/5 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec None None) (path_template 3).

(* Disjoint k=2 (= Abelian): Tg=2, N=4, L=1, eps=1 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec None None) (disjoint_template 2).

(* OC(2,3): Tg=2, N=4, L=2, eps=1 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec None None) (oc_template 2 3).

(* Cyclic n=4: Tg=1, N=4, L=1 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec None None) (cyclic_template 4).

(* Cyclic n=5: Tg=1, N=5, L=1 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec None None) (cyclic_template 5).

(* Star m=5: Tg=6, N=8 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec None None) (star_template 5).

(* With target epsilon: Star m=2 with target eps <= 6/5 *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec (Some (6, 5)) None) (star_template 2).

(* With target epsilon: Star m=2 with target eps <= 1/2 -> None *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec (Some (1, 2)) None) (star_template 2).

(* Cyclic n=2 with target eps <= 0.01 -> None *)
Eval vm_compute in dealer_solve
  (MkSecuritySpec (Some (1, 100)) None) (cyclic_template 2).

(******************************************************************************)
(*     vm_compute demonstrations: raw fiber epsilon                          *)
(******************************************************************************)

Eval vm_compute in fiber_eps_nat (star_desc 2) 1.   (* = (6, 5) *)
Eval vm_compute in fiber_eps_nat (path_desc 3) 1.   (* = (6, 5) *)
Eval vm_compute in fiber_eps_nat (oc_desc 2 3) 2.   (* = (1, 1) *)
Eval vm_compute in fiber_eps_nat (disjoint_desc 2) 1. (* = (1, 1) *)
Eval vm_compute in fiber_eps_nat (cyclic_desc 4) 1. (* = (3, 2) *)
Eval vm_compute in fiber_eps_nat (cyclic_desc 5) 1. (* = (8, 5) *)

(* Cross-check: star_fiber_eps matches fiber_eps_nat *)
Eval vm_compute in (star_fiber_eps 2, fiber_eps_nat (star_desc 2) 1).
Eval vm_compute in (s5_fiber_eps, fiber_eps_nat (path_desc 3) 1).

(* Larger examples *)
Eval vm_compute in fiber_eps_nat (star_desc 5) 1.   (* m=5: Tg=6, N=8 *)
Eval vm_compute in fiber_eps_nat (star_desc 10) 1.  (* m=10: Tg=11, N=13 *)

(******************************************************************************)
(*     Fiber entropy computation (nat-level approximation)                    *)
(*                                                                            *)
(*     Computes an integer proxy for entropy deficit:                         *)
(*       entropy_deficit_num = Σ_{c_x > 0} c_x * (c_x - 1)                  *)
(*     which is 0 iff all nonempty fibers have size 1 (= injective perm_endpoint).  *)
(*     This is NOT the true entropy but a computable nat-level indicator of   *)
(*     fiber unevenness: 0 means all fibers are singletons (max entropy).    *)
(*                                                                            *)
(*     For true entropy, use the type-level fiber_entropy in                  *)
(*     legacy/security/pgg_entropy_security.v with real-valued log.           *)
(******************************************************************************)

(* Fiber unevenness indicator for card position s:
   Σ_{x} c_x * (c_x - 1) where c_x = endpoint_count fps s x.
   This is 0 iff all fibers are singletons (perm_endpoint injective). *)
Definition fiber_unevenness (fps : seq (seq nat)) (N s : nat) : nat :=
  sumn [seq let c := endpoint_count fps s x in c * (c - 1)
       | x <- iota 0 N].

(* Worst-case fiber unevenness over all card positions *)
Definition worst_unevenness (fps : seq (seq nat)) (N : nat) : nat :=
  foldr maxn 0 [seq fiber_unevenness fps N s | s <- iota 0 N].

(* Is perm_endpoint injective on achievable(L)? (all fibers are singletons) *)
Definition check_perm_endpoint_inj (desc : GroupDesc) (L : nat) : bool :=
  let fps := achievable_fps desc L in
  worst_unevenness fps (rd_N desc) == 0.

(* Fiber entropy summary: (total, worst_unevenness, is_injective)
   - total = |achievable(L)| = Tg^L when weval_inj
   - worst_unevenness = 0 iff perm_endpoint injective → H = log(total)
   - For exact H when unevenness > 0, use type-level fiber_entropy *)
Definition fiber_entropy_summary (desc : GroupDesc) (L : nat)
    : nat * nat * bool :=
  let fps := achievable_fps desc L in
  let total := size fps in
  let wu := worst_unevenness fps (rd_N desc) in
  (total, wu, wu == 0).

(******************************************************************************)
(*     vm_compute demonstrations: fiber entropy                              *)
(******************************************************************************)

(* Star m=2, L=1: unevenness > 0 (non-injective perm_endpoint) *)
Eval vm_compute in fiber_entropy_summary (star_desc 2) 1.

(* Path n=3 (= S5), L=1: unevenness > 0 *)
Eval vm_compute in fiber_entropy_summary (path_desc 3) 1.

(* OC(2,3), L=2: unevenness > 0 *)
Eval vm_compute in fiber_entropy_summary (oc_desc 2 3) 2.

(* Disjoint k=2 (= Abelian), L=1: check if perm_endpoint injective *)
Eval vm_compute in fiber_entropy_summary (disjoint_desc 2) 1.

(* Cyclic n=5, L=1: single generator *)
Eval vm_compute in fiber_entropy_summary (cyclic_desc 5) 1.

(* Cross-family comparison *)
Eval vm_compute in check_perm_endpoint_inj (star_desc 2) 1.
Eval vm_compute in check_perm_endpoint_inj (disjoint_desc 2) 1.
Eval vm_compute in check_perm_endpoint_inj (cyclic_desc 5) 1.
