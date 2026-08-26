(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm morphism bigop.
From mathcomp Require Import boolp reals.
From infotheo Require Import fdist.

(******************************************************************************)
(* PGG: Monodromy Representation Interface                                    *)
(*                                                                            *)
(* Layer 1 -- HB mixin (like HETypes + isEncDec):                             *)
(*   PGGTypes  == record bundling group type, card position count, and group  *)
(*   isMonodromyRepr == mixin providing the representation rho : G -> S_N     *)
(*   MonodromyReprType == HB structure packaging PGGTypes + isMonodromyRepr   *)
(*                                                                            *)
(* Derived operations:                                                        *)
(*   endpoint M g s == rho(g)(s), monodromy evaluation                        *)
(*   start_sheet PI i == starting card position of player i                   *)
(*   dealt_hand PI W i == player i's column of the permutation table          *)
(*   compute PI P i == endpoint for player i under word P                     *)
(*   endpoints PI P == T-tuple of all player endpoints                        *)
(*                                                                            *)
(* Layer 2 -- PGGInterface record (like DSDP_Interface):                     *)
(*   pgg_dtype  == session data type kind (DT_Sheet | DT_Hand | DT_Idx)       *)
(*   pgg_data N == protocol data: card position, dealt hand, or word index   *)
(*   PGGInterface M == protocol config (T players, starting card positions)  *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ========================================================================== *)
(* Layer 1: HB mixin -- Monodromy Representation                              *)
(* ========================================================================== *)

Record PGGTypes := MkPGG {
  pgg_gT : finGroupType ;
  pgg_N' : nat ;
  pgg_G  : {group pgg_gT} ;
}.

(* [pgg_rho] is the permutation representation realising the abstract
   group [pgg_G] on a deck of [pgg_N'.+1] physical card positions.
   In MathComp, [{perm 'I_n}] is the symmetric group S_n on the finite
   type 'I_n = {0,...,n-1}, so [pgg_rho] is literally a morphism
   G -> S_n. The target S_n is not a restriction but a mathematical
   necessity: any action on n fixed card positions is by definition a
   homomorphism into S_n. The generality of the framework instead
   lives in the source [pgg_gT : finGroupType], which is an arbitrary
   finite group type -- instantiated in this development as cyclic,
   abelian, Coxeter A_4 (RAAG for S_5), star, or monster groups, each
   specified by its own presentation rather than as a pre-chosen
   subgroup of S_n. *)
HB.mixin Record isMonodromyRepr (T : PGGTypes) := {
  pgg_rho : {morphism (pgg_G T) >-> {perm 'I_(pgg_N' T).+1}} ;
}.

#[short(type=MonodromyReprType)]
HB.structure Definition MonodromyRepr := { T of isMonodromyRepr T }.

HB.mixin Record hasGenerators (T : PGGTypes) := {
  pgg_ngens' : nat ;
  pgg_sigmas : pgg_ngens'.+1.-tuple (pgg_gT T) ;
  pgg_sigmas_gen : <<[set tnth pgg_sigmas i | i : 'I_pgg_ngens'.+1]>>%G = pgg_G T ;
}.

#[short(type=MonodromyReprWithGeneratorType)]
HB.structure Definition MonodromyReprWithGenerator :=
  { T of isMonodromyRepr T & hasGenerators T }.

(* ========================================================================== *)
(* Derived operations from monodromy representation                           *)
(* ========================================================================== *)

Section monodromy_ops.

Variable M : MonodromyReprType.

Let gT := pgg_gT M.
Let N := (pgg_N' M).+1.
Let G := pgg_G M.
Let rho := @pgg_rho M.

(* rho g s: the card position s reaches under the group element g. Every
   protocol operation below (compute, dealt_hand, endpoints) is defined as
   an instance of endpoint, so this accessor is the single primitive the
   rest of the framework is built on. *)
Definition endpoint (g : gT) (s : 'I_N) : 'I_N := rho g s.

(* endpoint (g*h) s = endpoint h (endpoint g s): evaluating a product at a
   card position agrees with composing the two endpoint maps in the same
   order. This is the action-morphism law that makes rho a genuine group
   action on card positions rather than a bare family of permutations, and
   it is what lets a shuffle word be replayed one generator at a time. *)
Lemma endpointM (g h : gT) (s : 'I_N) :
  g \in G -> h \in G ->
  endpoint (g * h) s = endpoint h (endpoint g s).
Proof. by move=> gG hG; rewrite /endpoint morphM //= permM. Qed.

(* endpoint 1 s = s: the identity element of G fixes every starting card
   position, the base case the action law endpointM builds words on top of. *)
Lemma endpoint1 (s : 'I_N) : endpoint 1 s = s.
Proof. by rewrite /endpoint morph1 perm1. Qed.

(* endpoint g is injective on card positions: no two starting positions are
   sent to the same place by a single group element. Distinctness of the
   dealt starting positions therefore survives any shuffle, which is what
   lets the verifier read T distinct endpoints back as T distinct players. *)
Lemma endpoint_inj (g : gT) : injective (endpoint g).
Proof. by move=> s1 s2; rewrite /endpoint; exact: perm_inj. Qed.

(* endpoint g^-1 undoes endpoint g on every card position: the shuffle
   applied by any group element g is reversible by evaluating its inverse. *)
Lemma endpointV (g : gT) (s : 'I_N) :
  g \in G -> endpoint g^-1 (endpoint g s) = s.
Proof.
move=> gG; rewrite -endpointM ?groupV // mulgV.
exact: endpoint1.
Qed.

End monodromy_ops.

Arguments endpoint {M}.

Section perm_endpoint_def.

Variable N' : nat.
Let N := N'.+1.

(* sigma s: the card position s reaches under a raw permutation sigma,
   bypassing the monodromy morphism rho entirely. Fiber counting and
   security analyses quantify directly over {perm 'I_N} rather than over the
   abstract group G, since the security argument depends only on which
   permutation is applied, not on which group element realises it. *)
Definition perm_endpoint (sigma : {perm 'I_N}) (s : 'I_N) : 'I_N :=
  sigma s.

End perm_endpoint_def.

(* ========================================================================== *)
(* Search space definitions from generators                                   *)
(* ========================================================================== *)

Section search_space_ops.

Variable M : MonodromyReprWithGeneratorType.

Let gT := pgg_gT M.
Let G := pgg_G M.
Let Tg := (@pgg_ngens' M).+1.
Let sigmas := @pgg_sigmas M.

(* A word of length L: sequence of generator indices *)
Definition pgg_word (L : nat) := L.-tuple 'I_Tg.

(* Evaluate a word by folding group multiplication *)
Definition word_eval (L : nat) (w : pgg_word L) : gT :=
  (\prod_(i < L) tnth sigmas (tnth w i))%g.

(* Set of achievable group elements from words of length L *)
Definition achievable (L : nat) : {set gT} :=
  [set word_eval w | w : pgg_word L].

(* Search space size *)
Definition search_space (L : nat) : nat :=
  #|achievable L|.

(* Upper bound: achievable ⊆ G *)
Lemma sigmas_in_G (i : 'I_Tg) : tnth sigmas i \in G.
Proof.
have HgenG := @pgg_sigmas_gen M.
suff : tnth sigmas i \in <<[set tnth sigmas j | j : 'I_Tg]>>%G.
  by rewrite HgenG.
by apply: mem_gen; apply/imsetP; exists i.
Qed.

(* Every group element reachable by an L-generator word is already in G,
   since each generator is. This is the step that lets search_space_leG
   bound the achievable-word count by |G| rather than only by the raw word
   count T^L. *)
Lemma achievable_sub (L : nat) : achievable L \subset G.
Proof.
apply/subsetP => g /imsetP [w _ ->].
rewrite /word_eval; apply: group_prod => i _ /=.
exact: sigmas_in_G.
Qed.

(* Upper bound: search space ≤ |G| *)
Lemma search_space_leG (L : nat) : search_space L <= #|G|.
Proof.
rewrite /search_space.
exact: (subset_leq_card (achievable_sub L)).
Qed.

(* Upper bound: search space ≤ T^L (number of words) *)
Lemma search_space_le_words (L : nat) : search_space L <= Tg ^ L.
Proof.
rewrite /search_space /achievable.
apply: leq_trans (leq_imset_card _ _) _.
by rewrite card_tuple card_ord.
Qed.

(* Word-eval injectivity: word evaluation is injective on L-words *)
Definition weval_inj (L : nat) : Prop :=
  injective (word_eval (L:=L)).

(* Word-eval injective generators achieve the maximal search space T^L *)
Lemma weval_inj_search_space (L : nat) :
  weval_inj L -> search_space L = Tg ^ L.
Proof.
move=> Hinj; rewrite /search_space /achievable.
rewrite card_imset; last exact: Hinj.
by rewrite card_tuple card_ord.
Qed.

(* The boolean form of weval_inj L, via MathComp's decidable injectiveb on
   the finite domain 'I_Tg^L. Boolean form is what lets weval_injP hand the
   propositional injectivity to ssreflect's reflection machinery. *)
Definition weval_injB (L : nat) : bool :=
  injectiveb (word_eval (L:=L)).

(* weval_injB reflects weval_inj: the boolean and propositional statements
   of length-L word-evaluation injectivity agree. *)
Lemma weval_injP (L : nat) : reflect (weval_inj L) (weval_injB L).
Proof. exact: injectiveP. Qed.

End search_space_ops.

(* ========================================================================== *)
(* Generic results from generator injectivity                                 *)
(* ========================================================================== *)

Section gen_inj_theory.

Variable M : MonodromyReprWithGeneratorType.

Let gT := pgg_gT M.
Let Tg := (@pgg_ngens' M).+1.
Let sigmas := @pgg_sigmas M.

(* Injective generators (as a bare index function) force word evaluation at
   length 1 to be injective in the general weval_inj sense, since a
   length-1 word is exactly its single generator. This is the bridge that
   lets the concrete generator hypothesis feed the generic search-space
   bound below. *)
Lemma gen_inj_weval_inj1 :
  injective (fun i : 'I_Tg => tnth sigmas i) ->
  @weval_inj M 1.
Proof.
move=> Hinj w1 w2 Heval.
apply: eq_from_tnth => i.
have -> : i = ord0 by apply: val_inj; case: i => -[].
apply: Hinj.
by move: Heval; rewrite /word_eval !big_ord_recl !big_ord0 !mulg1.
Qed.

(* Injective generators make the length-1 search space attain its maximum
   Tg: chaining gen_inj_weval_inj1 with weval_inj_search_space, every one of
   the Tg generators reaches a distinct group element, so the search space
   at word length 1 is as large as it can possibly be. *)
Lemma gen_inj_weval_inj1_search_space :
  injective (fun i : 'I_Tg => tnth sigmas i) ->
  @search_space M 1 = Tg.
Proof. by move/gen_inj_weval_inj1/weval_inj_search_space. Qed.

End gen_inj_theory.

(* ========================================================================== *)
(* Session Data Type Kind                                                     *)
(* ========================================================================== *)

Inductive pgg_dtype : Type := DT_Sheet | DT_Hand | DT_Idx.

(* Decidable equality on the three session-data tags DT_Sheet/DT_Hand/DT_Idx
   that classify what a wire message carries: a card position, a dealt hand,
   or a shuffle index. Session typing needs this tag comparable so the
   sender's declared alphabet letter can be checked against the receiver's
   expected one. *)
Definition pgg_dtype_eqb (d1 d2 : pgg_dtype) : bool :=
  match d1, d2 with
  | DT_Sheet, DT_Sheet => true
  | DT_Hand, DT_Hand => true
  | DT_Idx, DT_Idx => true
  | _, _ => false
  end.

(* pgg_dtype_eqb decides propositional equality on pgg_dtype, the fact
   registered below as the eqType instance every session-typed definition in
   this file relies on. *)
Lemma pgg_dtype_eqP : Equality.axiom pgg_dtype_eqb.
Proof. by move=> [] []; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build pgg_dtype pgg_dtype_eqP.

(* ========================================================================== *)
(* Protocol Data Type                                                         *)
(* ========================================================================== *)

Inductive pgg_data (N : nat) : Type :=
  | PGG_sheet (i : 'I_N)
  | PGG_hand (s : seq ('I_N))
  | PGG_idx (n : nat).

Arguments PGG_sheet {N}.
Arguments PGG_hand {N}.
Arguments PGG_idx {N}.

(* Reads off the pgg_dtype tag a pgg_data payload carries: a card position
   is DT_Sheet, a dealt hand is DT_Hand, a shuffle index is DT_Idx. Session
   types are indexed by pgg_dtype, so every send and receive in the
   card-exchange protocol is checked against this projection. *)
Definition pgg_data_dtype {N} (d : pgg_data N) : pgg_dtype :=
  match d with
  | PGG_sheet _ => DT_Sheet
  | PGG_hand _ => DT_Hand
  | PGG_idx _ => DT_Idx
  end.

(* Recovers the card position from a payload tagged PGG_sheet, or fails on
   any other tag. The session-typed Observe/Receive wrappers pattern-match
   through this projection to unwrap a DT_Sheet message into its 'I_N
   payload. *)
Definition from_sheet {N} (d : pgg_data N) : option ('I_N) :=
  if d is PGG_sheet i then Some i else None.

(* Recovers the dealt hand from a payload tagged PGG_hand, or fails on any
   other tag, the DT_Hand counterpart of from_sheet. *)
Definition from_hand {N} (d : pgg_data N) : option (seq ('I_N)) :=
  if d is PGG_hand s then Some s else None.

(* Recovers the shuffle index from a payload tagged PGG_idx, or fails on any
   other tag, the DT_Idx counterpart of from_sheet. *)
Definition from_idx {N} (d : pgg_data N) : option nat :=
  if d is PGG_idx n then Some n else None.

(* from_sheet undoes PGG_sheet: projecting a freshly tagged card position
   always recovers it. The card-exchange protocol programs and their
   duality checks use this to discharge the projection without unfolding
   the match by hand. *)
Lemma from_sheet_PGG_sheet {N} (i : 'I_N) :
  from_sheet (PGG_sheet i) = Some i.
Proof. by []. Qed.

(* from_hand undoes PGG_hand, the DT_Hand analogue of from_sheet_PGG_sheet. *)
Lemma from_hand_PGG_hand {N} (s : seq ('I_N)) :
  from_hand (PGG_hand s) = Some s.
Proof. by []. Qed.

(* from_idx undoes PGG_idx, the DT_Idx analogue of from_sheet_PGG_sheet. *)
Lemma from_idx_PGG_idx {N} (n : nat) :
  from_idx (@PGG_idx N n) = Some n.
Proof. by []. Qed.

(* ========================================================================== *)
(* Layer 2: PGGInterface -- Protocol Configuration                           *)
(* ========================================================================== *)

Record PGGInterface (M : MonodromyReprType) := MkPGGI {
  pi_T' : nat ;
  pi_starts : pi_T'.+1.-tuple 'I_(pgg_N' M).+1 ;
  pi_starts_uniq : uniq pi_starts ;
}.

Arguments pi_T' {M} _.
Arguments pi_starts {M} _.
Arguments pi_starts_uniq {M} _.

(* ========================================================================== *)
(* Protocol Operations                                                        *)
(* ========================================================================== *)

Section pgg_protocol_ops.

Variable M : MonodromyReprType.
Variable PI : PGGInterface M.

Let gT := pgg_gT M.
Let N := (pgg_N' M).+1.
Let T := (pi_T' PI).+1.
Let rho := @pgg_rho M.
Let starts := pi_starts PI.

Definition start_sheet (i : 'I_T) : 'I_N := tnth starts i.

Let x0 := tnth starts ord0.

(* Distinct players are assigned distinct starting card positions: pi_starts
   is a uniq tuple, so reading it by tnth is injective. This is the fact
   card_start_sheets below needs to turn the image set start_sheets back
   into a count of exactly T positions. *)
Lemma start_sheet_inj : injective start_sheet.
Proof.
move=> i j; rewrite /start_sheet => eq_ij.
have Hi : (i < size starts)%N by rewrite size_tuple.
have Hj : (j < size starts)%N by rewrite size_tuple.
have := @nth_uniq _ x0 starts i j Hi Hj (pi_starts_uniq PI).
have -> : nth x0 starts i = tnth starts i by rewrite (tnth_nth x0).
have -> : nth x0 starts j = tnth starts j by rewrite (tnth_nth x0).
rewrite eq_ij eqxx => /esym/eqP. exact: ord_inj.
Qed.

(* The image of the T players' starting positions under tnth starts, the set
   the verifier's T revealed card positions range over before any shuffle is
   applied. Security and fiber analyses quantify over this set as the
   protocol's fixed starting layout. *)
Definition start_sheets : {set 'I_N} :=
  [set tnth starts i | i : 'I_T].

(* start_sheets has exactly T elements: start_sheet_inj turns the T-player
   image set back into a count equal to the player count. Uniform-fiber
   counting and entropy analyses use this to identify "one starting position
   per player" with "T positions total". *)
Lemma card_start_sheets : #|start_sheets| = T.
Proof.
rewrite card_imset; first by rewrite card_ord.
exact: start_sheet_inj.
Qed.

(* The permutations rho w for w ranging over a word sequence W, in order.
   This is the intermediate object between an abstract sequence of group
   elements and the concrete card-position effects dealt_hand and compute
   read off it. *)
Definition perm_table (W : seq gT) : seq {perm 'I_N} :=
  [seq rho w | w <- W].

(* Player i's dealt hand: the sequence of card positions start_sheet i
   visits under each word in W, one entry per table column. This is the
   datum the dealer sends and the player later indexes into to reveal a
   single endpoint, so the whole card-exchange session type is built around
   its shape. *)
Definition dealt_hand (W : seq gT) (i : 'I_T) : seq ('I_N) :=
  [seq rho w (tnth starts i) | w <- W].

(* The single card position player i reveals to the verifier once the
   shuffle P has been selected: rho P applied to i's starting card
   position. This is
   the one entry of dealt_hand the protocol actually exposes. *)
Definition compute (P : gT) (i : 'I_T) : 'I_N :=
  rho P (tnth starts i).

(* The T-tuple collecting every player's revealed endpoint under a shared
   shuffle P, the full observation the verifier assembles before
   reconstruction. *)
Definition endpoints (P : gT) : T.-tuple 'I_N :=
  [tuple compute P i | i < T].

(* If P was among the words the dealer used to build W, then player i's
   revealed endpoint under P already sits in the hand dealt to i. This is
   the correctness link the player program relies on: looking up P in the
   dealt hand and evaluating compute P i agree. *)
Lemma compute_in_dealt_hand (W : seq gT) (P : gT) (i : 'I_T) :
  P \in W -> compute P i \in dealt_hand W i.
Proof.
move=> PW; rewrite /dealt_hand /compute.
by apply/mapP; exists P.
Qed.

(* Reading endpoints P at index i reduces to compute P i: the tuple
   abstraction over player endpoints computes componentwise to the raw
   monodromy evaluation, letting downstream proofs unfold endpoints without
   touching the tuple machinery. *)
Lemma endpointsE (P : gT) (i : 'I_T) :
  tnth (endpoints P) i = rho P (tnth starts i).
Proof. by rewrite tnth_mktuple. Qed.

(* Every shuffle g maps the T starting card positions to T pairwise-distinct
   endpoints: rho g is injective and starts is uniq, so the deck's initial
   distinctness is preserved through any single monodromy evaluation. This
   is what lets the verifier's T observed endpoints be read back as T
   distinct player contributions rather than a collapsed subset. *)
Lemma endpoint_starts_uniq (g : gT) :
  uniq (map (rho g) starts).
Proof.
rewrite map_inj_uniq; [exact: (pi_starts_uniq PI) | exact: perm_inj].
Qed.

End pgg_protocol_ops.

Arguments start_sheet {M} PI.
Arguments start_sheets {M} PI.
Arguments dealt_hand {M} PI.
Arguments compute {M} PI.
Arguments endpoints {M} PI.

(* ========================================================================== *)
(* Parameterized multi-generator instance                                     *)
(* ========================================================================== *)

Section generated_instance.

Variable m : nat.
Variable n : nat.
Let T := m.+1.
Let N := n.+2.
Let gT : finGroupType := {perm 'I_N}.

Variable sigmas : T.-tuple gT.

Let gen_set : {set gT} := [set tnth sigmas i | i : 'I_T].
Let G : {group gT} := <<gen_set>>%G.

(* Inclusion morphism: identity on the subgroup *)
Lemma gen_incl_morphM : {in G &, {morph (@id gT) : x y / (x * y)%g}}.
Proof. by []. Qed.

(* The identity map on the generated subgroup G <= {perm 'I_N}, packaged as
   a group morphism into {perm 'I_N} itself. Supplying pgg_rho as an
   inclusion rather than a nontrivial representation is what makes
   Gen_PGGTypes a template: the group already IS its own permutation action,
   so no separate representation needs to be constructed. *)
Definition gen_incl_morph : {morphism G >-> {perm 'I_N}} :=
  Morphism gen_incl_morphM.

(* The PGGTypes record built from an arbitrary generator tuple sigmas via
   the inclusion morphism gen_incl_morph. Every concrete group family in
   this development (Star, OC, Monster, ...) instantiates its monodromy
   representation by specialising this one template rather than by
   constructing a representation from scratch. *)
Definition Gen_PGGTypes := @MkPGG gT N.-1 G.

HB.instance Definition Gen_isMonodromyRepr :=
  @isMonodromyRepr.Build Gen_PGGTypes gen_incl_morph.

(* The generator set sigmas spans the carrier group G by construction, since
   G was defined as their generated subgroup. This is exactly the
   hasGenerators obligation pgg_sigmas_gen, discharged here for registration
   below. *)
Lemma gen_sigmas_gen :
  <<[set tnth sigmas i | i : 'I_T]>>%G = G.
Proof. by []. Qed.

HB.instance Definition Gen_hasGenerators :=
  @hasGenerators.Build Gen_PGGTypes m sigmas gen_sigmas_gen.

Let M : MonodromyReprType := Gen_PGGTypes.

(* The starting tuple [0; 1] for the smallest nontrivial interface, T = 2
   players. This is the concrete layout every native_compute duality check
   in this development runs its two-player instance against. *)
Definition gen_starts_2 : 2.-tuple 'I_N :=
  [tuple @Ordinal N 0 isT; @Ordinal N 1 isT].

(* The two entries of gen_starts_2 are distinct, the pi_starts_uniq
   obligation Gen_PGG_2 needs to package the tuple as a PGGInterface. *)
Lemma gen_starts_2_uniq : uniq gen_starts_2.
Proof. by vm_compute. Qed.

(* The smallest concrete PGGInterface over the generic template
   Gen_PGGTypes: two players starting at positions 0 and 1. Protocol
   duality is verified by native_compute against this instance. *)
Definition Gen_PGG_2 : PGGInterface M :=
  @MkPGGI M 1 gen_starts_2 gen_starts_2_uniq.

End generated_instance.

(* ========================================================================== *)
(* T-party interface for any T <= N                                           *)
(* ========================================================================== *)

Section gen_pgg_T.

Variable M : MonodromyReprType.
Variable T' : nat.
Let T := T'.+1.
Let N := (pgg_N' M).+1.
Hypothesis HT : T <= N.

(* Widening 'I_T along HT : T <= N and enumerating gives exactly T card
   positions, the size obligation the dependent Tuple constructor needs to
   package gen_starts_T below. *)
Lemma gen_starts_T_size : size (map (widen_ord HT) (enum 'I_T)) == T.
Proof. by rewrite size_map size_enum_ord. Qed.

(* The starting tuple assigning the first T card positions of the N-card
   deck to the T players, in order. This is the canonical layout every
   multi-player concrete instance (as opposed to the T = 2 template
   Gen_PGG_2) uses as its starts field. *)
Definition gen_starts_T : T.-tuple 'I_N := Tuple gen_starts_T_size.

(* The first T card positions are pairwise distinct, since widen_ord is
   injective and 'I_T enumerates without repetition. This is the
   pi_starts_uniq obligation Gen_PGG_T needs. *)
Lemma gen_starts_T_uniq : uniq gen_starts_T.
Proof.
rewrite /gen_starts_T /= map_inj_uniq ?enum_uniq //.
by move=> x y Heq; apply: val_inj; have := congr1 val Heq.
Qed.

(* The T-player PGGInterface built from the first T card positions, the
   uniform starting layout every multi-player concrete protocol instance in
   this development shares. *)
Definition Gen_PGG_T : PGGInterface M :=
  @MkPGGI M T' gen_starts_T gen_starts_T_uniq.

End gen_pgg_T.

(* ========================================================================== *)
(* Generic tuple construction from a generator function                       *)
(* ========================================================================== *)

Section gen_tuple_construction.

Variable T : nat.
Variable gT : finGroupType.
Variable gen : 'I_T.+1 -> gT.

(* Mapping gen over the T.+1-element enumeration of 'I_T.+1 produces a
   sequence of size T.+1, the obligation the dependent Tuple constructor
   needs to package gen_tuple_of below. *)
Lemma gen_map_size : size (map gen (enum 'I_T.+1)) == T.+1.
Proof. by rewrite size_map size_enum_ord. Qed.

(* Packages an arbitrary indexed generator function gen : 'I_T.+1 -> gT as
   the T.+1-tuple that Gen_PGGTypes expects for its sigmas field, so a
   concrete presentation can specify its generators by a formula rather than
   by an explicit tuple literal. *)
Definition gen_tuple_of : T.+1.-tuple gT := Tuple gen_map_size.

(* Reading gen_tuple_of at index i returns gen i: the tuple packaging is
   transparent to component access, so later proofs can reason about gen
   directly instead of unfolding the Tuple/nth_map construction. *)
Lemma gen_tuple_ofE (i : 'I_T.+1) : tnth gen_tuple_of i = gen i.
Proof.
rewrite (tnth_nth (gen ord0)) /= (nth_map ord0) ?size_enum_ord //.
by congr gen; rewrite nth_ord_enum.
Qed.

End gen_tuple_construction.

(* ========================================================================== *)
(* Permutation utilities for RAAG instances                                   *)
(* ========================================================================== *)

Local Lemma neqS {fT : eqType} {a b : fT} : a != b -> b != a.
Proof. by rewrite eq_sym. Qed.

(* Two transpositions (a b) and (c d) on pairwise-disjoint support commute:
   swapping one pair does not touch the other pair's points. This is the
   permutation identity that certifies commutativity witnesses for the
   abelian and star-type RAAG group presentations elsewhere in this
   development, where a generating set of disjoint transpositions is meant
   to realise a free abelian or star-shaped commuting structure. *)
Lemma tperm_disjoint_comm (fT : finType) (a b c d : fT) :
  a != c -> a != d -> b != c -> b != d ->
  (tperm a b * tperm c d = tperm c d * tperm a b)%g.
Proof.
move=> Hac Had Hbc Hbd.
have Hca := neqS Hac; have Hda := neqS Had.
have Hcb := neqS Hbc; have Hdb := neqS Hbd.
apply/permP => x; rewrite !permM.
have [->|Hxa] := eqVneq x a.
  by rewrite tpermL (tpermD Hca Hda) (tpermD Hcb Hdb) tpermL.
have [->|Hxb] := eqVneq x b.
  by rewrite tpermR (tpermD Hca Hda) (tpermD Hcb Hdb) tpermR.
have [->|Hxc] := eqVneq x c.
  by rewrite (tpermD Hac Hbc) !tpermL (tpermD Had Hbd).
have [->|Hxd] := eqVneq x d.
  by rewrite (tpermD Had Hbd) !tpermR (tpermD Hac Hbc).
by rewrite !(tpermD _ _) // 1?eq_sym.
Qed.

(* A single non-commuting pair of generators already forces the whole
   generated group G to be non-abelian, since G is generated by the
   sigmas and abelianity of a generated group is equivalent to its
   generators pairwise commuting. This is the one-witness criterion
   the RAAG presentations use to certify a non-abelian instance without
   checking every pair of group elements. *)
Lemma gen_nonabelian (M : MonodromyReprWithGeneratorType)
    (i j : 'I_(@pgg_ngens' M).+1) :
  i != j ->
  (tnth (@pgg_sigmas M) i * tnth (@pgg_sigmas M) j !=
   tnth (@pgg_sigmas M) j * tnth (@pgg_sigmas M) i)%g ->
  ~~ abelian (pgg_G M).
Proof.
move=> Hij Hnc.
rewrite -(pgg_sigmas_gen (s:=M)) abelian_gen.
apply/negP => /centsP Habel.
have Hi : tnth (@pgg_sigmas M) i \in
          [set tnth (@pgg_sigmas M) k | k : 'I_(@pgg_ngens' M).+1]
  by apply/imsetP; exists i.
have Hj : tnth (@pgg_sigmas M) j \in
          [set tnth (@pgg_sigmas M) k | k : 'I_(@pgg_ngens' M).+1]
  by apply/imsetP; exists j.
by move: Hnc; rewrite (Habel _ Hi _ Hj) eqxx.
Qed.

(******************************************************************************)
(*  Weighted generator distribution                                           *)
(******************************************************************************)

Local Open Scope fdist_scope.

HB.mixin Record hasWeights (R : realType) (T : PGGTypes)
    of MonodromyReprWithGenerator T := {
  pgg_gen_weights : R.-fdist 'I_(@pgg_ngens' T).+1 ;
}.

#[short(type=WeightedPGGType)]
HB.structure Definition WeightedPGG (R : realType) :=
  { T of isMonodromyRepr T & hasGenerators T & hasWeights R T }.
