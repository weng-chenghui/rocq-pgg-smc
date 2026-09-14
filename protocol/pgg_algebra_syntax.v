(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* The algebra block: a named surface for PGGAlgebraic                        *)
(*                                                                            *)
(* A PGGAlgebraic has sixteen fields and an instance writing it as one        *)
(* constructor application supplies sixteen positional arguments. This file   *)
(* gives the same record a block surface in which every component is written  *)
(* under a name, and it fills five of the fields on the instance's behalf.    *)
(* Two of the five are the seat starts and the shuffle action on share        *)
(* indices, and the third is the coordinate law relating them: with the seats *)
(* starting at the deck positions in order and the monodromy being the deck   *)
(* action transported along the share count, that law is ord_coordE and holds *)
(* for every instance of this shape, so an instance in the block surface      *)
(* writes no coordinate proof. The remaining two are the dealer readout,      *)
(* which the block fixes to the identity, and the share-count equation, which *)
(* the block asserts by reflexivity and so checks against the scheme.         *)
(*                                                                            *)
(* Three components of the threshold scheme are named in the block and        *)
(* checked against the scheme by conversion: its encoding, its reconstruction *)
(* and its privacy proof. The scheme itself would determine all three         *)
(* silently, and a reader of the block would then have to open the scheme's   *)
(* own file to learn what a share is; pinned_scheme is what puts them at the  *)
(* use site without letting them drift from it.                               *)
(*                                                                            *)
(* The token pgg_rho in the shuffle clause is a literal of the rule, not a    *)
(* slot: this surface fixes the shuffle action on share indices to the deck   *)
(* action, and the clause's only variable content is the proof that           *)
(* reconstruction is unchanged by it.                                         *)
(*                                                                            *)
(* Two clauses are optional. The walk clause names a second generating        *)
(* alphabet with the proof that it generates the same group, which is the     *)
(* alphabet a mixing argument runs on; without it a step takes the            *)
(* presentation generators. The leaks clause names a coalition size at which  *)
(* privacy fails, with the proof that it does; without it the instance claims *)
(* no failure. Neither clause reaches any proposition proved about a run.     *)
(*                                                                            *)
(* The block spends five identifiers as global keywords in every file that    *)
(* requires this one: encode, read, private, leaks and shuffled_by. Each of   *)
(* them follows a slot in some rule, which is what makes a token a keyword;   *)
(* the tokens algebra, mount, walk, along, seat, players, secret, deal,       *)
(* cache, seats and pgg_rho lead a rule or follow a literal and stay          *)
(* identifiers.                                                               *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   ord_monodromy   == the deck action read as an action on share indices    *)
(*   ord_starts      == the seats starting at the deck positions in order     *)
(*   mk_walk         == the walk clause's payload                             *)
(*   no_walk         == the absent walk clause                                *)
(*   mk_leaks        == the leaks clause's payload                            *)
(*   no_leaks        == the absent leaks clause                               *)
(*   pinned_scheme   == a scheme with its encoding, reconstruction and        *)
(*                      privacy proof checked against the ones written        *)
(*   mk_algebra      == the PGGAlgebraic a block builds                       *)
(*                                                                            *)
(* Key results:                                                               *)
(*   ord_starts_uniq == the seats of such an instance begin at distinct cards *)
(*   ord_coordE      == seat i's share index under a shuffle is that          *)
(*                      shuffle's image of seat i's start                     *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_instance.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     The three fields the block fills                                       *)
(******************************************************************************)

(* The shuffle action on share indices of an instance whose shares are the
   deck positions: the deck action, transported along the share-count equation.
   It is the map a block writes into pga_monodromy, and the reason an instance
   in this surface owes no relation between share indices and cards beyond the
   share count itself. *)
Definition ord_monodromy (m n : nat) (gens : m.+1.-tuple {perm 'I_n.+2})
    (T : nat) (Hc : T = n.+2) : {perm 'I_n.+2} -> {perm 'I_T} :=
  fun w0 => cast_perm (esym Hc) (@pgg_rho (Gen_PGGTypes gens) w0).

(* The seats of such an instance, starting at the deck positions in order and
   transported along the same equation. Seat i starts at card i, which is what
   makes the coordinate law below an identity rather than a hypothesis. *)
Definition ord_starts (n T : nat) (Hc : T = n.+2) : T.-tuple 'I_n.+2 :=
  tcast (esym Hc) (ord_tuple n.+2).

(* No two seats begin at the same card. The uniqueness pga_starts_uniq asks
   for, discharged once for the whole surface. *)
Lemma ord_starts_uniq (n T : nat) (Hc : T = n.+2) : uniq (ord_starts Hc).
Proof. by rewrite /ord_starts val_tcast val_ord_tuple enum_uniq. Qed.

(* Seat i's share index under a shuffle is the deck position that shuffle
   sends seat i's start to. The single coordinate hypothesis from which the
   framework derives static reconstruction, holding for every instance whose
   seats and monodromy are the two definitions above. *)
Lemma ord_coordE (m n : nat) (gens : m.+1.-tuple {perm 'I_n.+2})
    (T : nat) (Hc : T = n.+2) (w0 : {perm 'I_n.+2}) (i : 'I_T) :
  ord_monodromy gens Hc w0 i
  = cast_ord (esym Hc)
      (@pgg_rho (Gen_PGGTypes gens) w0 (tnth (ord_starts Hc) i)).
Proof.
rewrite /ord_monodromy /ord_starts cast_permE tcastE.
by rewrite esymK tnth_ord_tuple.
Qed.

(******************************************************************************)
(*     The two optional clauses                                               *)
(******************************************************************************)

(* The walk clause's payload: a second generating alphabet with the proof that
   it generates the group the presentation generators generate. *)
Definition mk_walk (m n k : nat) (gens : m.+1.-tuple {perm 'I_n.+2})
    (w : k.+1.-tuple {perm 'I_n.+2})
    (Hw : (<<[set tnth w i | i : 'I_k.+1]>>
           = <<[set tnth gens i | i : 'I_m.+1]>>)%G)
  : option { k : nat & { w : k.+1.-tuple {perm 'I_n.+2}
      | (<<[set tnth w i | i : 'I_k.+1]>>
         = <<[set tnth gens i | i : 'I_m.+1]>>)%G } } :=
  Some (existT _ k (exist _ w Hw)).
Arguments mk_walk {m n k} gens w Hw.

(* The absent walk clause: a step of this instance takes a presentation
   generator. *)
Definition no_walk (m n : nat) (gens : m.+1.-tuple {perm 'I_n.+2})
  : option { k : nat & { w : k.+1.-tuple {perm 'I_n.+2}
      | (<<[set tnth w i | i : 'I_k.+1]>>
         = <<[set tnth gens i | i : 'I_m.+1]>>)%G } } := None.
Arguments no_walk {m n} gens.

(* The leaks clause's payload: a coalition size and a proof that privacy fails
   there. The proposition is whatever the instance proved, because sharpness is
   stated in the instance's probability model and the algebra has none. *)
Definition mk_leaks (k : nat) (P : Prop) (H : P)
  : option { k : nat & { P : Prop & P } } :=
  Some (existT _ k (existT _ P H)).
Arguments mk_leaks k [P] H.

(* The absent leaks clause: the instance claims no coalition size at which
   privacy fails. *)
Definition no_leaks : option { k : nat & { P : Prop & P } } := None.

(******************************************************************************)
(*     The scheme with its three written parts pinned                         *)
(******************************************************************************)

(* The scheme itself, with its encoding, its reconstruction and its privacy
   proof checked by conversion against the three terms written in the block.
   The three equations are the whole content: the result is the scheme
   unchanged, and what the combinator buys is that a block naming a different
   encoding from the scheme's own is rejected where it is written. *)
Definition pinned_scheme (secretT shareT : Type)
    (S : ThresholdScheme secretT shareT)
    (e : secretT -> (ts_T' S).+1.-tuple shareT)
    (r : (ts_T' S).+1.-tuple shareT -> secretT)
    (p : forall (s1 s2 : secretT) (shares : (ts_T' S).+1.-tuple shareT)
                (C : {set 'I_(ts_T' S).+1}),
           #|C| < (ts_k' S).+1 -> ts_valid S s1 shares ->
           exists shares' : (ts_T' S).+1.-tuple shareT,
             ts_valid S s2 shares'
             /\ (forall i : 'I_(ts_T' S).+1,
                   i \in C -> tnth shares' i = tnth shares i))
    (_ : ts_encode S = e) (_ : ts_recon S = r) (_ : ts_private S = p)
    : ThresholdScheme secretT shareT := S.
Arguments pinned_scheme : clear implicits.

(******************************************************************************)
(*     The record a block builds                                              *)
(******************************************************************************)

(* The PGGAlgebraic of an instance whose shares are its deck positions: the
   generators, an optional walk alphabet, the scheme with its leak annotation,
   and the seat list, with the seat starts, the dealer readout, the monodromy
   and the coordinate law supplied by this file. The share-count equation is an
   argument rather than a field of the scheme, so a block whose deck size and
   share count disagree is rejected at the equation.

   The shuffle action is ord_monodromy and is not an argument. A block
   therefore names no action of its own, and the only variable content of its
   shuffle clause is Hinv, the proof that reconstruction survives that fixed
   action. An instance whose shares are not its deck positions is outside this
   surface and writes MkPGGAlgebraic directly. *)
Definition mk_algebra (m n : nat) (gens : m.+1.-tuple {perm 'I_n.+2})
    (mv : option { k : nat & { w : k.+1.-tuple {perm 'I_n.+2}
            | (<<[set tnth w i | i : 'I_k.+1]>>
               = <<[set tnth gens i | i : 'I_m.+1]>>)%G } })
    (secretT : Type) (S : ThresholdScheme secretT 'I_n.+2)
    (lk : option { k : nat & { P : Prop & P } })
    (Hc : (ts_T' S).+1 = n.+2)
    (Hst : uniq (ord_starts Hc))
    (Hinv : @ts_recon_perm_invariant _ (pgg_G (Gen_PGGTypes gens)) _ _ S
              (ord_monodromy gens Hc))
    (pl : seq 'I_(ts_T' S).+1)
    (Hpl : pl = enum 'I_(ts_T' S).+1) : PGGAlgebraic :=
  @MkPGGAlgebraic m n gens mv secretT S lk Hc (ord_starts Hc) Hst id
    (ord_monodromy gens Hc) Hinv (@ord_coordE m n gens _ Hc) pl Hpl.
Arguments mk_algebra : clear implicits.

(******************************************************************************)
(*     The block surface                                                      *)
(******************************************************************************)

(* The four rules are the walk clause present or absent against the leaks
   clause present or absent. Every rule repeats no slot, and all four are
   only parsing because the record they build prints as a record.

   In shuffled_by pgg_rho by Hinv the token pgg_rho is a literal of the rule
   and not a slot: the shuffle action of this surface is fixed to the deck
   action, and a block cannot substitute another one. What the clause takes is
   Hinv alone, the proof that reconstruction is unchanged by that action. The
   coordinate law relating share indices to cards is likewise not written,
   because at a fixed action and seats in order it is ord_coordE. *)

Notation "'algebra' '{' 'mount' '<<' gens '>>' ';' 'walk' 'along' w 'by' Hw ';' 'seat' 'players' st 'by' Hst ';' 'secret' T ';' 'deal' S 'encode' e 'read' r 'private' 'by' p 'leaks' 'at' k 'by' Hk 'shuffled_by' 'pgg_rho' 'by' Hinv ';' 'cache' 'seats' pl 'by' Hpl '}'" :=
  (@mk_algebra _ _ gens (mk_walk gens w Hw) T
     (@pinned_scheme T _ S e r p erefl erefl erefl)
     (@mk_leaks k _ Hk) erefl (Hst : uniq st) Hinv pl Hpl)
  (at level 0, gens at level 0, w at level 0, Hw at level 0,
   st at level 0, Hst at level 0, T at level 0, S at level 0,
   e at level 0, r at level 0, p at level 0, k at level 0, Hk at level 0,
   Hinv at level 0, pl at level 0, Hpl at level 0, only parsing).

Notation "'algebra' '{' 'mount' '<<' gens '>>' ';' 'walk' 'along' w 'by' Hw ';' 'seat' 'players' st 'by' Hst ';' 'secret' T ';' 'deal' S 'encode' e 'read' r 'private' 'by' p 'shuffled_by' 'pgg_rho' 'by' Hinv ';' 'cache' 'seats' pl 'by' Hpl '}'" :=
  (@mk_algebra _ _ gens (mk_walk gens w Hw) T
     (@pinned_scheme T _ S e r p erefl erefl erefl)
     no_leaks erefl (Hst : uniq st) Hinv pl Hpl)
  (at level 0, gens at level 0, w at level 0, Hw at level 0,
   st at level 0, Hst at level 0, T at level 0, S at level 0,
   e at level 0, r at level 0, p at level 0, Hinv at level 0,
   pl at level 0, Hpl at level 0, only parsing).

Notation "'algebra' '{' 'mount' '<<' gens '>>' ';' 'seat' 'players' st 'by' Hst ';' 'secret' T ';' 'deal' S 'encode' e 'read' r 'private' 'by' p 'leaks' 'at' k 'by' Hk 'shuffled_by' 'pgg_rho' 'by' Hinv ';' 'cache' 'seats' pl 'by' Hpl '}'" :=
  (@mk_algebra _ _ gens (no_walk gens) T
     (@pinned_scheme T _ S e r p erefl erefl erefl)
     (@mk_leaks k _ Hk) erefl (Hst : uniq st) Hinv pl Hpl)
  (at level 0, gens at level 0, st at level 0, Hst at level 0,
   T at level 0, S at level 0, e at level 0, r at level 0, p at level 0,
   k at level 0, Hk at level 0, Hinv at level 0,
   pl at level 0, Hpl at level 0, only parsing).

Notation "'algebra' '{' 'mount' '<<' gens '>>' ';' 'seat' 'players' st 'by' Hst ';' 'secret' T ';' 'deal' S 'encode' e 'read' r 'private' 'by' p 'shuffled_by' 'pgg_rho' 'by' Hinv ';' 'cache' 'seats' pl 'by' Hpl '}'" :=
  (@mk_algebra _ _ gens (no_walk gens) T
     (@pinned_scheme T _ S e r p erefl erefl erefl)
     no_leaks erefl (Hst : uniq st) Hinv pl Hpl)
  (at level 0, gens at level 0, st at level 0, Hst at level 0,
   T at level 0, S at level 0, e at level 0, r at level 0, p at level 0,
   Hinv at level 0, pl at level 0, Hpl at level 0, only parsing).
