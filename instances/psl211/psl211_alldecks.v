(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* psl211_alldecks: the laid deck of the twelve-card chirality instance and   *)
(*                  the deal counts of its two chiralities                    *)
(*                                                                            *)
(* The dealer of psl211_exec.v draws a chirality bit and lays the scheme's    *)
(* own encoding of it.  The dealer written here is handed a whole deck        *)
(* description instead: a chirality bit, one of the 132 block lines of that   *)
(* chirality's Steiner system for the six heart positions, one labelling of   *)
(* the six heart codes and one of the six club codes.  It lays that           *)
(* description as the dealt deck and recovers the chirality bit of its own    *)
(* input.  Every deal of either chirality is therefore a run of this          *)
(* instance, which is what lets a probability model average over decks        *)
(* instead of fixing a representative one.                                    *)
(*                                                                            *)
(* The counting half of the file says what a coalition of at most five seats  *)
(* learns from the codes it reads: at every cut and every reading, the deck   *)
(* descriptions of one chirality producing that reading are exactly as many   *)
(* as those of the other.  The deals of class b producing a reading are       *)
(* indexed by the blocks of the class's Steiner system meeting the cut image  *)
(* of the coalition in the reading's heart pattern, times one extension       *)
(* count for the heart labelling and one for the club labelling; the block    *)
(* counts agree because both tables are S(5,6,12) designs and the pattern has *)
(* at most five points, and the two extension counts do not mention the       *)
(* class.                                                                     *)
(*                                                                            *)
(* The laid deck reduces at no input.  A position enters its labelling        *)
(* through inord, whose insub is guarded by the Qed-opaque idP, so vm_compute *)
(* stops inside the ordinal and every statement below is proved               *)
(* symbolically.  This is not a consequence of the 136857600 deck             *)
(* descriptions: it holds at a single fixed one.                              *)
(*                                                                            *)
(* This file deliberately omits Set Implicit Arguments, as psl211_orbit.v     *)
(* does: every helper below is applied at explicit block rows and explicit    *)
(* labellings, and a stolen leading parameter is the mistake hardest to       *)
(* diagnose in that position.                                                 *)
(*                                                                            *)
(* The counting half cites card_prescribed from lib/perm_uniform.v:117, whose *)
(* own imports pull in all_algebra, boolp, reals and infotheo's fdist, proba, *)
(* jfdist_cond and entropy.  That import was measured at 4.31 s against       *)
(* 0.52 s for a version using only perm_exchange, by the plan audit on        *)
(* 2026-09-15 and not re-measured here.  This file itself compiles in about   *)
(* ten seconds at a peak of 1.96 GB, one rocqworker (measured 2026-09-15,     *)
(* 7.3 s to 11.3 s across runs).                                              *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   psl211_deal             == a block line and two colour labellings        *)
(*   psl211_inputT           == a chirality bit and a deal                    *)
(*   psl211_code12           == a card code read modulo twelve                *)
(*   psl211_class_tbl b      == the 132-row block table of the class b        *)
(*   psl211_alldecks_row     == the block line a description names            *)
(*   psl211_alldecks_corow   == the six positions outside that block line     *)
(*   psl211_alldecks_seq     == the deck a description names, by position     *)
(*   psl211_alldecks_layout  == the deck a description names, as a tuple      *)
(*   psl211_alldecks_expected == the value the run recovers, the class bit    *)
(*   psl211_alldecks_params  == the run-level data of the all-decks run       *)
(*   psl211_alldecks_recon   == the reconstruction obligation of that run     *)
(*   psl211_alldecks_view    == the codes a coalition reads at a cut          *)
(*                                                                            *)
(* Key results:                                                               *)
(*   psl211_alldecks_gt0        == the description carrier is inhabited       *)
(*   psl211_alldecks_cardE      == it has 2 * 132 * 6! * 6! points            *)
(*   psl211_alldecks_uniq       == the laid deck has twelve distinct cards    *)
(*   psl211_alldecks_heart_setE == its heart positions are the named block    *)
(*   psl211_alldecks_subset_valid == its heart set is a block of one system   *)
(*   psl211_alldecks_classE     == its chirality is the input's class bit     *)
(*   psl211_alldecks_valid      == it is a valid deal of that bit             *)
(*   psl211_alldecks_ts_valid   == the same in the framework's spelling       *)
(*   psl211_alldecks_terminates == every process finishes inside the fuel     *)
(*   psl211_prescribed_of_set, psl211_perm_ext_count_ord,                     *)
(*   psl211_perm_ext_count0_ord == the same two counts at any N               *)
(*   psl211_perm_ext_count      == a labelling prescribed injectively on k    *)
(*                                 ranks extends in (6 - k)! ways             *)
(*   psl211_perm_ext_count0     == a prescription that repeats a code has no  *)
(*                                 extension                                  *)
(*   psl211_alldecks_read_setE  == the positions read are the cut image of    *)
(*                                 the coalition, of the coalition's size     *)
(*   psl211_alldecks_per_cut_count  == at one cut the two chiralities have    *)
(*                                 equally many deals producing a reading     *)
(*   psl211_alldecks_fiber_transfer == the same summed over the cuts          *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From pgg_smc Require Import smc_interpreter pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_instance.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.
From pgg_smc Require Import psl211_blocks psl211_group psl211_orbit.
From pgg_smc Require Import psl211_scheme psl211_profile psl211_exec.
From pgg_smc Require Import perm_uniform.

(* -------------------------------------------------------------------------- *)
(* The carrier, the layout and the run.                                       *)
(* -------------------------------------------------------------------------- *)

(* A Notation and not a Definition: behind a Definition the product's finite
   structure is not found where the carrier appears. *)
(** psl211_deal — a deal of the twelve-card chirality instance below the
    class: which block of the class's 132-row table carries the hearts, which
    labelling of the six heart codes it carries, and which labelling of the
    six club codes the complement carries. *)
Notation psl211_deal := (('I_132 * {perm 'I_6} * {perm 'I_6})%type).

(** psl211_inputT — the run argument of the all-decks dealer: a class bit and
    a deal.  The class bit is first and separate so that the secret is fst and
    the generic bridge applies with s := fst. *)
Notation psl211_inputT := ((bool * psl211_deal)%type).

(** psl211_code12 k — the card code k as a card of the twelve-card deck, read
    modulo twelve. *)
Definition psl211_code12 (k : nat) : 'I_12 := Ordinal (ltn_pmod k (ltn0Sn 11)).

(** psl211_class_tbl b — the 132-row block table of the class named by b. *)
Definition psl211_class_tbl (b : bool) : seq (seq nat) :=
  if b then psl211_mirror_tbl else psl211_hexad_tbl.

(** psl211_alldecks_row x — the block of the class's table that carries the
    hearts of the deck x names. *)
Definition psl211_alldecks_row (x : psl211_inputT) : seq nat :=
  nth [::] (psl211_class_tbl x.1) (val x.2.1.1).

(** psl211_alldecks_corow x — the six positions outside that block, in
    ascending order. *)
Definition psl211_alldecks_corow (x : psl211_inputT) : seq nat :=
  [seq p <- iota 0 12 | p \notin psl211_alldecks_row x].

(** psl211_alldecks_seq x — the deck the input names, as a list of codes by
    position: a position of the chosen block carries the heart code its
    labelling gives to the position's rank in the block, and every other
    position carries the club code its labelling gives to the position's rank
    in the complement. *)
Definition psl211_alldecks_seq (x : psl211_inputT) : seq nat :=
  let: (b, (j, ph, pc)) := x in
  let H := psl211_alldecks_row x in
  let K := psl211_alldecks_corow x in
  [seq (if p \in H then val (ph (inord (index p H)))
        else 6 + val (pc (inord (index p K)))) | p <- iota 0 12].

(** psl211_alldecks_layout x — that deck as the twelve-tuple the framework's
    sharing family lays, one card per position. *)
Definition psl211_alldecks_layout (x : psl211_inputT)
  : (ts_T' (pga_scheme psl211_algebra)).+1.-tuple 'I_(pga_n psl211_algebra).+2
  := [tuple psl211_code12 (nth 0 (psl211_alldecks_seq x) (val i)) | i < 12].

(** psl211_alldecks_expected x — the value the all-decks run recovers is the
    class bit of its input. *)
Definition psl211_alldecks_expected (x : psl211_inputT) : bool := x.1.

(** psl211_alldecks_params — the run-level data of the all-decks run: the run
    argument is a whole deck description rather than a bare secret, the layout
    lays that description as the dealt deck, and the value the run recovers is
    the class bit of its input.  This is the supplied-layout mode of the
    framework; the dealer-dealt mode of psl211_exec.v is this mode at the
    canonical encoding, which is why the endpoint equation serves both. *)
Definition psl211_alldecks_params : ExecutionParams psl211_algebra :=
  supplied_input_params psl211_algebra psl211_inputT
    psl211_alldecks_layout psl211_alldecks_expected psl211_fuel.

(* At [set: _] and not at the argument-type predicate {: _}, because `U is
   fdist_uniform_supp and takes a {set _}. *)
(** psl211_alldecks_gt0 — the carrier of deck descriptions is inhabited, so a
    uniform draw over it exists. *)
Lemma psl211_alldecks_gt0 : (0 < #|[set: psl211_inputT]|)%N.
Proof. by apply/card_gt0P; exists (true, (ord0, 1%g, 1%g)); rewrite inE. Qed.

(* Left factored: the product as one nat literal is a Nat.of_num_uint term
   whose unary expansion the kernel would have to build. *)
(** psl211_alldecks_cardE — the deck descriptions number two classes, times
    132 block lines per class, times a labelling of each of the two six-code
    colour groups. *)
Lemma psl211_alldecks_cardE : #|{: psl211_inputT}| = 2 * 132 * 6`! * 6`!.
Proof. by rewrite !card_prod card_bool card_ord !card_Sn mulnA. Qed.

(* -------------------------------------------------------------------------- *)
(* The deal function, named apart from the table lookup.                      *)
(* -------------------------------------------------------------------------- *)

(** ad_code H K ph pc p — the card code laid at position p by a deal whose
    hearts sit on the block H: the heart code the labelling ph gives to p's
    rank inside H when p lies in H, and otherwise the club code the labelling
    pc gives to p's rank inside the complement K, shifted past the six heart
    codes.  Naming it separates the two colour branches, which carry the whole
    content of distinctness and of the heart set, from the table lookup that
    chose H, which carries the chirality. *)
Local Definition ad_code (H K : seq nat) (ph pc : {perm 'I_6}) (p : nat)
  : nat :=
  if p \in H then nat_of_ord (ph (inord (index p H)))
  else 6 + nat_of_ord (pc (inord (index p K))).

(** ad_heart_lt12 — a heart code is a card code. *)
Local Lemma ad_heart_lt12 (m : 'I_6) : (nat_of_ord m < 12)%N.
Proof. by apply: (leq_trans (ltn_ord m)). Qed.

(** ad_club_lt12 — a club code is a card code: the six club codes occupy the
    upper half of the twelve, which is why the two colour branches of ad_code
    can never collide. *)
Local Lemma ad_club_lt12 (m : 'I_6) : (6 + nat_of_ord m < 12)%N.
Proof. by move: (ltn_ord m); rewrite -(ltn_add2l 6). Qed.

(** ad_inordK — the rank injection into 'I_6 is the identity on ranks below
    six, so a rank inside a six-element row survives the passage through the
    labelling's index type. *)
Local Lemma ad_inordK (m : nat) (Hm : (m < 6)%N) :
  nat_of_ord (inord m : 'I_6) = m.
Proof. by apply: inordK. Qed.

(* -------------------------------------------------------------------------- *)
(* The block row the class table and the index name.                          *)
(* -------------------------------------------------------------------------- *)

(** ad_class_tbl_size — either Steiner system is listed by 132 rows, so every
    ordinal of 'I_132 names a row of either class. *)
Local Lemma ad_class_tbl_size (b : bool) : size (psl211_class_tbl b) = 132.
Proof.
have E : forall tbl : seq (seq nat), psl211_tbl_ok tbl -> size tbl = 132.
  by move=> tbl; case/andP => /eqP.
by case: b; [exact: (E _ psl211_tbl_ok_mirrorT)
           | exact: (E _ psl211_tbl_ok_hexadT)].
Qed.

(** ad_class_tbl_asc6 — every row of either class's table is an ascending
    six-list of positions below twelve. *)
Local Lemma ad_class_tbl_asc6 (b : bool) : all psl211_asc6 (psl211_class_tbl b).
Proof.
by case: b; [exact: (psl211_tbl_ok_asc6 psl211_tbl_ok_mirrorT)
           | exact: (psl211_tbl_ok_asc6 psl211_tbl_ok_hexadT)].
Qed.

(* The one use of the block index, and it is symbolic: mem_nth against the
   table size, never the row literal. *)
(** ad_row_mem — the row an input names is a row of its class's table. *)
Local Lemma ad_row_mem (x : psl211_inputT) :
  psl211_alldecks_row x \in psl211_class_tbl x.1.
Proof.
rewrite /psl211_alldecks_row; apply: mem_nth.
by rewrite ad_class_tbl_size; exact: ltn_ord.
Qed.

(** ad_row_asc6 — the heart block of an all-decks input is an ascending
    six-list of positions below twelve. *)
Local Lemma ad_row_asc6 (x : psl211_inputT) :
  psl211_asc6 (psl211_alldecks_row x).
Proof. exact: (allP (ad_class_tbl_asc6 x.1) _ (ad_row_mem x)). Qed.

(** ad_asc6_uniq — an ascending list repeats no entry. *)
Local Lemma ad_asc6_uniq (H : seq nat) : psl211_asc6 H -> uniq H.
Proof.
by case/and3P => Hso _ _; move: Hso; rewrite ltn_sorted_uniq_leq => /andP[].
Qed.

(** ad_asc6_size — an ascending six-list has six entries. *)
Local Lemma ad_asc6_size (H : seq nat) : psl211_asc6 H -> size H = 6.
Proof. by case/and3P => _ _ /eqP. Qed.

(** ad_asc6_lt12 — an entry of an ascending six-list is a position of the
    twelve-card deck. *)
Local Lemma ad_asc6_lt12 (H : seq nat) (p : nat) :
  psl211_asc6 H -> p \in H -> (p < 12)%N.
Proof. by case/and3P => _ /allP Hlt _ /Hlt. Qed.

(* -------------------------------------------------------------------------- *)
(* The complement of the block row.                                           *)
(* -------------------------------------------------------------------------- *)

(* count_predC spells the complement as a simpl_pred and does not match
   psl211_alldecks_corow's fun p => p \notin H, hence this restatement. *)
(** ad_size_filter_split — a list splits by a predicate into two parts whose
    sizes add up. *)
Local Lemma ad_size_filter_split (T : eqType) (a : pred T) (s : seq T) :
  (size [seq x <- s | a x] + size [seq x <- s | ~~ a x])%N = size s.
Proof.
by elim: s => [|x s IH] //=;
  case: (a x) => /=; [rewrite addSn IH | rewrite addnS IH].
Qed.

(** ad_corow_size — the complement of a heart block inside the twelve
    positions has six positions, so the club labelling has exactly as many
    ranks to name as it has codes. *)
Local Lemma ad_corow_size (H : seq nat) :
  psl211_asc6 H -> size [seq p <- iota 0 12 | p \notin H] = 6.
Proof.
move=> HA.
have Hin : [seq p <- iota 0 12 | p \in H] =i H.
  move=> p; rewrite mem_filter mem_iota add0n /=.
  case Hp : (p \in H) => //=.
  exact: (ad_asc6_lt12 H p HA Hp).
(* The numeral 6 is a subterm of the numeral 12, so a backwards rewrite with
   size H = 6 would fire inside iota 0 12.  The size is transported through the
   permutation instead. *)
have Hperm : perm_eq [seq p <- iota 0 12 | p \in H] H.
  apply: uniq_perm.
  - by apply: filter_uniq; exact: iota_uniq.
  - exact: (ad_asc6_uniq H HA).
  - exact: Hin.
have Hs6 : size [seq p <- iota 0 12 | p \in H] = 6.
  by rewrite (perm_size Hperm) (ad_asc6_size H HA).
have Hsp := ad_size_filter_split _ (fun p : nat => p \in H) (iota 0 12).
rewrite Hs6 size_iota in Hsp.
by apply/eqP; rewrite -(eqn_add2l 6) Hsp.
Qed.

(** ad_corow_mem — a position outside the heart block is a position of the
    complement, which is what lets the club branch of ad_code be read as a
    rank inside a six-element list. *)
Local Lemma ad_corow_mem (H : seq nat) (i : 'I_12) :
  (nat_of_ord i \in H) = false ->
  nat_of_ord i \in [seq p <- iota 0 12 | p \notin H].
Proof.
by move=> Hi; rewrite mem_filter Hi mem_iota add0n /=; exact: ltn_ord.
Qed.

(* -------------------------------------------------------------------------- *)
(* Reading one position of the layout.                                        *)
(* -------------------------------------------------------------------------- *)

(** ad_tnthE — a position of the layout carries the code the deal list holds
    at that position, taken modulo twelve by the layout's card injection. *)
Local Lemma ad_tnthE (x : psl211_inputT) (i : 'I_12) :
  nat_of_ord (tnth (psl211_alldecks_layout x) i)
  = (nth 0 (psl211_alldecks_seq x) (nat_of_ord i) %% 12)%N.
Proof. by rewrite /psl211_alldecks_layout tnth_mktuple. Qed.

(** ad_seqE — the deal list of an input written in its destructured form is
    the deal function applied along the twelve positions. *)
Local Lemma ad_seqE (b : bool) (j : 'I_132) (ph pc : {perm 'I_6}) :
  psl211_alldecks_seq (b, (j, ph, pc))
  = [seq ad_code (psl211_alldecks_row (b, (j, ph, pc)))
                 (psl211_alldecks_corow (b, (j, ph, pc))) ph pc p
    | p <- iota 0 12].
Proof. by []. Qed.

(** ad_entryE — the card at a position of the layout is exactly the code the
    deal function gives that position: the modulus of the layout's card
    injection never fires, because both colour branches already lie below
    twelve.  Every statement about the layout below is read through this
    equation. *)
Local Lemma ad_entryE (b : bool) (j : 'I_132) (ph pc : {perm 'I_6})
    (i : 'I_12) :
  nat_of_ord (tnth (psl211_alldecks_layout (b, (j, ph, pc))) i)
  = ad_code (psl211_alldecks_row (b, (j, ph, pc)))
            (psl211_alldecks_corow (b, (j, ph, pc))) ph pc (nat_of_ord i).
Proof.
rewrite ad_tnthE ad_seqE (nth_map 0); last by rewrite size_iota; exact: ltn_ord.
rewrite nth_iota; last exact: ltn_ord.
rewrite add0n; apply: modn_small.
rewrite /ad_code; case: ifP => _; [exact: ad_heart_lt12 | exact: ad_club_lt12].
Qed.

(* -------------------------------------------------------------------------- *)
(* Distinctness.                                                              *)
(* -------------------------------------------------------------------------- *)

(** ad_idx6 — the rank of an entry inside a six-element list is below six. *)
Local Lemma ad_idx6 (L : seq nat) (p : nat) :
  size L = 6 -> p \in L -> (index p L < 6)%N.
Proof. by move=> HL Hp; rewrite -HL index_mem. Qed.

(** ad_idx_inj — two positions of a six-element list that a labelling sends to
    the same code are the same position.  The labelling is injective, the rank
    injection is injective below six, and the rank of a member recovers the
    member, so a colour branch of ad_code is injective on its own colour. *)
Local Lemma ad_idx_inj (L : seq nat) (p q : nat) (g : {perm 'I_6}) :
  size L = 6 -> p \in L -> q \in L ->
  g (inord (index p L)) = g (inord (index q L)) -> p = q.
Proof.
move=> HL Hp Hq /perm_inj Hio.
have E : index p L = index q L.
  rewrite -(ad_inordK (index p L) (ad_idx6 L p HL Hp)) Hio.
  exact: (ad_inordK (index q L) (ad_idx6 L q HL Hq)).
by rewrite -(nth_index 0 Hp) E (nth_index 0 Hq).
Qed.

(* Over an abstract layout and an abstract block, so that the block index
   never has to be enumerated. *)
(** ad_uniq_gen — a twelve-position layout read by the deal function of an
    ascending six-block deals twelve distinct cards.  The hearts are distinct
    because the heart labelling and the rank map are injective on the block,
    the clubs likewise on the complement, and no heart code equals a club code
    because the club codes start at six. *)
Local Lemma ad_uniq_gen (H : seq nat) (ph pc : {perm 'I_6})
    (L : 12.-tuple 'I_12) :
  psl211_asc6 H ->
  (forall i : 'I_12,
     nat_of_ord (tnth L i)
     = ad_code H [seq p <- iota 0 12 | p \notin H] ph pc (nat_of_ord i)) ->
  uniq L.
Proof.
move=> HA HE.
have HsH : size H = 6 := ad_asc6_size H HA.
have HsK : size [seq p <- iota 0 12 | p \notin H] = 6 := ad_corow_size H HA.
apply/tuple_uniqP => i1 i2 Heq.
apply: val_inj.
have E : ad_code H [seq p <- iota 0 12 | p \notin H] ph pc (nat_of_ord i1)
       = ad_code H [seq p <- iota 0 12 | p \notin H] ph pc (nat_of_ord i2).
  by rewrite -!HE Heq.
move: E; rewrite /ad_code.
case: ifP => Hi1; case: ifP => Hi2.
- by move/ord_inj/(ad_idx_inj H (nat_of_ord i1) (nat_of_ord i2) ph HsH Hi1 Hi2).
- move=> E; move: (ltn_ord (ph (inord (index (nat_of_ord i1) H)))).
  by rewrite E ltnNge leq_addr.
- move=> E; move: (ltn_ord (ph (inord (index (nat_of_ord i2) H)))).
  by rewrite -E ltnNge leq_addr.
- move/eqP; rewrite eqn_add2l; move/eqP/ord_inj.
  by move/(ad_idx_inj [seq p <- iota 0 12 | p \notin H]
            (nat_of_ord i1) (nat_of_ord i2) pc HsK
            (ad_corow_mem H i1 Hi1) (ad_corow_mem H i2 Hi2)).
Qed.

(** psl211_alldecks_uniq — the all-decks layout deals twelve distinct cards,
    for every class bit, every block line and every pair of labellings.  The
    hearts are distinct because the heart labelling and the rank map are
    injective on the block, the clubs likewise on the complement, and no heart
    code equals a club code because the club codes start at six.  This is
    psl211_deck_ok of the layout, the first of the three conjuncts of the
    orbit scheme's validity predicate, and it is what lets the dealer be
    driven by a uniform draw over the whole input carrier instead of by a
    chosen representative deal. *)
Lemma psl211_alldecks_uniq (x : psl211_inputT) :
  uniq (psl211_alldecks_layout x).
Proof.
case: x => b [[j ph] pc].
apply: (ad_uniq_gen (psl211_alldecks_row (b, (j, ph, pc))) ph pc
                    (psl211_alldecks_layout (b, (j, ph, pc)))).
- exact: ad_row_asc6.
- exact: ad_entryE.
Qed.

(* -------------------------------------------------------------------------- *)
(* The heart positions of a deal.                                             *)
(* -------------------------------------------------------------------------- *)

(** ad_valE — the subtype projection of an ordinal is its coercion to nat.
    psl211_orbit.v writes the heart test and the code-list bridge with the
    subtype projection while the layout of this file is read through the
    coercion; the two are the same map, and this lemma is what lets one be
    rewritten into the other. *)
Local Lemma ad_valE (n : nat) (c : 'I_n) : val c = nat_of_ord c.
Proof. by []. Qed.

(** ad_heart_gen — a twelve-position layout read by the deal function of a
    block H holds a heart exactly at the positions of H.  The heart branch of
    the deal function lands below six and the club branch lands at six or
    above, so the colour of a position is decided by nothing but membership of
    H; the block is therefore recoverable from the deal, which is what the
    chirality readout needs.  No shape hypothesis on H is used. *)
Local Lemma ad_heart_gen (H : seq nat) (ph pc : {perm 'I_6})
    (L : 12.-tuple 'I_12) :
  (forall i : 'I_12,
     nat_of_ord (tnth L i)
     = ad_code H [seq p <- iota 0 12 | p \notin H] ph pc (nat_of_ord i)) ->
  psl211_heart_set L = psl211_list_to_set H.
Proof.
move=> HE; apply/setP => i.
rewrite /psl211_heart_set /psl211_list_to_set !inE /psl211_is_heart !ad_valE.
rewrite HE /ad_code.
(* case: ifP replaces the membership test on both sides of the equation, so
   each branch is the colour bound of that branch and nothing else. *)
case: ifP => _; first exact: ltn_ord.
by rewrite ltnNge leq_addr.
Qed.

(** psl211_alldecks_heart_setE — the heart positions of the all-decks layout
    are the block the input names.  Read the other way, the dealer's only
    freedom that touches the secret is the choice of table, since the block
    line and the two labellings leave the heart set on the same block. *)
Lemma psl211_alldecks_heart_setE (x : psl211_inputT) :
  psl211_heart_set (psl211_alldecks_layout x)
  = psl211_list_to_set (psl211_alldecks_row x).
Proof.
case: x => b [[j ph] pc].
apply: (ad_heart_gen (psl211_alldecks_row (b, (j, ph, pc))) ph pc
                     (psl211_alldecks_layout (b, (j, ph, pc)))).
exact: ad_entryE.
Qed.

(* -------------------------------------------------------------------------- *)
(* The heart set is a block of one of the two systems.                        *)
(* -------------------------------------------------------------------------- *)

(* Only this direction of the table-to-family bridge is needed, and
   psl211_orbit.v's own bridge is Local. *)
(** ad_row_in_mirror_blocks — a row of the mirror table denotes a block of the
    mirror system. *)
Local Lemma ad_row_in_mirror_blocks (R : seq nat) :
  R \in psl211_mirror_tbl -> psl211_list_to_set R \in psl211_mirror_blocks.
Proof.
move=> HR; rewrite /psl211_mirror_blocks /psl211_sets_of inE.
by apply/hasP; exists R; [exact: HR | exact: eqxx].
Qed.

(** ad_row_in_hexad_blocks — a row of the hexad table denotes a block of the
    hexad system. *)
Local Lemma ad_row_in_hexad_blocks (R : seq nat) :
  R \in psl211_hexad_tbl -> psl211_list_to_set R \in psl211_hexad_blocks.
Proof.
move=> HR; rewrite /psl211_hexad_blocks /psl211_sets_of inE.
by apply/hasP; exists R; [exact: HR | exact: eqxx].
Qed.

(** psl211_alldecks_subset_valid — the heart set of the all-decks layout is a
    block of one of the two Steiner systems.  This is the second conjunct of
    psl211_orbit_valid, the condition that says the deal is one the scheme can
    have produced, and it holds for every input rather than for a chosen
    representative deal. *)
Lemma psl211_alldecks_subset_valid (x : psl211_inputT) :
  psl211_subset_valid (psl211_heart_set (psl211_alldecks_layout x)).
Proof.
rewrite psl211_alldecks_heart_setE /psl211_subset_valid.
move: (ad_row_mem x); rewrite /psl211_class_tbl.
case: (x.1) => Hm; apply/orP; [left | right].
- exact: (ad_row_in_mirror_blocks _ Hm).
- exact: (ad_row_in_hexad_blocks _ Hm).
Qed.

(* -------------------------------------------------------------------------- *)
(* The chirality the layout carries, and its validity.                        *)
(* -------------------------------------------------------------------------- *)

(** psl211_alldecks_classE — the chirality bit read off the all-decks layout
    is the class bit of the input.  The mirror direction is the table-to-
    family bridge; the hexad direction is that bridge together with the
    disjointness of the two Steiner systems, which is the only place the two
    systems are compared and the only reason the classifier is not merely a
    membership test that could accidentally hold. *)
Lemma psl211_alldecks_classE (x : psl211_inputT) :
  psl211_orbit_class (psl211_alldecks_layout x) = x.1.
Proof.
rewrite /psl211_orbit_class psl211_alldecks_heart_setE /psl211_subset_class.
move: (ad_row_mem x); rewrite /psl211_class_tbl.
case: (x.1) => Hm; first exact: (ad_row_in_mirror_blocks _ Hm).
apply: (disjointFl psl211_blocks_disjoint).
exact: (ad_row_in_hexad_blocks _ Hm).
Qed.

(** psl211_alldecks_valid — the all-decks layout is a valid deal of the class
    bit of its input: twelve distinct cards, a heart set that is a block of
    one of the two Steiner systems, and a chirality readout that returns the
    bit.  Because this holds at every input, the dealer may be driven by a
    uniform draw over the whole input carrier rather than by a fixed
    representative deal. *)
Lemma psl211_alldecks_valid (x : psl211_inputT) :
  psl211_orbit_valid x.1 (psl211_alldecks_layout x).
Proof.
split; first exact: psl211_alldecks_uniq.
by split; [exact: psl211_alldecks_subset_valid | exact: psl211_alldecks_classE].
Qed.

(** psl211_alldecks_ts_valid — the same validity in the sharing framework's
    own spelling, at the scheme the algebraic record of the instance carries
    and at the expected secret the supplied-input parameters name.  The two
    spellings agree by conversion, so the framework's obligation is discharged
    by the scheme-level statement with no transport. *)
Lemma psl211_alldecks_ts_valid (x : psl211_inputT) :
  ts_valid (pga_scheme psl211_algebra)
    (psl211_alldecks_expected x) (psl211_alldecks_layout x).
Proof. exact: psl211_alldecks_valid. Qed.

(* -------------------------------------------------------------------------- *)
(* The run facts of the all-decks run.                                        *)
(* -------------------------------------------------------------------------- *)

(* vm_compute never destructs the layout, so its stuck ordinal content is
   carried through unchanged and the all-decks mode needs no more reduction
   to terminate than the dealer-dealt one. *)
(** psl211_alldecks_terminates — every process of the fourteen-process
    all-decks run finishes inside the fuel, at every deck description and
    every cut. *)
Lemma psl211_alldecks_terminates :
  instance_terminates_stmt psl211_alldecks_params.
Proof. by vm_compute. Qed.

(** psl211_alldecks_recon — decoding the coalition-free endpoints of the
    all-decks run returns the class bit, from validity alone.  The framework
    derives it from the coordinate law, so all reconstruction requires of this
    instance is distinctness, the heart set and the chirality readout. *)
Definition psl211_alldecks_recon : instance_recon_stmt psl211_alldecks_params :=
  supplied_static_recon psl211_algebra psl211_alldecks_ts_valid.

(* -------------------------------------------------------------------------- *)
(* The extension count of a prescribed labelling.                             *)
(* -------------------------------------------------------------------------- *)

Section psl211_ext_count.
Variable N : nat.

(** psl211_prescribed_of_set — the permutations agreeing with t on K are the
    prescription of t along the canonical indexing of K, which is the form
    perm_uniform.v counts. *)
Lemma psl211_prescribed_of_set (K : {set 'I_N}) (t : 'I_N -> 'I_N) :
  [set ph : {perm 'I_N} | [forall k in K, ph k == t k]]
  = prescribed (@enum_val _ K) (fun i => t (@enum_val _ K i)).
Proof.
apply/setP => ph; rewrite inE.
apply/idP/prescribedP => [/forallP H i|H].
  by apply/eqP; move: (H (@enum_val _ K i)); rewrite enum_valP.
apply/forallP => x; apply/implyP => Hx.
have Hx' := enum_rankK_in Hx Hx.
by move: (H (enum_rank_in Hx x)); rewrite Hx' => ->.
Qed.

(** psl211_perm_ext_count_ord — a permutation prescribed injectively on a set
    of k points extends in (N - k)! ways. *)
Lemma psl211_perm_ext_count_ord (K : {set 'I_N}) (t : 'I_N -> 'I_N) :
  {in K &, injective t} ->
  #|[set ph : {perm 'I_N} | [forall k in K, ph k == t k]]| = (N - #|K|)`!.
Proof.
move=> Hinj.
have Hv : injective (fun i : 'I_#|K| => t (@enum_val _ K i)).
  move=> i j Hij; apply: enum_val_inj.
  by apply: Hinj; [exact: enum_valP | exact: enum_valP | exact: Hij].
have HkN : (#|K| <= N)%N by have := max_card (mem K); rewrite card_ord.
rewrite psl211_prescribed_of_set.
by rewrite (card_prescribed (@enum_val_inj _ K) Hv HkN).
Qed.

(** psl211_perm_ext_count0_ord — a prescription that is not injective on K is
    met by no permutation. *)
Lemma psl211_perm_ext_count0_ord (K : {set 'I_N}) (t : 'I_N -> 'I_N) :
  ~ {in K &, injective t} ->
  #|[set ph : {perm 'I_N} | [forall k in K, ph k == t k]]| = 0.
Proof.
move=> Hni; apply/eqP; rewrite cards_eq0; apply/eqP; apply/setP => ph.
rewrite !inE; apply: negbTE; apply/negP => /forallP Hall.
apply: Hni => x y Hx Hy Hxy.
have Hpx : ph x = t x by move: (Hall x); rewrite Hx /= => /eqP.
have Hpy : ph y = t y by move: (Hall y); rewrite Hy /= => /eqP.
by apply: (perm_inj (s := ph)); rewrite Hpx Hpy.
Qed.

End psl211_ext_count.

(** psl211_perm_ext_count — a labelling of the six codes of one colour that is
    prescribed on a set K of ranks, injectively, extends in exactly
    (6 - |K|)! ways.  This is the labelling factor of the deal count: a
    reading pins the labelling on the ranks the coalition sees and leaves the
    rest free, and the factor depends on the size of K alone, so it is the
    same on both sides of the class comparison. *)
Lemma psl211_perm_ext_count (K : {set 'I_6}) (t : 'I_6 -> 'I_6) :
  {in K &, injective t} ->
  #|[set ph : {perm 'I_6} | [forall k in K, ph k == t k]]| = (6 - #|K|)`!.
Proof. exact: (@psl211_perm_ext_count_ord 6 K t). Qed.

(** psl211_perm_ext_count0 — a prescription that is not injective on K has no
    extension at all.  This is the colour-inconsistent branch of the deal
    count: a reading that names one code at two ranks is produced by no deal
    of either class. *)
Lemma psl211_perm_ext_count0 (K : {set 'I_6}) (t : 'I_6 -> 'I_6) :
  ~ {in K &, injective t} ->
  #|[set ph : {perm 'I_6} | [forall k in K, ph k == t k]]| = 0.
Proof. exact: (@psl211_perm_ext_count0_ord 6 K t). Qed.

(* -------------------------------------------------------------------------- *)
(* The coalition's reading and the positions it covers.                       *)
(* -------------------------------------------------------------------------- *)

(* Both are spelled through the derived profile rather than as 'I_12, so that
   the framework's obligations unify with the instance's statements by
   conversion. *)
(** seatT — a seat of the instance's starting interface, the index a coalition
    is a set of. *)
Local Notation seatT :=
  ('I_(pi_T' (mp_PI (instance_profile psl211_algebra))).+1).

(** cardT — a card of the twelve-card deck, the value a seat reads. *)
Local Notation cardT :=
  ('I_(pgg_N' (mp_M (instance_profile psl211_algebra))).+1).

(** psl211_alldecks_view C x g — the coalition's reading of the all-decks
    deck, written on the instance's own side: seat i in C reads the card the
    laid deck puts at the shuffle image of i, every other seat reads ord0.
    The counting argument is stated about this function; the framework's
    static_coalition_obs is the same reading in the framework's own
    spelling. *)
Definition psl211_alldecks_view (C : {set seatT}) (x : psl211_inputT)
    (g : pgg_gT psl211_M) : {ffun seatT -> cardT} :=
  [ffun i => if i \in C
             then tnth (psl211_alldecks_layout x) (@pgg_rho psl211_M g i)
             else ord0].

(** psl211_alldecks_read_setE — the positions a coalition reads are the image
    of the coalition under the cut, and that image has the coalition's own
    size because a shuffle is a permutation.  The image, not the preimage, is
    the set the block count is taken over, and its size is what bounds that
    count to at most five points. *)
Lemma psl211_alldecks_read_setE (C : {set seatT}) (g : pgg_gT psl211_M) :
  #|[set (@pgg_rho psl211_M g i) | i in C]| = #|C|.
Proof. by rewrite card_imset //; exact: perm_inj. Qed.

(* -------------------------------------------------------------------------- *)
(* Ranks inside a block, and the code lists of position sets.                 *)
(* -------------------------------------------------------------------------- *)

(** ad_row b j — the block line j of the class b, as a list of positions. *)
Local Definition ad_row (b : bool) (j : 'I_132) : seq nat :=
  nth [::] (psl211_class_tbl b) (nat_of_ord j).

(** ad_co H — the positions outside the block H, in ascending order. *)
Local Definition ad_co (H : seq nat) : seq nat :=
  [seq p <- iota 0 12 | p \notin H].

(** ad_row_asc6' — ad_row_asc6 at the block line spelled as ad_row b j: a
    block line of either class is an ascending six-list of positions below
    twelve. *)
Local Lemma ad_row_asc6' (b : bool) (j : 'I_132) : psl211_asc6 (ad_row b j).
Proof. exact: (ad_row_asc6 (b, (j, 1%g, 1%g))). Qed.

(** ad_row_size — a block line carries six positions. *)
Local Lemma ad_row_size (b : bool) (j : 'I_132) : size (ad_row b j) = 6.
Proof. exact: (ad_asc6_size _ (ad_row_asc6' b j)). Qed.

(** ad_co_size — the complement of a block line carries the other six. *)
Local Lemma ad_co_size (b : bool) (j : 'I_132) :
  size (ad_co (ad_row b j)) = 6.
Proof. exact: (ad_corow_size _ (ad_row_asc6' b j)). Qed.

(** ad_entryRE — the entry equation of the layout, at the block line named by
    the deal and independently of the two labellings. *)
Local Lemma ad_entryRE (b : bool) (j : 'I_132) (ph pc : {perm 'I_6})
    (i : 'I_12) :
  nat_of_ord (tnth (psl211_alldecks_layout (b, (j, ph, pc))) i)
  = ad_code (ad_row b j) (ad_co (ad_row b j)) ph pc (nat_of_ord i).
Proof. by rewrite ad_entryE. Qed.

(** ad_inter_nil — an empty coalition traces no position on any row. *)
Local Lemma ad_inter_nil (R : seq nat) : psl211_inter R [::] = [::].
Proof. by rewrite /psl211_inter; elim: R => //= x R IH; rewrite in_nil IH. Qed.

(** ad_rank H p — the rank of the position p inside the six-list H. *)
Local Definition ad_rank (H : seq nat) (p : 'I_12) : 'I_6 :=
  inord (index (nat_of_ord p) H).

(** ad_pos H r — the position of rank r inside the six-list H. *)
Local Definition ad_pos (H : seq nat) (r : 'I_6) : 'I_12 :=
  inord (nth 0 H (nat_of_ord r)).

(** ad_rankE — the rank of a member of a six-list is its index there. *)
Local Lemma ad_rankE (H : seq nat) (p : 'I_12) :
  size H = 6 -> nat_of_ord p \in H ->
  nat_of_ord (ad_rank H p) = index (nat_of_ord p) H.
Proof. by move=> HL Hp; apply: ad_inordK; exact: ad_idx6. Qed.

(** ad_posK — the position of the rank of a member of a six-list is that
    member, so rank and position are mutually inverse on the list. *)
Local Lemma ad_posK (H : seq nat) (p : 'I_12) :
  size H = 6 -> nat_of_ord p \in H -> ad_pos H (ad_rank H p) = p.
Proof.
move=> HL Hp; rewrite /ad_pos (ad_rankE H p HL Hp) (nth_index 0 Hp).
exact: inord_val.
Qed.

(** ad_inH — membership of the set coded by H is membership of H. *)
Local Lemma ad_inH (H : seq nat) (p : 'I_12) :
  (p \in psl211_list_to_set H) = (nat_of_ord p \in H).
Proof. by rewrite /psl211_list_to_set inE. Qed.

(** ad_list_to_setK — the code list of a position set codes that set back. *)
Local Lemma ad_list_to_setK (S : {set 'I_12}) :
  psl211_list_to_set (map val (enum S)) = S.
Proof.
by apply/setP => i; rewrite /psl211_list_to_set inE (mem_map val_inj) mem_enum.
Qed.

(** ad_enum_lt12 — a code list of a position set lists positions. *)
Local Lemma ad_enum_lt12 (S : {set 'I_12}) :
  all (fun n => (n < 12)%N) (map val (enum S)).
Proof. by apply/allP => n /mapP[p _ ->]; exact: ltn_ord. Qed.

(** ad_perm_list_to_set — the code list of the set coded by an ascending list
    of positions permutes that list. *)
Local Lemma ad_perm_list_to_set (L : seq nat) :
  sorted ltn L -> all (fun n => (n < 12)%N) L ->
  perm_eq (map val (enum (psl211_list_to_set L))) L.
Proof.
move=> Hsort Hall.
apply: uniq_perm.
- rewrite (map_inj_uniq val_inj); exact: enum_uniq.
- exact: (sorted_uniq ltn_trans ltnn Hsort).
- move=> n; apply/mapP/idP => [[i Hi ->]|Hn];
    first by move: Hi; rewrite mem_enum inE.
  have Hn12 : (n < 12)%N by move/allP: Hall => /(_ n Hn).
  by exists (Ordinal Hn12); [rewrite mem_enum inE|].
Qed.

(** ad_list_to_set_inj — an ascending list of positions is recovered from the
    set it codes, so a set-level pattern equation and its code-list form say
    the same thing. *)
Local Lemma ad_list_to_set_inj (L L' : seq nat) :
  sorted ltn L -> all (fun n => (n < 12)%N) L ->
  sorted ltn L' -> all (fun n => (n < 12)%N) L' ->
  psl211_list_to_set L = psl211_list_to_set L' -> L = L'.
Proof.
move=> S1 A1 S2 A2 Heq; apply: (irr_sorted_eq ltn_trans ltnn) => //.
move=> n; rewrite -(perm_mem (ad_perm_list_to_set L S1 A1)) Heq.
by rewrite (perm_mem (ad_perm_list_to_set L' S2 A2)).
Qed.

(** ad_inter_setE — the set coded by the trace of a row on a code list is the
    intersection of the coded set with the coded position set. *)
Local Lemma ad_inter_setE (R : seq nat) (S : {set 'I_12}) :
  psl211_list_to_set (psl211_inter R (map val (enum S)))
  = psl211_list_to_set R :&: S.
Proof.
apply/setP => p; rewrite !inE /psl211_inter mem_filter.
by rewrite (mem_map val_inj) mem_enum andbC.
Qed.

(** ad_interE — the code-list form of a pattern equation and its set form
    agree.  psl211_pattern_count is a count over code lists and
    psl211_pattern_transfer is a statement about position sets; this is what
    carries one to the other at a single row. *)
Local Lemma ad_interE (R : seq nat) (S A : {set 'I_12}) :
  sorted ltn R -> all (fun n => (n < 12)%N) R ->
  (psl211_inter R (map val (enum S)) == map val (enum A))
  = (psl211_list_to_set R :&: S == A).
Proof.
move=> HR HR12; apply/eqP/eqP => [HI|HI].
  by rewrite -ad_inter_setE HI ad_list_to_setK.
apply: ad_list_to_set_inj.
- by apply: sorted_filter => // y x z; exact: ltn_trans.
- by apply/allP => n; rewrite mem_filter => /andP[_]; move/allP: HR12; apply.
- exact: psl211_sorted_val_enum.
- exact: ad_enum_lt12.
- by rewrite ad_inter_setE ad_list_to_setK.
Qed.

(** ad_forall_imset — a bounded quantifier over the image of a set is the
    quantifier over the set, composed with the map. *)
Local Lemma ad_forall_imset (D : {set 'I_12}) (f : 'I_12 -> 'I_6)
    (q : 'I_6 -> bool) :
  [forall k in [set f p | p in D], q k] = [forall p in D, q (f p)].
Proof.
apply/forallP/forallP => [H p|H k].
  by apply/implyP => Hp; move: (H (f p)) => /implyP; apply; exact: imset_f.
by apply/implyP => /imsetP[p Hp ->]; move: (H p) => /implyP; apply.
Qed.

(** ad_card_index_count — counting the rows of a 132-row table that satisfy a
    predicate through their index is counting them directly.  The deal set is
    split over an ordinal block line and psl211_pattern_count is a count over
    the table; this is the passage between the two. *)
Local Lemma ad_card_index_count (p : pred (seq nat)) (tbl : seq (seq nat)) :
  size tbl = 132 ->
  #|[set j : 'I_132 | p (nth [::] tbl (nat_of_ord j))]| = count p tbl.
Proof.
move=> Hsz; rewrite -sum1_card.
rewrite (eq_bigl (fun j : 'I_132 => p (nth [::] tbl (nat_of_ord j))));
  last by move=> j; rewrite inE.
rewrite -(big_mkord (fun i => p (nth [::] tbl i)) (fun=> 1%N)).
by rewrite -Hsz -(big_nth [::] p (fun=> 1%N)) sum1_count.
Qed.

(* -------------------------------------------------------------------------- *)
(* The deal count at one cut.                                                 *)
(* -------------------------------------------------------------------------- *)

(* The two counting statements below are pinned by their closed type and not
   by their source text: they are stated over the section variables C, g and
   v, generalized in that order, while the plan displays them with explicit
   binders.  A text diff against the plan shows that difference, which is not
   drift; the plan's own spelling is closed by exact: in
   notes/probes/2026-09-15-psl211-planb/t4_landed_canary.v. *)
Section psl211_alldecks_fibers.

Variable C : {set seatT}.
Variable g : pgg_gT psl211_M.
Variable v : {ffun seatT -> cardT}.

(** ad_P — the positions the coalition reads at the cut. *)
Local Definition ad_P : {set 'I_12} := [set (@pgg_rho psl211_M g i) | i in C].

(** ad_read p — the code the reading names at the position p. *)
Local Definition ad_read (p : 'I_12) : cardT :=
  v (((@pgg_rho psl211_M g)^-1)%g p).

(** ad_A — the positions the reading names with a heart code. *)
Local Definition ad_A : {set 'I_12} :=
  [set p in ad_P | psl211_is_heart (ad_read p)].

(** ad_offok — the reading is ord0 off the coalition, which is what the view
    of a coalition is by construction. *)
Local Definition ad_offok : bool :=
  [forall i, (i \notin C) ==> (v i == ord0)].

(** ad_readinj — the reading names distinct codes at distinct positions.  A
    reading that fails this is produced by no deal of either class, because
    every deal lays twelve distinct cards. *)
Local Definition ad_readinj : bool :=
  [forall p in ad_P, [forall q in ad_P, (ad_read p == ad_read q) ==> (p == q)]].

(** ad_ok — the reading is one a deal can produce at all: it vanishes off the
    coalition and it names distinct codes at distinct read positions.  Both
    conditions are properties of the reading and the cut alone, so a reading
    that fails either has no deal of either chirality behind it and the two
    counts are zero together. *)
Local Definition ad_ok : bool := ad_offok && ad_readinj.

(** ad_A_sub — the heart positions of the reading are positions the coalition
    reads. *)
Local Lemma ad_A_sub : ad_A \subset ad_P.
Proof. by apply/subsetP => p; rewrite inE => /andP[]. Qed.

(** ad_PE — the coalition reads as many positions as it has seats. *)
Local Lemma ad_PE : #|ad_P| = #|C|.
Proof. exact: psl211_alldecks_read_setE. Qed.

(** ad_inA — the reading names a heart at a position it reads exactly when
    that position is one of the heart positions. *)
Local Lemma ad_inA (p : 'I_12) :
  (p \in ad_A) = (p \in ad_P) && psl211_is_heart (ad_read p).
Proof. by rewrite /ad_A inE. Qed.

(** ad_readP — a position the coalition reads is the image of a seat and the
    reading there is that seat's. *)
Local Lemma ad_readP (i : seatT) :
  i \in C -> ad_read (@pgg_rho psl211_M g i) = v i.
Proof. by move=> _; rewrite /ad_read permK. Qed.

(** ad_memE — a deal produces the reading exactly when the reading vanishes
    off the coalition and the laid deck carries the named code at every
    position the coalition reads. *)
Local Lemma ad_memE (x : psl211_inputT) :
  (psl211_alldecks_view C x g == v)
  = ad_offok
    && [forall p in ad_P, tnth (psl211_alldecks_layout x) p == ad_read p].
Proof.
apply/idP/idP => [/eqP/ffunP Hv0|/andP[/forallP Hoff /forallP HP]].
  apply/andP; split.
    apply/forallP => i; apply/implyP => Hi.
    by move: (Hv0 i); rewrite ffunE (negbTE Hi) => <-.
  apply/forallP => p; apply/implyP => /imsetP[i Hi Hp].
  by rewrite Hp (ad_readP i Hi); move: (Hv0 i); rewrite ffunE Hi => ->.
apply/eqP/ffunP => i; rewrite ffunE; case: ifPn => Hi; last first.
  by move: (Hoff i); rewrite Hi /= => /eqP ->.
have HPi : (@pgg_rho psl211_M g i) \in ad_P by exact: imset_f.
move: (HP (@pgg_rho psl211_M g i)); rewrite HPi /= => /eqP ->.
exact: (ad_readP i Hi).
Qed.

(* -------------------------------------------------------------------------- *)
(* The prescriptions one row forces.                                          *)
(* -------------------------------------------------------------------------- *)

(** ad_hpin H — the heart ranks the reading pins inside the block H. *)
Local Definition ad_hpin (H : seq nat) : {set 'I_6} :=
  [set ad_rank H p | p in ad_A].

(** ad_cpin H — the club ranks the reading pins inside the complement. *)
Local Definition ad_cpin (H : seq nat) : {set 'I_6} :=
  [set ad_rank (ad_co H) p | p in ad_P :\: ad_A].

(** ad_th H — the heart code the reading forces at a rank of the block. *)
Local Definition ad_th (H : seq nat) (r : 'I_6) : 'I_6 :=
  inord (nat_of_ord (ad_read (ad_pos H r))).

(** ad_tc H — the club code the reading forces at a rank of the complement,
    decoded back into the six club codes. *)
Local Definition ad_tc (H : seq nat) (r : 'I_6) : 'I_6 :=
  inord (nat_of_ord (ad_read (ad_pos (ad_co H) r)) - 6).

(** ad_thE — at a heart position the block prescription names the code the
    reading names there. *)
Local Lemma ad_thE (H : seq nat) (p : 'I_12) :
  size H = 6 -> nat_of_ord p \in H -> psl211_is_heart (ad_read p) ->
  nat_of_ord (ad_th H (ad_rank H p)) = nat_of_ord (ad_read p).
Proof.
move=> HL Hp Hh; rewrite /ad_th (ad_posK H p HL Hp).
by apply: ad_inordK; exact: Hh.
Qed.

(** ad_tcE — at a club position the complement prescription names the
    reading's code decoded past the six heart codes. *)
Local Lemma ad_tcE (H : seq nat) (p : 'I_12) :
  size (ad_co H) = 6 -> nat_of_ord p \in ad_co H ->
  ~~ psl211_is_heart (ad_read p) ->
  nat_of_ord (ad_tc H (ad_rank (ad_co H) p))
  = (nat_of_ord (ad_read p) - 6)%N.
Proof.
move=> HK Hp Hc; rewrite /ad_tc (ad_posK _ p HK Hp).
apply: ad_inordK.
have Hge : (6 <= nat_of_ord (ad_read p))%N by rewrite leqNgt; exact: Hc.
by rewrite -(ltn_add2r 6) (subnK Hge); exact: ltn_ord.
Qed.

(** ad_patE — the pattern equation read at one position: a read position lies
    on the block line exactly when the reading names a heart there. *)
Local Lemma ad_patE (b : bool) (j : 'I_132) (p : 'I_12) :
  psl211_list_to_set (ad_row b j) :&: ad_P = ad_A ->
  (nat_of_ord p \in ad_row b j) && (p \in ad_P) = (p \in ad_A).
Proof. by move=> Hpat; rewrite -Hpat inE ad_inH. Qed.

(** ad_A_inrow — a heart position of the reading lies on the block line, once
    the block line meets the read positions in the reading's heart pattern. *)
Local Lemma ad_A_inrow (b : bool) (j : 'I_132) (p : 'I_12) :
  psl211_list_to_set (ad_row b j) :&: ad_P = ad_A ->
  p \in ad_A -> nat_of_ord p \in ad_row b j.
Proof. by move=> Hpat; rewrite -(ad_patE b j p Hpat) => /andP[]. Qed.

(** ad_D_incorow — a club position of the reading lies off the block line. *)
Local Lemma ad_D_incorow (b : bool) (j : 'I_132) (p : 'I_12) :
  psl211_list_to_set (ad_row b j) :&: ad_P = ad_A ->
  p \in ad_P :\: ad_A -> nat_of_ord p \in ad_co (ad_row b j).
Proof.
move=> Hpat; rewrite inE => /andP[HnA HP].
apply: ad_corow_mem; apply/negbTE; apply: contra HnA => Hin.
by rewrite -(ad_patE b j p Hpat) Hin HP.
Qed.


(** ad_patternE — a deal producing the reading has its block line meeting the
    read positions exactly in the reading's heart pattern.  This is the
    passage from the reading seat by seat to the set-level pattern the block
    count is taken at. *)
Local Lemma ad_patternE (b : bool) (j : 'I_132) (ph pc : {perm 'I_6}) :
  [forall p in ad_P,
     tnth (psl211_alldecks_layout (b, (j, ph, pc))) p == ad_read p] ->
  psl211_list_to_set (ad_row b j) :&: ad_P = ad_A.
Proof.
move=> /forallP Hall; apply/setP => p; rewrite inE ad_inH ad_inA.
case HpP : (p \in ad_P); last by rewrite andbF.
rewrite andbT /=.
have Hent : tnth (psl211_alldecks_layout (b, (j, ph, pc))) p = ad_read p.
  by apply/eqP; move: (Hall p); rewrite HpP.
have Hhs := psl211_alldecks_heart_setE (b, (j, ph, pc)).
have Hp12 : psl211_is_heart (tnth (psl211_alldecks_layout (b, (j, ph, pc))) p)
          = (nat_of_ord p \in ad_row b j).
  by move/setP/(_ p): Hhs; rewrite inE ad_inH.
by rewrite -Hp12 Hent.
Qed.

(** ad_factorE — at a block line meeting the read positions in the reading's
    heart pattern, producing the reading is exactly prescribing the heart
    labelling on the heart ranks and the club labelling on the club ranks.
    The two prescriptions are independent, which is what makes the fiber a
    product of two extension counts. *)
Local Lemma ad_factorE (b : bool) (j : 'I_132) (ph pc : {perm 'I_6}) :
  psl211_list_to_set (ad_row b j) :&: ad_P = ad_A ->
  [forall p in ad_P,
     tnth (psl211_alldecks_layout (b, (j, ph, pc))) p == ad_read p]
  = [forall k in ad_hpin (ad_row b j), ph k == ad_th (ad_row b j) k]
    && [forall k in ad_cpin (ad_row b j), pc k == ad_tc (ad_row b j) k].
Proof.
move=> Hpat.
have HL := ad_row_size b j.
have HK := ad_co_size b j.
apply/idP/idP => [/forallP Hall|/andP[]].
  apply/andP; split.
    rewrite /ad_hpin ad_forall_imset; apply/forallP => p; apply/implyP => HpA.
    have HpP : p \in ad_P := subsetP ad_A_sub _ HpA.
    have HpH : nat_of_ord p \in ad_row b j := ad_A_inrow b j p Hpat HpA.
    have Hh : psl211_is_heart (ad_read p).
      by move: HpA; rewrite ad_inA => /andP[].
    apply/eqP/ord_inj; rewrite (ad_thE _ p HL HpH Hh).
    have Hent : tnth (psl211_alldecks_layout (b, (j, ph, pc))) p = ad_read p.
      by apply/eqP; move: (Hall p); rewrite HpP.
    rewrite -Hent ad_entryRE /ad_code ifT //.
  rewrite /ad_cpin ad_forall_imset; apply/forallP => p; apply/implyP => HpD.
  have HpP : p \in ad_P by move: HpD; rewrite inE => /andP[].
  have HpK : nat_of_ord p \in ad_co (ad_row b j) := ad_D_incorow b j p Hpat HpD.
  have HnA : p \notin ad_A by move: HpD; rewrite inE => /andP[].
  have Hc : ~~ psl211_is_heart (ad_read p).
    by apply: contra HnA => Hh; rewrite ad_inA HpP Hh.
  have HpH : (nat_of_ord p \in ad_row b j) = false.
    by move: HpK; rewrite mem_filter => /andP[/negbTE].
  apply/eqP/ord_inj; rewrite (ad_tcE _ p HK HpK Hc).
  have Hent : tnth (psl211_alldecks_layout (b, (j, ph, pc))) p = ad_read p.
    by apply/eqP; move: (Hall p); rewrite HpP.
  by rewrite -Hent ad_entryRE /ad_code HpH addKn.
rewrite /ad_hpin /ad_cpin !ad_forall_imset => /forallP Hh /forallP Hc.
apply/forallP => p; apply/implyP => HpP.
case HpH : (nat_of_ord p \in ad_row b j).
  have HpA : p \in ad_A by rewrite -(ad_patE b j p Hpat) HpH HpP.
  have Hhb : psl211_is_heart (ad_read p).
    by move: HpA; rewrite ad_inA => /andP[].
  apply/eqP/ord_inj; rewrite ad_entryRE /ad_code ifT //.
  by move: (Hh p); rewrite HpA /= => /eqP ->; rewrite (ad_thE _ p HL HpH Hhb).
have HpA : (p \in ad_A) = false by rewrite -(ad_patE b j p Hpat) HpH.
have HpD : p \in ad_P :\: ad_A by rewrite inE HpA HpP.
have HpK : nat_of_ord p \in ad_co (ad_row b j) := ad_D_incorow b j p Hpat HpD.
have Hcb : ~~ psl211_is_heart (ad_read p).
  by move: HpA; rewrite ad_inA HpP /= => ->.
have Hge : (6 <= nat_of_ord (ad_read p))%N by rewrite leqNgt; exact: Hcb.
apply/eqP/ord_inj; rewrite ad_entryRE /ad_code HpH.
move: (Hc p); rewrite HpD /= => /eqP ->.
by rewrite (ad_tcE _ p HK HpK Hcb) (subnKC Hge).
Qed.

(** ad_hpin_card — the heart ranks the reading pins are as many as the heart
    positions it names, because rank and position are mutually inverse on the
    block line.  This is what turns the extension count's (6 - |K|)! into a
    factor the class comparison can cancel. *)
Local Lemma ad_hpin_card (b : bool) (j : 'I_132) :
  psl211_list_to_set (ad_row b j) :&: ad_P = ad_A ->
  #|ad_hpin (ad_row b j)| = #|ad_A|.
Proof.
move=> Hpat.
have Hinj : {in ad_A &, injective (ad_rank (ad_row b j))}.
  move=> p q Hp Hq Heq.
  rewrite -(ad_posK _ p (ad_row_size b j) (ad_A_inrow b j p Hpat Hp)) Heq.
  exact: (ad_posK _ q (ad_row_size b j) (ad_A_inrow b j q Hpat Hq)).
by rewrite /ad_hpin (card_in_imset Hinj).
Qed.

(** ad_cpin_card — the club ranks the reading pins are as many as the club
    positions it names. *)
Local Lemma ad_cpin_card (b : bool) (j : 'I_132) :
  psl211_list_to_set (ad_row b j) :&: ad_P = ad_A ->
  #|ad_cpin (ad_row b j)| = #|ad_P :\: ad_A|.
Proof.
move=> Hpat.
have Hinj : {in ad_P :\: ad_A &, injective (ad_rank (ad_co (ad_row b j)))}.
  move=> p q Hp Hq Heq.
  rewrite -(ad_posK _ p (ad_co_size b j) (ad_D_incorow b j p Hpat Hp)) Heq.
  exact: (ad_posK _ q (ad_co_size b j) (ad_D_incorow b j q Hpat Hq)).
by rewrite /ad_cpin (card_in_imset Hinj).
Qed.

(** ad_th_inj — the heart prescription is injective on the ranks it pins, so
    the extension count is the positive one.  Injectivity of the reading on
    the read positions is what decides this, and it mentions no class. *)
Local Lemma ad_th_inj (b : bool) (j : 'I_132) :
  ad_readinj -> psl211_list_to_set (ad_row b j) :&: ad_P = ad_A ->
  {in ad_hpin (ad_row b j) &, injective (ad_th (ad_row b j))}.
Proof.
move=> /forallP Hri Hpat k1 k2.
rewrite /ad_hpin => /imsetP[p Hp ->] /imsetP[q Hq ->] Heq.
have HpH := ad_A_inrow b j p Hpat Hp.
have HqH := ad_A_inrow b j q Hpat Hq.
have Hhp : psl211_is_heart (ad_read p).
  by move: Hp; rewrite ad_inA => /andP[].
have Hhq : psl211_is_heart (ad_read q).
  by move: Hq; rewrite ad_inA => /andP[].
have Hr : ad_read p = ad_read q.
  apply: ord_inj.
  by rewrite -(ad_thE _ p (ad_row_size b j) HpH Hhp) Heq
             (ad_thE _ q (ad_row_size b j) HqH Hhq).
have HpP : p \in ad_P := subsetP ad_A_sub _ Hp.
have HqP : q \in ad_P := subsetP ad_A_sub _ Hq.
move: (Hri p); rewrite HpP /= => /forallP/(_ q); rewrite HqP /=.
by rewrite Hr eqxx /= => /eqP ->.
Qed.

(** ad_tc_inj — the club prescription is injective on the ranks it pins. *)
Local Lemma ad_tc_inj (b : bool) (j : 'I_132) :
  ad_readinj -> psl211_list_to_set (ad_row b j) :&: ad_P = ad_A ->
  {in ad_cpin (ad_row b j) &, injective (ad_tc (ad_row b j))}.
Proof.
move=> /forallP Hri Hpat k1 k2.
rewrite /ad_cpin => /imsetP[p Hp ->] /imsetP[q Hq ->] Heq.
have HpK := ad_D_incorow b j p Hpat Hp.
have HqK := ad_D_incorow b j q Hpat Hq.
have HpP : p \in ad_P by move: Hp; rewrite inE => /andP[].
have HqP : q \in ad_P by move: Hq; rewrite inE => /andP[].
have Hcp : ~~ psl211_is_heart (ad_read p).
  have HnA : p \notin ad_A by move: Hp; rewrite inE => /andP[].
  by apply: contra HnA => Hh; rewrite ad_inA HpP Hh.
have Hcq : ~~ psl211_is_heart (ad_read q).
  have HnA : q \notin ad_A by move: Hq; rewrite inE => /andP[].
  by apply: contra HnA => Hh; rewrite ad_inA HqP Hh.
have Hgp : (6 <= nat_of_ord (ad_read p))%N by rewrite leqNgt; exact: Hcp.
have Hgq : (6 <= nat_of_ord (ad_read q))%N by rewrite leqNgt; exact: Hcq.
have Hr : ad_read p = ad_read q.
  apply: ord_inj; rewrite -(subnKC Hgp) -(subnKC Hgq).
  by rewrite -(ad_tcE _ p (ad_co_size b j) HpK Hcp) Heq
             (ad_tcE _ q (ad_co_size b j) HqK Hcq).
move: (Hri p); rewrite HpP /= => /forallP/(_ q); rewrite HqP /=.
by rewrite Hr eqxx /= => /eqP ->.
Qed.

(* The ad_ok premise is a departure from the audit counter-probe, which
   assumed this equation unconditionally as a section hypothesis
   (notes/probes/2026-09-15-psl211-planb/audit-plan/audit_t4_percut.v).  The
   unconditional form is false.  A reading that is nonzero off the coalition,
   or that names one code at two read positions, is produced by no deal, so
   its left side is 0 at every block line, while the right side is
   (6 - #|ad_A|)! * (6 - #|ad_P :\: ad_A|)! at every block line meeting the
   read positions in the pattern.  The premise constrains the reading and the
   cut alone and never the class, so ad_fiber_empty answers its negation with
   0 on both sides. *)
(** ad_fiber_at_row — the deals on one block line producing the reading are
    the pairs of labellings prescribed by that reading: the product of the two
    extension counts when the block line meets the read positions in the
    reading's heart pattern, and none otherwise.  Both factors are functions
    of the pattern alone, so neither mentions the class. *)
Local Lemma ad_fiber_at_row (b : bool) (j : 'I_132) :
  ad_ok ->
  #|[set pp : {perm 'I_6} * {perm 'I_6} |
       psl211_alldecks_view C (b, (j, pp.1, pp.2)) g == v]|
  = (if psl211_list_to_set (ad_row b j) :&: ad_P == ad_A
     then (6 - #|ad_A|)`! * (6 - #|ad_P :\: ad_A|)`!
     else 0)%N.
Proof.
case/andP => Hoff Hri; case: ifPn => [/eqP Hpat|Hpat]; last first.
  apply/eqP; rewrite cards_eq0; apply/eqP; apply/setP => pp; rewrite !inE.
  apply/negbTE/negP; rewrite ad_memE => /andP[_ Hall].
  by move: Hpat; rewrite (ad_patternE b j pp.1 pp.2 Hall) eqxx.
set H := ad_row b j.
have -> : [set pp : {perm 'I_6} * {perm 'I_6} |
             psl211_alldecks_view C (b, (j, pp.1, pp.2)) g == v]
        = setX [set ph : {perm 'I_6} |
                  [forall k in ad_hpin H, ph k == ad_th H k]]
               [set pc : {perm 'I_6} |
                  [forall k in ad_cpin H, pc k == ad_tc H k]].
  apply/setP => pp; rewrite !inE ad_memE Hoff /=.
  by rewrite (ad_factorE b j pp.1 pp.2 Hpat).
rewrite cardsX.
rewrite (psl211_perm_ext_count _ _ (ad_th_inj b j Hri Hpat)).
rewrite (psl211_perm_ext_count _ _ (ad_tc_inj b j Hri Hpat)).
by rewrite (ad_hpin_card b j Hpat) (ad_cpin_card b j Hpat).
Qed.

(** ad_fiber_empty — a reading that does not vanish off the coalition, or
    that names one code at two read positions, is produced by no deal of
    either class: every laid deck carries twelve distinct cards. *)
Local Lemma ad_fiber_empty (b : bool) :
  ~~ ad_ok ->
  #|[set y : psl211_deal | psl211_alldecks_view C (b, y) g == v]| = 0.
Proof.
move=> Hnok; apply/eqP; rewrite cards_eq0; apply/eqP; apply/setP => y.
rewrite !inE; apply/negbTE/negP => Hm.
move: Hnok => /negP; apply; rewrite /ad_ok.
move: Hm; rewrite ad_memE => /andP[-> /forallP Hall] /=.
have Hinj := tuple_uniqP _ (psl211_alldecks_uniq (b, y)).
apply/forallP => p; apply/implyP => HpP.
apply/forallP => q; apply/implyP => HqP; apply/implyP => /eqP Heq.
have Hp : tnth (psl211_alldecks_layout (b, y)) p = ad_read p.
  by apply/eqP; move: (Hall p); rewrite HpP.
have Hq : tnth (psl211_alldecks_layout (b, y)) q = ad_read q.
  by apply/eqP; move: (Hall q); rewrite HqP.
by apply/eqP; apply: Hinj; rewrite Hp Hq Heq.
Qed.

(** ad_split_over_row — the deals producing the reading split over the block
    line they name.  The block line is the coordinate the chirality enters
    through, so it is the coordinate the count is taken along. *)
Local Lemma ad_split_over_row (b : bool) :
  #|[set y : psl211_deal | psl211_alldecks_view C (b, y) g == v]|
  = (\sum_(j : 'I_132)
       #|[set pp : {perm 'I_6} * {perm 'I_6} |
            psl211_alldecks_view C (b, (j, pp.1, pp.2)) g == v]|)%N.
Proof.
rewrite -sum1_card.
rewrite (partition_big (fun y : psl211_deal => y.1.1) predT) //=.
apply: eq_bigr => j _.
rewrite (reindex_onto (fun pp : {perm 'I_6} * {perm 'I_6} => ((j, pp.1), pp.2))
                      (fun y : psl211_deal => (y.1.2, y.2))) /=; last first.
  by case=> [[jj ph] pc]; rewrite inE /= => /andP[_ /eqP ->].
rewrite -sum1_card; apply: eq_bigl; case=> ph pc.
by rewrite !inE /= !eqxx !andbT.
Qed.

(** ad_deal_count — the deals of one class producing the reading are the
    block lines of that class's Steiner system meeting the read positions in
    the reading's heart pattern, each carrying the same pair of labelling
    factors.  Only the first factor mentions the class. *)
Local Lemma ad_deal_count (b : bool) :
  ad_ok ->
  #|[set y : psl211_deal | psl211_alldecks_view C (b, y) g == v]|
  = (psl211_pattern_count (psl211_class_tbl b) (map val (enum ad_P))
                          (map val (enum ad_A))
     * ((6 - #|ad_A|)`! * (6 - #|ad_P :\: ad_A|)`!))%N.
Proof.
move=> Hok.
have Hc : count (fun R => psl211_list_to_set R :&: ad_P == ad_A)
                (psl211_class_tbl b)
        = psl211_pattern_count (psl211_class_tbl b) (map val (enum ad_P))
                               (map val (enum ad_A)).
  rewrite /psl211_pattern_count; apply: eq_in_count => R HR.
  case/and3P: (allP (ad_class_tbl_asc6 b) _ HR) => Hs Hl _.
  by rewrite (ad_interE R ad_P ad_A Hs Hl).
rewrite ad_split_over_row.
rewrite (eq_bigr _ (fun j _ => ad_fiber_at_row b j Hok)).
rewrite -big_mkcond /= sum_nat_const.
congr (_ * _)%N.
rewrite -Hc -(ad_card_index_count _ (psl211_class_tbl b) (ad_class_tbl_size b)).
by apply: eq_card => j; rewrite !inE.
Qed.

(* The plan's route step 4 puts the empty-coalition case at the top of
   psl211_alldecks_per_cut_count.  It is discharged here instead, where both
   sides collapse to the table size by ad_inter_nil and ad_class_tbl_size and
   the view never has to be shown constant. *)
(** ad_pattern_classE — the two Steiner systems have equally many block lines
    meeting the read positions in the reading's heart pattern.  Both are
    S(5,6,12) designs and the pattern has at most five points, so no block
    count a coalition of that size can take separates them.  At an empty
    coalition both counts are the whole table, which is where
    psl211_pattern_transfer's positivity premise is avoided rather than
    met. *)
Local Lemma ad_pattern_classE :
  (#|C| <= 5)%N ->
  psl211_pattern_count (psl211_class_tbl true) (map val (enum ad_P))
                       (map val (enum ad_A))
  = psl211_pattern_count (psl211_class_tbl false) (map val (enum ad_P))
                         (map val (enum ad_A)).
Proof.
move=> HC5; case: (posnP #|C|) => [HC0|HC0].
  have HP0 : ad_P = set0 by apply/eqP; rewrite -cards_eq0 ad_PE HC0.
  have HA0 : ad_A = set0.
    apply/eqP; rewrite -subset0; apply/subsetP => p Hp.
    by move: (subsetP ad_A_sub _ Hp); rewrite HP0.
  have He : forall tbl : seq (seq nat),
      psl211_pattern_count tbl [::] [::] = size tbl.
    move=> tbl; rewrite /psl211_pattern_count -[RHS]count_predT.
    by apply: eq_count => R; rewrite ad_inter_nil eqxx.
  have Hnil : map val (enum (set0 : {set 'I_12})) = [::] by rewrite enum_set0.
  by rewrite HP0 HA0 Hnil !He !ad_class_tbl_size.
have HP0' : (0 < #|ad_P|)%N by rewrite ad_PE.
have HP5 : (#|ad_P| <= 5)%N by rewrite ad_PE.
have -> : psl211_class_tbl true = psl211_mirror_tbl by [].
have -> : psl211_class_tbl false = psl211_hexad_tbl by [].
rewrite -(psl211_pattern_countE _ _ _
            (psl211_tbl_ok_asc6 psl211_tbl_ok_mirrorT) psl211_mirror_tbl_uniq).
rewrite -(psl211_pattern_countE _ _ _
            (psl211_tbl_ok_asc6 psl211_tbl_ok_hexadT) psl211_hexad_tbl_uniq).
rewrite -/psl211_mirror_blocks -/psl211_hexad_blocks.
by apply: psl211_pattern_transfer => //; exact: ad_A_sub.
Qed.

(** psl211_alldecks_per_cut_count — at one cut, one coalition of at most five
    seats and one reading, the two chiralities have equally many deals
    producing that reading.  The deals of class b producing a reading are
    indexed by the blocks of the class's Steiner system meeting the cut image
    of the coalition in the reading's heart pattern, times one extension count
    for the heart labelling and one for the club labelling; the block counts
    agree between the two systems because both are S(5,6,12) designs and the
    pattern has at most five points, and the two extension counts do not
    depend on the class at all.  This is the per-cut form;
    psl211_alldecks_fiber_transfer is its sum over the group and is the form
    the bridge consumes. *)
Lemma psl211_alldecks_per_cut_count :
  (#|C| <= 5)%N ->
  #|[set y : psl211_deal | psl211_alldecks_view C (true, y) g == v]|
  = #|[set y : psl211_deal | psl211_alldecks_view C (false, y) g == v]|.
Proof.
move=> HC5; case: (boolP ad_ok) => [Hok|Hnok]; last first.
  have Ht := ad_fiber_empty true Hnok.
  have Hf := ad_fiber_empty false Hnok.
  by transitivity 0; [exact: Ht | rewrite Hf].
have Ht := ad_deal_count true Hok.
have Hf := ad_deal_count false Hok.
have Hp := ad_pattern_classE HC5.
(* The two sides name the two tables, and a rewrite that is free to look at
   both makes unification compare the 132-row literals: psl211_class_tbl
   true and psl211_class_tbl false unfold to the two tables and the match
   descends into them.  The single rewrite was stopped here by Timeout 40 at
   40 s (measured 2026-09-15); the plan audit measured the related step-11
   shape, with the two table-size hypotheses in context, at 280 s and at
   420 s with one rocqworker at 3.3 GB (AUDIT-PLAN-B.md:37).  Each side is
   therefore reached by transitivity through a term that names one table
   only, and the last step is an exact. *)
transitivity (psl211_pattern_count (psl211_class_tbl true)
                (map val (enum ad_P)) (map val (enum ad_A))
              * ((6 - #|ad_A|)`! * (6 - #|ad_P :\: ad_A|)`!))%N.
  exact: Ht.
rewrite Hp; symmetry; exact: Hf.
Qed.

End psl211_alldecks_fibers.

(* The class bit is stripped by reindex_onto, not by an injection on pairs:
   no such injection lemma exists under this import set. *)
(** ad_partition_cut — the deck descriptions and cuts producing a reading
    split over the cut they name. *)
Local Lemma ad_partition_cut (C : {set seatT}) (v : {ffun seatT -> cardT})
    (b : bool) :
  #|[set u : psl211_inputT * pgg_gT psl211_M |
       (u.1.1 == b) && (u.2 \in pgg_G psl211_M)
       && (psl211_alldecks_view C u.1 u.2 == v)]|
  = (\sum_(g in pgg_G psl211_M)
       #|[set y : psl211_deal | psl211_alldecks_view C (b, y) g == v]|)%N.
Proof.
rewrite -sum1_card.
rewrite (partition_big (fun u : psl211_inputT * pgg_gT psl211_M => u.2)
                       (fun g => g \in pgg_G psl211_M)) /=; last first.
  by move=> u; rewrite inE => /andP[/andP[_ ->]].
apply: eq_bigr => g Hg.
rewrite (reindex_onto (fun y : psl211_deal => ((b, y), g))
                      (fun u : psl211_inputT * pgg_gT psl211_M => u.1.2)) /=;
  last by case=> [[bb y] gg]; rewrite inE /=
            => /andP[/andP[/andP[/eqP -> _] _] /eqP ->].
rewrite -sum1_card; apply: eq_bigl => y.
by rewrite !inE /= !eqxx Hg /= !andbT.
Qed.

(** psl211_alldecks_fiber_transfer — the same counts summed over the cuts of
    the group: for every reading of a coalition of at most five seats, the
    deck descriptions and cuts producing it are as many under one chirality as
    under the other.  This is the counting premise the uniform-pair bridge
    consumes: no other instance-specific fact enters the independence
    statement. *)
Lemma psl211_alldecks_fiber_transfer (C : {set seatT})
    (v : {ffun seatT -> cardT}) :
  (#|C| <= 5)%N ->
  #|[set u : psl211_inputT * pgg_gT psl211_M |
       (u.1.1 == true) && (u.2 \in pgg_G psl211_M)
       && (psl211_alldecks_view C u.1 u.2 == v)]|
  = #|[set u : psl211_inputT * pgg_gT psl211_M |
       (u.1.1 == false) && (u.2 \in pgg_G psl211_M)
       && (psl211_alldecks_view C u.1 u.2 == v)]|.
Proof.
move=> HC5; rewrite !ad_partition_cut.
by apply: eq_bigr => g _; exact: (psl211_alldecks_per_cut_count C g v HC5).
Qed.
