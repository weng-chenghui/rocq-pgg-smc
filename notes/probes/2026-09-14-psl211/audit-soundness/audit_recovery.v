(* audit_recovery: ledger row L16 of the PSL(2,11) spec.  What does the
   eleven-reveal statement of probe_decomposition.v actually say?  Compile with
     sh run.sh audit-soundness/audit_recovery.v
   from notes/probes/2026-09-14-psl211. *)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** deck_eleven - two distinct-card decks that agree at eleven of the twelve
    positions are the same deck.  This is pigeonhole on the CODES and holds
    for any twelve-card deck whatever, with no reference to the two Steiner
    systems: psl211_eleven_reveal_class (probe_decomposition.v line 78) is
    this statement composed with orbit_class, so it carries no design
    content and says nothing about the colour observer the privacy half of
    the spec is stated for. *)
Lemma deck_eleven (sh sh' : 12.-tuple 'I_12) (j : 'I_12) :
  uniq sh -> uniq sh' ->
  (forall i, i != j -> tnth sh' i = tnth sh i) -> sh' = sh.
Proof.
move=> /tuple_uniqP finj /tuple_uniqP f'inj Hoff.
apply: eq_from_tnth => i.
have [->|ine] := eqVneq i j; last exact: Hoff.
have [k f'k] : exists k, tnth sh' k = tnth sh j.
  by have [g _ gc] := injF_bij f'inj; exists (g (tnth sh j)); rewrite gc.
have [kj|kne] := eqVneq k j; first by rewrite -f'k kj.
have Hk : tnth sh k = tnth sh j by rewrite -(Hoff k kne) f'k.
by move/finj: Hk => kj; rewrite kj eqxx in kne.
Qed.

(** colour_eleven - the statement the colour observer actually needs: two
    heart sets of the six cards of one colour that agree at eleven of the
    twelve positions are equal, so eleven revealed COLOURS determine the
    class.  This is the colour pigeonhole the spec names in section 4, and
    it is a different statement from deck_eleven: it constrains only the
    colour of each card, which is all a coalition of the physical model
    ever sees. *)
Lemma colour_eleven (H H' : {set 'I_12}) (j : 'I_12) :
  #|H| = 6 -> #|H'| = 6 ->
  (forall i, i != j -> (i \in H') = (i \in H)) -> H' = H.
Proof.
move=> H6 H'6 Hoff.
have Hd : H' :\ j = H :\ j.
  by apply/setP => i; rewrite !in_setD1; case: (eqVneq i j) => //= ij;
     rewrite Hoff.
have Hc : (j \in H') + #|H' :\ j| = (j \in H) + #|H :\ j|.
  by rewrite -!(cardsD1 j) H6 H'6.
have Hj : (j \in H') = (j \in H).
  by move: Hc; rewrite Hd => /addIn /(congr1 odd) /=; case: (j \in H');
     case: (j \in H).
apply/setP => i; have [->|ij] := eqVneq i j; first exact: Hj.
exact: Hoff.
Qed.
