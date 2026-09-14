(* audit-naming scratch: what does the `Fail Lemma ... Proof. ... Qed.`
   shape of probe_bridge.v:128-132 actually check?  `Fail` swallows only the
   `Lemma` sentence; the `Proof. ... Qed.` that follows runs on its own. *)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype.

Fail Lemma bogus : 1 = 2.
Proof. reflexivity. Qed.
