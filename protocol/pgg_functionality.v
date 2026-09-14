(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Functionality: the ideal function a run realises                           *)
(*                                                                            *)
(* A secure computation is specified by an ideal function and a coalition     *)
(* size it tolerates, and is realised by an execution whose output matches    *)
(* that function and whose coalition views carry no more information than     *)
(* the output does. This file carries the specification side of that          *)
(* correspondence and the correctness half of the correspondence itself; the  *)
(* execution side is OE.ObservedExecution of pgg_observed_execution.v and     *)
(* the privacy half is stated per instance.                                   *)
(*                                                                            *)
(* Correctness is available in two forms. realises is pointwise: at every     *)
(* run argument and every shuffle in the group, decoding the static endpoint  *)
(* reading returns the ideal function's value. realises_expected identifies   *)
(* the record's recovered value with the ideal function as terms, which       *)
(* conversion decides, so an instance whose expected value is written as the  *)
(* ideal function discharges it by reflexivity. The second implies the first  *)
(* and also transfers to the executed endpoints, so an instance proves the    *)
(* term identification alone.                                                 *)
(*                                                                            *)
(* The conditional-mutual-information form of standard security is stated     *)
(* over an arbitrary probability model rather than over an execution,         *)
(* because an execution carries no probability model: the model an instance   *)
(* analyses it in is a separate value.                                        *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   Functionality         == the ideal function and the tolerated coalition  *)
(*                            size                                            *)
(*   algebra_functionality == the specification a dealer-dealt run of an      *)
(*                            algebra meets                                   *)
(*   oe_inputT, oe_outT, oe_gT, oe_k                                          *)
(*                         == the carriers a realisation is stated in         *)
(*   realises              == the run decodes to the ideal function           *)
(*   realises_expected     == the run's recovered value is the ideal function *)
(*   output_is_f           == the output variable is the ideal function of    *)
(*                            the input variable                              *)
(*   standard_security_cmi == correct output and a view of zero conditional   *)
(*                            mutual information                              *)
(*                                                                            *)
(* Key results:                                                               *)
(*   realises_expected_run == the executed run decodes to the ideal function  *)
(*   realises_of_expected  == the term identification implies the pointwise   *)
(*                            correspondence                                  *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext realType_ln fdist proba entropy.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_smc Require Import pgg_interface pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_smc Require Import pgg_instance.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     The ideal functionality                                                *)
(******************************************************************************)

(* The specification of a secure computation: the function fn_f the parties
   want evaluated on their joint input, and the largest coalition size
   fn_threshold at which nothing is to be learned beyond the output. The
   record holds the function as a term rather than behind an interface, so
   two candidate specifications of the same protocol are compared by
   conversion and a specification that merely agrees pointwise with the
   intended one is a different value. *)
Record Functionality (inputT outT : Type) := MkFunctionality {
  fn_f : inputT -> outT ;
  fn_threshold : nat }.

(* The specification a dealer-dealt run of an algebra meets: the identity on
   the dealt secret, at one seat below the scheme's privacy threshold. Both
   components are forced rather than chosen. The ideal function is the
   identity because a run that deals a secret and reconstructs it computes
   nothing from several parties' inputs, and the tolerated coalition size is
   the scheme's own ts_k', because the sizes at which the shares reveal
   nothing are the scheme's and no part of the execution narrows them.

   A sharing family names no ideal function at all. Its expected value, the
   identity for a dealt secret and the designated entry of the tape for a
   supplied layout, is the value the run reads back off its own argument, not
   a function of any committer's input. Only the input family states an ideal
   function, and only there is a specification something the run could fail
   to meet. *)
Definition algebra_functionality (A : PGGAlgebraic)
    : Functionality (pga_secretT A) (pga_secretT A) :=
  MkFunctionality id (ts_k' (pga_scheme A)).

(* The carriers a realisation statement is made in: the type of one run
   argument, the type of the reconstructed value, the shuffle group, and the
   privacy threshold read off the profile's scheme. Naming them lets a
   Functionality be typed against an execution without mentioning any of the
   records the execution is assembled from. oe_k is the threshold the
   execution delivers and fn_threshold is the one the specification asks for;
   nothing here relates them, because the privacy claim that would is stated
   per instance, against that instance's own probability model. *)
Definition oe_inputT (oe : OE.ObservedExecution) : Type :=
  ep_inputT (OE.oe_execution oe).
Definition oe_outT (oe : OE.ObservedExecution) : Type :=
  mp_secretT (OE.oe_profile oe).
Definition oe_gT (oe : OE.ObservedExecution) : finGroupType :=
  pgg_gT (mp_M (OE.oe_profile oe)).
Definition oe_k (oe : OE.ObservedExecution) : nat :=
  profile_k (OE.oe_profile oe).

(* The execution computes the functionality: at every run argument and every
   shuffle in the group, decoding the static endpoint reading returns fn_f F
   at that argument. The correctness half of a security claim, stated at the
   static group-action reading, which is where a coalition's view is also
   stated, so correctness and privacy speak about the same object. *)
Definition realises (oe : OE.ObservedExecution)
    (F : Functionality (oe_inputT oe) (oe_outT oe)) : Prop :=
  forall (x : oe_inputT oe) (w0 : oe_gT oe),
    w0 \in pgg_G (mp_M (OE.oe_profile oe)) ->
    forall sz_ep : size (@exec_static_endpoints (OE.oe_profile oe)
                           (OE.oe_execution oe) (OE.oe_content_obs oe) x w0)
                 = (pi_T' (mp_PI (OE.oe_profile oe))).+1,
    @exec_decode (OE.oe_profile oe) (OE.oe_execution oe)
      (@exec_static_endpoints (OE.oe_profile oe) (OE.oe_execution oe)
         (OE.oe_content_obs oe) x w0)
      sz_ep
    = fn_f F x.
Arguments realises : clear implicits.

(* The value the execution is built to recover is the functionality's function,
   as terms. Conversion decides this, so an instance that writes its recovered
   value as the ideal function discharges it by reflexivity, and one whose
   recovered value only agrees pointwise with the ideal function does not
   discharge it by reflexivity. That case still closes through funext, at the
   price of functional_extensionality_dep and propositional_extensionality in
   the row's assumption list, so the difference between the two specifications
   is visible in Print Assumptions rather than in provability. *)
Definition realises_expected (oe : OE.ObservedExecution)
    (F : Functionality (oe_inputT oe) (oe_outT oe)) : Prop :=
  OE.oe_expected oe = fn_f F.
Arguments realises_expected : clear implicits.

(* The executed run, not only its direct computation, decodes to the ideal
   function's value at every argument and every shuffle in the group. The
   step from the direct computation to the executed endpoints is the execution
   record's own derivation, so identifying the recovered value with the ideal
   function is all an instance supplies to obtain end-to-end correctness. *)
Lemma realises_expected_run (oe : OE.ObservedExecution)
    (F : Functionality (oe_inputT oe) (oe_outT oe)) :
  realises_expected oe F ->
  forall (x : oe_inputT oe) (w0 : oe_gT oe),
    w0 \in pgg_G (mp_M (OE.oe_profile oe)) ->
    @exec_decode (OE.oe_profile oe) (OE.oe_execution oe)
      (@exec_endpoints (OE.oe_profile oe) (OE.oe_execution oe) x w0
         (OE.oe_P_idx oe))
      (OE.oe_endpoints_size oe x w0)
    = fn_f F x.
Proof.
by rewrite /realises_expected => <- x w0 Gw0; exact: OE.oe_run_recovers.
Qed.

(* The term identification implies the pointwise correspondence. The converse
   fails, so realises is the weaker of the two and the one a specification
   given up to pointwise equality can still meet. *)
Lemma realises_of_expected (oe : OE.ObservedExecution)
    (F : Functionality (oe_inputT oe) (oe_outT oe)) :
  realises_expected oe F -> realises oe F.
Proof.
by move=> H x w0 Gw0 sz_ep; rewrite -H; exact: OE.oe_static_recon.
Qed.

(******************************************************************************)
(*     Standard security in a probability model                               *)
(******************************************************************************)

(* The output random variable is the ideal function of the input random
   variable, at every point of the sample space. Stated pointwise rather than
   as an equality of random variables so that it needs no functional
   extensionality. It is the clause that makes a zero-information claim about
   a view a statement about this protocol: without it, a view independent of
   the inputs is compatible with an execution that computes nothing. *)
Definition output_is_f (R : realType) (Om : finType) (PP : R.-fdist Om)
    (inputT outT : finType) (F : Functionality inputT outT)
    (X : {RV PP -> inputT}) (Y : {RV PP -> outT}) : Prop :=
  forall w : Om, Y w = fn_f F (X w).
Arguments output_is_f : clear implicits.

(* Standard security of a protocol against a coalition whose view is V: the
   output is the ideal function of the inputs, and the view carries no
   information about the inputs once the output is known. The second clause
   is an equality of a conditional mutual information to zero, so the
   guarantee is information-theoretic and conditional on no computational
   assumption. A simulator is not named: at zero conditional mutual
   information the view is reconstructible from the output alone. *)
Definition standard_security_cmi (R : realType) (Om : finType)
    (PP : R.-fdist Om) (inputT outT viewT : finType)
    (F : Functionality inputT outT)
    (X : {RV PP -> inputT}) (V : {RV PP -> viewT}) (Y : {RV PP -> outT})
    : Prop :=
  output_is_f R Om PP inputT outT F X Y
  /\ cond_mutual_info (`p_ [% X, V, Y]) = 0.
Arguments standard_security_cmi : clear implicits.
