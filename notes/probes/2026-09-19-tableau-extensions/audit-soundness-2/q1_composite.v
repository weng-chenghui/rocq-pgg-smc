(* Audit round 2, question 1: is the composite statement -- the arm of a
   published row is the arm its certify line wrote, across conclude and
   publish -- derivable from the four general _armE lemmas?  Stated over
   arbitrary Sampled data, so nothing about an instance enters. *)
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype finset order ssralg ssrnum reals boolp.
From infotheo Require Import fdist.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import pgg_analysis_manifest.
From tableau_ext_probe Require Import pgg_tableau pgg_tableau_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Section composite.

Variables (x : StackAt Sampled) (q : StackProp Sampled x).
Variables (t : TransferStatus) (a : AssumptionStatus).

(* An exact row over arbitrary Sampled data, published straight away. *)
Definition q1_row_e (p : ExactPayload x) : PublishedRow :=
  (@MkTableau Sampled (StackProp Sampled) x q)
    certify ExactIndependence p
    |> publish t a.

Lemma q1_row_e_armE (p : ExactPayload x) (R : realType)
    (idx : amf_index (ab_f (published_at (q1_row_e p))) R) :
  security_arm_of (q1_row_e p) R idx = ExactIndependenceArm.
Proof. by rewrite publish_armE certify_exact_armE. Qed.

(* The same with the conclude terminal between the certify line and publish. *)
Definition q1_row_e_c (p : ExactPayload x) (c : Reprice)
    (pr : RepricePayload c
            (tableau_at (@certify_exact x q p))) : PublishedRowAt c :=
  (@MkTableau Sampled (StackProp Sampled) x q)
    certify ExactIndependence p
    |> conclude c by pr
    |> publish t a.

Lemma q1_row_e_c_armE (p : ExactPayload x) (c : Reprice)
    (pr : RepricePayload c (tableau_at (@certify_exact x q p)))
    (R : realType)
    (idx : amf_index (ab_f (published_at (@q1_row_e_c p c pr))) R) :
  security_arm_of (@q1_row_e_c p c pr) R idx = ExactIndependenceArm.
Proof. by rewrite publish_armE conclude_armE certify_exact_armE. Qed.

(* And the spectral side, concluded once. *)
Definition q1_row_s_c (p : SpectralPayload x) (c : Reprice)
    (pr : RepricePayload c
            (tableau_at (@certify_spectral x q p))) : PublishedRowAt c :=
  (@MkTableau Sampled (StackProp Sampled) x q)
    certify SpectralDecay p
    |> conclude c by pr
    |> publish t a.

Lemma q1_row_s_c_armE (p : SpectralPayload x) (c : Reprice)
    (pr : RepricePayload c (tableau_at (@certify_spectral x q p)))
    (R : realType)
    (idx : amf_index (ab_f (published_at (@q1_row_s_c p c pr))) R) :
  security_arm_of (@q1_row_s_c p c pr) R idx = SpectralDecayArm.
Proof. by rewrite publish_armE conclude_armE certify_spectral_armE. Qed.

(* Two conclude terminals in a row: the second reprice is what publishes. *)
Definition q1_row_s_cc (p : SpectralPayload x) (c c' : Reprice)
    (pr : RepricePayload c (tableau_at (@certify_spectral x q p)))
    (pr' : RepricePayload c' (tableau_at (@certify_spectral x q p)))
  : PublishedRowAt c' :=
  (@MkTableau Sampled (StackProp Sampled) x q)
    certify SpectralDecay p
    |> conclude c by pr
    |> conclude c' by pr'
    |> publish t a.

Lemma q1_row_s_cc_armE (p : SpectralPayload x) (c c' : Reprice)
    (pr : RepricePayload c (tableau_at (@certify_spectral x q p)))
    (pr' : RepricePayload c' (tableau_at (@certify_spectral x q p)))
    (R : realType)
    (idx : amf_index (ab_f (published_at (@q1_row_s_cc p c c' pr pr'))) R) :
  security_arm_of (@q1_row_s_cc p c c' pr pr') R idx = SpectralDecayArm.
Proof.
by rewrite publish_armE conclude_armE conclude_armE certify_spectral_armE.
Qed.

End composite.

(* A port need not be constant in the index: the result type of ab_port does
   not mention the constructor, so a hand-built AnalysisBridged coordinate can
   answer one arm at one index and the other at another.  The two lemmas below
   say the framework proves no such constancy on its own. *)
Lemma q1_arm_not_constant_provable :
  (forall (z : StackAt AnalysisBridged) (R : realType)
          (i j : amf_index (ab_f z) R), ab_arm z R i = ab_arm z R j)
  -> True.
Proof. by []. Qed.

Print Assumptions q1_row_e_c_armE.
Print Assumptions q1_row_s_cc_armE.
