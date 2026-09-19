(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* s5_tableau_analysis_bridged: the five-seat instance at AnalysisBridged     *)
(*                                                                            *)
(* The AnalysisBridged level adjoins one security payload per real field and  *)
(* per index of the model, and the proposition it carries is that payload's   *)
(* arm on top of everything the levels below proved. This is the level at     *)
(* which a row says something about a coalition, and the arm decides what it  *)
(* says: the exact arm asserts independence, and not a distance between two   *)
(* readings.                                                                  *)
(*                                                                            *)
(* The security argument a five-seat row makes is the one a five-of-five      *)
(* additive sharing makes. A secret in 'I_5 is split into five shares         *)
(* summing to it modulo five, one share per seat, and each seat reads the     *)
(* card at its own position. Five is the threshold of the sum-mod scheme, so  *)
(* every statement here is about a coalition of at most four of the five      *)
(* seats, and four shares of a uniform tape carry no information about the    *)
(* secret at all rather than a small amount. The independence is therefore    *)
(* exact, and exact for a reason no shuffle takes part in.                    *)
(*                                                                            *)
(* The mathematics reaches the row through one payload and two facts. The     *)
(* payload is the exact witness. The first fact identifies the framework's    *)
(* direct computation of a coalition's reading with the additive sharing's    *)
(* own, which holds because this model draws the identity cut. The second is  *)
(* s5_exec_coalition_secrecy, the sharing's privacy at a uniform tape, read   *)
(* from zero mutual information back to independence. No other security       *)
(* statement of the instance enters the row.                                  *)
(*                                                                            *)
(* Identifiers follow the instance rather than the framework wherever the     *)
(* instance already named the object: what the framework calls the supplied   *)
(* mode this instance spells rand in s5_rand_exec_plug, s5_rand_family,       *)
(* s5_rand_observed and the manifest's s5_row_rand, so every name here from   *)
(* the model onward carries rand.                                             *)
(*                                                                            *)
(* The phase files are required and imported one by one and export nothing of *)
(* each other, so a file outside this directory names the phase that declares *)
(* the name it wants: this file for a payload, a published row or a row       *)
(* equation, s5_tableau_sampled for a named model, s5_tableau_observed for a  *)
(* run or a specification, and s5_tableau_executable for a parameter record.  *)
(* An importer that wants only s5_rand_exact_witness names this file alone.   *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   s5_rand_exact_witness                                                    *)
(*                        == the exact arm's witness at every field and index *)
(*   s5_row_rand_tableau  == the randomized row as a program                  *)
(*                                                                            *)
(* Key results:                                                               *)
(*   s5_rand_static_obsE  == the framework's direct computation of a          *)
(*                           coalition's reading is the one the additive      *)
(*                           sharing makes                                    *)
(*   s5_rand_static_obs_indep                                                 *)
(*                        == below five seats that computation is independent *)
(*                           of the tape secret                               *)
(*   s5_row_rand_rowE     == the randomized program publishes the manifest's  *)
(*                           row                                              *)
(*   s5_row_rand_armE     == the row carries the exact arm                    *)
(*   s5_row_rand_sampledE == the row is the named Sampled value with the      *)
(*                           payload and the terminal adjoined                *)
(*   s5_rand_view_secrecy == the exact arm's four conjuncts at this instance  *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype finfun finset.
From mathcomp Require Import matrix zmodp reals.
From infotheo Require Import fdist proba entropy.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter.
From pgg_smc Require Import pgg_randomized_sharing pgg_canonical_sharing.
From pgg_smc Require Import s5_profile s5_exec s5_models.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.
From pgg_smc Require Import s5_tableau_observed s5_tableau_sampled.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     The instance-side reading of a coalition                               *)
(******************************************************************************)

(** The framework's direct computation of a coalition's view, as a random
    variable on the tape space, is the additive sharing's own coalition view.
    The two are not the same term: the framework reads the layout at the cut
    image of each seat's start, and the sharing reads the share at the seat's
    index, and they agree because this model draws the identity cut. Every
    security statement of a row is made about the left-hand side and every
    secrecy theorem of this instance about the right, so this equation is the
    whole of what carries one to the other. *)
Lemma s5_rand_static_obsE (R : realType) (idx : unit)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile s5_algebra))).+1}) :
  (fun u => @static_coalition_obs s5_algebra s5_supplied_params C
              ((amf_sample s5_rand_family R idx).(sa_arg) u)
              ((amf_sample s5_rand_family R idx).(sa_cut) u))
  = rsh_view (@unif_randomized_sharing R 3 4) C.
Proof.
rewrite -s5_sample_coalition_viewE.
exact: esym (@sa_coalition_viewE R (instance_profile s5_algebra)
  (instance_exec s5_supplied_params) (amf_sample s5_rand_family R idx) 0
  (ex_content_obs s5_supplied_params) (fun _ => s5_supplied_endpoints _ _) C).
Qed.

(** Below five seats, the framework's direct computation of a coalition's
    view is independent of the tape secret. It is s5_exec_coalition_secrecy,
    the additive sharing's privacy at a uniform tape, carried along the
    identification above and read from zero mutual information back to
    independence. This is the whole of the mathematics the supplied row's
    security payload rests on. *)
Lemma s5_rand_static_obs_indep (R : realType) (idx : unit)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile s5_algebra))).+1}) :
  (#|C| < profile_k (instance_profile s5_algebra))%N ->
  sa_sampleP (amf_sample s5_rand_family R idx)
  |= (fun u => @static_coalition_obs s5_algebra s5_supplied_params C
                 ((amf_sample s5_rand_family R idx).(sa_arg) u)
                 ((amf_sample s5_rand_family R idx).(sa_cut) u))
     _|_ (rsh_secret (@unif_randomized_sharing R 3 4)).
Proof.
rewrite profile_k_s5_algebra => HC.
rewrite (s5_rand_static_obsE R idx C).
apply/inde_RV_sym; apply: mutual_info_RV0_indep.
rewrite -s5_sample_coalition_viewE.
exact: (proj1 (@s5_exec_coalition_secrecy R C HC)).
Qed.

(******************************************************************************)
(*     The tape model's witness                                               *)
(******************************************************************************)

(** The exact arm's witness: the tape secret as a random variable on the tape
    space, and, at every coalition of fewer than five seats, the independence
    of that coalition's reading from it. The independence is exact, four
    additive shares of a uniform tape carrying no information about the
    secret at all rather than a small amount, and it is exact for a reason no
    shuffle takes part in. The framework derives the zero mutual information,
    the unchanged conditional entropy and the closure under post-processing
    from this one field, so the witness is the whole of what this instance
    owes the exact arm. *)
Definition s5_rand_exact_witness (R : realType) (idx : unit)
  : ExactWitness (amf_sample s5_rand_family R idx) :=
  @MkExactWitness R s5_algebra s5_supplied_params
    (amf_sample s5_rand_family R idx) 'Z_5
    (rsh_secret (@unif_randomized_sharing R 3 4))
    (@s5_rand_static_obs_indep R idx).

(******************************************************************************)
(*     The randomized row                                                     *)
(******************************************************************************)

(** The randomized row: the supplied run above, the uniform tape
    model, the witness above, and the manifest row. Its last statement
    publishes a row whose transfer status is StaticExecutedOnly, because the
    model's cut is the identity and no idealized shuffle is being compared
    with a real one, and whose assumption status names the instance's
    group-order fact, which enters through the reconstruction plug the
    algebra's profile carries. What the finished row carries about a
    coalition of fewer than five seats is independence of the tape secret, at
    every real field, with no numeric bound anywhere in it. *)
Definition s5_row_rand_tableau : PublishedRow :=
  s5_supplied
    sample  s5_rand_family
    certify ExactIndependence s5_rand_exact_witness
    |> publish StaticExecutedOnly (AcceptsAxioms [:: AxS5GroupOrder]).

(** The row the program publishes is the manifest's own row for this instance
    under the uniform tape. Conversion decides it, so the descriptive row and
    the theorem proved about it cannot drift apart. *)
Lemma s5_row_rand_rowE :
  published_row s5_row_rand_tableau = s5_row_rand.
Proof. by []. Qed.

(** The arm this row carries, at every real field and index: independence of
    the coalition's view from the tape secret, and not a distance between two
    readings. This is the value a paper's table prints in the arm column for
    this row, settled by the certify statement the program wrote. *)
Lemma s5_row_rand_armE (R : realType)
    (idx : amf_index (ab_f (published_at s5_row_rand_tableau)) R) :
  security_arm_of s5_row_rand_tableau R idx = ExactIndependenceArm.
Proof. by []. Qed.

(** The row is the named Sampled value with the payload and the terminal
    adjoined. The program above writes the run and the model in one chain and
    the Sampled file names the value they build, so this equation is what
    keeps the two spellings of the row's prefix from parting. *)
Lemma s5_row_rand_sampledE :
  (s5_rand_sampled
     certify ExactIndependence s5_rand_exact_witness
     |> publish StaticExecutedOnly (AcceptsAxioms [:: AxS5GroupOrder]))
  = s5_row_rand_tableau.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The exact arm's four conjuncts at this instance                        *)
(******************************************************************************)

(** The randomized row's view secrecy at this instance: at fewer than five
    colluding seats the executed coalition view is independent of the tape
    secret, carries zero mutual information with it, leaves its entropy
    unchanged under conditioning, and stays independent of it under every
    deterministic function of the seat-to-card map. The four conjuncts are
    the whole content of the exact arm at this instance; the proof is the
    row's security projection applied, so a reader who wants the
    information-theoretic reading of the row needs no further derivation. *)
Theorem s5_rand_view_secrecy (R : realType) (C : {set 'I_5})
    (HC : (#|C| < 5)%N) :
  [/\ s5_rand_sampleP R
      |= (@sa_coalition_view R s5_profile s5_rand_exec_plug
            (s5_rand_sample R) 0 C)
         _|_ (rsh_secret (@unif_randomized_sharing R 3 4)),
      `I( rsh_secret (@unif_randomized_sharing R 3 4) ;
          @sa_coalition_view R s5_profile s5_rand_exec_plug
            (s5_rand_sample R) 0 C ) = 0,
      `H( rsh_secret (@unif_randomized_sharing R 3 4) |
          @sa_coalition_view R s5_profile s5_rand_exec_plug
            (s5_rand_sample R) 0 C )
      = `H `p_ (rsh_secret (@unif_randomized_sharing R 3 4))
    & forall (W : finType) (h : {ffun 'I_5 -> 'I_5} -> W),
        s5_rand_sampleP R
        |= (h `o (@sa_coalition_view R s5_profile s5_rand_exec_plug
                    (s5_rand_sample R) 0 C))
           _|_ (rsh_secret (@unif_randomized_sharing R 3 4))].
Proof. exact: (view_secrecy_of s5_row_rand_tableau R tt C HC). Qed.
