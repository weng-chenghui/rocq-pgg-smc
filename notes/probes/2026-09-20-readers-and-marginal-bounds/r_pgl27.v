(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* r_pgl27: the eight-card orbit instance's second reader                     *)
(*                                                                            *)
(* PROBE FILE. Nothing permanent requires it. Ledger rows R4, R5, R6 (trace   *)
(* part) and R7 of                                                            *)
(* notes/20260920-readers-and-marginal-bounds-probe-design.md.                *)
(*                                                                            *)
(* This instance proves two theorems that publish one number, 2^-39, about    *)
(* two different readers of one run: the coalition's endpoint reading and the *)
(* coalition's content trace. The file names the second reader, restates the  *)
(* trace theorem as the input-indistinguishability proposition at it, settles *)
(* which of the two readers is a function of the other, and cites the         *)
(* executed trace's identification with the static one.                       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_sample_adapter pgg_weighted_words.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_trace pgl27_mixing.
From pgg_smc Require Import pgl27_word_privacy pgl27_exec pgl27_models.
From pgg_smc Require Import pgl27_proximity.
From pgg_smc Require Import pgl27_tableau_analysis_bridged.
From readersprobe Require Import r_framework.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.


Section pgl27_readers.

Variable R : realType.

(******************************************************************************)
(*     R4: the coalition's content trace as a static reader                   *)
(******************************************************************************)

(* The content trace of a coalition as a static reader of this instance's run:
   at each coalition, the seat-indexed record of the card each member's
   interpreter row carries, and ord0 outside the coalition. It is a second
   reader of the same run and not a second statement of the program: the
   Tableau's stack is untouched. *)
Definition pgl27_trace_reader : StaticReader pgl27_dealt_params :=
  @MkStaticReader pgl27_algebra pgl27_dealt_params
    (fun _ => [the finType of {ffun 'I_8 -> 'I_8}])
    (fun C x g => pgl27_coalition_trace R C (x, g)).

(* The trace theorem of the word model as the input-indistinguishability
   proposition at the trace reader. The number and the threshold are the cited
   theorem's own: two dealt secrets give coalition traces within 2^-39 in the
   sum of absolute differences, at every coalition of fewer than four seats. A
   distinguisher's advantage against the trace is therefore at most 2^-40. *)
Theorem pgl27_word_trace_indistinguishability_at_reader
    (secretP : R.-fdist bool) :
  @ReaderIndistinguishabilityPropAt R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP) pgl27_trace_reader (2%:R^-39).
Proof.
move=> C x x' HC.
rewrite (pgl27_word_cut_distE secretP).
exact: (@pgl27_word_trace_indistinguishability R C x x' HC).
Qed.

(* The privacy threshold the framework states, fewer than k seats, is at this
   instance the threshold the cited theorems state, at most three seats. *)
Lemma pgl27_threshold_readE
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  (#|C| < profile_k (instance_profile pgl27_algebra))%N = (#|C| <= 3)%N.
Proof. exact: erefl. Qed.


(******************************************************************************)
(*     R5: which of the two readers is a function of the other                *)
(******************************************************************************)

(* The coalition's endpoint reading is the identity function of its content
   trace. What the coalition's interpreter rows carry and what its seats hold
   after the shuffle are one record at this instance, so neither reader is
   finer than the other and the same number bounds both. *)
Lemma pgl27_reading_of_trace
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1})
    (x : ex_inputT pgl27_dealt_params)
    (g : pgg_gT (mp_M (instance_profile pgl27_algebra))) :
  sr_read (coalition_reading_reader pgl27_dealt_params) C x g
  = id (sr_read pgl27_trace_reader C x g).
Proof.
rewrite /= (pgl27_coalition_trace_E R C).
exact: (pgl27_static_obsE R C x g).
Qed.

(* The content trace is the identity function of the endpoint reading, the
   same equation read in the other direction. *)
Lemma pgl27_trace_of_reading
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1})
    (x : ex_inputT pgl27_dealt_params)
    (g : pgg_gT (mp_M (instance_profile pgl27_algebra))) :
  sr_read pgl27_trace_reader C x g
  = id (sr_read (coalition_reading_reader pgl27_dealt_params) C x g).
Proof. exact: (esym (pgl27_reading_of_trace C x g)). Qed.

(* The word model's input-indistinguishability proposition at the coalition's
   endpoint reading, derived from the trace theorem by post-processing. The
   number does not move, the factorisation being the identity. *)
Corollary pgl27_word_reading_indistinguishability_by_postprocessing
    (secretP : R.-fdist bool) :
  @ReaderIndistinguishabilityPropAt R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP)
    (coalition_reading_reader pgl27_dealt_params) (2%:R^-39).
Proof.
apply: (@reader_indistinguishability_postprocessing R pgl27_algebra
          pgl27_dealt_params (amf_sample pgl27_word_family R secretP)
          pgl27_trace_reader (coalition_reading_reader pgl27_dealt_params)
          (fun _ => id) pgl27_reading_of_trace (2%:R^-39)).
exact: pgl27_word_trace_indistinguishability_at_reader.
Qed.

(* The same proposition at the same number through the framework's own
   composition law, from the word program's certificate. The certificate's own
   bound is the marginal bound's 2^-40 taken twice, which is the 2^-39 the
   trace route publishes, so the two routes agree on the number and neither is
   the weaker statement. *)
Corollary pgl27_word_reading_indistinguishability_by_certificate
    (secretP : R.-fdist bool) :
  @ReaderIndistinguishabilityPropAt R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP)
    (coalition_reading_reader pgl27_dealt_params) (2%:R^-39).
Proof.
move=> C x x' HC.
rewrite -(pow2_split R).
exact: (indistinguishability_tail (@pgl27_word_cert R secretP) C x x' HC).
Qed.

(* The certificate's own bound is the number the trace route publishes. *)
Lemma pgl27_word_cert_epsE (secretP : R.-fdist bool) :
  cert_eps (@pgl27_word_cert R secretP) = 2%:R^-40 + 2%:R^-40 :> R.
Proof. exact: erefl. Qed.


(******************************************************************************)
(*     R6: exact independence at the trace reader                             *)
(******************************************************************************)

(* Exact independence at the trace reader of the exact model: below the
   privacy threshold, a coalition's content trace under the uniform PGL(2,7)
   cut is independent of the dealt orbit secret. The statement is exact, the
   uniform cut leaving the trace with no information about the secret at all,
   and it is the independence the instance's entropy equality for the trace is
   itself derived from. *)
Theorem pgl27_trace_exact_at_reader :
  @ReaderExactPropAt R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_exact_family R tt) pgl27_trace_reader bool
    (pgl27_secret R).
Proof.
move=> C HC.
have -> : (fun u => sr_read pgl27_trace_reader C
                      ((amf_sample pgl27_exact_family R tt).(sa_arg) u)
                      ((amf_sample pgl27_exact_family R tt).(sa_cut) u))
        = pgl27_view R C.
  rewrite -(pgl27_coalition_trace_E R C).
  by apply: boolp.funext; case=> s g.
exact: (@pgl27_view_indep R C HC).
Qed.

(* The entropy equality the instance publishes about the coalition's trace,
   obtained from exact independence at the trace reader. The independence is
   the upstream fact and the entropy equality its consequence, so the reader
   form needs no converse of the entropy equality. *)
Corollary pgl27_trace_entropy_of_reader
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  (#|C| < profile_k (instance_profile pgl27_algebra))%N ->
  `H( pgl27_secret R | pgl27_coalition_trace R C ) = `H `p_ (pgl27_secret R).
Proof. by move=> HC; exact: (@pgl27_coalition_trace_secrecy R C HC). Qed.


(******************************************************************************)
(*     R7: the executed content trace against the static trace                *)
(******************************************************************************)

(* The executed content trace of the word model is the trace reader's reading
   of that model's run argument and cut, at every sample point. It is the
   trace reader's counterpart of the link lemma the Sampled level proves for
   the coalition's endpoint reading, and it is what makes a statement at the
   trace reader a statement about the interpreter's own rows. *)
Lemma pgl27_exec_trace_link (secretP : R.-fdist bool)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  (fun u => pgl27_exec_content_trace C
              ((amf_sample pgl27_word_family R secretP).(sa_arg) u)
              ((amf_sample pgl27_word_family R secretP).(sa_cut) u))
  = (fun u => sr_read pgl27_trace_reader C
                ((amf_sample pgl27_word_family R secretP).(sa_arg) u)
                ((amf_sample pgl27_word_family R secretP).(sa_cut) u)).
Proof.
apply: boolp.funext => u.
exact: (pgl27_content_traceE R C (u.1, @word_eval pgl27_Msym 200 u.2)).
Qed.

End pgl27_readers.
