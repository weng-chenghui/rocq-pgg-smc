(******************************************************************************)
(* landing_fidelity.v                                                         *)
(*                                                                            *)
(* The staged text of landing 1 against the statements the probe compiled.    *)
(* It Requires the staged copies through the shadowing load path of           *)
(* _CoqProject, where the staged roots are mapped to pgg_smc after            *)
(* production's, and restates, at the probe's own statements, every           *)
(* declaration landing 1 adds to or removes from production. A drift between  *)
(* the staged text and those statements is a compile error here.              *)
(*                                                                            *)
(* Nothing below is a new mathematical claim. Every restatement is closed by  *)
(* the staged declaration it restates, or by conversion where the staged      *)
(* declaration is a definition and the restatement is its unfolding.          *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import order ssrnum ssralg boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter pgg_observed_execution.
From pgg_smc Require Import pgg_analysis_status pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import pgl27_models.
From pgg_smc Require Import pgl27_rows five_card_rows s5_rows psl211_rows.
From pgg_smc Require Import psl211_reading_constancy.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     The proximity arm's certificate, field by field                        *)
(******************************************************************************)

Section proximity_cert_fields.
Variable R : realType.
Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable sa : SampleAdapter R (instance_exec E).
Variable cert : IdealProximityCert sa.

(** The ideal is a second sample adapter over the row's own execution, and it
    carries an exact witness, so the model the number is measured against is
    one whose own privacy is proved. *)
Check (ipc_ideal cert : SampleAdapter R (instance_exec E)).
Check (ipc_witness cert : ExactWitness (ipc_ideal cert)).

(** The actual model's secret is typed at the carrier the ideal's witness
    names, which is what makes the two models speak of one secret. *)
Check (ipc_secret cert
       : {RV (sa_sampleP sa) -> ew_secretT (ipc_witness cert)}).
Check (ipc_eps cert : R).

(** The distance field, restated in full. It is a bound on the sum of
    absolute differences of two joint laws of a coalition's reading with the
    secret, one law under the actual model and one under the ideal, at every
    coalition below the privacy threshold. It is not a distinguisher's
    advantage, which is at most half of it. *)
Check (ipc_close cert
       : forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
         (#|C| < profile_k (instance_profile A))%N ->
         var_dist
           (fdistmap (fun u => (static_coalition_obs C (sa.(sa_arg) u)
                                  (sa.(sa_cut) u), ipc_secret cert u))
              (sa_sampleP sa))
           (fdistmap (fun u => (static_coalition_obs C
                                  ((ipc_ideal cert).(sa_arg) u)
                                  ((ipc_ideal cert).(sa_cut) u),
                                ew_secret (ipc_witness cert) u))
              (sa_sampleP (ipc_ideal cert)))
         <= ipc_eps cert).

End proximity_cert_fields.

(** The proposition the proximity arm publishes, restated by unfolding. Its
    left side is the joint law of the coalition's executed reading with the
    secret under the actual model, and its right side is the product of the
    ideal model's two marginals and not a joint law, so it is a different
    statement from the ipc_close field restated above. *)
Lemma landing_idealproximity_propE (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IdealProximityCert sa) (c : R) :
  IdealProximityPropAt cert c
  = forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
      (#|C| < profile_k (instance_profile A))%N ->
      var_dist
        (fdistmap (fun u => (@sa_coalition_view R (instance_profile A)
                               (instance_exec E) sa 0 C u, ipc_secret cert u))
           (sa_sampleP sa))
        ((fdistmap (@sa_coalition_view R (instance_profile A)
                      (instance_exec E) (ipc_ideal cert) 0 C)
            (sa_sampleP (ipc_ideal cert)))
         `x (fdistmap (ew_secret (ipc_witness cert))
               (sa_sampleP (ipc_ideal cert))))
      <= c.
Proof. exact: erefl. Qed.

(** The projection a reader of the proximity arm is pointed at is the term
    the other two arms' readers are pointed at, so an arm's name on a
    projection tells a reader what to expect and decides nothing. *)
Lemma landing_view_proximity_of (c : Reprice) (r : PublishedRowAt c) :
  view_proximity_of r = view_indistinguishability_of r.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The arm reader                                                         *)
(******************************************************************************)

(** The reader answers from the port's constructor alone, at all three arms. *)
Lemma landing_port_arm_exact (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (w : ExactWitness sa) :
  port_arm (ExactIndependence w) = ExactIndependenceArm.
Proof. exact: erefl. Qed.

Lemma landing_port_arm_indistinguishability (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IndistinguishabilityCert sa) :
  port_arm (InputIndistinguishability cert) = InputIndistinguishabilityArm.
Proof. exact: erefl. Qed.

Lemma landing_port_arm_idealproximity (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (cert : IdealProximityCert sa) :
  port_arm (IdealProximity cert) = IdealProximityArm.
Proof. exact: erefl. Qed.

(** A published row's arm is the arm of its data at AnalysisBridged. *)
Lemma landing_security_arm_of (c : Reprice) (r : PublishedRowAt c)
    (R : realType) (idx : amf_index (ab_f (published_at r)) R) :
  security_arm_of r R idx = ab_arm (published_at r) R idx.
Proof. exact: erefl. Qed.

(** The five general pins: each certify statement writes its own arm, and
    neither terminal moves it. *)
Lemma landing_certify_exact_armE (x : StackAt Sampled)
    (q : StackProp Sampled x) (p : ExactPayload x) (R : realType)
    (idx : amf_index (ab_f (tableau_at (@certify_exact x q p))) R) :
  ab_arm (tableau_at (@certify_exact x q p)) R idx = ExactIndependenceArm.
Proof. exact: certify_exact_armE. Qed.

Lemma landing_certify_indistinguishability_armE (x : StackAt Sampled)
    (q : StackProp Sampled x) (p : IndistinguishabilityPayload x)
    (R : realType)
    (idx : amf_index
             (ab_f (tableau_at (@certify_indistinguishability x q p))) R) :
  ab_arm (tableau_at (@certify_indistinguishability x q p)) R idx
  = InputIndistinguishabilityArm.
Proof. exact: certify_indistinguishability_armE. Qed.

Lemma landing_certify_idealproximity_armE (x : StackAt Sampled)
    (q : StackProp Sampled x) (p : IdealProximityPayload x) (R : realType)
    (idx : amf_index (ab_f (tableau_at (@certify_idealproximity x q p))) R) :
  ab_arm (tableau_at (@certify_idealproximity x q p)) R idx
  = IdealProximityArm.
Proof. exact: certify_idealproximity_armE. Qed.

Lemma landing_conclude_armE (c : Reprice) (q : StackAt AnalysisBridged)
    (pf : StackProp AnalysisBridged q) (p : ConcludePayload c q)
    (R : realType)
    (idx : amf_index (ab_f (tableau_at (conclude c q pf p))) R) :
  ab_arm (tableau_at (conclude c q pf p)) R idx = ab_arm q R idx.
Proof. exact: conclude_armE. Qed.

Lemma landing_publish_armE (a : AssumptionStatus) (c : Reprice)
    (q : StackAt AnalysisBridged) (pf : BridgedProp c q) (t : TransferStatus)
    (R : realType)
    (idx : amf_index (ab_f (published_at (publish a q pf t))) R) :
  security_arm_of (publish a q pf t) R idx = ab_arm q R idx.
Proof. exact: publish_armE. Qed.

(******************************************************************************)
(*     The terminal's obligation, weakened to an inequality                   *)
(******************************************************************************)

(** The obligation of conclude, restated by unfolding. An exact port owes
    nothing, and each of the two arms that carry a number owes that the number
    the row publishes is at least the number the row's own certificate
    proved. *)
Lemma landing_conclude_obligation (c : Reprice) (q : StackAt AnalysisBridged) :
  ConcludePayload c q
  = forall (R : realType) (idx : amf_index (ab_f q) R),
      match ab_port q R idx with
      | ExactIndependence _ => unit
      | InputIndistinguishability cert =>
          cert_eps cert <= odflt (cert_eps cert) (c R)
      | IdealProximity cert => ipc_eps cert <= odflt (ipc_eps cert) (c R)
      end.
Proof. exact: erefl. Qed.

(** The port law behind it: a port's proposition survives a move of its number
    to any upper bound. *)
Lemma landing_port_conclude (c : Reprice) (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (p : SecurityPort sa) :
  PortProp no_reprice p ->
  (match p with
   | ExactIndependence _ => unit
   | InputIndistinguishability cert =>
       cert_eps cert <= odflt (cert_eps cert) (c R)
   | IdealProximity cert => ipc_eps cert <= odflt (ipc_eps cert) (c R)
   end) ->
  PortProp c p.
Proof. exact: port_conclude. Qed.

(** The two names the obligation carried before it was weakened are gone. *)
Fail Check RepricePayload.
Fail Check port_reprice.

(******************************************************************************)
(*     The per-program arm pins of the four rows files                        *)
(******************************************************************************)

Lemma landing_pgl27_exact_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_exact_tableau)) R) :
  security_arm_of pgl27_row_exact_tableau R idx = ExactIndependenceArm.
Proof. exact: pgl27_row_exact_armE. Qed.

Lemma landing_pgl27_word_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_word_tableau)) R) :
  security_arm_of pgl27_row_word_tableau R idx = InputIndistinguishabilityArm.
Proof. exact: pgl27_row_word_armE. Qed.

Lemma landing_pgl27_word39_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_word39)) R) :
  security_arm_of pgl27_row_word39 R idx = InputIndistinguishabilityArm.
Proof. exact: pgl27_row_word39_armE. Qed.

Lemma landing_five_card_uniform_armE (R : realType)
    (idx : amf_index (ab_f (published_at five_card_row_uniform_tableau)) R) :
  security_arm_of five_card_row_uniform_tableau R idx = ExactIndependenceArm.
Proof. exact: five_card_row_uniform_armE. Qed.

Lemma landing_five_card_repeated_armE (R : realType)
    (idx : amf_index
             (ab_f (published_at
                      five_card_row_repeated_indistinguishability_tableau)) R) :
  security_arm_of five_card_row_repeated_indistinguishability_tableau R idx
  = InputIndistinguishabilityArm.
Proof. exact: five_card_row_repeated_indistinguishability_armE. Qed.

Lemma landing_five_card_biased_armE (R : realType)
    (idx : amf_index
             (ab_f (published_at
                      five_card_row_biased_indistinguishability_tableau)) R) :
  security_arm_of five_card_row_biased_indistinguishability_tableau R idx
  = InputIndistinguishabilityArm.
Proof. exact: five_card_row_biased_indistinguishability_armE. Qed.

Lemma landing_five_card_repeated39_armE (R : realType)
    (idx : amf_index (ab_f (published_at five_card_row_repeated39)) R) :
  security_arm_of five_card_row_repeated39 R idx
  = InputIndistinguishabilityArm.
Proof. exact: five_card_row_repeated39_armE. Qed.

Lemma landing_five_card_biased_inv25_armE (R : realType)
    (idx : amf_index (ab_f (published_at five_card_row_biased_inv25)) R) :
  security_arm_of five_card_row_biased_inv25 R idx
  = InputIndistinguishabilityArm.
Proof. exact: five_card_row_biased_inv25_armE. Qed.

Lemma landing_s5_rand_armE (R : realType)
    (idx : amf_index (ab_f (published_at s5_row_rand_tableau)) R) :
  security_arm_of s5_row_rand_tableau R idx = ExactIndependenceArm.
Proof. exact: s5_row_rand_armE. Qed.

Lemma landing_psl211_alldecks_armE (R : realType)
    (idx : amf_index (ab_f (published_at psl211_row_alldecks_tableau)) R) :
  security_arm_of psl211_row_alldecks_tableau R idx = ExactIndependenceArm.
Proof. exact: psl211_row_alldecks_armE. Qed.

(******************************************************************************)
(*     The manifest rows the four rows files publish                          *)
(******************************************************************************)

Lemma landing_pgl27_exact_rowE :
  published_row pgl27_row_exact_tableau = pgl27_row_exact.
Proof. exact: pgl27_row_exact_rowE. Qed.

Lemma landing_pgl27_word_rowE :
  published_row pgl27_row_word_tableau = pgl27_row_word.
Proof. exact: pgl27_row_word_rowE. Qed.

Lemma landing_five_card_uniform_rowE :
  published_row five_card_row_uniform_tableau = five_card_row_uniform.
Proof. exact: five_card_row_uniform_rowE. Qed.

Lemma landing_five_card_repeated_rowE :
  published_row five_card_row_repeated_indistinguishability_tableau
  = five_card_row_repeated.
Proof. exact: five_card_row_repeated_indistinguishability_rowE. Qed.

Lemma landing_five_card_biased_rowE :
  published_row five_card_row_biased_indistinguishability_tableau
  = five_card_row_biased.
Proof. exact: five_card_row_biased_indistinguishability_rowE. Qed.

Lemma landing_five_card_biased_formsE :
  published_row five_card_row_biased_indistinguishability_tableau
  = published_row five_card_row_biased_inv25.
Proof. exact: five_card_row_biased_forms_publishedE. Qed.

Lemma landing_s5_rand_rowE :
  published_row s5_row_rand_tableau = s5_row_rand.
Proof. exact: s5_row_rand_rowE. Qed.

Lemma landing_psl211_alldecks_rowE :
  published_row psl211_row_alldecks_tableau = psl211_row_alldecks.
Proof. exact: psl211_row_alldecks_rowE. Qed.

(** The repeated row concluded at 2^-39 and the row at the bundle's own number
    accumulate one stack, so the terminal moved a number and no data. *)
Lemma landing_five_card_repeated39_atE :
  published_at five_card_row_repeated39
  = published_at five_card_row_repeated_indistinguishability_tableau.
Proof. exact: five_card_row_repeated39_atE. Qed.

(******************************************************************************)
(*     The numbers the concluded rows publish                                 *)
(******************************************************************************)

(** The repeated five-card row still publishes two to the minus thirty-ninth,
    on the route through kim_centi_cert_eps_lt weakened by ltW, which is what
    the withdrawal below leaves it with. *)
Lemma landing_five_card_reprice39 (R : realType) :
  five_card_reprice39 R = Some (2%:R ^- 39 : R).
Proof. exact: erefl. Qed.

(** The PGL(2,7) word row publishes the same constant, on the route through
    pow2_split wrapped in eqW. *)
Lemma landing_pgl27_reprice39 (R : realType) :
  pgl27_reprice39 R = Some (2%:R ^- 39 : R).
Proof. exact: erefl. Qed.

(** The one-cut five-card row publishes one twenty-fifth. *)
Lemma landing_five_card_reprice_inv25 (R : realType) :
  five_card_reprice_inv25 R = Some (1 / 25 : R).
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     The withdrawal                                                         *)
(******************************************************************************)

(** The constant-bound repeated certificate and its number are gone from the
    tree. The repeated row is unchanged: it publishes the same constant, from
    the certificate at the bundle's own spectral number. *)
Fail Check kim_centi_cert40.
Fail Check kim_centi_cert40_epsE.

Check (five_card_row_repeated39 : PublishedRowAt five_card_reprice39).

(******************************************************************************)
(*     The word model named at Sampled, and its concluded continuation        *)
(******************************************************************************)

(** The named branch point is the dealt prefix sampled at the word family, so
    naming it costs the rows that continue from it nothing they would not
    otherwise carry. *)
Lemma landing_pgl27_word_sampled :
  pgl27_word_sampled = (pgl27_dealt sample pgl27_word_family).
Proof. exact: erefl. Qed.

Check (pgl27_word_sampled : Tableau Sampled).
Check (pgl27_row_word_branch39 : PublishedRowAt pgl27_reprice39).

(** The continuation of the name at 2^-39 and the unbranched row at the same
    number publish one manifest row, so the name changes no published
    coordinate. *)
Lemma landing_pgl27_branch39_rowE :
  published_row pgl27_row_word_branch39 = published_row pgl27_row_word39.
Proof. exact: erefl. Qed.

(** The two rows accumulate one stack, so naming the Sampled value changes
    the data the row carries in nothing, and not only its manifest row. *)
Lemma landing_pgl27_branch39_atE :
  published_at pgl27_row_word_branch39 = published_at pgl27_row_word39.
Proof. exact: erefl. Qed.

(** The branch row carries the input-indistinguishability arm, so the name
    at Sampled leaves the arm where the certify statement put it. *)
Lemma landing_pgl27_branch39_armE (R : realType)
    (idx : amf_index (ab_f (published_at pgl27_row_word_branch39)) R) :
  security_arm_of pgl27_row_word_branch39 R idx
  = InputIndistinguishabilityArm.
Proof. exact: erefl. Qed.

(******************************************************************************)
(*     Assumptions                                                            *)
(*                                                                            *)
(* The pass criterion is the three classical axioms of boolp, except the S5   *)
(* row, which rests on the production Axiom s5_group_order_eq as it did       *)
(* before this landing.                                                       *)
(******************************************************************************)

(* The framework the landing adds. *)
Print Assumptions port_conclude.
Print Assumptions idealproximity_tail.
Print Assumptions certify_idealproximity_armE.
Print Assumptions conclude_armE.
Print Assumptions publish_armE.
Print Assumptions certify_exact_armE.
Print Assumptions certify_indistinguishability_armE.

(* PGL(2,7). *)
Print Assumptions pgl27_row_exact_tableau.
Print Assumptions pgl27_row_word_tableau.
Print Assumptions pgl27_row_word39.
Print Assumptions pgl27_row_word39_bind.
Print Assumptions pgl27_row_word_branch39.
Print Assumptions pgl27_row_exact_rowE.
Print Assumptions pgl27_row_word_rowE.
Print Assumptions pgl27_row_exact_armE.
Print Assumptions pgl27_row_word_armE.
Print Assumptions pgl27_row_word39_armE.
Print Assumptions pgl27_row_word39_bindE.

(* Kim's five-card rows. *)
Print Assumptions five_card_row_uniform_tableau.
Print Assumptions five_card_row_repeated_indistinguishability_tableau.
Print Assumptions five_card_row_biased_indistinguishability_tableau.
Print Assumptions five_card_row_repeated39.
Print Assumptions five_card_row_biased_inv25.
Print Assumptions five_card_row_uniform_rowE.
Print Assumptions five_card_row_uniform_armE.
Print Assumptions five_card_row_repeated_indistinguishability_rowE.
Print Assumptions five_card_row_biased_indistinguishability_rowE.
Print Assumptions five_card_row_biased_forms_publishedE.
Print Assumptions five_card_row_repeated39_atE.
Print Assumptions five_card_row_repeated_indistinguishability_armE.
Print Assumptions five_card_row_biased_indistinguishability_armE.
Print Assumptions five_card_row_repeated39_armE.
Print Assumptions five_card_row_biased_inv25_armE.

(* S5. *)
Print Assumptions s5_row_rand_tableau.
Print Assumptions s5_row_rand_rowE.
Print Assumptions s5_row_rand_armE.

(* PSL(2,11). *)
Print Assumptions psl211_row_alldecks_tableau.
Print Assumptions psl211_row_alldecks_rowE.
Print Assumptions psl211_row_alldecks_armE.
