(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgl27_rows: the eight-card orbit instance's two rows, written as programs  *)
(*                                                                            *)
(* The security argument a PGL(2,7) row makes is the one a threshold sharing  *)
(* makes: the dealer's secret, one of the two orbit classes, is dealt into    *)
(* eight cards by the orbit scheme, the deck is shuffled, each seat reads the *)
(* card at its own position, and any three seats together are meant to learn  *)
(* nothing about the secret. Four is the threshold, so every statement below  *)
(* is about a coalition of at most three of the eight seats. How nearly that  *)
(* holds is what the two families analysed below differ in.                   *)
(* The exact family draws the cut uniformly from the group, where             *)
(* three-transitivity makes the coalition's reading independent of the secret *)
(* outright. The word family draws it as a product of two hundred letters of  *)
(* the walk alphabet, where the same conclusion holds only up to the distance *)
(* that walk still has from uniform.                                          *)
(*                                                                            *)
(* Each family's row is one program. Its lines are the statements of          *)
(* pgg_tableau.v: the shared prefix deals the secret and adjoins the three   *)
(* run facts, one further line adjoins the family, one adjoins that family's  *)
(* security witness, and the last publishes the manifest row. The published   *)
(* rows are the manifest's pgl27_row_exact and pgl27_row_word, and the two    *)
(* rowE lemmas below hold by conversion, so the manifest's claim about this   *)
(* instance and the proof of it are one term.                                 *)
(*                                                                            *)
(* No line of a program is a theorem about this instance. What the instance   *)
(* supplies it supplies as a payload: the algebra and the interpreter budget  *)
(* on the first two lines, the three run facts on the third, the              *)
(* probability model on the fourth, and one security record on the fifth.     *)
(* The security mathematics reaches a row through that last payload alone,    *)
(* and through three named facts: pgl27_static_obsE,                          *)
(* which identifies the framework's seat reader with the instance's and which *)
(* the two witnesses consume in the function and sample-point forms           *)
(* pgl27_static_obs_funE and pgl27_exact_viewE; pgl27_word_cut_distE, which   *)
(* identifies the word adapter's cut law with rho_word; and                   *)
(* pgl27_word_marginal_bound, the walk's marginal bound. Two further          *)
(* things stay outside the programs: the reprice of the word row's bound from *)
(* 2^-40 + 2^-40 to 2^-39, which moves a number and proves nothing new about  *)
(* a coalition, and the two bridge lemmas that carry a row's accumulated      *)
(* proposition to the statement a paper cites.                                *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   pgl27_dealt             == the prefix shared by both rows                *)
(*   pgl27_exact_witness     == the exact arm's witness at every field and    *)
(*                              index                                         *)
(*   pgl27_word_cert         == the spectral arm's certificate                *)
(*   pgl27_row_exact_tableau == the exact row as a program                    *)
(*   pgl27_row_word_tableau  == the word row as a program                     *)
(*   pgl27_reprice39         == the name 2^-39 for the word row's bound       *)
(*   pgl27_row_word39        == the word row republished at that name         *)
(*   pgl27_word_target       == the word row's published statement            *)
(*   pgl27_exact_target      == the exact row's published statement           *)
(*   pgl27_word_restated     == the word row through the restate terminal     *)
(*   pgl27_exact_restated    == the exact row through the restate terminal    *)
(*   pgl27_word_same_statement                                                *)
(*                         == the published word statement and the word row's *)
(*                            restatement inhabit one type                    *)
(*   pgl27_exact_same_statement                                               *)
(*                         == the published exact statement and the exact     *)
(*                            row's restatement inhabit one type              *)
(*   pgl27_F                 == the ideal functionality the run realises      *)
(*                                                                            *)
(* Key results:                                                               *)
(*   pgl27_static_obsE     == the framework's seat reader is the instance's   *)
(*   pgl27_static_obs_funE == the same with the cut left free                 *)
(*   pgl27_exact_viewE     == the same with the secret left in the sample     *)
(*                            point                                           *)
(*   pgl27_row_exact_rowE  == the exact program publishes the manifest's row  *)
(*   pgl27_row_word_rowE   == the word program publishes the manifest's row   *)
(*   pgl27_word_bridge     == the word row's proposition gives its published  *)
(*                            statement                                       *)
(*   pgl27_exact_bridge    == the exact row's proposition gives its published *)
(*                            statement                                       *)
(*   pgl27_word_view_indist_restated                                          *)
(*                         == the word statement, from the word row alone     *)
(*   pgl27_exec_exact_view_indep_restated                                     *)
(*                         == the exact statement, from the exact row alone   *)
(*   pgl27_exact_view_secrecy                                                 *)
(*                         == the exact arm's four conjuncts at this instance *)
(*   pgl27_realises_expected                                                  *)
(*                         == the run recovers the functionality's value      *)
(******************************************************************************)

From mathcomp Require Import fintype finset reals.
From infotheo Require Import fdist.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgl27_group pgl27_profile pgl27_run.
From pgg_smc Require Import pgl27_secrecy pgl27_mixing pgl27_word_privacy.
From pgg_smc Require Import pgl27_exec pgl27_models.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     The prefix both rows share                                             *)
(******************************************************************************)

(** The first three lines of every eight-card orbit row: the algebra, the
    secret dealt at pgl27_fuel, and the three run facts. Sequencing stops here
    because the two rows part at the next line, where each adjoins its own
    probability model; everything up to this point is common to both, and what
    has been proved at this point is run correctness and nothing about a
    coalition. *)
Definition pgl27_dealt : Tableau Observed :=
  tableau_start pgl27_algebra
    ;;; dealt_step of pgl27_fuel
    ;;; execute_step of (existT _ pgl27_dealt_terminates
                           (existT _ pgl27_dealt_endpoints pgl27_dealt_recon)).

(******************************************************************************)
(*     The instance-side reading of a coalition                               *)
(******************************************************************************)

(** Seat i's entry of the framework's static coalition reading is seat i's
    entry of the instance's coalition view. The two are not the same term: the
    framework reads seat i at tnth (pi_starts _) i and the instance reads it at
    i, and they agree because this instance's seats start at the eight card
    positions in order. Every security statement of a row is made about the
    left-hand side and every theorem of this instance about the right, so this
    equation is the whole of what carries one to the other. *)
Lemma pgl27_static_obsE (R : realType) (C : {set 'I_8}) (s : bool)
    (g : pgg_gT pgl27_M) :
  @static_coalition_obs pgl27_algebra pgl27_dealt_params C s g
  = pgl27_view R C (s, g).
Proof.
apply/ffunP => i.
rewrite /static_coalition_obs /pgl27_view [LHS]ffunE [RHS]ffunE.
by case: ifP => // _; rewrite tnth_ord_tuple.
Qed.

(** The same identification with the cut left free, as an equality of functions
    of the cut. The spectral arm compares two laws obtained by pushing a reader
    forward along a distribution on cuts, so it needs the reader as one
    function and not as its values. *)
Lemma pgl27_static_obs_funE (R : realType) (C : {set 'I_8}) (s : bool) :
  @static_coalition_obs pgl27_algebra pgl27_dealt_params C s
  = (fun g => pgl27_view R C (s, g)).
Proof. by apply: boolp.funext => g; exact: pgl27_static_obsE. Qed.

(******************************************************************************)
(*     The exact family's witness                                             *)
(******************************************************************************)

(** The same identification once more, with the secret left inside the sample
    point. The exact arm compares a coalition's reading with the secret on one
    probability space, so the secret cannot be fixed first: the reader is a
    random variable of the pair, and that random variable is pgl27_view R C. *)
Lemma pgl27_exact_viewE (R : realType) (idx : unit)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile pgl27_algebra))).+1}) :
  (fun u => @static_coalition_obs pgl27_algebra pgl27_dealt_params C
              ((amf_sample pgl27_exact_family R idx).(sa_arg) u)
              ((amf_sample pgl27_exact_family R idx).(sa_cut) u))
  = pgl27_view R C.
Proof. by apply: boolp.funext; case=> s g; exact: pgl27_static_obsE. Qed.

(** The exact arm's witness: the dealt secret as a random variable on the exact
    sample space, and, at every coalition of fewer than four seats, the
    independence of that coalition's reading from it. The independence is
    pgl27_view_indep, which is three-transitivity of PGL(2,7) on the eight
    points read as a privacy statement, and it is exact: the uniform cut makes
    the reading carry no information about the secret at all, not a small
    amount. The framework derives the zero mutual information, the unchanged
    conditional entropy and the closure under post-processing from this one
    field, so the witness is the whole of what this instance owes the exact
    arm. *)
Definition pgl27_exact_witness (R : realType) (idx : unit)
  : ExactWitness (amf_sample pgl27_exact_family R idx) :=
  @MkExactWitness R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_exact_family R idx) bool (pgl27_secret R)
    (fun C HC =>
       let H3 : (#|C| <= 3)%N := HC in
       (eq_ind_r
          (fun v => pgl27P R |= v _|_ pgl27_secret R)
          (pgl27_view_indep R H3)
          (pgl27_exact_viewE R idx C))).

(******************************************************************************)
(*     The word family's certificate                                          *)
(******************************************************************************)

(** The spectral arm's certificate at each secret prior. Its five fields are
    the two-hundred-letter walk's marginal bound; the identification of that
    bound's law with the law the word adapter draws its cut from, which is
    pgl27_word_cut_distE read backwards; the uniform distribution on the group
    as the ideal cut; the distance pgl27_word_mixing of the walk from that
    ideal, an unconditional theorem about the walk whose bound is 2^-40; and
    the constancy of a coalition's reading of the ideal cut in the dealt secret,
    which is pgl27_view_law_const and is exact. The two currencies are visible
    in the fields: everything about the ideal cut is exact and three-transitive,
    and the only inexact quantity anywhere in this row is the walk's 2^-40. *)
Definition pgl27_word_cert (R : realType) (secretP : R.-fdist bool)
  : SpectralCert (amf_sample pgl27_word_family R secretP) :=
  @MkSpectralCert R pgl27_algebra pgl27_dealt_params
    (amf_sample pgl27_word_family R secretP)
    (pgl27_word_marginal_bound R)
    (esym (pgl27_word_cut_distE secretP))
    (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
    (pgl27_word_mixing R)
    (fun C HC s s' =>
       let H3 : (#|C| <= 3)%N := HC in
       (eq_ind_r
          (fun v => fdistmap v (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
                    = fdistmap (static_coalition_obs C s')
                        (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M)))
          (eq_ind_r
             (fun v => fdistmap (fun g => pgl27_view R C (s, g))
                         (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M))
                       = fdistmap v
                           (`U pgl27_G_pos : R.-fdist (pgg_gT pgl27_M)))
             (pgl27_view_law_const R s s' H3)
             (pgl27_static_obs_funE R C s'))
          (pgl27_static_obs_funE R C s))).

(******************************************************************************)
(*     The two row programs                                                   *)
(******************************************************************************)

(** The exact row: the shared prefix, the exact-shuffle model, the witness
    above, and the manifest row. Its last line publishes a row whose transfer
    status is StaticExecutedOnly, because the cut this model draws is already
    the uniform one and no idealized shuffle is being compared with a real
    one. What the finished row carries about a coalition of fewer than four
    seats is independence of the dealt secret, at every real field, with no
    numeric bound anywhere in it. *)
Definition pgl27_row_exact_tableau : PublishedRow :=
  pgl27_dealt
    ;;; sample_step of pgl27_exact_family
    ;;; certify_exact of pgl27_exact_witness
    ;;; publish BaselineClassicalOnly of StaticExecutedOnly.

(** The word row: the same prefix, the two-hundred-letter word model, the
    certificate above, and the manifest row at transfer status IdealFinite,
    which records that a finite walk is being compared with the ideal uniform
    cut. What the finished row carries is a variation distance between the
    readings of two dealt secrets, bounded by 2^-40 + 2^-40: the framework's
    transfer inequality crosses from the walk to the ideal cut and back again,
    and each crossing spends the same mixing bound once. *)
Definition pgl27_row_word_tableau : PublishedRow :=
  pgl27_dealt
    ;;; sample_step of pgl27_word_family
    ;;; certify_spectral of pgl27_word_cert
    ;;; publish BaselineClassicalOnly of IdealFinite.

(** The row the exact program publishes is the manifest's own row for this
    instance. Conversion decides it, so the descriptive row and the theorem
    proved about it cannot drift apart. *)
Lemma pgl27_row_exact_rowE :
  published_row pgl27_row_exact_tableau = pgl27_row_exact.
Proof. by []. Qed.

(** The same for the word program and the manifest's word row. The two rowE
    lemmas together are what makes the manifest a claim this file discharges
    rather than a table maintained beside it. *)
Lemma pgl27_row_word_rowE :
  published_row pgl27_row_word_tableau = pgl27_row_word.
Proof. by []. Qed.

(******************************************************************************)
(*     The word row republished at 2^-39                                      *)
(******************************************************************************)

(** The name 2^-39 for a bound, at every real field. A single real will not
    serve, because the security port quantifies over the field. *)
Definition pgl27_reprice39 : Reprice := fun R => Some (2%:R^-39 : R).

(** The word row with its bound republished as the single constant 2^-39. The
    accumulated bound is 2^-40 twice, and the identity that adds the two copies
    is pow2_split; the data, the model and the certificate are untouched, so the
    republished row asserts exactly what the row above asserts, at the number a
    reader expects to cite. *)
Definition pgl27_row_word39 : PublishedRowAt pgl27_reprice39 :=
  pgl27_dealt
    ;;; sample_step of pgl27_word_family
    ;;; certify_spectral of pgl27_word_cert
    ;;; conclude pgl27_reprice39 of (fun R _ => pow2_split R)
    ;;; publish BaselineClassicalOnly of IdealFinite.

(** The reprice obligation is one identity per real field and per index of the
    family, and pow2_split alone is an identity at one field. Supplying it bare
    is rejected, which is what keeps a row from republishing a bound that holds
    only at the field a reader happened to pick. *)
Fail Definition pgl27_row_word39_bare : PublishedRowAt pgl27_reprice39 :=
  pgl27_dealt
    ;;; sample_step of pgl27_word_family
    ;;; certify_spectral of pgl27_word_cert
    ;;; conclude pgl27_reprice39 of pow2_split
    ;;; publish BaselineClassicalOnly of IdealFinite.

(******************************************************************************)
(*     The word statement, from the word row                                  *)
(******************************************************************************)

(** The word family's published statement, as a proposition: at fewer than
    four seats, the coalition-view laws of two dealt secrets under the word
    shuffle are within 2^-39 in variation distance. This is the statement a
    reader of this instance cites, written out so that a row can be handed
    over as it. *)
Definition pgl27_word_target (R : realType) : Prop :=
  forall (C : {set 'I_8}) (s s' : bool), (#|C| <= 3)%N ->
    var_dist (fdistmap (fun g => pgl27_view R C (s, g)) (rho_word R))
             (fdistmap (fun g => pgl27_view R C (s', g)) (rho_word R))
    <= 2%:R^-39.

(** The derivation from the word row's accumulated proposition to that
    statement. Three rewritings and nothing else: the published 2^-39 is
    unfolded into the two copies of 2^-40 the row accumulated, the framework's
    seat reader is replaced by the instance's at each of the two secrets, and
    the adapter's cut law is replaced by rho_word. No step of the mathematics
    is repeated here; the bound itself comes from the row. *)
Lemma pgl27_word_bridge (R : realType) (secretP : R.-fdist bool)
    (q : StackAt AnalysisBridged)
    (Hq : q = tableau_at (pgl27_dealt
                         ;;; sample_step of pgl27_word_family
                         ;;; certify_spectral of pgl27_word_cert)) :
  StackProp AnalysisBridged q -> pgl27_word_target R.
Proof.
rewrite Hq => pf C s s' HC.
rewrite -pow2_split.
rewrite -(pgl27_static_obs_funE R C s) -(pgl27_static_obs_funE R C s').
rewrite -(pgl27_word_cut_distE secretP).
exact: (proj2 pf R secretP C s s' HC).
Qed.

(** The word row handed over as its published statement. The restate terminal
    keeps the row's data and replaces its accumulated conjunction by the
    proposition the caller wrote out, proved by the bridge above. *)
Definition pgl27_word_restated (R : realType) (secretP : R.-fdist bool)
    : RestatedTableau (pgl27_word_target R) :=
  pgl27_dealt
    ;;; sample_step of pgl27_word_family
    ;;; certify_spectral of pgl27_word_cert
    ;;; restate (pgl27_word_target R)
        of (pgl27_word_bridge secretP (q := _) erefl).

(** Two dealt secrets give coalition-view laws within 2^-39 under the word
    shuffle, at fewer than four seats. The statement is that of
    pgl27_word_view_indist, re-proved by reading the restated row's theorem
    field and applying it, with no proof step of its own; the secret prior is
    an argument because the word model is a family indexed by it, and any one
    index witnesses a statement the prior does not appear in. *)
Theorem pgl27_word_view_indist_restated (R : realType)
    (secretP : R.-fdist bool) (C : {set 'I_8}) (s s' : bool) :
  (#|C| <= 3)%N ->
  var_dist (fdistmap (fun g => pgl27_view R C (s, g)) (rho_word R))
           (fdistmap (fun g => pgl27_view R C (s', g)) (rho_word R))
  <= 2%:R^-39.
Proof. exact: (rq_thm (pgl27_word_restated secretP) C s s'). Qed.

(******************************************************************************)
(*     The exact statement, from the exact row                                *)
(******************************************************************************)

(** The exact family's published statement, as a proposition: at fewer than
    four seats, the joint law of the executed coalition reading and the dealt
    secret is the product of its two marginals. It is the product form of
    independence, which is what a reader comparing this instance with an ideal
    execution wants to see. *)
Definition pgl27_exact_target (R : realType) : Prop :=
  forall C : {set 'I_8}, (#|C| <= 3)%N ->
    fdistmap (fun u => (pgl27_view R C u, pgl27_secret R u)) (pgl27P R)
    = ((@sa_coalition_dist R pgl27_profile pgl27_exec_plug (pgl27_sample R)
          0 C) `x (fdistmap (pgl27_secret R) (pgl27P R)))%fdist.

(** The derivation from the exact row's accumulated proposition to that
    statement. The row's first conjunct of the arm is independence of the
    executed reader from the secret, which gives the product law directly; what
    remains is to rewrite the executed reader as the instance's view, using the
    row's own view identification and then pgl27_static_obsE. *)
Lemma pgl27_exact_bridge (R : realType) (q : StackAt AnalysisBridged)
    (Hq : q = tableau_at (pgl27_dealt
                         ;;; sample_step of pgl27_exact_family
                         ;;; certify_exact of pgl27_exact_witness)) :
  StackProp AnalysisBridged q -> pgl27_exact_target R.
Proof.
rewrite Hq => pf C HC.
case: (proj2 pf R tt C HC) => Hi _ _ _.
have Hd := inde_dist_of_RV2 Hi.
rewrite (_ : (fun u => (pgl27_view R C u, pgl27_secret R u))
           = (fun u => (@sa_coalition_view R pgl27_profile pgl27_exec_plug
                          (pgl27_sample R) 0 C u, pgl27_secret R u))).
  by rewrite -Hd.
apply: boolp.funext => u; congr (_, _).
by rewrite (proj2 (proj1 pf) R tt C) (pgl27_static_obsE R C u.1 u.2).
Qed.

(** The exact row handed over as its published statement, by the bridge above.
    The row's data is kept and only its accumulated conjunction is traded. *)
Definition pgl27_exact_restated (R : realType)
    : RestatedTableau (pgl27_exact_target R) :=
  pgl27_dealt
    ;;; sample_step of pgl27_exact_family
    ;;; certify_exact of pgl27_exact_witness
    ;;; restate (pgl27_exact_target R)
        of (@pgl27_exact_bridge R _ erefl).

(** At fewer than four seats the executed coalition reading of the exact model
    and the dealt secret have a product joint law. The statement is that of
    pgl27_exec_exact_view_indep, re-proved by reading the restated row's
    theorem field and applying it. *)
Theorem pgl27_exec_exact_view_indep_restated (R : realType)
    (C : {set 'I_8}) (HC : (#|C| <= 3)%N) :
  fdistmap (fun u => (pgl27_view R C u, pgl27_secret R u)) (pgl27P R)
  = ((@sa_coalition_dist R pgl27_profile pgl27_exec_plug (pgl27_sample R)
        0 C) `x (fdistmap (pgl27_secret R) (pgl27P R)))%fdist.
Proof. exact: (rq_thm (pgl27_exact_restated R) C HC). Qed.

(******************************************************************************)
(*     The exact arm's four conjuncts at this instance                        *)
(******************************************************************************)

(** The exact row's view secrecy at this instance: at fewer than four colluding
    seats the executed coalition reading is independent of the dealt secret,
    carries zero mutual information with it, leaves the secret's entropy
    unchanged under conditioning, and stays independent of it under every
    deterministic function of the seat-to-card map. The four conjuncts are the
    whole content of the exact arm at this instance; the proof is the row's
    security projection applied, so a reader who wants the
    information-theoretic reading of the row needs no further derivation. *)
Theorem pgl27_exact_view_secrecy (R : realType) (C : {set 'I_8})
    (HC : (#|C| < 4)%N) :
  [/\ pgl27P R |= (@sa_coalition_view R pgl27_profile pgl27_exec_plug
                     (pgl27_sample R) 0 C) _|_ (pgl27_secret R),
      `I( pgl27_secret R ;
          @sa_coalition_view R pgl27_profile pgl27_exec_plug
            (pgl27_sample R) 0 C ) = 0,
      `H( pgl27_secret R |
          @sa_coalition_view R pgl27_profile pgl27_exec_plug
            (pgl27_sample R) 0 C ) = `H `p_ (pgl27_secret R)
    & forall (W : finType) (h : {ffun 'I_8 -> 'I_8} -> W),
        pgl27P R |= (h `o (@sa_coalition_view R pgl27_profile pgl27_exec_plug
                             (pgl27_sample R) 0 C)) _|_ (pgl27_secret R)].
Proof. exact: (view_secrecy_of pgl27_row_exact_tableau R tt C HC). Qed.

(******************************************************************************)
(*     Each published statement and its restatement are one statement         *)
(******************************************************************************)

(** The published word statement and the theorem the word row restates inhabit
    one pair type, so the two are the same proposition and not merely two
    propositions about the same objects. A row that reached a weaker bound, a
    larger coalition or a different reader would fail here rather than pass
    with a different theorem under the same name. *)
Definition pgl27_word_same_statement (R : realType) (secretP : R.-fdist bool) :
  (forall (C : {set 'I_8}) (s s' : bool), (#|C| <= 3)%N ->
     var_dist (fdistmap (fun g => pgl27_view R C (s, g)) (rho_word R))
              (fdistmap (fun g => pgl27_view R C (s', g)) (rho_word R))
     <= 2%:R^-39)
  * (forall (C : {set 'I_8}) (s s' : bool), (#|C| <= 3)%N ->
     var_dist (fdistmap (fun g => pgl27_view R C (s, g)) (rho_word R))
              (fdistmap (fun g => pgl27_view R C (s', g)) (rho_word R))
     <= 2%:R^-39) :=
  (@pgl27_word_view_indist R, @pgl27_word_view_indist_restated R secretP).

(** The same check for the exact published statement and the theorem the exact
    row restates. *)
Definition pgl27_exact_same_statement (R : realType) :
  (forall C : {set 'I_8}, (#|C| <= 3)%N ->
     fdistmap (fun u => (pgl27_view R C u, pgl27_secret R u)) (pgl27P R)
     = ((@sa_coalition_dist R pgl27_profile pgl27_exec_plug (pgl27_sample R)
           0 C) `x (fdistmap (pgl27_secret R) (pgl27P R)))%fdist)
  * (forall C : {set 'I_8}, (#|C| <= 3)%N ->
     fdistmap (fun u => (pgl27_view R C u, pgl27_secret R u)) (pgl27P R)
     = ((@sa_coalition_dist R pgl27_profile pgl27_exec_plug (pgl27_sample R)
           0 C) `x (fdistmap (pgl27_secret R) (pgl27P R)))%fdist) :=
  (@pgl27_exec_exact_view_indep R, @pgl27_exec_exact_view_indep_restated R).

(** The two arms are different claims, and the difference is visible in what a
    row's projection takes after the coalition. A row certifying decay is asked
    here for a threshold proof in the position where it expects the first of two
    dealt secrets, and is rejected: what the word row proves at a coalition is a
    distance between the readings of two secrets, so the two secrets come before
    the threshold proof. *)
Fail Definition pgl27_word_arm_is_not_exact (R : realType)
    (secretP : R.-fdist bool) (C : {set 'I_8}) (HC : (#|C| < 4)%N) :=
  view_secrecy_of pgl27_row_word_tableau R secretP C HC.

(******************************************************************************)
(*     The ideal functionality                                                *)
(******************************************************************************)

(** The functionality the eight-card orbit run realises: the identity on the
    dealer's secret, tolerating coalitions of up to three seats. The function is
    the identity because this protocol reconstructs what was dealt rather than
    computing anything from several parties' inputs, and the tolerated size is
    one below the scheme's threshold of four. *)
Definition pgl27_F
    : Functionality (oe_inputT pgl27_observed) (oe_outT pgl27_observed) :=
  MkFunctionality id 3.

(** The value the run is built to recover is that functionality's function, as
    terms. Conversion decides it, so this correspondence needs no funext and
    carries no extensionality axiom of its own; a specification agreeing with
    the recovered value only pointwise would close through funext instead, and
    the difference would be visible in Print Assumptions. *)
Lemma pgl27_realises_expected : realises_expected pgl27_observed pgl27_F.
Proof. by []. Qed.
