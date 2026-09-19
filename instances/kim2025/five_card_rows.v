(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* five_card_rows: the five-card instance's three rows, as seven programs     *)
(*                                                                            *)
(* The security argument a five-card row makes is the threshold-sharing half  *)
(* of den Boer's trick: two parties commit one bit each, the dealer assembles *)
(* the five-card layout of that pair, the deck is cut at a uniformly drawn    *)
(* rotation, each seat reads the card at its own position, and one seat alone *)
(* is meant to learn nothing about the conjunction. Two is the privacy        *)
(* threshold of the five-card scheme, so every coalition statement below is   *)
(* about a coalition of at most one of the five seats, and that restriction   *)
(* is the scheme's own: leak_view_set records the exact leakage of every one  *)
(* of the thirty-two reveal patterns, and sends to zero the patterns of at    *)
(* most one card. Not every statement below is a coalition statement. The     *)
(* other half of den Boer's claim, that the full reveal discloses the         *)
(* conjunction and nothing further about the two bits separately, is input    *)
(* privacy, and five_card_row_biased_leak_bound states a ceiling on it under  *)
(* the biased cut, at a reveal of any list of card positions.                 *)
(*                                                                            *)
(* The uniform row is written in the statement surface of                     *)
(* pgg_tableau_syntax.v over the statements of pgg_tableau.v: the prefix      *)
(* names the ideal function, drives the run in the encoded-run mode and       *)
(* adjoins the three run facts, one further statement adjoins the uniform     *)
(* rotation model, one adjoins the exact witness, and the last publishes the  *)
(* manifest row. The published row is the manifest's five_card_row_uniform,   *)
(* and the rowE lemma below holds by conversion, so the manifest's claim      *)
(* about this instance and the proof of it are one term. The manifest's two   *)
(* further five-card rows are each written twice. One program per row stops   *)
(* at Sampled and names its model and nothing else. Beside it a certified     *)
(* program publishes that manifest row through the                            *)
(* input-indistinguishability arm, and what the arm certifies is this: for    *)
(* each real field, for every coalition of at most one of the five seats and  *)
(* for every two committed pairs, the law of that coalition's static endpoint *)
(* reading under the row's own cut law is within the row's published number   *)
(* of the same law at the other pair, the ideal cut being the uniform         *)
(* rotation law on the cut group. That is not independence of the reading     *)
(* from the secret, which the exact arm states and which the uniform row      *)
(* alone carries. It is conditional on a coalition of fewer than two seats.   *)
(* And it says nothing about the full reveal. Each certified row is written   *)
(* in both of the forms the tree uses, once at the certificate's own          *)
(* spectral number and once repriced to the constant a text quotes, two to    *)
(* the minus thirty-ninth for the repeated row and one twenty-fifth for the   *)
(* one-cut row.                                                               *)
(*                                                                            *)
(* The two Sampled programs stay as the programs that stop before a claim.    *)
(* What is proved beside them is of another kind: the endpoint marginal of    *)
(* one starting position under the seven-cut law, which                       *)
(* five_card_row_repeated_endpoint_lt carries, and Kim's ceiling on the       *)
(* information a reveal of any list of card positions gives about the two     *)
(* inputs, which five_card_row_biased_leak_bound carries. Neither arm of      *)
(* certify takes a bound of either kind: the exact arm asks for independence  *)
(* of the static coalition observation from a secret, which the development   *)
(* states under the uniform cut and not under the biased one, and a           *)
(* conditional mutual information is not a variation distance.                *)
(* AnalysisBridged is one constructor with two admission criteria. The        *)
(* manifest admits a row to it on any theorem about the sampled distribution  *)
(* and the observer, which is how manifest/pgg_analysis_status.v defines the  *)
(* level and which a leakage bound meets. A program reaches it only through   *)
(* one of the two arms of certify. Both criteria are met at both Kim rows.    *)
(* instances/s5/s5_rows.v records for s5_row_word the gap this file no longer *)
(* has: there the constancy an input-indistinguishability certificate asks    *)
(* for is false.                                                              *)
(*                                                                            *)
(* No statement of a program is a theorem about this instance. What the       *)
(* instance supplies it supplies inside a clause. In the uniform row the      *)
(* algebra, the ideal function, the input carrier, the layout, the decoder,   *)
(* the committers and the budget are the clause arguments of the first two    *)
(* statements; den_boer_assemble_valid and the three run facts are the        *)
(* obligations those same two statements ask for; the probability model is    *)
(* the argument of the fourth statement and one security record the payload   *)
(* of the fifth. The security mathematics reaches that row through the last   *)
(* payload alone, and through two named facts: five_card_static_obsE, which   *)
(* identifies the framework's direct computation of a coalition's view with   *)
(* the leakage space's colour reading encoded back into card positions, and   *)
(* five_card_viewS_indep, where leak_view_set gives that colour reading a     *)
(* leakage of zero at a pattern of at most one card. The sharpness annotation *)
(* pgl27_row_exact_tableau carries, that some coalition at the threshold      *)
(* already leaks, is not written here, because the closed forms of leak at    *)
(* two or more cards are proved positive nowhere.                             *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   five_card_committed     == the prefix: the encoded run with its three    *)
(*                              run facts                                     *)
(*   five_card_colour_fill   == a coalition's colours read back as card       *)
(*                              positions                                     *)
(*   five_card_exact_witness == the exact arm's witness at every field and    *)
(*                              index                                         *)
(*   five_card_row_uniform_tableau                                            *)
(*                           == the uniform row as a program                  *)
(*   five_card_row_repeated_tableau                                           *)
(*                           == the repeated row as a program, stopping at    *)
(*                              Sampled                                       *)
(*   five_card_row_biased_tableau                                             *)
(*                           == the biased row as a program, stopping at      *)
(*                              Sampled                                       *)
(*   kim_centi_cert, kim_biased_cert                                          *)
(*                           == each Kim row's certificate at its own         *)
(*                              bundle's spectral number                      *)
(*   kim_centi_cert40, kim_biased_cert_exact                                  *)
(*                           == the same two at the constants the rows        *)
(*                              republish                                     *)
(*   five_card_row_repeated_indistinguishability_tableau                      *)
(*   five_card_row_biased_indistinguishability_tableau                        *)
(*                           == each Kim row certified against the uniform    *)
(*                              rotation law and published                    *)
(*   five_card_row_repeated39, five_card_row_biased_inv25                     *)
(*                           == the same two repriced to 2^-39 and 1/25       *)
(*   five_card_reprice39, five_card_reprice_inv25                             *)
(*                           == the names 2^-39 and 1/25 for a bound          *)
(*   five_card_target        == the algebra with the ideal function a run of  *)
(*                              it computes                                   *)
(*   five_card_F             == the ideal functionality the run realises      *)
(*   five_card_F_ite         == that ideal function, in its conditional       *)
(*                              spelling                                      *)
(*                                                                            *)
(* Key results:                                                               *)
(*   five_card_viewS_nth     == a coalition's colour tuple read at one of its *)
(*                              own seats                                     *)
(*   five_card_static_obsE   == the framework's direct computation of a       *)
(*                              coalition's view is the instance's colour     *)
(*                              reading encoded                               *)
(*   five_card_viewS_indep   == at most one revealed colour is independent of *)
(*                              the conjunction                               *)
(*   five_card_exact_viewE   == the identification with the committed pair    *)
(*                              and the cut left in the sample point          *)
(*   five_card_static_obs_indep                                               *)
(*                           == below the threshold the direct computation is *)
(*                              independent of the conjunction                *)
(*   five_card_committed_paramsE                                              *)
(*                           == the prefix drives the run five_card_params    *)
(*                              names                                         *)
(*   five_card_row_uniform_rowE                                               *)
(*                           == the program publishes the manifest's row      *)
(*   five_card_row_repeated_indistinguishability_rowE                         *)
(*   five_card_row_biased_indistinguishability_rowE                           *)
(*                           == each certified program publishes its own      *)
(*                              manifest row                                  *)
(*   five_card_row_repeated_indistinguishability_publishedE                   *)
(*   five_card_row_biased_indistinguishability_publishedE                     *)
(*                           == the three coordinates each certified program  *)
(*                              publishes                                     *)
(*   five_card_row_biased_forms_publishedE                                    *)
(*                           == the two one-cut programs publish one row      *)
(*   kim_biased_epsE         == the one-cut bundle's marginal bound in closed *)
(*                              form                                          *)
(*   kim_biased_exact_le_eps == the exact one-cut distance is under that      *)
(*                              bound                                         *)
(*   kim_centi_cert_epsE, kim_biased_cert_epsE                                *)
(*                           == the number each certificate publishes         *)
(*   kim_centi_cert40_epsE   == the number the constant repeated certificate  *)
(*                              publishes                                     *)
(*   kim_centi_cert_eps_lt   == the repeated row's number is under the        *)
(*                              constant PGL(2,7)'s word row publishes        *)
(*   kim_biased_cert_eps_lt2 == the one-cut row's number is under the         *)
(*                              ceiling a variation distance has              *)
(*   five_card_pow2_39_split, five_card_inv50_split                           *)
(*                           == the identity each reprice discharges          *)
(*   five_card_reprice_inv25_lt2                                              *)
(*                           == the repriced one-cut number under the ceiling *)
(*   five_card_row_repeated_prefixE                                           *)
(*   five_card_row_biased_prefixE                                             *)
(*                           == each Kim row carries the prefix's algebra,    *)
(*                              parameters and observed execution             *)
(*   five_card_row_repeated_modelE                                            *)
(*   five_card_row_biased_modelE                                              *)
(*                           == each Kim row samples its manifest row's       *)
(*                              model                                         *)
(*   five_card_row_biased_levelE                                              *)
(*                           == the manifest's completion level for the       *)
(*                              biased row, which its Sampled program does    *)
(*                              not reach                                     *)
(*   five_card_row_repeated_endpoint_lt                                       *)
(*                           == one starting position's endpoint marginal     *)
(*                              under the repeated row's cut law              *)
(*   kim_centi_small         == the smallness condition at bias one           *)
(*                              hundredth                                     *)
(*   five_card_row_biased_leak_bound                                          *)
(*                           == Kim's input-privacy bound at the law the      *)
(*                              biased row samples                            *)
(*   five_card_FE            == that functionality is the conjunction at one  *)
(*                              tolerated seat                                *)
(*   five_card_realises_expected                                              *)
(*                           == the run recovers the functionality's value    *)
(*   five_card_exact_view_secrecy                                             *)
(*                           == the exact arm's four conjuncts at this        *)
(*                              instance                                      *)
(******************************************************************************)

Require Import Lia.
From mathcomp Require Import zify.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import reals boolp lra.
From infotheo Require Import fdist proba entropy.
From pgg_smc Require Import pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter pgg_trace_secrecy.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage five_card_exec five_card_models.
From pgg_smc Require Import kim_input_privacy.
From pgg_smc Require Import five_card_mixing.
From pgg_smc Require Import pgg_analysis_manifest pgg_tableau.
From pgg_smc Require Import pgg_tableau_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     The prefix the row is built on                                         *)
(******************************************************************************)

(** The first three statements of the five-card row: the algebra with the
    ideal function a run of it computes, the run driven in the
    encoded-run mode at fuel 100, and the three run facts. What has been
    proved at this point is run correctness, that the interpreter finishes,
    collects one endpoint per seat and decodes them to the conjunction of the
    two committed bits, and nothing about a coalition. *)
Definition five_card_committed : Tableau Observed :=
  five_card_algebra functionality (fun ab : bool * bool => ab.1 && ab.2)
  encoded inputs (bool * bool)
          layout den_boer_layout
          by den_boer_assemble_valid
          decoded_by den_boer_decode
          committed_by five_card_commits
          fuel 100
  execute terminates by five_card_terminates
          endpoints by five_card_endpoints
          recon by five_card_recon.

(** The run the prefix builds is the one five_card_params names. The clauses
    above spell the parameter record out a second time, and this equation is
    what keeps the two spellings from parting: every statement below is made
    at five_card_params, and the row is made at the clauses. *)
Lemma five_card_committed_paramsE :
  projT1 (projT2 (tableau_at five_card_committed)) = five_card_params.
Proof. by []. Qed.

(******************************************************************************)
(*     The instance-side reading of a coalition                               *)
(******************************************************************************)

(** A coalition's colours read back as card positions: seat i of the coalition
    holds the card encoding the colour the coalition's tuple records at i, and
    every seat outside it holds ord0. The framework reads a coalition as a
    finite function into card positions and the leakage space reads it as a
    tuple of colours in ascending seat order, and this is the map from the
    second shape to the first. *)
Definition five_card_colour_fill (C : {set 'I_5}) (t : #|C|.-tuple bool)
    : {ffun 'I_5 -> 'I_5} :=
  [ffun i => if i \in C then encode_bool (nth false t (index i (enum C)))
             else ord0].
Arguments five_card_colour_fill : clear implicits.

(** The entry of a coalition's colour tuple at the rank of one of its own
    seats is that seat's colour. The tuple is indexed by rank in the ascending
    enumeration of the coalition and the framework's direct computation is
    indexed by the seat itself, so this equation is the whole of the
    reindexing between them. *)
Lemma five_card_viewS_nth (R : realType) (C : {set 'I_5})
    (u : five_card_leakage.Omega) (i : 'I_5) :
  i \in C ->
  nth false (ViewS R C u) (index i (enum C)) = nth false (arr u) i.
Proof.
move=> iC.
rewrite /ViewS ViewTE.
rewrite (nth_map i) ?nth_index ?mem_enum //.
by rewrite index_mem mem_enum.
Qed.

(** Seat i's entry of the framework's direct computation of a coalition's
    view is the card encoding the colour the leakage space's cut row carries
    at seat i. The two are not the same term: the framework reads the dealt
    layout at the cut image of seat i's start, and the leakage space reads
    the rotated colour row at i. Every security statement of a row is made
    about the left-hand side and every theorem of this instance about the
    right, so this equation is the whole of what carries one to the other. *)
Lemma five_card_static_obsE (R : realType) (C : {set 'I_5})
    (u : five_card_leakage.Omega) :
  @static_coalition_obs five_card_algebra five_card_params C u.1
    (five_card_group.fc_sigma ^+ u.2)%g
  = five_card_colour_fill C (ViewS R C u).
Proof.
apply/ffunP => i.
rewrite static_coalition_obsE /five_card_colour_fill ffunE.
case: ifPn => // iC.
have -> : @ex_content_obs five_card_algebra five_card_params u.1
            ((five_card_group.fc_sigma ^+ u.2)%g,
             tnth (pi_starts (mp_PI (instance_profile five_card_algebra))) i)
        = tnth (den_boer_layout u.1)
            (@pgg_rho FiveCardKim_M (five_card_group.fc_sigma ^+ u.2)%g
               (tnth (pi_starts FiveCardKim_PI) i)) by [].
case: u iC => -[a b] k iC /=.
have Hcol : tnth (den_boer_layout (a, b))
              (@pgg_rho FiveCardKim_M (five_card_group.fc_sigma ^+ k)%g
                 (tnth (pi_starts FiveCardKim_PI) i))
          = encode_bool (nth false (arr (a, b, k)) i).
  rewrite -(five_card_layout_colourE R a b k i).
  by rewrite /den_boer_layout tnth_map !decode_encode_bool.
by rewrite Hcol (@five_card_viewS_nth R C (a, b, k) i iC).
Qed.

(******************************************************************************)
(*     The uniform family's witness                                           *)
(******************************************************************************)

(** At most one revealed colour of the cut row is independent of the
    conjunction. It is leak_view_set, the exact mutual information of a reveal
    pattern, at a pattern of at most one position, where that information is
    zero: every committed pair is dealt as three hearts and two clubs, so one
    card read after a uniform rotation is a heart with probability three
    fifths whatever was committed. This is the whole of the mathematics the
    row's security payload rests on. *)
Lemma five_card_viewS_indep (R : realType) (C : {set 'I_5}) :
  (#|C| < 2)%N -> P R |= (ViewS R C) _|_ (Secret R).
Proof.
move=> HC; apply/inde_RV_sym; apply: mutual_info_RV0_indep.
rewrite leak_view_set.
case: (ltnP #|C| 1) => H1.
  by apply: leakE0; apply/eqP; rewrite -leqn0 -ltnS.
by apply: leakE1; apply/eqP; rewrite eqn_leq H1 andbT -ltnS.
Qed.

(** The same identification as five_card_static_obsE, with the committed pair
    and the cut left inside the sample point. The exact arm compares a
    coalition's reading with the secret on one probability space, so neither
    can be fixed first: the direct computation is a random variable of the
    sample point, and that random variable is the coalition's colour reading
    encoded. *)
Lemma five_card_exact_viewE (R : realType) (idx : unit)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1}) :
  (fun u => @static_coalition_obs five_card_algebra five_card_params C
              ((amf_sample five_card_uniform_family R idx).(sa_arg) u)
              ((amf_sample five_card_uniform_family R idx).(sa_cut) u))
  = (five_card_colour_fill C) `o (ViewS R C).
Proof. by apply: boolp.funext => u; exact: five_card_static_obsE. Qed.

(** Below the threshold, the framework's direct computation of a coalition's
    view is independent of the conjunction. That computation is a
    deterministic function of the colours the coalition holds, so the
    independence is five_card_viewS_indep carried along the identification
    above by inde_RV_comp, and no probability is computed a second time. *)
Lemma five_card_static_obs_indep (R : realType) (idx : unit)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile five_card_algebra))).+1}) :
  (#|C| < profile_k (instance_profile five_card_algebra))%N ->
  sa_sampleP (amf_sample five_card_uniform_family R idx)
  |= (fun u => @static_coalition_obs five_card_algebra five_card_params C
                 ((amf_sample five_card_uniform_family R idx).(sa_arg) u)
                 ((amf_sample five_card_uniform_family R idx).(sa_cut) u))
     _|_ (Secret R).
Proof.
move=> HC; rewrite (five_card_exact_viewE R idx C).
by apply: pgg_trace_secrecy.inde_RV_comp; exact: five_card_viewS_indep.
Qed.

(** The exact arm's witness: the conjunction of the two committed bits as a
    random variable on the uniform sample space, and, at every coalition of
    fewer than two seats, the independence of that coalition's reading from
    it. The independence is exact, the uniform rotation making the reading
    carry no information about the conjunction at all rather than a small
    amount. The framework derives the zero mutual information, the unchanged
    conditional entropy and the closure under post-processing from this one
    field, so the witness is the whole of what this instance owes the exact
    arm. *)
Definition five_card_exact_witness (R : realType) (idx : unit)
  : ExactWitness (amf_sample five_card_uniform_family R idx) :=
  @MkExactWitness R five_card_algebra five_card_params
    (amf_sample five_card_uniform_family R idx) bool (Secret R)
    (@five_card_static_obs_indep R idx).

(******************************************************************************)
(*     The uniform row                                                        *)
(******************************************************************************)

(** The uniform row: the prefix above, the uniform rotation model, the witness
    above, and the manifest row. Its last statement publishes a row whose
    transfer status is StaticExecutedOnly, because the cut this model draws is
    already the uniform one and no idealized shuffle is being compared with a
    real one. What the finished row carries about a coalition of fewer than two
    seats is independence of the conjunction, at every real field, with no
    numeric bound anywhere in it. *)
Definition five_card_row_uniform_tableau : PublishedRow :=
  five_card_committed
    sample  five_card_uniform_family
    certify ExactIndependence five_card_exact_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(** The row the program publishes is the manifest's own row for the five-card
    development under the uniform cut. Conversion decides it, so the
    descriptive row and the theorem proved about it cannot drift apart. *)
Lemma five_card_row_uniform_rowE :
  published_row five_card_row_uniform_tableau = five_card_row_uniform.
Proof. by []. Qed.

(******************************************************************************)
(*     The exact arm's four conjuncts at this instance                        *)
(******************************************************************************)

(** The row's view secrecy at this instance: at fewer than two colluding seats
    the executed coalition view is independent of the conjunction of the
    committed bits, carries zero mutual information with it, leaves its
    entropy unchanged under conditioning, and stays independent of it under
    every deterministic function of the seat-to-card map. The four conjuncts
    are the whole content of the exact arm at this instance; the proof is the
    row's security projection applied, so a reader who wants the
    information-theoretic reading of the row needs no further derivation. *)
Theorem five_card_exact_view_secrecy (R : realType) (C : {set 'I_5})
    (HC : (#|C| < 2)%N) :
  [/\ P R |= (@sa_coalition_view R five_card_profile five_card_exec_plug
                (five_card_sample R) 0 C) _|_ (Secret R),
      `I( Secret R ;
          @sa_coalition_view R five_card_profile five_card_exec_plug
            (five_card_sample R) 0 C ) = 0,
      `H( Secret R |
          @sa_coalition_view R five_card_profile five_card_exec_plug
            (five_card_sample R) 0 C ) = `H `p_ (Secret R)
    & forall (W : finType) (h : {ffun 'I_5 -> 'I_5} -> W),
        P R |= (h `o (@sa_coalition_view R five_card_profile
                        five_card_exec_plug (five_card_sample R) 0 C))
               _|_ (Secret R)].
Proof. exact: (view_secrecy_of five_card_row_uniform_tableau R tt C HC). Qed.

(******************************************************************************)
(*     Kim's two rows                                                         *)
(******************************************************************************)

(** The repeated row sampled and not certified: the prefix above and the
    seven-cut model at bias one hundredth. The program stops at Sampled, one
    level under the AnalysisBridged the manifest records for this row. It
    names its model and nothing else, and what is proved beside it is the law
    of one starting position's endpoint under its cut, a statement about
    where a single starting position is sent and not about what any set of
    seats reads, so no security payload follows this program.
    five_card_row_repeated_indistinguishability_tableau is the certified
    program for the same row. *)
Definition five_card_row_repeated_tableau : Tableau Sampled :=
  five_card_committed
    sample kim_centi_family.

(** The biased row sampled and not certified: the same prefix and the single
    cut at the same bias. The program stops at Sampled, one level under the
    AnalysisBridged the manifest records for this row, because
    five_card_colour_view_leak_bound bounds a conditional mutual information
    and neither arm of certify takes a bound of that kind. The manifest's
    level for this row rests on that theorem and on the certificate
    five_card_row_biased_indistinguishability_tableau carries, and on no
    payload of this program. *)
Definition five_card_row_biased_tableau : Tableau Sampled :=
  five_card_committed
    sample kim_biased_family.

(** A model built over one run does not sample another. The two models above
    are typed over this prefix's observed execution, so the two statements
    hold; a family typed over a different instance's observed execution is
    rejected where it is written. *)
Fail Definition five_card_row_s5_family : Tableau Sampled :=
  five_card_committed
    sample S5Analysis.rand_family.

(** The three rows are one prefix and three continuations: the algebra, the
    run parameters and the observed execution of each Kim row are those of
    five_card_committed, as terms, and the observed execution carries the
    three run facts in its own fields. A reader comparing the three rows is
    therefore comparing probability models and nothing else. *)
Lemma five_card_row_repeated_prefixE :
  [/\ projT1 (tableau_at five_card_row_repeated_tableau)
      = projT1 (tableau_at five_card_committed),
      projT1 (projT2 (tableau_at five_card_row_repeated_tableau))
      = projT1 (projT2 (tableau_at five_card_committed))
    & sp_obs (tableau_at five_card_row_repeated_tableau)
      = ob_obs (tableau_at five_card_committed)].
Proof. by split. Qed.

(** The same for the biased row. *)
Lemma five_card_row_biased_prefixE :
  [/\ projT1 (tableau_at five_card_row_biased_tableau)
      = projT1 (tableau_at five_card_committed),
      projT1 (projT2 (tableau_at five_card_row_biased_tableau))
      = projT1 (projT2 (tableau_at five_card_committed))
    & sp_obs (tableau_at five_card_row_biased_tableau)
      = ob_obs (tableau_at five_card_committed)].
Proof. by split. Qed.

(** The model each program samples is the model the manifest's row for it
    names. Conversion decides both, so the manifest's description of these
    two five-card paths and the programs are one term, as
    five_card_row_uniform_rowE makes them for the uniform path. *)
Lemma five_card_row_repeated_modelE :
  sp_f (tableau_at five_card_row_repeated_tableau)
  = apr_model five_card_row_repeated.
Proof. by []. Qed.

(** The same for the biased row and the manifest's biased row. *)
Lemma five_card_row_biased_modelE :
  sp_f (tableau_at five_card_row_biased_tableau)
  = apr_model five_card_row_biased.
Proof. by []. Qed.

(** The manifest's completion level for the biased row is AnalysisBridged.
    five_card_row_biased_tableau reaches Sampled, so this equation and the
    rejected ascription that follows are the two halves of that one
    program's level gap. The equation is a fact about the manifest's row and
    not about anything any program proves, and the biased path also carries a
    program that does reach AnalysisBridged. *)
Lemma five_card_row_biased_levelE :
  apr_completion five_card_row_biased = AnalysisBridged.
Proof. by []. Qed.

(** five_card_row_biased_tableau admits no ascription at the manifest's
    level: that program reaches Sampled and the manifest records
    AnalysisBridged for the row. The two levels differ, and the difference is
    rejected by the kernel here rather than asserted in prose. It is a fact
    about this one program and not about the biased path, which
    five_card_row_biased_indistinguishability_tableau carries to
    AnalysisBridged. *)
Fail Definition five_card_row_biased_at_manifest_level
  : Tableau (apr_completion five_card_row_biased) :=
  five_card_row_biased_tableau.

(******************************************************************************)
(*     Kim's two rows, certified against the uniform rotation law             *)
(******************************************************************************)

(** The one-cut bundle's marginal bound is sqrt 5 over eighty. A row built on
    it publishes twice that, because the comparison through the ideal cut
    spends the number once for each of the two committed pairs. *)
Lemma kim_biased_epsE (R : realType) :
  sw_bound_eps (kim_biased_marginal_bound R) = Num.sqrt 5%:R * (1 / 80).
Proof. by rewrite /kim_biased_marginal_bound /= kim_lambda2_at_centi expr1. Qed.

(** The exact one-cut distance of kim_one_cut_centiE, one fiftieth, is at
    most the one-cut bundle's spectral number sqrt 5 over eighty, the epsilon
    of the marginal bound the certificate carries and half the number a row
    built on it publishes. The certificate therefore overstates the distance
    it certifies by about two fifths, and the gap is the price of quoting the
    bundle's number rather than the exact one. *)
Lemma kim_biased_exact_le_eps (R : realType) :
  1 / 50 <= sw_bound_eps (kim_biased_marginal_bound R) :> R.
Proof.
rewrite kim_biased_epsE -(@ler_pXn2r R 2 isT).
2: by rewrite nnegrE divr_ge0.
2: by rewrite nnegrE mulr_ge0 ?sqrtr_ge0 ?divr_ge0.
rewrite [X in _ <= X]exprMn sqr_sqrtr ?ler0n //.
rewrite !expr_div_n !expr1n [X in _ <= X]mulrA mulr1.
rewrite ler_pdivrMr ?exprn_gt0 ?ltr0n // mulrAC.
rewrite ler_pdivlMr ?exprn_gt0 ?ltr0n // mul1r.
rewrite -!natrX -natrM ler_nat.
by lia.
Qed.

(** The input-indistinguishability certificate of the repeated row. Its five
    fields are the seven-cut bundle's marginal bound; the identification of
    that bound's law with the law the repeated adapter draws its cut from;
    the uniform rotation law as the ideal cut; the distance of the seven-cut
    law from that ideal; and the constancy, at every coalition of at most one
    seat, of the reading of the ideal cut in the committed pair. The only
    inexact quantity in the row is the bundle's spectral number; the ideal
    cut and the constancy field are exact. *)
Definition kim_centi_cert (R : realType) (idx : unit)
  : IndistinguishabilityCert (amf_sample kim_centi_family R idx) :=
  @MkIndistinguishabilityCert R five_card_algebra five_card_params
    (amf_sample kim_centi_family R idx)
    (scb_bound (kim_security_bundle_centi R))
    (esym (kim_centi_cut_distE R))
    (sa_cut_dist (five_card_sample R))
    (@kim_centi_cut_mixing R)
    (@five_card_static_obs_const R).

(** The input-indistinguishability certificate of the one-cut row, with the
    same five fields at word length one. The ideal cut and the constancy, at
    every coalition of at most one seat, of the reading of it are the same
    two terms as in the repeated row's certificate, so the two rows differ
    only in the shuffle and its number. *)
Definition kim_biased_cert (R : realType) (idx : unit)
  : IndistinguishabilityCert (amf_sample kim_biased_family R idx) :=
  @MkIndistinguishabilityCert R five_card_algebra five_card_params
    (amf_sample kim_biased_family R idx)
    (kim_biased_marginal_bound R)
    (kim_biased_sample_cut_witnessE R)
    (sa_cut_dist (five_card_sample R))
    (@kim_biased_cut_mixing R)
    (@five_card_static_obs_const R).

(** Kim's repeated row certified by the input-indistinguishability arm and
    published at IdealFinite. The status is a parameter of publish and
    nothing checks it, so it is claimed against the criterion
    pgg_analysis_status.v states for IdealFinite: a cut-carrier transfer
    whose base premise is discharged, which is what a certificate comparing
    a finite shuffle with a named ideal cut supplies. *)
Definition five_card_row_repeated_indistinguishability_tableau : PublishedRow :=
  five_card_committed
    sample kim_centi_family
    certify InputIndistinguishability kim_centi_cert
    |> publish IdealFinite BaselineClassicalOnly.

(** Kim's one-cut row certified by the same arm and published at the same
    transfer status. Its certificate has the shape the repeated row's has,
    over the same ideal cut and with the same constancy field, so the same
    status is the honest one for it. *)
Definition five_card_row_biased_indistinguishability_tableau : PublishedRow :=
  five_card_committed
    sample kim_biased_family
    certify InputIndistinguishability kim_biased_cert
    |> publish IdealFinite BaselineClassicalOnly.

(** The repeated row's certified program publishes the manifest's row for that
    path. Conversion decides it, as it does for the uniform row. An
    AnalysisPathRow stores descriptive metadata and no Prop, so this equation
    fixes which path the program is written for and asserts nothing about the
    certificate the program carries. *)
Lemma five_card_row_repeated_indistinguishability_rowE :
  published_row five_card_row_repeated_indistinguishability_tableau
  = five_card_row_repeated.
Proof. by []. Qed.

(** The same for the one-cut row and the manifest's biased row. *)
Lemma five_card_row_biased_indistinguishability_rowE :
  published_row five_card_row_biased_indistinguishability_tableau
  = five_card_row_biased.
Proof. by []. Qed.

(** What a row equation does reject is a program written for another path.
    The repeated row's certified program publishes the seven-cut model at
    IdealFinite and the uniform row holds the uniform family at
    StaticExecutedOnly, so the two rows differ in two of their five fields
    and the equation is refused. *)
Fail Definition five_card_row_repeated_indistinguishability_uniform_rowE
  : published_row five_card_row_repeated_indistinguishability_tableau
    = five_card_row_uniform
  := erefl.

(** The three coordinates the repeated row's certified program publishes. *)
Lemma five_card_row_repeated_indistinguishability_publishedE :
  apr_completion
    (published_row five_card_row_repeated_indistinguishability_tableau)
    = AnalysisBridged
  /\ apr_transfer
       (published_row five_card_row_repeated_indistinguishability_tableau)
     = IdealFinite
  /\ apr_assumptions
       (published_row five_card_row_repeated_indistinguishability_tableau)
     = BaselineClassicalOnly.
Proof. by []. Qed.

(** The three coordinates the one-cut row's certified program publishes. *)
Lemma five_card_row_biased_indistinguishability_publishedE :
  apr_completion
    (published_row five_card_row_biased_indistinguishability_tableau)
    = AnalysisBridged
  /\ apr_transfer
       (published_row five_card_row_biased_indistinguishability_tableau)
     = IdealFinite
  /\ apr_assumptions
       (published_row five_card_row_biased_indistinguishability_tableau)
     = BaselineClassicalOnly.
Proof. by []. Qed.

(** Two copies of two to the minus fortieth make two to the minus
    thirty-ninth. An input-indistinguishability certificate publishes its
    marginal bound twice, once for each of the two committed pairs, so a row
    at the constant bound publishes a sum of two equal terms, and this
    identity is what names that sum by a single constant. *)
(* The mulr_natl and mulr_natr routes fail here because the ring numeral 2
   is itself a natmul and the rewrite fires inside it, yielding
   (2 * 1) ^- 40. *)
Fact five_card_pow2_39_split (R : realType) :
  (2%:R : R)^-40 + 2%:R^-40 = 2%:R^-39.
Proof. by rewrite [RHS]splitr exprSr invfM. Qed.

Section kim_cert_numbers.
Variable R : realType.

(** The repeated row's published bound in closed form: twice the bundle's
    spectral number at word length seven. It is the quantity a reader of the
    row sees, before any reprice names it by a constant. *)
Lemma kim_centi_cert_epsE (idx : unit) :
  cert_eps (kim_centi_cert R idx)
  = Num.sqrt 5%:R * (1 / 80) ^+ 7 + Num.sqrt 5%:R * (1 / 80) ^+ 7.
Proof. by rewrite /cert_eps /= kim_lambda2_at_centi. Qed.

(** That bound is under two to the minus thirty-ninth, which is the number
    PGL(2,7)'s word row publishes. *)
Lemma kim_centi_cert_eps_lt (idx : unit) :
  cert_eps (kim_centi_cert R idx) < 2%:R ^- 39.
Proof.
rewrite /cert_eps.
have -> : (2%:R : R) ^- 39 = 2%:R ^- 40 + 2%:R ^- 40.
  by rewrite five_card_pow2_39_split.
by apply: ltrD; exact: kim_bound_centi.
Qed.

(** The one-cut row's published bound in closed form: twice the bundle's
    spectral number at word length one, sqrt 5 over forty. *)
Lemma kim_biased_cert_epsE (idx : unit) :
  cert_eps (kim_biased_cert R idx)
  = Num.sqrt 5%:R * (1 / 80) + Num.sqrt 5%:R * (1 / 80).
Proof. by rewrite /cert_eps !kim_biased_epsE. Qed.

(** The one-cut row's bound is under two, the ceiling var_dist_le2 gives for
    a variation distance. The row therefore rules out a coalition of at most
    one seat telling the two committed pairs apart with certainty, which a
    bound at the ceiling would not. At about three percent of the ceiling it
    is not a strong statement. *)
Lemma kim_biased_cert_eps_lt2 (idx : unit) :
  cert_eps (kim_biased_cert R idx) < 2%:R.
Proof.
have Hs0 : 0 <= Num.sqrt 5%:R :> R by exact: sqrtr_ge0.
have Hs : Num.sqrt 5%:R <= 3%:R :> R.
  rewrite -(@ler_pXn2r R 2 isT).
  2: by rewrite nnegrE sqrtr_ge0.
  2: by rewrite nnegrE ler0n.
  by rewrite sqr_sqrtr ?ler0n // -natrX ler_nat.
by rewrite kim_biased_cert_epsE; lra.
Qed.

End kim_cert_numbers.

(******************************************************************************)
(*     The same two rows at the constants they republish                      *)
(******************************************************************************)

(** The repeated row's certificate with the constant in the marginal-bound
    field. The ideal cut, the identification equation and the constancy of
    the reading at every coalition of at most one seat are the same terms as
    in kim_centi_cert; the marginal bound carries two to the minus fortieth
    in place of the spectral expression, and the mixing field is the same
    distance bounded by that constant. *)
Definition kim_centi_cert40 (R : realType) (idx : unit)
  : IndistinguishabilityCert (amf_sample kim_centi_family R idx) :=
  @MkIndistinguishabilityCert R five_card_algebra five_card_params
    (amf_sample kim_centi_family R idx)
    (kim_centi_marginal_bound40 R)
    (esym (kim_centi_cut_distE R))
    (sa_cut_dist (five_card_sample R))
    (@kim_centi_cut_mixing40 R)
    (@five_card_static_obs_const R).

(** The certificate's own bound is then two copies of two to the minus
    fortieth, by conversion and with no arithmetic. *)
Lemma kim_centi_cert40_epsE (R : realType) (idx : unit) :
  cert_eps (kim_centi_cert40 R idx) = 2%:R ^- 40 + 2%:R ^- 40 :> R.
Proof. by []. Qed.

(** The name two to the minus thirty-ninth for a bound, at every real
    field. *)
Definition five_card_reprice39 : Reprice := fun R => Some (2%:R ^- 39 : R).

(** The repeated row republished at that constant. The reprice supplies the
    identity five_card_pow2_39_split and changes nothing else: the data, the
    model and the certificate are the same terms, so what a coalition of at
    most one seat is shown is the same statement under a different name for
    the number. *)
Definition five_card_row_repeated39 : PublishedRowAt five_card_reprice39 :=
  five_card_committed
    ;;; sample_step of kim_centi_family
    ;;; certify_indistinguishability of kim_centi_cert40
    ;;; conclude five_card_reprice39 of (fun R _ => five_card_pow2_39_split R)
    ;;; publish BaselineClassicalOnly of IdealFinite.

(** The reprice obligation is one identity per real field and per index.
    five_card_pow2_39_split is quantified over every real field but not over
    the family index, so it does not have the shape conclude asks for. *)
Fail Definition five_card_row_repeated39_bare
  : PublishedRowAt five_card_reprice39 :=
  five_card_committed
    ;;; sample_step of kim_centi_family
    ;;; certify_indistinguishability of kim_centi_cert40
    ;;; conclude five_card_reprice39 of five_card_pow2_39_split
    ;;; publish BaselineClassicalOnly of IdealFinite.

(** The one-cut row's certificate at the exact number one fiftieth. *)
Definition kim_biased_cert_exact (R : realType) (idx : unit)
  : IndistinguishabilityCert (amf_sample kim_biased_family R idx) :=
  @MkIndistinguishabilityCert R five_card_algebra five_card_params
    (amf_sample kim_biased_family R idx)
    (kim_biased_marginal_bound_exact R)
    (kim_biased_sample_cut_witnessE R)
    (sa_cut_dist (five_card_sample R))
    (@kim_biased_cut_mixing_exact R)
    (@five_card_static_obs_const R).

(** Two copies of one fiftieth make one twenty-fifth. It is the identity
    that names the sum of the one-cut row's two exact per-card-position
    numbers by the single constant that row publishes. *)
Fact five_card_inv50_split (R : realType) : (1 / 50 : R) + 1 / 50 = 1 / 25.
Proof. by lra. Qed.

(** The name one twenty-fifth for a bound, at every real field. *)
Definition five_card_reprice_inv25 : Reprice := fun R => Some (1 / 25 : R).

(** The one-cut row republished at the exact constant, at the same transfer
    status as the row at the spectral number. The certificate it carries
    compares the same cut with the same ideal, so the number it publishes
    changes and the status it earns does not. *)
Definition five_card_row_biased_inv25
  : PublishedRowAt five_card_reprice_inv25 :=
  five_card_committed
    ;;; sample_step of kim_biased_family
    ;;; certify_indistinguishability of kim_biased_cert_exact
    ;;; conclude five_card_reprice_inv25 of (fun R _ => five_card_inv50_split R)
    ;;; publish BaselineClassicalOnly of IdealFinite.

(** The two one-cut programs publish one row, although their certificates
    carry different numbers, sqrt 5 over forty against one twenty-fifth. An
    AnalysisPathRow holds descriptive metadata and no Prop, so an equation
    between two published rows says nothing about either certificate, and in
    particular cannot say which transfer status is the honest one. *)
Lemma five_card_row_biased_forms_publishedE :
  published_row five_card_row_biased_indistinguishability_tableau
  = published_row five_card_row_biased_inv25.
Proof. exact: erefl. Qed.

(** One twenty-fifth is under two, the ceiling var_dist_le2 gives for a
    variation distance, so the repriced one-cut row is not vacuous. *)
Lemma five_card_reprice_inv25_lt2 (R : realType) : (1 / 25 : R) < 2%:R.
Proof. by lra. Qed.

(******************************************************************************)
(*     What the two rows carry beside their programs                          *)
(******************************************************************************)

(** The law of the image of one starting position under the cut the repeated
    row samples is within two to the minus fortieth of the uniform law on the
    five card positions, in variation distance, at every starting position and
    every real field. Both laws are laws on card positions, so this is one
    position's endpoint marginal, and the statement names no seat, no set of
    seats and no secret. It is kim_deal_centi_lt read at the law the program
    names, through kim_centi_cut_distE. *)
Lemma five_card_row_repeated_endpoint_lt (R : realType) (s : 'I_5) :
  var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
              (sa_cut_dist (amf_sample kim_centi_family R tt)))
           (fdist_uniform (card_ord 5))
  < 2%:R ^- 40.
Proof. by rewrite kim_centi_cut_distE; exact: kim_deal_centi_lt. Qed.

(** The bias one hundredth is smaller in absolute value than one fifth, the
    smallness condition of kim_input_private. It is the fourth of the side
    conditions on this bias, beside kim_centi_lt, kim_centi_gt and
    kim_centi_spec of five_card_kim.v, and the one Kim's input-privacy bound
    consumes. *)
Lemma kim_centi_small (R : realType) : 0 < 5%:R^-1 - `|1 / 100 : R|.
Proof.
by rewrite subr_gt0 ger0_norm ?divr_ge0// ltr_pdivrMr ?ltr0n//
   mulrC ltr_pdivlMr ?ltr0n// mul1r ltr_nat.
Qed.

(** The conditional mutual information between the two committed inputs and
    the executed colour reading at a list of card positions, given the
    conjunction the run computes, is at most kim_leak_bound at bias one
    hundredth, under the law the biased row samples. It is
    five_card_colour_view_leak_bound with every random variable typed at
    that law, which is what sa_sampleP of the family's member is by
    conversion. The statement is a numeric ceiling on that information and
    not the assertion that the information vanishes, it is about a reading
    at a list of card positions and not about a coalition of seats, and it
    is carried beside the program above rather than by it. *)
Lemma five_card_row_biased_leak_bound (R : realType) (A : seq nat) :
  cond_mutual_info
    (`p_ [% (kim_inputs (kim_centi_lt R) (kim_centi_gt R)
             : {RV (sa_sampleP (amf_sample kim_biased_family R tt))
                   -> bool * bool}),
            ((fun w : five_card_leakage.Omega =>
                five_card_exec_colour_view A w.1
                  (five_card_group.fc_sigma ^+ w.2)%g)
             : {RV (sa_sampleP (amf_sample kim_biased_family R tt))
                   -> (size A).-tuple bool}),
            (kim_secret (kim_centi_lt R) (kim_centi_gt R)
             : {RV (sa_sampleP (amf_sample kim_biased_family R tt)) -> bool})])
  <= kim_leak_bound (1 / 100 : R).
Proof. exact: (five_card_colour_view_leak_bound _ _ (kim_centi_small R)). Qed.

(******************************************************************************)
(*     The ideal functionality                                                *)
(******************************************************************************)

(** The algebra together with the ideal function a run of it computes. A
    dealer-dealt run has the identity forced on it and writes no such record;
    a run whose input is committed by two parties does not, and the function
    has to be named. The prefix above names the same one in its own
    functionality clause, and the two spellings are held together by
    five_card_realises_expected below, which is reflexivity only while they
    agree. *)
Definition five_card_target : Targeted :=
  five_card_algebra functionality (fun ab : bool * bool => ab.1 && ab.2).

(** The functionality the five-card run realises: the conjunction of the two
    committed bits, tolerating a coalition of one seat. The tolerated size is
    not chosen here but read off the algebra's scheme by targeted_F, which is
    what makes the specification a consequence of the instance rather than a
    second description of it that could disagree with the first. *)
Definition five_card_F
    : Functionality (oe_inputT five_card_observed) (oe_outT five_card_observed)
  := targeted_F five_card_target.

(** The ideal function and the tolerated coalition size of this instance,
    written out. Both are read off the target and the algebra, so this
    equation is where a reader of five_card_F learns which two values they
    are. *)
Lemma five_card_FE :
  five_card_F = MkFunctionality (fun ab : bool * bool => ab.1 && ab.2) 1.
Proof. by []. Qed.

(** The ideal function is checked up to conversion and not up to spelling: the
    conditional form of the conjunction names the same function. *)
Definition five_card_F_ite
  : fn_f five_card_F = (fun ab : bool * bool => if ab.1 then ab.2 else false)
  := erefl.

(** A different Boolean function of the same two bits is rejected where it is
    written, so the function a row names is decided by the kernel rather than
    by the reader. *)
Fail Definition five_card_F_or
  : fn_f five_card_F = (fun ab : bool * bool => ab.1 || ab.2) := erefl.

(** The value the run is built to recover is that functionality's function, as
    terms. Conversion decides it, so this correspondence needs no funext and
    carries no extensionality axiom of its own; a specification agreeing with
    the recovered value only pointwise would close through funext instead, and
    the difference would be visible in Print Assumptions. *)
Lemma five_card_realises_expected :
  realises_expected five_card_observed five_card_F.
Proof. by []. Qed.
