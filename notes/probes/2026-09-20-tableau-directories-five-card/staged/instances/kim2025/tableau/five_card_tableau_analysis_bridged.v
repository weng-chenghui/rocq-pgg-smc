(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* five_card_tableau_analysis_bridged: the five-card instance at the          *)
(* AnalysisBridged level                                                      *)
(*                                                                            *)
(* The AnalysisBridged level adjoins one security arm to a Sampled value, and *)
(* the proposition it carries is that arm's own, on top of run correctness    *)
(* and of the identification of the two readings of a coalition. A publish    *)
(* terminal then turns the value into a PublishedRow. Every payload this      *)
(* instance owes an arm is here, every row it publishes is here, and every    *)
(* statement whose subject is a payload or a row is here. The one security    *)
(* statement of the instance whose subject is neither is Kim's input-privacy  *)
(* bound, which is in five_card_tableau_sampled.v.                            *)
(*                                                                            *)
(* Three arms are used over the one committed run. The exact arm takes an     *)
(* ExactWitness, whose one field is independence of a coalition's reading     *)
(* from the conjunction of the two committed bits; under the uniform rotation *)
(* this is leak_view_set, the exact mutual information of a reveal pattern,   *)
(* at a pattern of at most one card, where that information is zero, and the  *)
(* arm carries no number. The input-indistinguishability arm takes a          *)
(* certificate comparing the readings of two committed pairs under one model, *)
(* with the uniform rotation law as the ideal cut. The proximity arm takes a  *)
(* certificate comparing one model with an ideal one at the same index, and   *)
(* the ideal it names here is the uniform model itself, whose own privacy is  *)
(* the exact arm's theorem.                                                   *)
(*                                                                            *)
(* Four numbers, each carried by one certificate. kim_centi_cert carries the  *)
(* seven-cut bundle's marginal bound, the square root of five times the       *)
(* seventh power of one eightieth, and its cert_eps is that number added to   *)
(* itself, one for each of the two committed pairs it compares.               *)
(* kim_biased_cert carries the one-cut bundle's marginal bound, the square    *)
(* root of five over eighty, so its cert_eps is the square root of five over  *)
(* forty. kim_biased_cert_exact carries the exact one-cut number, one         *)
(* fiftieth, so its cert_eps is one twenty-fifth. kim_biased_proximity_cert   *)
(* carries one fiftieth and compares one law with one law, so that is also    *)
(* what its row publishes.                                                    *)
(*                                                                            *)
(* Two terminals restate a certificate's number as a constant a text quotes.  *)
(* five_card_row_repeated39 concludes the repeated row at two to the minus    *)
(* thirty-ninth, and kim_centi_cert_eps_lt is strict, so the number the row   *)
(* publishes is strictly above the number the certificate proved.             *)
(* five_card_row_biased_inv25 concludes the one-cut row at one twenty-fifth,  *)
(* and five_card_inv50_split is an equality, so there the two numbers are the *)
(* same. Each of these numbers bounds a sum of absolute differences, twice a  *)
(* total variation distance, so a distinguisher's advantage against a row is  *)
(* at most half the number that row publishes: one hundredth at the proximity *)
(* row, one fiftieth at the one-cut row concluded at one twenty-fifth.        *)
(* five_card_biased_view_own_marginals removes the ideal from the proximity   *)
(* row's statement, at three fiftieths, which leaves an advantage of at most  *)
(* three hundredths.                                                          *)
(*                                                                            *)
(* Two is the threshold the derived profile declares, so every statement here *)
(* that quantifies over a coalition quantifies over at most one of the five   *)
(* seats, each seat reading the card at the cut image of its own position. No *)
(* sharpness annotation is written at any row of this instance, because the   *)
(* closed forms of the leakage at two or more cards are proved positive       *)
(* nowhere.                                                                   *)
(*                                                                            *)
(* Seven rows are published, and the three the manifest carries for this      *)
(* instance are among them: five_card_row_uniform_rowE,                       *)
(* five_card_row_repeated_indistinguishability_rowE and                       *)
(* five_card_row_biased_indistinguishability_rowE discharge                   *)
(* five_card_row_uniform, five_card_row_repeated and five_card_row_biased of  *)
(* pgg_analysis_manifest.v by conversion, and those three are all the         *)
(* AnalysisPathRows the manifest carries over the five-card instance. The     *)
(* manifest publishes none of the three by a route this development's         *)
(* programs do not take. Of the other four, three write a claim the manifest  *)
(* already carries a second way: the repeated row and the one-cut row         *)
(* concluded at the constants a text quotes, and the one-cut row continued    *)
(* from its named Sampled value. The fourth is the proximity row, which       *)
(* publishes that same AnalysisPathRow under a different arm. A published row *)
(* is a program, and an AnalysisPathRow holds descriptive metadata and no     *)
(* Prop, so two rows publishing one AnalysisPathRow say nothing about each    *)
(* other's claim.                                                             *)
(*                                                                            *)
(* Where each published row's chain is, one entry per row.                    *)
(* five_card_row_uniform_tableau, under The uniform row:                      *)
(*     five_card_row_uniform_sampledE, five_card_row_uniform_rowE,            *)
(*     five_card_row_uniform_armE, and the reading                            *)
(*     five_card_exact_view_secrecy.                                          *)
(* five_card_row_repeated_indistinguishability_tableau, under Kim's two       *)
(*     rows, certified against the uniform rotation law:                      *)
(*     five_card_row_repeated_indistinguishability_sampledE, _rowE, _armE     *)
(*     and _publishedE, and no reading of its own.                            *)
(* five_card_row_biased_indistinguishability_tableau, under the same          *)
(*     banner: five_card_row_biased_indistinguishability_sampledE, _rowE,     *)
(*     _armE and _publishedE, and no reading of its own.                      *)
(* five_card_row_repeated39, under The same two rows at the constants         *)
(*     they publish: five_card_row_repeated39_sampledE,                       *)
(*     five_card_row_repeated39_atE, five_card_row_repeated39_armE, no        *)
(*     _rowE of its own, and no reading of its own.                           *)
(* five_card_row_biased_inv25, under the same banner:                         *)
(*     five_card_row_biased_inv25_sampledE,                                   *)
(*     five_card_row_biased_inv25_armE,                                       *)
(*     five_card_row_biased_forms_publishedE in place of a _rowE of its       *)
(*     own, and no reading of its own.                                        *)
(* five_card_row_biased_branch_indistinguishability, under One model, two     *)
(*     claims, two rows: written from five_card_row_biased_tableau, so no     *)
(*     _sampledE, then _atE, _rowE and _armE, and no reading of its own.      *)
(* five_card_row_biased_proximity, under the same banner: written from        *)
(*     five_card_row_biased_tableau, so no _sampledE,                         *)
(*     five_card_row_biased_proximity_rowE, _publishedE and _armE, and the    *)
(*     readings five_card_biased_view_proximity and                           *)
(*     five_card_biased_view_own_marginals.                                   *)
(*                                                                            *)
(* An importer of this instance names one module per kind of name. The        *)
(* algebraic file declares the Algebraic value and the Targeted; the          *)
(* executable file the Executable value and its parameter equation; the       *)
(* observed file the prefix, its two equations and the ideal functionality;   *)
(* the sampled file the three named models, their equations against the       *)
(* prefix and the three statements carried beside them; this file the         *)
(* payloads, the rows, the row, arm and re-cut equations, the numbers and the *)
(* arm theorems; and the checks file the recorded rejections and the          *)
(* comparison of the two one-cut rows' arms. No file of the six uses Require  *)
(* Export.                                                                    *)
(*                                                                            *)
(* This file requires instances/kim2025/five_card_proximity.v, which holds    *)
(* the laws and the distance the proximity certificate is built from: the     *)
(* uniform law on the pair of committed bits under either cardinality proof,  *)
(* the factorisation of a coalition's reading and the secret through the pair *)
(* of the committed bits and the cut, that pair's joint law at a product law  *)
(* on the sample space, and the bound of one fiftieth on the distance between *)
(* the two models' joint laws, which is the certificate's last field. The six *)
(* link lemmas of the exact arm are not there but here, because no proof that *)
(* stays uses them.                                                           *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   five_card_colour_fill   == a coalition's colours read back as card       *)
(*                              positions                                     *)
(*   five_card_exact_witness == the exact arm's witness at every field and    *)
(*                              index                                         *)
(*   five_card_row_uniform_tableau                                            *)
(*                           == the uniform row as a program                  *)
(*   kim_centi_cert          == the repeated row's certificate at its         *)
(*                              bundle's number                               *)
(*   kim_biased_cert         == the one-cut row's certificate at its bundle's *)
(*                              number                                        *)
(*   five_card_row_repeated_indistinguishability_tableau                      *)
(*                           == the repeated row as a program at the input-   *)
(*                              indistinguishability arm                      *)
(*   five_card_row_biased_indistinguishability_tableau                        *)
(*                           == the one-cut row as a program at that same arm *)
(*   five_card_reprice39     == the name two to the minus thirty-ninth for a  *)
(*                              bound                                         *)
(*   five_card_row_repeated39                                                 *)
(*                           == the repeated row concluded at that number     *)
(*   kim_biased_cert_exact   == the one-cut row's certificate at the exact    *)
(*                              number one fiftieth                           *)
(*   five_card_reprice_inv25 == the name one twenty-fifth for a bound         *)
(*   five_card_row_biased_inv25                                               *)
(*                           == the one-cut row concluded at that number      *)
(*   kim_biased_proximity_cert                                                *)
(*                           == the one-cut model's proximity certificate     *)
(*   five_card_row_biased_branch_indistinguishability                         *)
(*                           == the one-cut row at the input-                 *)
(*                              indistinguishability arm, continued from the  *)
(*                              named model                                   *)
(*   five_card_row_biased_proximity                                           *)
(*                           == the one-cut row as a program at the proximity *)
(*                              arm, published at one fiftieth                *)
(*   five_card_reprice_inv100                                                 *)
(*                           == the name one hundredth for a bound            *)
(*   five_card_biased_proximity_at_singleton                                  *)
(*                           == the proximity row's claim at one concrete     *)
(*                              seat                                          *)
(*                                                                            *)
(* Key results:                                                               *)
(*   five_card_viewS_nth     == a coalition's colour tuple read at one of its *)
(*                              own seats                                     *)
(*   five_card_static_obsE   == the framework's direct computation of a       *)
(*                              coalition's reading is the instance's colour  *)
(*                              reading encoded                               *)
(*   five_card_viewS_indep   == at most one revealed colour is independent of *)
(*                              the conjunction                               *)
(*   five_card_exact_viewE   == the same identification with the committed    *)
(*                              pair and the cut left in the sample point     *)
(*   five_card_static_obs_indep                                               *)
(*                           == below the threshold of two, that is at a      *)
(*                              coalition of at most one of the five seats,   *)
(*                              the direct computation is independent of the  *)
(*                              conjunction                                   *)
(*   five_card_row_uniform_sampledE                                           *)
(*                           == the uniform row continues the named uniform   *)
(*                              model                                         *)
(*   five_card_row_uniform_rowE                                               *)
(*                           == the uniform program publishes the manifest's  *)
(*                              row                                           *)
(*   five_card_row_uniform_armE                                               *)
(*                           == the uniform row carries the exact arm         *)
(*   five_card_exact_view_secrecy                                             *)
(*                           == at a coalition of at most one of the five     *)
(*                              seats, the exact arm's four conjuncts at this *)
(*                              instance                                      *)
(*   kim_biased_epsE         == the one-cut bundle's marginal bound in closed *)
(*                              form                                          *)
(*   kim_biased_exact_le_eps == the exact one-cut distance is under that      *)
(*                              bound                                         *)
(*   five_card_row_repeated_indistinguishability_sampledE                     *)
(*                           == the repeated certified row continues the      *)
(*                              named repeated model                          *)
(*   five_card_row_biased_indistinguishability_sampledE                       *)
(*                           == the one-cut certified row continues the named *)
(*                              one-cut model                                 *)
(*   five_card_row_repeated_indistinguishability_rowE                         *)
(*                           == the repeated certified program publishes the  *)
(*                              manifest's row                                *)
(*   five_card_row_biased_indistinguishability_rowE                           *)
(*                           == the one-cut certified program publishes the   *)
(*                              manifest's row                                *)
(*   five_card_row_repeated_indistinguishability_armE                         *)
(*                           == the repeated certified row carries the input- *)
(*                              indistinguishability arm                      *)
(*   five_card_row_biased_indistinguishability_armE                           *)
(*                           == the one-cut certified row carries that same   *)
(*                              arm                                           *)
(*   five_card_row_repeated_indistinguishability_publishedE                   *)
(*                           == the three coordinates the repeated certified  *)
(*                              program publishes                             *)
(*   five_card_row_biased_indistinguishability_publishedE                     *)
(*                           == the three coordinates the one-cut certified   *)
(*                              program publishes                             *)
(*   five_card_pow2_39_split == two to the minus thirty-ninth as a sum of two *)
(*                              per-pair bounds                               *)
(*   kim_centi_cert_epsE     == the repeated row's number in closed form      *)
(*   kim_centi_cert_eps_lt   == that number is under two to the minus thirty- *)
(*                              ninth, strictly                               *)
(*   kim_biased_cert_epsE    == the one-cut row's number in closed form       *)
(*   kim_biased_cert_eps_lt2 == that number is under two, the bound           *)
(*                              var_dist_le2 gives                            *)
(*   five_card_row_repeated39_sampledE                                        *)
(*                           == the concluded repeated row continues the      *)
(*                              named repeated model                          *)
(*   five_card_row_repeated39_atE                                             *)
(*                           == the repeated row at two to the minus thirty-  *)
(*                              ninth and at its own number carry one         *)
(*                              accumulated stack                             *)
(*   five_card_row_repeated39_armE                                            *)
(*                           == the concluded repeated row carries that same  *)
(*                              arm                                           *)
(*   five_card_inv50_split   == one twenty-fifth as a sum of two per-pair     *)
(*                              bounds                                        *)
(*   five_card_row_biased_inv25_sampledE                                      *)
(*                           == the concluded one-cut row continues the named *)
(*                              one-cut model                                 *)
(*   five_card_row_biased_forms_publishedE                                    *)
(*                           == the two one-cut certified programs publish    *)
(*                              one row                                       *)
(*   five_card_row_biased_inv25_armE                                          *)
(*                           == the concluded one-cut row carries that same   *)
(*                              arm                                           *)
(*   five_card_reprice_inv25_lt2                                              *)
(*                           == one twenty-fifth is under two                 *)
(*   kim_biased_proximity_cert_idealE                                         *)
(*                           == the certificate's ideal is the uniform row's  *)
(*                              model, and the port built from its witness is *)
(*                              that row's port                               *)
(*   kim_biased_proximity_cert_epsE                                           *)
(*                           == the certificate's number is one fiftieth      *)
(*   kim_biased_proximity_eps_halfE                                           *)
(*                           == the exact input-indistinguishability          *)
(*                              certificate's number is twice the proximity   *)
(*                              certificate's                                 *)
(*   kim_biased_proximity_cert_eps_lt2                                        *)
(*                           == that number is under two, the bound           *)
(*                              var_dist_le2 gives                            *)
(*   five_card_row_biased_branch_indistinguishability_atE                     *)
(*                           == the branch and the program written out from   *)
(*                              the prefix hold one coordinate                *)
(*   five_card_row_biased_branch_indistinguishability_rowE                    *)
(*                           == the branch publishes the manifest's row for   *)
(*                              the one-cut path                              *)
(*   five_card_row_biased_proximity_rowE                                      *)
(*                           == the proximity row publishes that same row     *)
(*   five_card_row_biased_proximity_publishedE                                *)
(*                           == the three coordinates the proximity row       *)
(*                              publishes                                     *)
(*   five_card_row_biased_branch_indistinguishability_armE                    *)
(*                           == the branch carries the input-                 *)
(*                              indistinguishability arm                      *)
(*   five_card_row_biased_proximity_armE                                      *)
(*                           == the proximity row carries the proximity arm   *)
(*   five_card_biased_view_proximity                                          *)
(*                           == at a coalition of at most one of the five     *)
(*                              seats, the proximity row's security           *)
(*                              statement, at one fiftieth                    *)
(*   five_card_biased_view_own_marginals                                      *)
(*                           == the same at the same coalitions with the      *)
(*                              ideal removed, at three fiftieths             *)
(*   kim_biased_conclude_below_false                                          *)
(*                           == the conclude obligation at a number below the *)
(*                              certificate's own is false                    *)
(*   five_card_singleton_below_threshold                                      *)
(*                           == one seat is below the five-card privacy       *)
(*                              threshold                                     *)
(*   five_card_biased_proximity_prop_holds                                    *)
(*                           == the proximity arm's proposition at the number *)
(*                              the row publishes                             *)
(*   five_card_biased_indistinguishability_implies_proximity                  *)
(*                           == the input-indistinguishability proposition    *)
(*                              implies it, its premise discarded             *)
(******************************************************************************)

Require Import Lia.
From mathcomp Require Import zify.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import bigop order ssrnum ssralg reals boolp lra.
From infotheo Require Import realType_ext fdist proba variation_dist entropy.
From pgg_smc Require Import pgg_interface pgg_session_types.
From pgg_smc Require Import pgg_monodromy_profile pgg_execution_plug.
From pgg_smc Require Import pgg_observed_execution pgg_analysis_status.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgg_sample_adapter pgg_trace_secrecy.
From pgg_smc Require Import pgg_collusion_bound var_dist_supp.
From pgg_smc Require Import var_dist_joint_law.
From pgg_smc Require Import five_card_group five_card_program.
From pgg_smc Require Import five_card_kim five_card_family.
From pgg_smc Require Import den_boer_encoding den_boer_run.
From pgg_smc Require Import five_card_leakage five_card_exec five_card_models.
From pgg_smc Require Import kim_input_privacy.
From pgg_smc Require Import five_card_mixing.
From pgg_smc Require Import pgg_analysis_manifest.
From pgg_smc Require Import pgg_tableau pgg_tableau_syntax.
From pgg_smc Require Import five_card_proximity.
From pgg_smc Require Import five_card_tableau_observed.
From pgg_smc Require Import five_card_tableau_sampled.

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

(** The uniform row: the prefix five_card_committed, the uniform rotation
    model, the witness above, and the manifest row. Its last statement
    publishes a row whose transfer status is StaticExecutedOnly, because the
    cut this model draws is already the uniform one and no idealized shuffle
    is being compared with a real one. What the finished row carries about a
    coalition of fewer than two seats is independence of the conjunction, at
    every real field, with no numeric bound anywhere in it. *)
Definition five_card_row_uniform_tableau : PublishedRow :=
  five_card_committed
    sample  five_card_uniform_family
    certify ExactIndependence five_card_exact_witness
    |> publish StaticExecutedOnly BaselineClassicalOnly.

(** The uniform row continues the named uniform model. The program above
    writes the sample statement and the certify statement in one term and
    the Sampled file names the value between them, so this equation is what
    lets a statement made at five_card_uniform_sampled be read as a
    statement about the row. *)
Lemma five_card_row_uniform_sampledE :
  (five_card_uniform_sampled
     certify ExactIndependence five_card_exact_witness
     |> publish StaticExecutedOnly BaselineClassicalOnly)
  = five_card_row_uniform_tableau.
Proof. exact: erefl. Qed.

(** The row the program publishes is the manifest's own row for the five-card
    development under the uniform cut. Conversion decides it, so the
    descriptive row and the theorem proved about it cannot drift apart. *)
Lemma five_card_row_uniform_rowE :
  published_row five_card_row_uniform_tableau = five_card_row_uniform.
Proof. by []. Qed.

(** The arm this row carries, at every real field and index: independence of
    the coalition's view from the conjunction of the committed bits, and not a
    distance between two readings. This is the value a paper's table prints in
    the arm column for this row, settled by the certify statement the program
    wrote. *)
Lemma five_card_row_uniform_armE (R : realType)
    (idx : amf_index (ab_f (published_at five_card_row_uniform_tableau)) R) :
  security_arm_of five_card_row_uniform_tableau R idx = ExactIndependenceArm.
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
(*     Kim's two certificates                                                 *)
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


(******************************************************************************)
(*     Kim's two rows, certified against the uniform rotation law             *)
(******************************************************************************)

(** Kim's repeated row certified by the input-indistinguishability arm and
    published at IdealFinite. The status is a parameter of publish and
    nothing checks it, so it is claimed against the criterion
    pgg_analysis_status.v states for IdealFinite: a cut-carrier transfer
    whose base premise is discharged, which is what a certificate comparing a
    finite shuffle with a named ideal cut supplies. *)
Definition five_card_row_repeated_indistinguishability_tableau : PublishedRow :=
  five_card_committed
    sample kim_centi_family
    certify InputIndistinguishability kim_centi_cert
    |> publish IdealFinite BaselineClassicalOnly.

(** The repeated certified row continues the named repeated model, so the
    model a reader of the row meets and the model the Sampled file names are
    one name and not two spellings. *)
Lemma five_card_row_repeated_indistinguishability_sampledE :
  (five_card_row_repeated_tableau
     certify InputIndistinguishability kim_centi_cert
     |> publish IdealFinite BaselineClassicalOnly)
  = five_card_row_repeated_indistinguishability_tableau.
Proof. exact: erefl. Qed.

(** Kim's one-cut row certified by the same arm and published at the same
    transfer status. Its certificate has the shape the repeated row's has,
    over the same ideal cut and with the same constancy field, so the same
    status is the honest one for it. *)
Definition five_card_row_biased_indistinguishability_tableau : PublishedRow :=
  five_card_committed
    sample kim_biased_family
    certify InputIndistinguishability kim_biased_cert
    |> publish IdealFinite BaselineClassicalOnly.

(** The same for the one-cut row and the named one-cut model. *)
Lemma five_card_row_biased_indistinguishability_sampledE :
  (five_card_row_biased_tableau
     certify InputIndistinguishability kim_biased_cert
     |> publish IdealFinite BaselineClassicalOnly)
  = five_card_row_biased_indistinguishability_tableau.
Proof. exact: erefl. Qed.

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

(** The arm the repeated row's certified program carries, at every real field
    and index: a variation distance between the readings of the cut at two
    committed pairs, and not independence of the view from the conjunction of
    the committed bits. This is the value a paper's table prints in the arm
    column for this row, settled by the certify statement the program
    wrote. *)
Lemma five_card_row_repeated_indistinguishability_armE (R : realType)
    (idx : amf_index
             (ab_f (published_at
                      five_card_row_repeated_indistinguishability_tableau)) R) :
  security_arm_of five_card_row_repeated_indistinguishability_tableau R idx
  = InputIndistinguishabilityArm.
Proof. exact: erefl. Qed.

(** The arm the one-cut row's certified program carries. The two Kim rows
    publish different manifest rows, and a reader of the manifest alone could
    not tell which arm either committed to. *)
Lemma five_card_row_biased_indistinguishability_armE (R : realType)
    (idx : amf_index
             (ab_f (published_at
                      five_card_row_biased_indistinguishability_tableau)) R) :
  security_arm_of five_card_row_biased_indistinguishability_tableau R idx
  = InputIndistinguishabilityArm.
Proof. exact: erefl. Qed.

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


(******************************************************************************)
(*     The number each certificate publishes                                  *)
(******************************************************************************)

(** Two copies of two to the minus fortieth make two to the minus
    thirty-ninth. A certificate's cert_eps is its marginal bound's epsilon
    twice, once for each of the two committed pairs, and this identity puts
    the constant the repeated row publishes into that same shape, so the
    certificate's two spectral terms can be compared with it one at a
    time. *)
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
    row sees, before a terminal concludes the row at a constant. *)
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

(** The one-cut row's bound is under two, the bound var_dist_le2 gives for a
    variation distance. The row therefore rules out a coalition of at most
    one seat telling the two committed pairs apart with certainty, which a
    bound at two would not. At about three percent of that bound it is not a
    strong statement. *)
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
(*     The same two rows at the constants they publish                        *)
(******************************************************************************)

(** The name two to the minus thirty-ninth for a bound, at every real
    field. *)
Definition five_card_reprice39 : Reprice := fun R => Some (2%:R ^- 39 : R).

(** The repeated row concluded at that constant, continuing from the
    certificate at the bundle's own spectral number. The data, the model and
    the certificate are the same terms, and kim_centi_cert_eps_lt is strict,
    so the number the row publishes is strictly above the number the
    certificate proved and the row asserts about a coalition of at most one
    seat no more than that certificate did, at the number a reader cites. *)
(* The terminal's payload is kim_centi_cert_eps_lt weakened by ltW. *)
Definition five_card_row_repeated39 : PublishedRowAt five_card_reprice39 :=
  five_card_committed
    sample  kim_centi_family
    certify InputIndistinguishability kim_centi_cert
    |> conclude five_card_reprice39
       by (fun R idx => Order.POrderTheory.ltW (kim_centi_cert_eps_lt R idx))
    |> publish IdealFinite BaselineClassicalOnly.

(** The concluded repeated row continues the named repeated model as well,
    so the row at the constant a text quotes and the row at the
    certificate's own number read their model off one name. *)
Lemma five_card_row_repeated39_sampledE :
  (five_card_row_repeated_tableau
     certify InputIndistinguishability kim_centi_cert
     |> conclude five_card_reprice39
        by (fun R idx =>
              Order.POrderTheory.ltW (kim_centi_cert_eps_lt R idx))
     |> publish IdealFinite BaselineClassicalOnly)
  = five_card_row_repeated39.
Proof. exact: erefl. Qed.

(** The repeated row concluded at 2^-39 and the row at the bundle's own number
    accumulate one stack, so the constant a text cites and the expression the
    certificate proved are two readings of one security claim and not two
    claims a reader must reconcile. *)
(* reflexivity and not exact: erefl. Both close this goal by the kernel's
   conversion, and only reflexivity reaches it: the refine path ssreflect's
   erefl takes spent 147 s here against reflexivity's 0.07 s. Measured on
   2026-09-19; the numbers are in
   notes/probes/2026-09-19-tableau-extensions/STATUS.md, section F2. *)
Lemma five_card_row_repeated39_atE :
  published_at five_card_row_repeated39
  = published_at five_card_row_repeated_indistinguishability_tableau.
Proof. reflexivity. Qed.

(** The arm the concluded repeated row carries. Concluding at a number at or
    above the certificate's own leaves the port where the certify statement
    put it, so the row at 2^-39 and the row at the bundle's spectral number
    print one arm column. *)
Lemma five_card_row_repeated39_armE (R : realType)
    (idx : amf_index (ab_f (published_at five_card_row_repeated39)) R) :
  security_arm_of five_card_row_repeated39 R idx
  = InputIndistinguishabilityArm.
Proof. exact: erefl. Qed.

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
    that equates the sum of the one-cut row's two exact per-card-position
    numbers with the single constant that row publishes. *)
Fact five_card_inv50_split (R : realType) : (1 / 50 : R) + 1 / 50 = 1 / 25.
Proof. by lra. Qed.

(** The name one twenty-fifth for a bound, at every real field. *)
Definition five_card_reprice_inv25 : Reprice := fun R => Some (1 / 25 : R).

(** The one-cut row concluded at the exact constant, at the same transfer
    status as the row at the spectral number. The certificate it carries
    compares the same cut with the same ideal, so the number it publishes
    changes and the status it earns does not. It continues from the exact
    certificate and not from kim_biased_cert, because a row publishes a number
    at least its certificate's, and the bound kim_biased_cert publishes is
    twice the bundle's number, sqrt 5 over forty, which is above one
    twenty-fifth. *)
Definition five_card_row_biased_inv25
  : PublishedRowAt five_card_reprice_inv25 :=
  five_card_committed
    sample  kim_biased_family
    certify InputIndistinguishability kim_biased_cert_exact
    |> conclude five_card_reprice_inv25
       by (fun R _ => ssr_ext.eqW (five_card_inv50_split R))
    |> publish IdealFinite BaselineClassicalOnly.

(** The concluded one-cut row continues the named one-cut model. *)
Lemma five_card_row_biased_inv25_sampledE :
  (five_card_row_biased_tableau
     certify InputIndistinguishability kim_biased_cert_exact
     |> conclude five_card_reprice_inv25
        by (fun R _ => ssr_ext.eqW (five_card_inv50_split R))
     |> publish IdealFinite BaselineClassicalOnly)
  = five_card_row_biased_inv25.
Proof. exact: erefl. Qed.

(** The two one-cut programs publish one row, although their certificates
    carry different numbers, sqrt 5 over forty against one twenty-fifth. An
    AnalysisPathRow holds descriptive metadata and no Prop, so an equation
    between two published rows says nothing about either certificate, and in
    particular cannot say which transfer status is the honest one. *)
Lemma five_card_row_biased_forms_publishedE :
  published_row five_card_row_biased_indistinguishability_tableau
  = published_row five_card_row_biased_inv25.
Proof. exact: erefl. Qed.

(** The arm the concluded one-cut row carries. It carries the exact
    certificate where five_card_row_biased_indistinguishability_tableau
    carries the spectral one, so the two rows differ in the number they
    publish and not in what kind of fact they state about a coalition. *)
Lemma five_card_row_biased_inv25_armE (R : realType)
    (idx : amf_index (ab_f (published_at five_card_row_biased_inv25)) R) :
  security_arm_of five_card_row_biased_inv25 R idx
  = InputIndistinguishabilityArm.
Proof. exact: erefl. Qed.

(** One twenty-fifth is under two, the bound var_dist_le2 gives for a
    variation distance, so the concluded one-cut row is not vacuous. *)
Lemma five_card_reprice_inv25_lt2 (R : realType) : (1 / 25 : R) < 2%:R.
Proof. by lra. Qed.


(******************************************************************************)
(*     The proximity certificate, and its ideal                               *)
(******************************************************************************)

(** The proximity certificate of Kim's one-cut row. Its five fields are the
    den Boer uniform model as the ideal; that model's exact witness, which
    is what makes the ideal an execution whose coalitions learn nothing at
    all; the conjunction of the committed bits as the one-cut model's own
    secret; one fiftieth; and the distance above. The ideal and the witness
    are the terms the published uniform row carries, which
    kim_biased_proximity_cert_idealE states, and the secret is the same
    conjunction that row's witness is stated at. The number is the bound
    kim_biased_cut_mixing_exact proves on the cut group's own distance, and
    the last field is kim_biased_proximity_close of five_card_proximity.v,
    which says the distance between the two joint laws is at most that
    number. *)
Definition kim_biased_proximity_cert (R : realType) (idx : unit)
  : IdealProximityCert (amf_sample kim_biased_family R idx) :=
  @MkIdealProximityCert R five_card_algebra five_card_params
    (amf_sample kim_biased_family R idx)
    (amf_sample five_card_uniform_family R idx)
    (five_card_exact_witness R idx)
    (five_card_leakage.Secret R)
    (1 / 50)
    (fun C _ => @kim_biased_proximity_close R C).

(** The model the certificate calls ideal is the model the published uniform
    row carries, and the port built from the certificate's witness is that
    row's port. Conversion decides both, so the ideal a biased row is
    measured against is the uniform row's own model and not a second
    description of it. *)
Lemma kim_biased_proximity_cert_idealE (R : realType) (idx : unit) :
  ipc_ideal (kim_biased_proximity_cert R idx)
  = amf_sample (ab_f (published_at five_card_row_uniform_tableau)) R idx
  /\ ExactIndependence (ipc_witness (kim_biased_proximity_cert R idx))
     = ab_port (published_at five_card_row_uniform_tableau) R idx.
Proof. by split. Qed.


(******************************************************************************)
(*     The number                                                             *)
(******************************************************************************)

Section kim_biased_proximity_numbers.
Variable R : realType.

(** The certificate's number is one fiftieth, the variation distance
    kim_biased_cut_mixing_exact proves between Kim's one biased cut and the
    uniform rotation on the cut group. *)
Lemma kim_biased_proximity_cert_epsE (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx) = 1 / 50 :> R.
Proof. exact: erefl. Qed.

(** The number kim_biased_cert_exact carries at this model is twice the
    number kim_biased_proximity_cert carries. Both are read off
    kim_biased_cut_mixing_exact, the one distance on the cut group; the
    input-indistinguishability arm spends it once for each of the two
    committed pairs it compares and the proximity arm compares one law with
    one law. The relation is between these two certificates and not between
    the two arms: the same model also carries kim_biased_cert, whose marginal
    bound is sqrt 5 over eighty and which therefore publishes sqrt 5 over
    forty, so neither arm determines the number of the other. *)
Lemma kim_biased_proximity_eps_halfE (idx : unit) :
  cert_eps (kim_biased_cert_exact R idx)
  = ipc_eps (kim_biased_proximity_cert R idx)
    + ipc_eps (kim_biased_proximity_cert R idx).
Proof. exact: erefl. Qed.

(** The certificate's own number is under two, the bound var_dist_le2 gives
    for a variation distance, so the certificate is not vacuous. At one
    percent of that bound it is a weak separation and not a cryptographic
    one, as is kim_biased_cert_exact at one twenty-fifth. *)
Lemma kim_biased_proximity_cert_eps_lt2 (idx : unit) :
  ipc_eps (kim_biased_proximity_cert R idx) < 2%:R.
Proof. by rewrite kim_biased_proximity_cert_epsE; lra. Qed.

End kim_biased_proximity_numbers.


(******************************************************************************)
(*     One model, two claims, two rows                                        *)
(******************************************************************************)

(** Kim's one-cut model certified by the input-indistinguishability arm,
    continued from the named Sampled value rather than written out from the
    prefix. It is the sibling of the proximity row below: the two continue
    one term, so what separates them is the arm and nothing about the
    algebra, the run or the law. *)
Definition five_card_row_biased_branch_indistinguishability : PublishedRow :=
  five_card_row_biased_tableau
    certify InputIndistinguishability kim_biased_cert
    |> publish IdealFinite BaselineClassicalOnly.

(** The branch and the program written out from the prefix hold one
    AnalysisBridged coordinate, so naming the Sampled value costs the
    input-indistinguishability row nothing. *)
(* exact: erefl and not by [], because done does not return on an equation
   between two rows' coordinates. *)
Lemma five_card_row_biased_branch_indistinguishability_atE :
  published_at five_card_row_biased_branch_indistinguishability
  = published_at five_card_row_biased_indistinguishability_tableau.
Proof. exact: erefl. Qed.

(** The branch publishes the manifest's own row for the biased path. *)
Lemma five_card_row_biased_branch_indistinguishability_rowE :
  published_row five_card_row_biased_branch_indistinguishability
  = five_card_row_biased.
Proof. exact: erefl. Qed.

(** Kim's one-cut model certified by the proximity arm and published at its
    certificate's own number, one fiftieth. What a coalition of fewer than
    two seats is shown is that the joint law of its reading with the
    conjunction of the committed bits is within that number of the product of
    the two marginals the den Boer uniform execution has, where the reading
    and the conjunction are independent outright. The number is spent once,
    against the input-indistinguishability row's twice. Its transfer status is
    IdealFinite, the same the input-indistinguishability row carries, and the
    two certificates compare against the same ideal cut. *)
Definition five_card_row_biased_proximity : PublishedRow :=
  five_card_row_biased_tableau
    certify IdealProximity kim_biased_proximity_cert
    |> publish IdealFinite BaselineClassicalOnly.

(** The proximity row publishes the manifest's row for the biased path, as
    its input-indistinguishability sibling does. An AnalysisPathRow holds
    descriptive metadata and no Prop, so one manifest row carrying an
    input-indistinguishability row and a proximity row says nothing about
    either claim. *)
Lemma five_card_row_biased_proximity_rowE :
  published_row five_card_row_biased_proximity = five_card_row_biased.
Proof. exact: erefl. Qed.

(** The three coordinates the proximity row publishes. *)
Lemma five_card_row_biased_proximity_publishedE :
  apr_completion (published_row five_card_row_biased_proximity)
    = AnalysisBridged
  /\ apr_transfer (published_row five_card_row_biased_proximity) = IdealFinite
  /\ apr_assumptions (published_row five_card_row_biased_proximity)
     = BaselineClassicalOnly.
Proof. by []. Qed.

(** The arm the input-indistinguishability branch carries, at every real
    field and index. *)
Lemma five_card_row_biased_branch_indistinguishability_armE (R : realType)
    (idx : amf_index
             (ab_f (published_at
                      five_card_row_biased_branch_indistinguishability))
             R) :
  security_arm_of five_card_row_biased_branch_indistinguishability R idx
  = InputIndistinguishabilityArm.
Proof. by []. Qed.

(** The arm the proximity row carries, at every real field and index: the
    distance to a private ideal model, and not the distance between two
    readings of one model. *)
Lemma five_card_row_biased_proximity_armE (R : realType)
    (idx : amf_index (ab_f (published_at five_card_row_biased_proximity)) R) :
  security_arm_of five_card_row_biased_proximity R idx = IdealProximityArm.
Proof. by []. Qed.


(******************************************************************************)
(*     What the proximity row states at this instance                         *)
(******************************************************************************)

(** The proximity row's security statement at the five-card instance: at fewer
    than two colluding seats, the joint law of the coalition's executed
    reading and the conjunction of the committed bits under Kim's one biased
    cut is within one fiftieth of the product of the two marginals of the den
    Boer uniform execution. The proof is the row's security projection
    applied, so the row and this statement are one theorem. *)
Theorem five_card_biased_view_proximity (R : realType) (C : {set 'I_5})
    (HC : (#|C| < 2)%N) :
  var_dist
    (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                           five_card_exec_plug
                           (amf_sample kim_biased_family R tt) 0 C u,
                         five_card_leakage.Secret R u))
       (sa_sampleP (amf_sample kim_biased_family R tt)))
    ((fdistmap (@sa_coalition_view R five_card_profile five_card_exec_plug
                  (five_card_sample R) 0 C) (P R))
     `x (fdistmap (five_card_leakage.Secret R) (P R)))
  <= 1 / 50.
Proof. exact: (view_proximity_of five_card_row_biased_proximity R tt C HC). Qed.

(** The one-cut row's bound restated against the executed law's own two
    marginals: at fewer than two colluding seats, the joint law of the
    coalition's reading with the conjunction of the committed bits is within
    three fiftieths of the product of that same law's two marginals. The den
    Boer uniform model has left the statement. What remains is a bound on how
    far the one-cut run is from making a coalition's reading and the secret
    independent, and the advantage a distinguisher gets from it is at most
    three hundredths. *)
Theorem five_card_biased_view_own_marginals (R : realType) (C : {set 'I_5})
    (HC : (#|C| < 2)%N) :
  var_dist
    (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                           five_card_exec_plug
                           (amf_sample kim_biased_family R tt) 0 C u,
                         five_card_leakage.Secret R u))
       (sa_sampleP (amf_sample kim_biased_family R tt)))
    ((fdistmap fst
        (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                               five_card_exec_plug
                               (amf_sample kim_biased_family R tt) 0 C u,
                             five_card_leakage.Secret R u))
           (sa_sampleP (amf_sample kim_biased_family R tt))))
     `x (fdistmap snd
           (fdistmap (fun u => (@sa_coalition_view R five_card_profile
                                  five_card_exec_plug
                                  (amf_sample kim_biased_family R tt) 0 C u,
                                five_card_leakage.Secret R u))
              (sa_sampleP (amf_sample kim_biased_family R tt)))))
  <= 3%:R * (1 / 50).
Proof.
exact: (var_dist_own_marginals (@five_card_biased_view_proximity R C HC)).
Qed.


(******************************************************************************)
(*     A number below the certificate's is refused                            *)
(******************************************************************************)

(** The name one hundredth, half of what Kim's one-cut proximity certificate
    proves. *)
Definition five_card_reprice_inv100 : Reprice := fun R => Some (1 / 100 : R).

(** The obligation conclude asks of a terminal that would republish Kim's
    one-cut proximity row at one hundredth is false, and not merely beyond
    what could be proved: one fiftieth is not at most one hundredth. A
    published number may therefore be moved upward and never downward, and
    that is decided by the ordering ConcludePayload states and not by which
    tactic a terminal reaches for. *)
Lemma kim_biased_conclude_below_false (R : realType) (idx : unit) :
  ~ (ipc_eps (kim_biased_proximity_cert R idx)
     <= odflt (ipc_eps (kim_biased_proximity_cert R idx))
          (five_card_reprice_inv100 R)).
Proof. rewrite kim_biased_proximity_cert_epsE /= => H; lra. Qed.


(******************************************************************************)
(*     Every hypothesis discharged at one concrete coalition                  *)
(******************************************************************************)

(** One seat is below the five-card privacy threshold. *)
Fact five_card_singleton_below_threshold (i : 'I_5) :
  (#|[set i]| < profile_k (instance_profile five_card_algebra))%N.
Proof. by rewrite cards1. Qed.

(** Kim's one-cut row's claim with every hypothesis discharged: one real
    field, one coalition of one named seat, and the threshold condition proved
    rather than assumed. The coalition is not empty, so the reading the bound
    is stated on is the seat's own content observation at that seat, where the
    empty coalition's reading is ord0 at every seat. *)
Definition five_card_biased_proximity_at_singleton (R : realType) (i : 'I_5) :=
  @five_card_biased_view_proximity R [set i]
    (five_card_singleton_below_threshold i).


(******************************************************************************)
(*     The proximity proposition at this instance, and what implies it        *)
(******************************************************************************)

(** The proximity proposition of Kim's one-cut row at the number that row
    publishes, taken off the published row itself. It is the arm's conclusion
    standing on its own at this instance. *)
Lemma five_card_biased_proximity_prop_holds (R : realType) :
  IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 50).
Proof. exact: (view_proximity_of five_card_row_biased_proximity R tt). Qed.

(** The input-indistinguishability proposition implies the proximity
    proposition at the five-card instance, at every constant the
    input-indistinguishability premise is stated at, because the conclusion
    is a theorem there and the premise is discarded. The implication holds
    and carries no information: a derivation that reads the
    input-indistinguishability certificate's fields is a different statement
    and is not this one. *)
Lemma five_card_biased_indistinguishability_implies_proximity
    (R : realType) (c : R) :
  IndistinguishabilityPropAt (kim_biased_cert R tt) c ->
  IdealProximityPropAt (kim_biased_proximity_cert R tt) (1 / 50).
Proof. by move=> _; exact: five_card_biased_proximity_prop_holds. Qed.
