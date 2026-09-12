(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* pgg_analysis_manifest: the repository-level analysis manifest              *)
(*                                                                            *)
(* The manifest re-exports the three instance facades, so that one import     *)
(* reaches every public alias of the eight-card orbit instance, the five-card *)
(* development of den Boer and Kim and the five-seat S_5 instance, and        *)
(* records one row per analysis path. Each row names its protocol instance,   *)
(* probability model, profile, execution, observed-execution and sample       *)
(* aliases, its observers with their carriers, its correctness theorem, its   *)
(* security, leakage, mixing or limitation theorem, its static-to-executed    *)
(* bridge and model-transfer theorem when present, the missing model-transfer *)
(* premise when none is claimed, its exact capability, its completion level   *)
(* and its assumption status.                                                 *)
(*                                                                            *)
(* Each row is also a typed value of AnalysisPathRow below, carrying the      *)
(* observed execution of the path, its typed model slot apr_model, an         *)
(* AnalysisModelFamily witness mandatory at Sampled and AnalysisBridged and   *)
(* optional below, and the three typed statuses of pgg_analysis_status.v.     *)
(* The record stores no theorem: theorems stay facade aliases and are pinned  *)
(* by spelled type in the checker at the end of this file.                    *)
(*                                                                            *)
(* Completion levels are the constructors of CompletionLevel. They are        *)
(* cumulative and are read off the typed witnesses this manifest names, never *)
(* asserted:                                                                  *)
(*                                                                            *)
(*   Algebraic       profile alias                                            *)
(*   Executable      + execution-plug alias indexed by that profile           *)
(*   Observed        + observed-execution alias indexed by profile and plug   *)
(*   Sampled         + sample-adapter alias AND its distribution-to-observer  *)
(*                    bridge                                                  *)
(*   AnalysisBridged + bridge alias to a named security, leakage, mixing or   *)
(*                    limitation theorem about the same distribution and the  *)
(*                    same observer                                           *)
(*                                                                            *)
(* AnalysisBridged is the typed form of the prose label Security-bridged of   *)
(* the earlier banner. The neutral name is what lets a row classify           *)
(* accurately when its bridged theorem is an endpoint marginal mixing bound   *)
(* and not a privacy claim, as on the S_5 finite-word path.                   *)
(*                                                                            *)
(* Three conventions hold throughout the rows.                                *)
(*                                                                            *)
(* (1) The classical trio propositional_extensionality,                       *)
(* functional_extensionality_dep and constructive_indefinite_description is   *)
(* the repository baseline, inherited from boolp through the infotheo         *)
(* probability layer. It is NOT listed in an assumption status. A row is      *)
(* BaselineClassicalOnly when Print Assumptions reports the trio and        *)
(* nothing else, and                                                          *)
(* AcceptsAxioms when it reports named repository assumptions beyond it. The  *)
(* three constructors of PggAxiom are the only such assumptions, and a status *)
(* covers the public results of the path, not only the values the row stores. *)
(*                                                                            *)
(* (2) Completion levels are cumulative and are stated at the level the       *)
(* theorems actually reach. The S_5 word row is AnalysisBridged: its executed *)
(* theorem is stated at sa_seat_dist of the interpreter-executed finite-word  *)
(* adapter, against the encoder-image ideal, next to the kept cut-level       *)
(* result at the card position's endpoint reader of the word-cut              *)
(* distribution.                                                              *)
(*                                                                            *)
(* (3) A capability line uses the narrowest label the theorem statement       *)
(* supports, from the closed vocabulary correctness, exact privacy,           *)
(* approximate privacy, trace secrecy, conditional entropy, mutual            *)
(* information or endpoint marginal mixing. A theorem conditional on the      *)
(* trusted analytical certificate s5_rayleigh_Q2_R is described as            *)
(* conditional in every capability line that depends on it.                   *)
(*                                                                            *)
(* Every identifier in the tables below is checked at the end of this file by *)
(* one Timeout-guarded Check against its spelled type, and every row by one   *)
(* Check against AnalysisPathRow together with three erefl pins on its status *)
(* fields. Deleting an alias makes its line fail with a reference-not-found   *)
(* message, retyping one makes it fail with a type mismatch and restatusing a *)
(* row makes its pin fail, so the tables cannot drift away from the code.     *)
(******************************************************************************)

From pgg_smc Require Export pgl27_analysis five_card_analysis s5_analysis.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory Num.Theory.

Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope ring_scope.

(******************************************************************************)
(*     Row 1: eight-card orbit instance, exact uniform shuffle                *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol family and model | PGL(2,7) orbit deck, exact uniform cut |     *)
(* | profile alias      | PGL27Analysis.profile |                             *)
(* | execution alias    | PGL27Analysis.exec_plug |                           *)
(* | observed alias     | PGL27Analysis.observed |                            *)
(* | sample alias       | PGL27Analysis.exact_sample,                         *)
(*                        PGL27Analysis.fixed_exact_sample |                  *)
(* | observers          | PGL27Analysis.coalition_endpoints                   *)
(*                          : {ffun 'I_8 -> 'I_8}, executed;                  *)
(*                        PGL27Analysis.content_trace                         *)
(*                          : {ffun 'I_8 -> 'I_8}, executed;                  *)
(*                        PGL27Analysis.static_view                           *)
(*                          : {ffun 'I_8 -> 'I_8}, random variable on prior;  *)
(*                        PGL27Analysis.coalition_trace                       *)
(*                          : {ffun 'I_8 -> 'I_8}, random variable on prior;  *)
(*                        PGL27Analysis.secret : bool |                       *)
(* | distribution-to-observer bridges | PGL27Analysis.sample_cut_distE,       *)
(*                        PGL27Analysis.fixed_cut_distE,                      *)
(*                        PGL27Analysis.exact_coalition_distE,                *)
(*                        PGL27Analysis.content_traceE |                      *)
(* | bound or certificate | PGL27Analysis.marginal_bound,                     *)
(*                          PGL27Analysis.certificate_bundle |                *)
(* | final bridge theorem | PGL27Analysis.exact_view_indep |                  *)
(* | correctness theorem  | PGL27Analysis.observed_recovers |                 *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | none: the path compares no idealized model, its   *)
(*                          shuffle being the exact uniform distribution on   *)
(*                          the group already |                               *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | StaticExecutedOnly |                              *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed row            | pgl27_row_exact |                                 *)
(*                                                                            *)
(* Capabilities, one line per (theorem, distribution, observer, notion):      *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | exact_view_indep | prior R, the distribution of exact_sample             *)
(*   | coalition_endpoints, through exact_coalition_distE | exact privacy |   *)
(* | coalition_trace_secrecy | prior R                                        *)
(*   | coalition_trace, linked to content_trace by content_traceE             *)
(*   | conditional entropy |                                                  *)
(* | observed_recovers | none, the statement is distribution-free             *)
(*   | the executed endpoint list | correctness |                             *)
(*                                                                            *)
(* Level justification. profile gives Algebraic; exec_plug is indexed by      *)
(* profile, giving Executable; observed is the ObservedExecution over that    *)
(* profile and plug, giving Observed; exact_sample is a SampleAdapter over    *)
(* that plug and exact_coalition_distE identifies its executed coalition      *)
(* distribution with the pushforward of prior along static_view, giving       *)
(* Sampled; exact_view_indep is a security theorem whose right-hand side      *)
(* names sa_coalition_dist (exact_sample R) 0 C itself, so the theorem, the   *)
(* distribution and the observer are this row's own, giving                   *)
(* AnalysisBridged.                                                           *)
(*                                                                            *)
(*     Row 2: eight-card orbit instance, finite two-hundred-letter word       *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol family and model | PGL(2,7) orbit deck, word shuffle at         *)
(*                               length 200 |                                 *)
(* | profile alias      | PGL27Analysis.profile |                             *)
(* | execution alias    | PGL27Analysis.exec_plug |                           *)
(* | observed alias     | PGL27Analysis.observed |                            *)
(* | sample alias       | PGL27Analysis.word_sample at an arbitrary secret    *)
(*                        prior, PGL27Analysis.fixed_word_sample at a fixed   *)
(*                        secret |                                            *)
(* | observers          | PGL27Analysis.coalition_endpoints                   *)
(*                          : {ffun 'I_8 -> 'I_8}, executed;                  *)
(*                        PGL27Analysis.content_trace                         *)
(*                          : {ffun 'I_8 -> 'I_8}, executed;                  *)
(*                        PGL27Analysis.static_view,                          *)
(*                        PGL27Analysis.coalition_trace                       *)
(*                          : {ffun 'I_8 -> 'I_8};                            *)
(*                        PGL27Analysis.secret : bool |                       *)
(* | distribution-to-observer bridges | PGL27Analysis.word_cut_distE,         *)
(*                        PGL27Analysis.fixed_word_cut_distE,                 *)
(*                        PGL27Analysis.fixed_word_coalition_distE,           *)
(*                        PGL27Analysis.fixed_word_content_trace_distE,       *)
(*                        PGL27Analysis.word_joint_viewE,                     *)
(*                        PGL27Analysis.word_sample_joint_distE |             *)
(* | bound or certificate | PGL27Analysis.word_mixing, the 2^-40 distance of  *)
(*                          the word shuffle from uniform |                   *)
(* | final bridge theorem | PGL27Analysis.exec_view_indist,                   *)
(*                          PGL27Analysis.exec_trace_indist,                  *)
(*                          PGL27Analysis.word_view_indist_via_transfer |     *)
(* | correctness theorem  | PGL27Analysis.observed_recovers |                 *)
(* | model transfer       | PGL27Analysis.var_dist_transfer, discharged at    *)
(*                          this instance by                                  *)
(*                          PGL27Analysis.word_view_indist_via_transfer |     *)
(* | missing premise      | none: PGL27Analysis.word_mixing supplies the      *)
(*                          base-distribution bound the generic transfer      *)
(*                          inequality needs, on the cut carrier itself |     *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | IdealFinite |                                     *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed row            | pgl27_row_word |                                  *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | exec_view_indist | rho_word, the cut distribution of fixed_word_sample   *)
(*   by fixed_word_cut_distE | coalition_endpoints, executed, through         *)
(*   fixed_word_coalition_distE | approximate privacy at 2^-39 |              *)
(* | exec_trace_indist | rho_word | content_trace, executed, through          *)
(*   fixed_word_content_trace_distE | approximate privacy at 2^-39 |          *)
(* | word_view_indist | rho_word | static_view                                *)
(*   | approximate privacy at 2^-39 |                                         *)
(* | word_trace_indist | rho_word | coalition_trace                           *)
(*   | approximate privacy at 2^-39 |                                         *)
(* | view_mixing | pgl27P_word_gen secretP, the joint distribution of         *)
(*   word_sample by word_sample_joint_distE | the pair of static_view and     *)
(*   secret | approximate privacy at 2^-40 |                                  *)
(* | word_view_indist_via_transfer | rho_word | static_view                   *)
(*   | approximate privacy at 2^-39, derived from var_dist_transfer and       *)
(*     word_mixing |                                                          *)
(*                                                                            *)
(* Level justification. The first three levels are witnessed by the same      *)
(* three aliases as row 1. fixed_word_sample is a SampleAdapter over that     *)
(* plug and fixed_word_coalition_distE identifies its executed coalition      *)
(* distribution with the pushforward of rho_word along static_view, giving    *)
(* Sampled. exec_view_indist and exec_trace_indist are stated directly at     *)
(* that sample layer, at the executed coalition observation and at the        *)
(* executed content reader, giving AnalysisBridged at both executed           *)
(* observers rather than at the static layer alone.                           *)
(*                                                                            *)
(*     Row 3: five-card development, uniform cut (den Boer)                   *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol family and model | five-card AND evaluation, uniform rotation   *)
(*                               cut |                                        *)
(* | profile alias      | FiveCardAnalysis.profile, and the same program      *)
(*                        under FiveCardAnalysis.den_boer_profile |           *)
(* | execution alias    | FiveCardAnalysis.exec_plug |                        *)
(* | observed alias     | FiveCardAnalysis.observed, and the same value under *)
(*                        FiveCardAnalysis.den_boer_observed |                *)
(* | sample alias       | FiveCardAnalysis.uniform_sample |                   *)
(* | observers          | FiveCardAnalysis.content_trace : 'I_5, executed;    *)
(*                        FiveCardAnalysis.dealer_trace : bool * bool,        *)
(*                          executed;                                         *)
(*                        FiveCardAnalysis.input_trace : 'I_5, executed;      *)
(*                        FiveCardAnalysis.verifier_endpoints                 *)
(*                          : seq 'I_5;                                       *)
(*                        FiveCardAnalysis.secret : bool |                    *)
(* | distribution-to-observer bridges | FiveCardAnalysis.sample_cut_distE,    *)
(*                        FiveCardAnalysis.sample_cut_witnessE,               *)
(*                        FiveCardAnalysis.witness_rotationE |                *)
(* | bound or certificate | FiveCardAnalysis.marginal_bound,                  *)
(*                          FiveCardAnalysis.perfect |                        *)
(* | final bridge theorem | FiveCardAnalysis.exec_trace_secrecy |             *)
(* | correctness theorem  | FiveCardAnalysis.observed_recovers |              *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | the ideal distribution equality: the second       *)
(*                          hypothesis of var_dist_fdistmap_transfer, an      *)
(*                          equality of two reader pushforwards under an      *)
(*                          ideal distribution, which the five-card           *)
(*                          development does not supply |                     *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | StaticExecutedOnly |                              *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed row            | five_card_row_uniform |                           *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | exec_trace_secrecy | prior R, the distribution of uniform_sample         *)
(*   | content_trace R ord0, executed | trace privacy |                       *)
(* | dealer_trace_centropy0 | prior R | dealer_trace, executed                *)
(*   | conditional entropy |                                                  *)
(* | dealer_pair_centropy0 | prior R | dealer_trace, executed                 *)
(*   | conditional entropy |                                                  *)
(* | input_trace_secrecy | prior R | input_trace, executed                    *)
(*   | conditional entropy (constant conditioning) |                          *)
(* | observed_recovers | none, the statement is distribution-free             *)
(*   | verifier_endpoints | correctness |                                     *)
(*                                                                            *)
(* Level justification, stated explicitly because this row is the one whose   *)
(* level depends on an identity rather than on a named bridge lemma.          *)
(* uniform_sample is the sample adapter whose carrier is the den Boer sample  *)
(* space, whose distribution is prior R, whose argument map is the first      *)
(* projection and whose cut map is the rotation fc_sigma ^+ k of the second.  *)
(* content_trace R ord0 is a random variable on that same prior R whose value *)
(* is the content of the executed seat row at exactly that argument and that  *)
(* cut. exec_trace_secrecy is stated at that random variable. So the          *)
(* theorem's distribution is the row's sample distribution, its observer is   *)
(* an aliased executed observer of the row, and sample_cut_distE names the    *)
(* row's cut distribution; the row is AnalysisBridged with the trace          *)
(* privacy capability. input_trace_secrecy is NOT counted towards that level: *)
(* the input rows of the executed trace are empty, so its conditioning        *)
(* variable is constant and it is recorded as conditional entropy under       *)
(* constant conditioning, an architecture statement rather than a privacy     *)
(* bound.                                                                     *)
(*                                                                            *)
(*     Row 4: five-card development, single biased cut                        *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol family and model | five-card AND evaluation, one biased cut at  *)
(*                               Kim's input distribution |                   *)
(* | profile alias      | FiveCardAnalysis.profile |                          *)
(* | execution alias    | FiveCardAnalysis.exec_plug |                        *)
(* | observed alias     | FiveCardAnalysis.observed |                         *)
(* | sample alias       | FiveCardAnalysis.single_biased_sample |             *)
(* | observers          | FiveCardAnalysis.colour_view                        *)
(*                          : (size A).-tuple bool, the decoded colour        *)
(*                            sequence at a list A of seat indices into the   *)
(*                            endpoint list |                                 *)
(* | distribution-to-observer bridges | FiveCardAnalysis.single_cut_distE,    *)
(*                        FiveCardAnalysis.colour_viewE,                      *)
(*                        FiveCardAnalysis.colour_view_RV_E |                 *)
(* | bound or certificate | none; kim_leak_bound is the numeric constant of   *)
(*                          the bridge theorem, not a shuffle certificate |   *)
(* | final bridge theorem | FiveCardAnalysis.colour_view_leak_bound |         *)
(* | correctness theorem  | FiveCardAnalysis.observed_recovers |              *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | the ideal distribution equality, as in row 3 |    *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | StaticExecutedOnly |                              *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed row            | five_card_row_biased |                            *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | colour_view_leak_bound | kim_input_dist eps_lt_inv5 eps_gt_neg4inv5,     *)
(*   the distribution of single_biased_sample | colour_view A, executed       *)
(*   | mutual information, at most kim_leak_bound eps |                       *)
(*                                                                            *)
(* Hypotheses of that capability: eps_lt_inv5, eps_gt_neg4inv5 and the        *)
(* small-bias hypothesis eps_small : 0 < 5^-1 - `|eps|. All three are         *)
(* explicit arguments of the aliased theorem; none is discharged silently.    *)
(*                                                                            *)
(* Level justification. single_biased_sample is the sample adapter with the   *)
(* same carrier and the same argument and cut maps as uniform_sample and with *)
(* Kim's biased distribution, and single_cut_distE identifies its cut         *)
(* distribution with the biased rotation, giving Sampled.                     *)
(* colour_view_leak_bound bounds a conditional mutual information of a joint  *)
(* distribution whose middle component is the executed reader colour_view     *)
(* itself, over that same biased distribution, giving AnalysisBridged.        *)
(*                                                                            *)
(*     Row 5: five-card development, repeated biased cuts and seven cuts      *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol family and model | five-card AND evaluation, L repeated biased  *)
(*                               cuts, and its seven-cut member at bias one   *)
(*                               hundredth |                                  *)
(* | profile alias      | FiveCardAnalysis.profile |                          *)
(* | execution alias    | FiveCardAnalysis.exec_plug |                        *)
(* | observed alias     | FiveCardAnalysis.observed |                         *)
(* | sample alias       | FiveCardAnalysis.repeated_sample,                   *)
(*                        FiveCardAnalysis.centi_sample |                     *)
(* | observers          | one seat's endpoint distribution, reached through   *)
(*                        FiveCardAnalysis.repeated_seat_distE and            *)
(*                        FiveCardAnalysis.centi_repeated_seat_distE;         *)
(*                        FiveCardAnalysis.verifier_endpoints : seq 'I_5 |    *)
(* | distribution-to-observer bridges | FiveCardAnalysis.repeated_cut_distE,  *)
(*                        FiveCardAnalysis.centi_cut_distE,                   *)
(*                        FiveCardAnalysis.centi_witness_rhoE,                *)
(*                        FiveCardAnalysis.repeated_seat_distE,               *)
(*                        FiveCardAnalysis.centi_repeated_seat_distE |        *)
(* | bound or certificate | FiveCardAnalysis.kim_bundle,                      *)
(*                          FiveCardAnalysis.centi_bundle,                    *)
(*                          FiveCardAnalysis.endpoint_bound,                  *)
(*                          FiveCardAnalysis.deal_centi_lt |                  *)
(* | final bridge theorem | NONE |                                            *)
(* | correctness theorem  | FiveCardAnalysis.observed_recovers |              *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | the ideal distribution equality, as in row 3, and *)
(*                          in addition no security statement is attached to  *)
(*                          either model |                                    *)
(* | completion level     | Sampled |                                         *)
(* | transfer status      | NoModelComparison |                               *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed row            | five_card_row_repeated |                          *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | endpoint_bound | the weighted word shuffle at word length L              *)
(*   | one seat's endpoint distribution | endpoint marginal bound |           *)
(* | deal_centi_lt | the cut distribution of centi_sample, by                 *)
(*   centi_cut_distE | one seat's endpoint distribution                       *)
(*   | endpoint marginal bound |                                              *)
(*                                                                            *)
(* Level justification. Both models are sample adapters over the plug and     *)
(* both cut distributions are named, giving Sampled. The row is NOT           *)
(* AnalysisBridged. endpoint_bound and deal_centi_lt bound the distance       *)
(* from uniform of ONE seat's endpoint distribution: neither quantifies over  *)
(* a coalition, neither mentions a second secret, and neither has the shape   *)
(* of an indistinguishability or leakage statement. A ShuffleCertificate-     *)
(* Bundle exists for both models and does not raise the level.                *)
(*                                                                            *)
(*     Row 6: five-seat S_5 instance, deterministic dealt position            *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol instance    | five-seat S_5 path-generated instance |           *)
(* | probability model    | none: the path is distribution-free |             *)
(* | profile alias        | S5Analysis.profile |                              *)
(* | execution alias      | S5Analysis.exec_plug |                            *)
(* | observed alias       | S5Analysis.observed |                             *)
(* | sample alias         | none |                                            *)
(* | observers            | S5Analysis.seat_endpoint : 'I_5, executed;        *)
(*                          S5Analysis.coalition_endpoints                    *)
(*                            : {ffun 'I_5 -> 'I_5}, executed;                *)
(*                          S5Analysis.verifier_endpoints : seq 'I_5,         *)
(*                            executed;                                       *)
(*                          S5Analysis.verifier_trace,                        *)
(*                          S5Analysis.player_raw_trace : message lists,      *)
(*                            navigation only, not random variables |         *)
(* | distribution-to-observer bridges | none: the path has no sample layer |  *)
(* | bound or certificate | none |                                            *)
(* | correctness theorem  | S5Analysis.exec_correct, S5Analysis.exec_recovers,*)
(*                          S5Analysis.observed_recovers |                    *)
(* | security, leakage, mixing or limitation theorem | none |                 *)
(* | final bridge theorem | NONE |                                            *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | not applicable: the path names no model, so there *)
(*                          is no distribution to compare with an idealized   *)
(*                          one |                                             *)
(* | completion level     | Observed |                                        *)
(* | transfer status      | NoModelComparison |                               *)
(* | assumption status    | AcceptsAxioms [:: AxS5GroupOrder] |               *)
(* | typed row            | s5_row_det |                                      *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | observed_recovers | none, the statement is distribution-free             *)
(*   | the executed endpoint list | correctness |                             *)
(*                                                                            *)
(* Level justification. profile gives Algebraic; exec_plug is indexed by that *)
(* profile, giving Executable; observed is the ObservedExecution over that    *)
(* profile and plug, giving Observed. No sample adapter stands over this      *)
(* plug, so the row stops at Observed with an empty optional model slot. The  *)
(* assumption status is the group-order assumption of the instance:           *)
(* Print Assumptions on the row reports s5_group_order_eq beyond the          *)
(* classical trio, because the profile's threshold data is proved from the    *)
(* order of the generated group.                                              *)
(*                                                                            *)
(*     Row 7: five-seat S_5 instance, randomized additive sharing             *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol instance    | five-seat S_5 path-generated instance |           *)
(* | probability model    | uniform independent tape 'rV['Z_5]_5 with the     *)
(*                          identity cut |                                    *)
(* | profile alias        | S5Analysis.profile |                              *)
(* | execution alias      | S5Analysis.rand_exec_plug |                       *)
(* | observed alias       | S5Analysis.rand_observed |                        *)
(* | sample alias         | S5Analysis.rand_sample |                          *)
(* | observers            | S5Analysis.rand_content_trace R i : 'I_5, a       *)
(*                            random variable on the tape distribution,       *)
(*                            executed;                                       *)
(*                          sa_coalition_view of rand_sample at offset zero   *)
(*                            : {ffun 'I_5 -> 'I_5}, executed;                *)
(*                          S5Analysis.rand_seat_endpoint : 'I_5, executed;   *)
(*                          S5Analysis.rand_verifier_endpoints : seq 'I_5;    *)
(*                          the secret is rsh_secret of the randomized        *)
(*                            sharing, carrier 'Z_5 |                         *)
(* | distribution-to-observer bridges | S5Analysis.rand_cut_distE,            *)
(*                          S5Analysis.rand_content_traceE,                   *)
(*                          S5Analysis.rand_coalition_viewE |                 *)
(* | bound or certificate | none |                                            *)
(* | correctness theorem  | S5Analysis.rand_correct,                          *)
(*                          S5Analysis.rand_recovers,                         *)
(*                          S5Analysis.rand_observed_recovers |               *)
(* | security, leakage, mixing or limitation theorem                          *)
(*                        | S5Analysis.exec_trace_secrecy,                    *)
(*                          S5Analysis.exec_coalition_secrecy |               *)
(* | final bridge theorem | S5Analysis.exec_coalition_secrecy |               *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | none is needed: the path states exact results at  *)
(*                          its own executed observers and compares no        *)
(*                          idealized model |                                 *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | StaticExecutedOnly |                              *)
(* | assumption status    | AcceptsAxioms [:: AxS5GroupOrder] |               *)
(* | typed row            | s5_row_rand |                                     *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | exec_coalition_secrecy | the uniform tape distribution of rand_sample    *)
(*   | sa_coalition_view of rand_sample at offset zero, executed              *)
(*   | exact privacy: zero mutual information, and conditional entropy equal  *)
(*     to entropy, for a coalition of fewer than five seats |                 *)
(* | exec_trace_secrecy | the same distribution                               *)
(*   | rand_content_trace R i, executed | trace secrecy |                     *)
(* | rand_observed_recovers | none, the statement is distribution-free        *)
(*   | the executed endpoint list | correctness |                             *)
(*                                                                            *)
(* Level justification. profile, rand_exec_plug and rand_observed give the    *)
(* first three levels. rand_sample is a SampleAdapter over rand_exec_plug and *)
(* rand_cut_distE names its cut distribution, giving Sampled.                 *)
(* exec_coalition_secrecy is stated at sa_coalition_view of rand_sample       *)
(* itself, so the theorem's distribution and observer are the row's own,      *)
(* giving AnalysisBridged. The two reader equalities rand_content_traceE and  *)
(* rand_coalition_viewE identify those executed observers with the static     *)
(* readers of s5_trace and s5_secrecy, which is the content of the            *)
(* StaticExecutedOnly status:                                                 *)
(* results travel from the static layer to the executed one, and no           *)
(* idealized model is compared.                                               *)
(*                                                                            *)
(*     Row 8: five-seat S_5 instance, finite generator word                   *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol instance    | five-seat S_5 path-generated instance |           *)
(* | probability model    | the product of an arbitrary secret prior with the *)
(*                          uniform distribution on generator words of length *)
(*                          L, the cut being the word's evaluation in S_5 |   *)
(* | profile alias        | S5Analysis.profile |                              *)
(* | execution alias      | S5Analysis.exec_plug |                            *)
(* | observed alias       | S5Analysis.observed |                             *)
(* | sample alias         | S5Analysis.word_sample at a secret prior and a    *)
(*                          word length; the row's typed model witness is     *)
(*                          S5Analysis.word_family, the family indexed by     *)
(*                          exactly that prior and that length |              *)
(* | observers            | one position's endpoint distribution (cut level,  *)
(*                          a pushforward of the cut distribution, carrier    *)
(*                          'I_5), and one seat's executed reading            *)
(*                          sa_seat_dist of the interpreter-executed adapter, *)
(*                          compared with the encoder-image ideal             *)
(*                          S5Analysis.ideal_reading |                        *)
(* | distribution-to-observer bridges | S5Analysis.word_cut_distE,            *)
(*                          S5Analysis.word_cut_imageE |                      *)
(* | bound or certificate | S5Analysis.word_endpoint_bound (cut level) and    *)
(*                          S5Analysis.exec_endpoint_bound (executed, against *)
(*                          the encoder-image ideal) |                        *)
(* | correctness theorem  | S5Analysis.observed_recovers, shared with row 6:  *)
(*                          the model stands over the same plug |             *)
(* | security, leakage, mixing or limitation theorem                          *)
(*                        | S5Analysis.exec_endpoint_bound, endpoint marginal *)
(*                          mixing at the executed observer |                 *)
(* | final bridge theorem | S5Analysis.exec_endpoint_bound |                  *)
(* | model transfer       | observer-level: S5Analysis.exec_endpoint_bound    *)
(*                          transfers the executed reading to the             *)
(*                          encoder-image ideal on the endpoint carrier       *)
(*                          'I_5; S5Analysis.word_transfer_conditional stays  *)
(*                          the generic cut-carrier inequality under the      *)
(*                          premise below |                                   *)
(* | missing premise      | S5Analysis.word_missing_premise: a bound          *)
(*                          var_dist (sa_cut_dist (word_sample secretP L)) Q  *)
(*                          <= delta on the cut carrier {perm 'I_5}, against  *)
(*                          a named reference distribution Q. The transfer of *)
(*                          this row is observer-level and does NOT discharge *)
(*                          it: the encoder-image ideal is not the            *)
(*                          group-uniform ideal, and no bound against group   *)
(*                          uniform on any carrier is stated or implied |     *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | IdealFinite |                                     *)
(* | assumption status    | AcceptsAxioms [:: AxS5GroupOrder; AxRayleighQ2R] |*)
(* | typed row            | s5_row_word |                                     *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | word_endpoint_bound | the cut distribution of word_sample, named by      *)
(*   word_cut_distE | one position's endpoint distribution                    *)
(*   | cut-level endpoint marginal mixing, conditional on s5_rayleigh_Q2_R |  *)
(* | exec_endpoint_bound | sa_seat_dist of word_sample                        *)
(*   | one seat's executed reading against the encoder-image ideal           *)
(*   | executed endpoint marginal mixing, conditional on s5_rayleigh_Q2_R |   *)
(*                                                                            *)
(* Level justification. word_sample is a SampleAdapter over exec_plug and     *)
(* word_cut_distE names its cut distribution, giving Sampled;                 *)
(* exec_endpoint_bound is a mixing theorem at the row's own executed          *)
(* observer, giving AnalysisBridged. It bounds ONE seat's endpoint marginal   *)
(* against the encoder-image ideal, which is neither uniform nor              *)
(* secret-independent; it quantifies over no coalition, mentions no second    *)
(* secret and has neither the shape of an indistinguishability statement nor  *)
(* that of a leakage statement. No finite-word coalition claim is made        *)
(* anywhere on this path. Both bounds are conditional on the trusted          *)
(* analytical certificate s5_rayleigh_Q2_R, which is why the assumption       *)
(* status of this row lists AxRayleighQ2R next to the instance's group-order  *)
(* assumption.                                                                *)
(*                                                                            *)
(*     Aliases carrying no capability yet                                     *)
(*                                                                            *)
(* These are public observers and correctness statements of the three facades *)
(* that no row above attaches a security notion to. They are named here so    *)
(* that the checker pins the whole facade surface, not only the rows.         *)
(*                                                                            *)
(* | facade | aliases |                                                       *)
(* |---|---|                                                                  *)
(* | PGL27Analysis | verifier_trace, player_raw_trace, coalition_raw_trace,   *)
(*                   seat_endpoint, prior, exec_correct, exec_recovers,       *)
(*                   var_dist_transfer |                                      *)
(* | FiveCardAnalysis | verifier_trace, player_raw_trace,                     *)
(*                      coalition_raw_trace, input_raw_trace,                 *)
(*                      dealer_raw_trace, prior, exec_correct, exec_recovers, *)
(*                      procs_biasE |                                         *)
(* | S5Analysis | profile_k, seat_endpoint, coalition_endpoints,              *)
(*                verifier_trace, verifier_endpoints, player_raw_trace,       *)
(*                rand_seat_endpoint, rand_coalition_endpoints,               *)
(*                rand_verifier_trace, rand_verifier_endpoints,               *)
(*                rand_player_raw_trace, exec_correct, exec_recovers,         *)
(*                rand_correct, rand_recovers, word_cut_imageE,               *)
(*                word_transfer_conditional |                                 *)
(*                                                                            *)
(*     Absent capabilities                                                    *)
(*                                                                            *)
(* No row is filled with a dummy theorem, an option-valued proof, an axiom or *)
(* a placeholder, no endpoint marginal bound is recorded as a privacy or      *)
(* security capability, and every path whose transfer status is               *)
(* NoModelComparison or StaticExecutedOnly names the premise it lacks. The    *)
(* IdealFinite word row 8 also keeps naming the absent cut-carrier premise    *)
(* below: its transfer is observer-level and never discharges it.             *)
(*                                                                            *)
(* Five-card development. No transfer-layer result exists: section 7 of its   *)
(* facade carries typed status aliases and no theorem. The absent premise is  *)
(* the second hypothesis of var_dist_fdistmap_transfer, an equality of two    *)
(* reader pushforwards under an ideal distribution, which the development     *)
(* does not supply.                                                           *)
(*                                                                            *)
(* S_5 finite-word path (row 8). The absent premise is                        *)
(* S5Analysis.word_missing_premise, that is                                   *)
(* var_dist (sa_cut_dist (S5Analysis.word_sample secretP L)) Q <= delta on    *)
(* the cut carrier {perm 'I_5}, against a named reference distribution Q.     *)
(* S5Analysis.word_endpoint_bound bounds a pushforward on the carrier 'I_5    *)
(* instead, and the executed transfer S5Analysis.exec_endpoint_bound compares *)
(* the executed reading with the encoder-image ideal, the content one seat    *)
(* reads when the dealt position is exactly uniform mixed over the secret     *)
(* prior, on the carrier 'I_5; neither discharges it. That ideal is not the   *)
(* group-uniform ideal. For Q the uniform distribution on the*)
(* generated group the premise is moreover UNSATISFIABLE at every delta below *)
(* one: every generator of this instance is a transposition, so a word of     *)
(* length L evaluates into the coset of the alternating subgroup determined   *)
(* by the parity of L, and the cut distribution has full-L1 distance one from *)
(* group uniform. That sign-coset confinement is not formalized at S_5, and   *)
(* no theorem of this repository asserts it there.                            *)
(******************************************************************************)

(******************************************************************************)
(*     The typed rows                                                         *)
(******************************************************************************)

(** A record bundling, per analysis path, its observed execution
    apr_observed (which carries the path's profile and execution plug as
    projections), its completion level apr_completion, its model slot
    apr_model of dependent type AnalysisModelSlot apr_observed
    apr_completion, and the two remaining statuses apr_transfer and
    apr_assumptions. It stores no theorem: theorems stay facade aliases,
    named separately and pinned by spelled type in the checker below. This
    is the manifest's row type; each value below is read off the path's
    typed witnesses rather than asserted, so a row cannot silently drift
    from the code it describes. *)
Record AnalysisPathRow := MkAnalysisPathRow {
  (* apr_observed is the executed run of the path together with its static
     observation and the value it recovers. *)
  apr_observed    : OE.ObservedExecution ;
  (* apr_completion is the level the path's theorems actually reach. *)
  apr_completion  : CompletionLevel ;
  (* apr_model is the path's typed model evidence: an AnalysisModelFamily
     over the row's own observed execution, mandatory at Sampled and
     AnalysisBridged, optional at the three lower levels. A parameterized
     model is carried as a family with its real index type, never as an
     empty slot. *)
  apr_model       : AnalysisModelSlot apr_observed apr_completion ;
  (* apr_transfer is the relation the path establishes between its executed
     model and an idealized one. *)
  apr_transfer    : TransferStatus ;
  (* apr_assumptions is the assumption status of the path's public results,
     the classical trio of the repository baseline excluded. *)
  apr_assumptions : AssumptionStatus ;
}.

(** The AnalysisPathRow for the eight-card orbit instance under its exact
    uniform shuffle: PGL27Analysis.observed paired with the exact-uniform
    model family PGL27Analysis.exact_family, AnalysisBridged,
    StaticExecutedOnly, BaselineClassicalOnly. exact_view_indep is proved at
    this row's own sample distribution and observer, which is what reaches
    AnalysisBridged; the shuffle is already the exact uniform distribution
    on the group, so no idealized model is compared. *)
Definition pgl27_row_exact : AnalysisPathRow :=
  @MkAnalysisPathRow PGL27Analysis.observed AnalysisBridged
    PGL27Analysis.exact_family StaticExecutedOnly BaselineClassicalOnly.

(** The AnalysisPathRow for the same instance under its two-hundred-letter
    word shuffle: PGL27Analysis.observed paired with the word model family
    indexed by the secret prior, AnalysisBridged, IdealFinite,
    BaselineClassicalOnly. word_mixing supplies the base-distribution bound
    the generic transfer inequality needs on the cut carrier itself, which
    is what makes the transfer status IdealFinite rather than merely
    StaticExecutedOnly. *)
Definition pgl27_row_word : AnalysisPathRow :=
  @MkAnalysisPathRow PGL27Analysis.observed AnalysisBridged
    PGL27Analysis.word_family IdealFinite BaselineClassicalOnly.

(** The AnalysisPathRow for the five-card development under the uniform
    rotation cut: FiveCardAnalysis.observed paired with the uniform model
    family, AnalysisBridged, StaticExecutedOnly, BaselineClassicalOnly.
    exec_trace_secrecy is stated at this row's own random variable
    content_trace R ord0 over its own sample distribution, reaching
    AnalysisBridged; the development supplies no ideal-distribution
    equality, so no model transfer is claimed. *)
Definition five_card_row_uniform : AnalysisPathRow :=
  @MkAnalysisPathRow FiveCardAnalysis.observed AnalysisBridged
    FiveCardAnalysis.uniform_family StaticExecutedOnly BaselineClassicalOnly.

(** The AnalysisPathRow for the same development under one biased cut at
    Kim's input distribution: FiveCardAnalysis.observed paired with the
    single-biased model family at bias one hundredth, AnalysisBridged,
    StaticExecutedOnly, BaselineClassicalOnly. colour_view_leak_bound bounds
    a conditional mutual information over that same biased distribution at
    the row's own executed reader colour_view, reaching AnalysisBridged. *)
Definition five_card_row_biased : AnalysisPathRow :=
  @MkAnalysisPathRow FiveCardAnalysis.observed AnalysisBridged
    FiveCardAnalysis.biased_family StaticExecutedOnly BaselineClassicalOnly.

(** The AnalysisPathRow for the same development under repeated biased
    cuts: FiveCardAnalysis.observed paired with the seven-cut model family
    at bias one hundredth, Sampled, NoModelComparison,
    BaselineClassicalOnly. endpoint_bound and deal_centi_lt bound one
    seat's endpoint distribution, not a coalition or a second secret, so
    the row stops at Sampled rather than reaching AnalysisBridged. *)
Definition five_card_row_repeated : AnalysisPathRow :=
  @MkAnalysisPathRow FiveCardAnalysis.observed Sampled
    FiveCardAnalysis.centi_family NoModelComparison BaselineClassicalOnly.

(** The AnalysisPathRow for the five-seat S_5 instance dealing a position
    deterministically: S5Analysis.observed, Observed, no model witness,
    NoModelComparison, AcceptsAxioms [:: AxS5GroupOrder]. The path names no
    sample layer, so the model slot is None; the axiom is the instance's
    group-order fact, needed because the profile's threshold data is
    proved from the order of the generated group. *)
Definition s5_row_det : AnalysisPathRow :=
  @MkAnalysisPathRow S5Analysis.observed Observed None
    NoModelComparison (AcceptsAxioms [:: AxS5GroupOrder]).

(** The AnalysisPathRow for the same instance dealing an additive sharing:
    S5Analysis.rand_observed paired with the randomized model family
    S5Analysis.rand_family, AnalysisBridged, StaticExecutedOnly,
    AcceptsAxioms [:: AxS5GroupOrder]. exec_coalition_secrecy is stated at
    sa_coalition_view of rand_sample itself, the row's own distribution and
    observer, reaching AnalysisBridged; no idealized model is compared. *)
Definition s5_row_rand : AnalysisPathRow :=
  @MkAnalysisPathRow S5Analysis.rand_observed AnalysisBridged
    S5Analysis.rand_family StaticExecutedOnly
    (AcceptsAxioms [:: AxS5GroupOrder]).

(** The AnalysisPathRow for the same instance under a finite generator
    word: S5Analysis.observed paired with the word model family indexed by
    a secret prior and a word length, AnalysisBridged, IdealFinite,
    AcceptsAxioms [:: AxS5GroupOrder; AxRayleighQ2R]. exec_endpoint_bound
    is a mixing theorem at the row's own executed observer against the
    encoder-image ideal, conditional on the trusted analytical certificate
    s5_rayleigh_Q2_R, which is why that axiom joins the group-order one. *)
Definition s5_row_word : AnalysisPathRow :=
  @MkAnalysisPathRow S5Analysis.observed AnalysisBridged
    S5Analysis.word_family IdealFinite
    (AcceptsAxioms [:: AxS5GroupOrder; AxRayleighQ2R]).

(******************************************************************************)
(*     The deterministic checker: eight-card orbit instance                   *)
(******************************************************************************)

(* --- 1 Program --- *)

Timeout 60 Check (PGL27Analysis.profile : MonodromyProfile).

(* --- 2 Execution --- *)

Timeout 60 Check (PGL27Analysis.exec_plug :
  ExecutionPlug PGL27Analysis.profile).

Timeout 60 Check (PGL27Analysis.verifier_trace :
  ep_inputT PGL27Analysis.exec_plug ->
  pgg_gT (mp_M PGL27Analysis.profile) -> nat ->
  seq (pgg_data (pgg_N' (mp_M PGL27Analysis.profile)).+1)).

(* --- 3 Observers --- *)

Timeout 60 Check (PGL27Analysis.player_raw_trace :
  bool -> pgg_gT (mp_M PGL27Analysis.profile) ->
  'I_(pi_T' (mp_PI PGL27Analysis.profile)).+1 ->
  seq (pgg_data (pgg_N' (mp_M PGL27Analysis.profile)).+1)).

Timeout 60 Check (PGL27Analysis.coalition_raw_trace :
  bool -> pgg_gT (mp_M PGL27Analysis.profile) ->
  {set 'I_(pi_T' (mp_PI PGL27Analysis.profile)).+1} ->
  {ffun 'I_(pi_T' (mp_PI PGL27Analysis.profile)).+1 ->
        seq (pgg_data (pgg_N' (mp_M PGL27Analysis.profile)).+1)}).

Timeout 60 Check (PGL27Analysis.seat_endpoint :
  ep_inputT PGL27Analysis.exec_plug ->
  pgg_gT (mp_M PGL27Analysis.profile) -> nat ->
  'I_(pi_T' (mp_PI PGL27Analysis.profile)).+1 ->
  'I_(pgg_N' (mp_M PGL27Analysis.profile)).+1).

Timeout 60 Check (PGL27Analysis.coalition_endpoints :
  ep_inputT PGL27Analysis.exec_plug ->
  pgg_gT (mp_M PGL27Analysis.profile) -> nat ->
  {set 'I_(pi_T' (mp_PI PGL27Analysis.profile)).+1} ->
  {ffun 'I_(pi_T' (mp_PI PGL27Analysis.profile)).+1 ->
        'I_(pgg_N' (mp_M PGL27Analysis.profile)).+1}).

Timeout 60 Check (PGL27Analysis.content_trace :
  {set 'I_8} -> bool -> pgg_gT (mp_M PGL27Analysis.profile) ->
  {ffun 'I_8 -> 'I_8}).

Timeout 60 Check (PGL27Analysis.static_view :
  forall R : realType,
    {set 'I_8} -> {RV (PGL27Analysis.prior R) -> {ffun 'I_8 -> 'I_8}}).

Timeout 60 Check (PGL27Analysis.coalition_trace :
  forall R : realType,
    {set 'I_8} -> {RV (PGL27Analysis.prior R) -> {ffun 'I_8 -> 'I_8}}).

Timeout 60 Check (PGL27Analysis.secret :
  forall R : realType, {RV (PGL27Analysis.prior R) -> bool}).

Timeout 60 Check (PGL27Analysis.prior :
  forall R : realType,
    R.-fdist (bool * pgg_gT (mp_M PGL27Analysis.profile))%type).

Timeout 60 Check (PGL27Analysis.observed : OE.ObservedExecution).

(* --- 4 Models --- *)

Timeout 60 Check (PGL27Analysis.exact_sample :
  forall R : realType, SampleAdapter R PGL27Analysis.exec_plug).

Timeout 60 Check (PGL27Analysis.word_sample :
  forall R : realType,
    R.-fdist bool -> SampleAdapter R PGL27Analysis.exec_plug).

Timeout 60 Check (PGL27Analysis.fixed_exact_sample :
  forall R : realType, bool -> SampleAdapter R PGL27Analysis.exec_plug).

Timeout 60 Check (PGL27Analysis.fixed_word_sample :
  forall R : realType, bool -> SampleAdapter R PGL27Analysis.exec_plug).

Timeout 60 Check (PGL27Analysis.sample_cut_distE :
  forall R : realType,
    sa_cut_dist (PGL27Analysis.exact_sample R)
    = sw_rho_dist (PGL27Analysis.marginal_bound R)).

Timeout 60 Check (PGL27Analysis.word_cut_distE :
  forall (R : realType) (secretP : R.-fdist bool),
    sa_cut_dist (@PGL27Analysis.word_sample R secretP)
    = pgl27_word_privacy.rho_word R).

Timeout 60 Check (PGL27Analysis.fixed_cut_distE :
  forall (R : realType) (s : bool),
    sa_cut_dist (PGL27Analysis.fixed_exact_sample R s)
    = (`U pgl27_profile.pgl27_G_pos
       : R.-fdist (pgg_gT (mp_M PGL27Analysis.profile)))).

Timeout 60 Check (PGL27Analysis.fixed_word_cut_distE :
  forall (R : realType) (s : bool),
    sa_cut_dist (PGL27Analysis.fixed_word_sample R s)
    = pgl27_word_privacy.rho_word R).

Timeout 60 Check (PGL27Analysis.exact_coalition_distE :
  forall (R : realType) (C : {set 'I_8}),
    sa_coalition_dist (PGL27Analysis.exact_sample R) 0 C
    = fdistmap (PGL27Analysis.static_view R C) (PGL27Analysis.prior R)).

Timeout 60 Check (PGL27Analysis.fixed_word_coalition_distE :
  forall (R : realType) (C : {set 'I_8}) (s : bool),
    sa_coalition_dist (PGL27Analysis.fixed_word_sample R s) 0 C
    = fdistmap (fun g => PGL27Analysis.static_view R C (s, g))
        (pgl27_word_privacy.rho_word R)).

Timeout 60 Check (PGL27Analysis.fixed_word_content_trace_distE :
  forall (R : realType) (C : {set 'I_8}) (s : bool),
    fdistmap (fun w : 200.-tuple 'I_5 =>
                PGL27Analysis.content_trace C s (word_eval w))
      (pgl27_exec.pgl27_word_wordP R)
    = fdistmap (fun g => PGL27Analysis.coalition_trace R C (s, g))
        (pgl27_word_privacy.rho_word R)).

Timeout 60 Check (PGL27Analysis.word_joint_viewE :
  forall (R : realType) (secretP : R.-fdist bool) (C : {set 'I_8}),
    fdistmap (fun u : bool * 200.-tuple 'I_5 =>
                (PGL27Analysis.coalition_endpoints u.1 (word_eval u.2) 0 C,
                 u.1))
      (@pgl27_exec.pgl27_word_sampleP R secretP)
    = fdistmap (fun v => (PGL27Analysis.static_view R C v,
                          PGL27Analysis.secret R v))
        (@pgl27_word_privacy.pgl27P_word_gen R secretP)).

Timeout 60 Check (PGL27Analysis.word_sample_joint_distE :
  forall (R : realType) (secretP : R.-fdist bool),
    sa_joint_dist (sa_arg (s := @PGL27Analysis.word_sample R secretP))
    = @pgl27_word_privacy.pgl27P_word_gen R secretP).

(* --- 5 Correctness --- *)

Timeout 60 Check (PGL27Analysis.exec_correct :
  forall (s : bool) (w0 : pgg_gT (mp_M PGL27Analysis.profile)),
    w0 \in pgg_G (mp_M PGL27Analysis.profile) ->
    [/\ (@exec_run PGL27Analysis.profile PGL27Analysis.exec_plug s w0 0).1
        = nseq (size (@exec_procs PGL27Analysis.profile
                        PGL27Analysis.exec_plug s w0 0))
            smc_interpreter.Finish,
        size (@exec_endpoints PGL27Analysis.profile PGL27Analysis.exec_plug
                s w0 0)
        = (pi_T' (mp_PI PGL27Analysis.profile)).+1
      & exec_decode PGL27Analysis.exec_plug
          (exec_endpoints_size (pgl27_exec.pgl27_exec_endpoints s w0)) = s]).

Timeout 60 Check (PGL27Analysis.exec_recovers :
  forall (s : bool) (w0 : pgg_gT (mp_M PGL27Analysis.profile)),
    w0 \in pgg_G (mp_M PGL27Analysis.profile) ->
    exec_decode PGL27Analysis.exec_plug
      (exec_endpoints_size (pgl27_exec.pgl27_exec_endpoints s w0)) = s).

Timeout 60 Check (PGL27Analysis.observed_recovers :
  forall (s : bool) (w0 : pgg_gT (mp_M PGL27Analysis.profile)),
    w0 \in pgg_G (mp_M PGL27Analysis.profile) ->
    exec_decode PGL27Analysis.exec_plug
      (OE.oe_endpoints_size PGL27Analysis.observed s w0) = s).

(* --- 6 Security --- *)

Timeout 60 Check (PGL27Analysis.content_traceE :
  forall (R : realType) (C : {set 'I_8})
    (u : bool * pgg_gT (mp_M PGL27Analysis.profile)),
    PGL27Analysis.content_trace C u.1 u.2
    = PGL27Analysis.coalition_trace R C u).

Timeout 60 Check (PGL27Analysis.word_view_indist :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N ->
    var_dist
      (fdistmap (fun g => PGL27Analysis.static_view R C (s, g))
         (pgl27_word_privacy.rho_word R))
      (fdistmap (fun g => PGL27Analysis.static_view R C (s', g))
         (pgl27_word_privacy.rho_word R))
    <= 2%:R^-39).

Timeout 60 Check (PGL27Analysis.word_trace_indist :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N ->
    var_dist
      (fdistmap (fun g => PGL27Analysis.coalition_trace R C (s, g))
         (pgl27_word_privacy.rho_word R))
      (fdistmap (fun g => PGL27Analysis.coalition_trace R C (s', g))
         (pgl27_word_privacy.rho_word R))
    <= 2%:R^-39).

Timeout 60 Check (PGL27Analysis.exec_view_indist :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N ->
    var_dist (sa_coalition_dist (PGL27Analysis.fixed_word_sample R s) 0 C)
             (sa_coalition_dist (PGL27Analysis.fixed_word_sample R s') 0 C)
    <= 2%:R^-39).

Timeout 60 Check (PGL27Analysis.exec_trace_indist :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N ->
    var_dist
      (fdistmap (fun w : 200.-tuple 'I_5 =>
                   PGL27Analysis.content_trace C s (word_eval w))
         (pgl27_exec.pgl27_word_wordP R))
      (fdistmap (fun w : 200.-tuple 'I_5 =>
                   PGL27Analysis.content_trace C s' (word_eval w))
         (pgl27_exec.pgl27_word_wordP R))
    <= 2%:R^-39).

Timeout 60 Check (PGL27Analysis.view_mixing :
  forall (R : realType) (secretP : R.-fdist bool) (C : {set 'I_8}),
    (#|C| <= 3)%N ->
    var_dist
      (fdistmap (fun u => (PGL27Analysis.static_view R C u,
                           PGL27Analysis.secret R u))
         (@pgl27_word_privacy.pgl27P_word_gen R secretP))
      ((fdistmap (PGL27Analysis.static_view R C)
          (@pgl27_word_privacy.pgl27P_gen R secretP))
       `x (fdistmap (PGL27Analysis.secret R)
             (@pgl27_word_privacy.pgl27P_gen R secretP)))%fdist
    <= 2%:R^-40).

Timeout 60 Check (PGL27Analysis.word_mixing :
  forall R : realType,
    var_dist
      (rho_from_words_weighted 200 pgl27_mixing.pgl27_sym_sigmas
         (pgl27_mixing.Wuni R))
      (`U pgl27_profile.pgl27_G_pos)
    <= 2%:R^-40).

Timeout 60 Check (PGL27Analysis.coalition_trace_secrecy :
  forall (R : realType) (C : {set 'I_8}),
    (#|C| <= 3)%N ->
    `H( (PGL27Analysis.secret R) | (PGL27Analysis.coalition_trace R C))
    = `H `p_ (PGL27Analysis.secret R)).

Timeout 60 Check (PGL27Analysis.exact_view_indep :
  forall (R : realType) (C : {set 'I_8}),
    (#|C| <= 3)%N ->
    fdistmap (fun u => (PGL27Analysis.static_view R C u,
                        PGL27Analysis.secret R u)) (PGL27Analysis.prior R)
    = ((sa_coalition_dist (PGL27Analysis.exact_sample R) 0 C)
       `x (fdistmap (PGL27Analysis.secret R) (PGL27Analysis.prior R)))%fdist).

Timeout 60 Check (PGL27Analysis.marginal_bound :
  forall R : realType,
    ShuffleMarginalBound R (mp_M PGL27Analysis.profile)).

Timeout 60 Check (PGL27Analysis.certificate_bundle :
  forall R : realType,
    ShuffleCertificateBundle R (mp_M PGL27Analysis.profile)).

(* --- 7 Transfer --- *)

Timeout 60 Check (PGL27Analysis.var_dist_transfer :
  forall (R : realType) (A B : finType) (P Q : R.-fdist A) (fx fy : A -> B)
    (delta : R),
    var_dist P Q <= delta ->
    fdistmap fx Q = fdistmap fy Q ->
    var_dist (fdistmap fx P) (fdistmap fy P) <= delta + delta).

Timeout 60 Check (PGL27Analysis.word_view_indist_via_transfer :
  forall (R : realType) (C : {set 'I_8}) (s s' : bool),
    (#|C| <= 3)%N ->
    var_dist
      (fdistmap (fun g => PGL27Analysis.static_view R C (s, g))
         (pgl27_word_privacy.rho_word R))
      (fdistmap (fun g => PGL27Analysis.static_view R C (s', g))
         (pgl27_word_privacy.rho_word R))
    <= 2%:R^-39).

Timeout 60 Check (erefl : PGL27Analysis.word_transfer_status = IdealFinite).

(******************************************************************************)
(*     The deterministic checker: five-card development                       *)
(******************************************************************************)

(* --- 1 Program --- *)

Timeout 60 Check (FiveCardAnalysis.profile : MonodromyProfile).

Timeout 60 Check (FiveCardAnalysis.den_boer_profile : MonodromyProfile).

(* --- 2 Execution --- *)

Timeout 60 Check (FiveCardAnalysis.exec_plug :
  ExecutionPlug FiveCardAnalysis.profile).

Timeout 60 Check (FiveCardAnalysis.verifier_trace :
  ep_inputT FiveCardAnalysis.exec_plug ->
  pgg_gT (mp_M FiveCardAnalysis.profile) -> nat ->
  seq (pgg_data (pgg_N' (mp_M FiveCardAnalysis.profile)).+1)).

(* --- 3 Observers --- *)

Timeout 60 Check (FiveCardAnalysis.player_raw_trace :
  bool * bool -> pgg_gT (mp_M FiveCardAnalysis.profile) ->
  'I_(pi_T' (mp_PI FiveCardAnalysis.profile)).+1 ->
  seq (pgg_data (pgg_N' (mp_M FiveCardAnalysis.profile)).+1)).

Timeout 60 Check (FiveCardAnalysis.coalition_raw_trace :
  bool * bool -> pgg_gT (mp_M FiveCardAnalysis.profile) ->
  {set 'I_(pi_T' (mp_PI FiveCardAnalysis.profile)).+1} ->
  {ffun 'I_(pi_T' (mp_PI FiveCardAnalysis.profile)).+1 ->
        seq (pgg_data (pgg_N' (mp_M FiveCardAnalysis.profile)).+1)}).

Timeout 60 Check (FiveCardAnalysis.input_raw_trace :
  bool * bool -> pgg_gT (mp_M FiveCardAnalysis.profile) -> nat ->
  seq (pgg_data (pgg_N' (mp_M FiveCardAnalysis.profile)).+1)).

Timeout 60 Check (FiveCardAnalysis.input_trace :
  forall R : realType, nat -> {RV (FiveCardAnalysis.prior R) -> 'I_5}).

Timeout 60 Check (FiveCardAnalysis.dealer_raw_trace :
  bool * bool -> pgg_gT (mp_M FiveCardAnalysis.profile) ->
  seq (pgg_data (pgg_N' (mp_M FiveCardAnalysis.profile)).+1)).

Timeout 60 Check (FiveCardAnalysis.dealer_trace :
  forall R : realType,
    {RV (FiveCardAnalysis.prior R) -> (bool * bool)%type}).

Timeout 60 Check (FiveCardAnalysis.verifier_endpoints :
  ep_inputT FiveCardAnalysis.exec_plug ->
  pgg_gT (mp_M FiveCardAnalysis.profile) -> nat ->
  seq 'I_(pgg_N' (mp_M FiveCardAnalysis.profile)).+1).

Timeout 60 Check (FiveCardAnalysis.content_trace :
  forall R : realType,
    'I_(pi_T' (mp_PI FiveCardAnalysis.profile)).+1 ->
    {RV (FiveCardAnalysis.prior R) -> 'I_5}).

Timeout 60 Check (FiveCardAnalysis.colour_view :
  forall A : seq nat,
    bool * bool -> pgg_gT (mp_M FiveCardAnalysis.profile) ->
    (size A).-tuple bool).

Timeout 60 Check (FiveCardAnalysis.secret :
  forall R : realType, {RV (FiveCardAnalysis.prior R) -> bool}).

Timeout 60 Check (FiveCardAnalysis.prior :
  forall R : realType, R.-fdist five_card_leakage.Omega).

Timeout 60 Check (FiveCardAnalysis.observed : OE.ObservedExecution).

Timeout 60 Check (FiveCardAnalysis.den_boer_observed : OE.ObservedExecution).

(* --- 4 Models --- *)

Timeout 60 Check (FiveCardAnalysis.uniform_sample :
  forall R : realType, SampleAdapter R FiveCardAnalysis.exec_plug).

Timeout 60 Check (FiveCardAnalysis.single_biased_sample :
  forall (R : realType) (eps : R),
    eps < 5%:R^-1 -> - (4%:R * 5%:R^-1) < eps ->
    SampleAdapter R FiveCardAnalysis.exec_plug).

Timeout 60 Check (FiveCardAnalysis.repeated_sample :
  forall (R : realType) (eps : R),
    eps < 5%:R^-1 -> - (4%:R * 5%:R^-1) < eps -> nat ->
    SampleAdapter R FiveCardAnalysis.exec_plug).

Timeout 60 Check (FiveCardAnalysis.centi_sample :
  forall R : realType, SampleAdapter R FiveCardAnalysis.exec_plug).

Timeout 60 Check (FiveCardAnalysis.sample_cut_distE :
  forall R : realType,
    five_card_exec.five_card_sample_cut_dist R
    = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
        (fdist_uniform (card_ord 5))).

Timeout 60 Check (FiveCardAnalysis.sample_cut_witnessE :
  forall R : realType,
    five_card_exec.five_card_sample_cut_dist R
    = sw_rho_dist (FiveCardAnalysis.marginal_bound R)).

Timeout 60 Check (FiveCardAnalysis.witness_rotationE :
  forall R : realType,
    sw_rho_dist (FiveCardAnalysis.marginal_bound R)
    = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
        (fdist_uniform (card_ord 5))).

Timeout 60 Check (FiveCardAnalysis.single_cut_distE :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps),
    sa_cut_dist (@FiveCardAnalysis.single_biased_sample R eps Hlt Hgt)
    = fdistmap (fun k : 'I_5 => (five_card_group.fc_sigma ^+ k)%g)
        (five_card_kim.kim_weight_dist Hlt Hgt)).

Timeout 60 Check (FiveCardAnalysis.repeated_cut_distE :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (L : nat),
    sa_cut_dist (@FiveCardAnalysis.repeated_sample R eps Hlt Hgt L)
    = rho_from_words_weighted L five_card_kim.fc_kim_sigmas
        (five_card_kim.kim_weight_dist Hlt Hgt)).

Timeout 60 Check (FiveCardAnalysis.repeated_seat_distE :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (L : nat)
    (i : 'I_(pi_T' (mp_PI FiveCardAnalysis.profile)).+1),
    sa_seat_dist (@FiveCardAnalysis.repeated_sample R eps Hlt Hgt L) 0 i
    = fdistmap
        (@sa_static_seat_view R FiveCardAnalysis.profile
           FiveCardAnalysis.exec_plug
           (@FiveCardAnalysis.repeated_sample R eps Hlt Hgt L)
           five_card_exec.five_card_content_obs i)
        (@five_card_models.kim_repeated_dist R eps Hlt Hgt L)).

Timeout 60 Check (FiveCardAnalysis.centi_cut_distE :
  forall R : realType,
    sa_cut_dist (FiveCardAnalysis.centi_sample R)
    = sw_rho_dist (scb_bound (FiveCardAnalysis.centi_bundle R))).

Timeout 60 Check (FiveCardAnalysis.centi_witness_rhoE :
  forall R : realType,
    sw_rho_dist (scb_bound (FiveCardAnalysis.centi_bundle R))
    = rho_from_words_weighted 7 five_card_kim.fc_kim_sigmas
        (five_card_kim.kim_weight_dist (five_card_kim.kim_centi_lt R)
           (five_card_kim.kim_centi_gt R))).

Timeout 60 Check (FiveCardAnalysis.centi_repeated_seat_distE :
  forall (R : realType) (i : 'I_(pi_T' (mp_PI FiveCardAnalysis.profile)).+1),
    sa_seat_dist
      (@FiveCardAnalysis.repeated_sample R (1 / 100)
         (five_card_kim.kim_centi_lt R) (five_card_kim.kim_centi_gt R) 7) 0 i
    = fdistmap
        (@sa_static_seat_view R FiveCardAnalysis.profile
           FiveCardAnalysis.exec_plug
           (@FiveCardAnalysis.repeated_sample R (1 / 100)
              (five_card_kim.kim_centi_lt R) (five_card_kim.kim_centi_gt R) 7)
           five_card_exec.five_card_content_obs i)
        (@five_card_models.kim_repeated_dist R (1 / 100)
           (five_card_kim.kim_centi_lt R) (five_card_kim.kim_centi_gt R) 7)).

(* --- 5 Correctness --- *)

Timeout 60 Check (FiveCardAnalysis.exec_correct :
  forall (a b : bool) (w0 : pgg_gT (mp_M FiveCardAnalysis.profile)),
    w0 \in pgg_G (mp_M FiveCardAnalysis.profile) ->
    [/\ (@exec_run FiveCardAnalysis.profile FiveCardAnalysis.exec_plug
           (a, b) w0 0).1
        = nseq (size (@exec_procs FiveCardAnalysis.profile
                        FiveCardAnalysis.exec_plug (a, b) w0 0))
            smc_interpreter.Finish,
        size (@exec_endpoints FiveCardAnalysis.profile
                FiveCardAnalysis.exec_plug (a, b) w0 0)
        = (pi_T' (mp_PI FiveCardAnalysis.profile)).+1
      & exec_decode FiveCardAnalysis.exec_plug
          (exec_endpoints_size
             (five_card_exec.five_card_exec_endpoints a b w0)) = a && b]).

Timeout 60 Check (FiveCardAnalysis.exec_recovers :
  forall (a b : bool) (w0 : pgg_gT (mp_M FiveCardAnalysis.profile)),
    w0 \in pgg_G (mp_M FiveCardAnalysis.profile) ->
    exec_decode FiveCardAnalysis.exec_plug
      (exec_endpoints_size (five_card_exec.five_card_exec_endpoints a b w0))
    = a && b).

Timeout 60 Check (FiveCardAnalysis.observed_recovers :
  forall (x : bool * bool) (w0 : pgg_gT (mp_M FiveCardAnalysis.profile)),
    w0 \in pgg_G (mp_M FiveCardAnalysis.profile) ->
    exec_decode FiveCardAnalysis.exec_plug
      (OE.oe_endpoints_size FiveCardAnalysis.observed x w0) = x.1 && x.2).

Timeout 60 Check (FiveCardAnalysis.procs_biasE :
  forall (a b : bool) (w0 : pgg_gT (mp_M FiveCardAnalysis.profile))
    (P_idx : nat),
    @exec_procs FiveCardAnalysis.profile FiveCardAnalysis.exec_plug
      (a, b) w0 P_idx
    = @exec_procs FiveCardAnalysis.profile FiveCardAnalysis.exec_plug
        (a, b) w0 P_idx).

(* --- 6 Security --- *)

Timeout 60 Check (FiveCardAnalysis.exec_trace_secrecy :
  forall R : realType,
    `H( (FiveCardAnalysis.secret R)
      | (FiveCardAnalysis.content_trace R ord0))
    = `H `p_ (FiveCardAnalysis.secret R)).

Timeout 60 Check (FiveCardAnalysis.input_trace_secrecy :
  forall (R : realType) (j : nat),
    `H( (FiveCardAnalysis.secret R) | (FiveCardAnalysis.input_trace R j))
    = `H `p_ (FiveCardAnalysis.secret R)).

Timeout 60 Check (FiveCardAnalysis.dealer_pair_centropy0 :
  forall R : realType,
    `H( [eta fst] | (FiveCardAnalysis.dealer_trace R)) = 0).

Timeout 60 Check (FiveCardAnalysis.dealer_trace_centropy0 :
  forall R : realType,
    `H( (FiveCardAnalysis.secret R) | (FiveCardAnalysis.dealer_trace R))
    = 0).

Timeout 60 Check (FiveCardAnalysis.colour_viewE :
  forall (R : realType) (A : seq nat) (w : five_card_leakage.Omega),
    FiveCardAnalysis.colour_view A w.1 (five_card_group.fc_sigma ^+ w.2)
    = five_card_leakage.ViewA R A w).

Timeout 60 Check (FiveCardAnalysis.colour_view_RV_E :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps) (A : seq nat),
    (fun w : five_card_leakage.Omega =>
       FiveCardAnalysis.colour_view A w.1 (five_card_group.fc_sigma ^+ w.2))
    = kim_input_privacy.kim_view Hlt Hgt A).

Timeout 60 Check (FiveCardAnalysis.colour_view_leak_bound :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps),
    0 < 5%:R^-1 - `|eps| ->
    forall A : seq nat,
      cond_mutual_info
        (`p_ [% kim_input_privacy.kim_inputs Hlt Hgt,
               (fun w : five_card_leakage.Omega =>
                  FiveCardAnalysis.colour_view A w.1
                    (five_card_group.fc_sigma ^+ w.2)),
               kim_input_privacy.kim_secret Hlt Hgt])
      <= kim_input_privacy.kim_leak_bound eps).

Timeout 60 Check (FiveCardAnalysis.marginal_bound :
  forall R : realType,
    ShuffleMarginalBound R (mp_M FiveCardAnalysis.profile)).

Timeout 60 Check (FiveCardAnalysis.perfect :
  forall R : realType, sw_bound_eps (FiveCardAnalysis.marginal_bound R) = 0).

(* --- bound (endpoint marginal, not security) --- *)

Timeout 60 Check (FiveCardAnalysis.kim_bundle :
  forall (R : realType) (eps : R),
    eps < 5%:R^-1 -> - (4%:R * 5%:R^-1) < eps -> `|eps| < 4%:R / 5%:R ->
    nat -> ShuffleCertificateBundle R (mp_M FiveCardAnalysis.profile)).

Timeout 60 Check (FiveCardAnalysis.centi_bundle :
  forall R : realType,
    ShuffleCertificateBundle R (mp_M FiveCardAnalysis.profile)).

Timeout 60 Check (FiveCardAnalysis.endpoint_bound :
  forall (R : realType) (eps : R) (Hlt : eps < 5%:R^-1)
    (Hgt : - (4%:R * 5%:R^-1) < eps),
    `|eps| < 4%:R / 5%:R ->
    forall (L : nat) (s : 'I_5),
      var_dist
        (endpoint_dist_weighted L five_card_kim.fc_kim_sigmas
           (five_card_kim.kim_weight_dist Hlt Hgt) s)
        (fdist_uniform (card_ord 5))
      <= Num.Def.sqrtr 5%:R * five_card_kim.kim_lambda2 eps ^+ L).

Timeout 60 Check (FiveCardAnalysis.deal_centi_lt :
  forall (R : realType) (s : 'I_5),
    var_dist
      (fdistmap (fun g : {perm 'I_5} => g s)
         (sw_rho_dist (scb_bound (FiveCardAnalysis.centi_bundle R))))
      (fdist_uniform (card_ord 5))
    < 2%:R^-40).

(* --- 7 Transfer: the five-card facade carries no transfer theorem, so the
   two typed statuses are all there is to check; the PGL transfer aliases are
   checked above. --- *)

Timeout 60 Check
  (erefl : FiveCardAnalysis.exec_transfer_status = StaticExecutedOnly).

Timeout 60 Check
  (erefl : FiveCardAnalysis.repeated_transfer_status = NoModelComparison).

(******************************************************************************)
(*     The deterministic checker: five-seat S_5 instance                      *)
(******************************************************************************)

(* --- 1 Program --- *)

Timeout 60 Check (S5Analysis.profile : MonodromyProfile).

Timeout 60 Check (S5Analysis.profile_k : profile_k S5Analysis.profile = 5%N).

(* --- 2 Execution --- *)

Timeout 60 Check (S5Analysis.exec_plug : ExecutionPlug S5Analysis.profile).

Timeout 60 Check (S5Analysis.rand_exec_plug :
  ExecutionPlug S5Analysis.profile).

(* --- 3 Observers --- *)

Timeout 60 Check (S5Analysis.seat_endpoint :
  ep_inputT S5Analysis.exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  'I_(pi_T' (mp_PI S5Analysis.profile)).+1 ->
  'I_(pgg_N' (mp_M S5Analysis.profile)).+1).

Timeout 60 Check (S5Analysis.coalition_endpoints :
  ep_inputT S5Analysis.exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  {set 'I_(pi_T' (mp_PI S5Analysis.profile)).+1} ->
  {ffun 'I_(pi_T' (mp_PI S5Analysis.profile)).+1 ->
        'I_(pgg_N' (mp_M S5Analysis.profile)).+1}).

Timeout 60 Check (S5Analysis.verifier_trace :
  ep_inputT S5Analysis.exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  seq (pgg_data (pgg_N' (mp_M S5Analysis.profile)).+1)).

Timeout 60 Check (S5Analysis.verifier_endpoints :
  ep_inputT S5Analysis.exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  seq 'I_(pgg_N' (mp_M S5Analysis.profile)).+1).

Timeout 60 Check (S5Analysis.player_raw_trace :
  ep_inputT S5Analysis.exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  'I_(pi_T' (mp_PI S5Analysis.profile)).+1 ->
  seq (pgg_data (pgg_N' (mp_M S5Analysis.profile)).+1)).

Timeout 60 Check (S5Analysis.observed : OE.ObservedExecution).

Timeout 60 Check (S5Analysis.rand_seat_endpoint :
  ep_inputT S5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  'I_(pi_T' (mp_PI S5Analysis.profile)).+1 ->
  'I_(pgg_N' (mp_M S5Analysis.profile)).+1).

Timeout 60 Check (S5Analysis.rand_coalition_endpoints :
  ep_inputT S5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  {set 'I_(pi_T' (mp_PI S5Analysis.profile)).+1} ->
  {ffun 'I_(pi_T' (mp_PI S5Analysis.profile)).+1 ->
        'I_(pgg_N' (mp_M S5Analysis.profile)).+1}).

Timeout 60 Check (S5Analysis.rand_content_trace :
  forall (R : realType) (i : 'I_(pi_T' (mp_PI S5Analysis.profile)).+1),
    {RV (s5_models.s5_rand_sampleP R) -> 'I_5}).

Timeout 60 Check (S5Analysis.rand_verifier_trace :
  ep_inputT S5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  seq (pgg_data (pgg_N' (mp_M S5Analysis.profile)).+1)).

Timeout 60 Check (S5Analysis.rand_verifier_endpoints :
  ep_inputT S5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  seq 'I_(pgg_N' (mp_M S5Analysis.profile)).+1).

Timeout 60 Check (S5Analysis.rand_player_raw_trace :
  ep_inputT S5Analysis.rand_exec_plug ->
  pgg_gT (mp_M S5Analysis.profile) -> nat ->
  'I_(pi_T' (mp_PI S5Analysis.profile)).+1 ->
  seq (pgg_data (pgg_N' (mp_M S5Analysis.profile)).+1)).

Timeout 60 Check (S5Analysis.rand_observed : OE.ObservedExecution).

(* --- 4 Models --- *)

Timeout 60 Check (S5Analysis.rand_sample :
  forall R : realType, SampleAdapter R S5Analysis.rand_exec_plug).

Timeout 60 Check (S5Analysis.word_sample :
  forall R : realType, R.-fdist 'I_5 -> forall L : nat,
    SampleAdapter R S5Analysis.exec_plug).

Timeout 60 Check (S5Analysis.rand_cut_distE :
  forall R : realType,
    sa_cut_dist (S5Analysis.rand_sample R) = fdist1 1%g).

Timeout 60 Check (S5Analysis.word_cut_distE :
  forall (R : realType) (secretP : R.-fdist 'I_5) (L : nat),
    sa_cut_dist (S5Analysis.word_sample secretP L)
    = rho_from_words L (pgg_raag_path.path_gen_tuple 3)).

Timeout 60 Check (S5Analysis.word_cut_imageE :
  forall (R : realType) (secretP : R.-fdist 'I_5) (L : nat),
    sa_cut_dist_image (S5Analysis.word_sample secretP L)
    = rho_from_words L (pgg_raag_path.path_gen_tuple 3)).

(* --- 5 Correctness --- *)

Timeout 60 Check (S5Analysis.exec_correct :
  forall (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    [/\ (@exec_run S5Analysis.profile S5Analysis.exec_plug s w0 0).1
        = nseq (size (@exec_procs S5Analysis.profile S5Analysis.exec_plug
                        s w0 0))
            smc_interpreter.Finish,
        size (@exec_endpoints S5Analysis.profile S5Analysis.exec_plug s w0 0)
        = (pi_T' (mp_PI S5Analysis.profile)).+1
      & exec_decode S5Analysis.exec_plug
          (exec_endpoints_size (s5_exec.s5_exec_endpoints s w0)) = s]).

Timeout 60 Check (S5Analysis.exec_recovers :
  forall (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    exec_decode S5Analysis.exec_plug
      (exec_endpoints_size (s5_exec.s5_exec_endpoints s w0)) = s).

Timeout 60 Check (S5Analysis.observed_recovers :
  forall (s : 'I_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    exec_decode S5Analysis.exec_plug
      (OE.oe_endpoints_size S5Analysis.observed s w0) = s).

Timeout 60 Check (S5Analysis.rand_correct :
  forall (u : 'rV['Z_5]_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    [/\ (@exec_run S5Analysis.profile S5Analysis.rand_exec_plug u w0 0).1
        = nseq (size (@exec_procs S5Analysis.profile
                        S5Analysis.rand_exec_plug u w0 0))
            smc_interpreter.Finish,
        size (@exec_endpoints S5Analysis.profile S5Analysis.rand_exec_plug
                u w0 0)
        = (pi_T' (mp_PI S5Analysis.profile)).+1
      & exec_decode S5Analysis.rand_exec_plug
          (exec_endpoints_size (s5_exec.s5_rand_endpoints u w0))
        = s5_exec.s5_codec (s5_exec.s5_tape_secret u)]).

Timeout 60 Check (S5Analysis.rand_recovers :
  forall (u : 'rV['Z_5]_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    exec_decode S5Analysis.rand_exec_plug
      (exec_endpoints_size (s5_exec.s5_rand_endpoints u w0))
    = s5_exec.s5_codec (s5_exec.s5_tape_secret u)).

Timeout 60 Check (S5Analysis.rand_observed_recovers :
  forall (u : 'rV['Z_5]_5) (w0 : pgg_gT (mp_M S5Analysis.profile)),
    w0 \in pgg_G (mp_M S5Analysis.profile) ->
    exec_decode S5Analysis.rand_exec_plug
      (OE.oe_endpoints_size S5Analysis.rand_observed u w0)
    = s5_exec.s5_codec (s5_exec.s5_tape_secret u)).

(* --- 6 Security --- *)

Timeout 60 Check (S5Analysis.exec_trace_secrecy :
  forall (R : realType) (i : 'I_(pi_T' (mp_PI S5Analysis.profile)).+1),
    `H( rsh_secret (@unif_randomized_sharing R 3 4)
      | S5Analysis.rand_content_trace R i)
    = `H `p_ (rsh_secret (@unif_randomized_sharing R 3 4))).

Timeout 60 Check (S5Analysis.exec_coalition_secrecy :
  forall (R : realType) (C : {set 'I_(pi_T' (mp_PI S5Analysis.profile)).+1}),
    (#|C| < 5)%N ->
    `I( rsh_secret (@unif_randomized_sharing R 3 4) ;
        @sa_coalition_view R S5Analysis.profile S5Analysis.rand_exec_plug
          (S5Analysis.rand_sample R) 0 C ) = 0 /\
    `H( rsh_secret (@unif_randomized_sharing R 3 4)
        | @sa_coalition_view R S5Analysis.profile S5Analysis.rand_exec_plug
            (S5Analysis.rand_sample R) 0 C )
      = `H `p_ (rsh_secret (@unif_randomized_sharing R 3 4))).

(* --- bound (endpoint marginal, not security) --- *)

Timeout 60 Check (S5Analysis.word_endpoint_bound :
  forall (R : realType) (secretP : R.-fdist 'I_5) (L : nat) (s : 'I_5),
    var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                (sa_cut_dist (S5Analysis.word_sample secretP L)))
             (fdist_uniform (card_ord 5))
    <= Num.sqrt 5%:R * (s5_mixing.s5_alpha_R R) ^+ L).

(* --- 7 Transfer --- *)

Timeout 60 Check (erefl : S5Analysis.det_transfer_status = NoModelComparison).

Timeout 60 Check
  (erefl : S5Analysis.rand_transfer_status = StaticExecutedOnly).

Timeout 60 Check (S5Analysis.rand_content_traceE :
  forall (R : realType) (i : 'I_(pi_T' (mp_PI S5Analysis.profile)).+1),
    S5Analysis.rand_content_trace R i = s5_trace.s5_player_trace R i).

Timeout 60 Check (S5Analysis.rand_coalition_viewE :
  forall (R : realType) (C : {set 'I_(pi_T' (mp_PI S5Analysis.profile)).+1}),
    @sa_coalition_view R S5Analysis.profile S5Analysis.rand_exec_plug
      (S5Analysis.rand_sample R) 0 C
    = rsh_view (@unif_randomized_sharing R 3 4) C).

Timeout 60 Check (erefl : S5Analysis.word_transfer_status = IdealFinite).

Timeout 60 Check (S5Analysis.word_missing_premise :
  forall R : realType, R.-fdist 'I_5 -> forall L : nat,
    R.-fdist {perm 'I_5} -> R -> Prop).

Timeout 60 Check (S5Analysis.word_transfer_conditional :
  forall (R : realType) (secretP : R.-fdist 'I_5) (L : nat)
    (Q : R.-fdist {perm 'I_5}) (delta : R) (B : finType)
    (fx fy : {perm 'I_5} -> B),
    S5Analysis.word_missing_premise secretP L Q delta ->
    fdistmap fx Q = fdistmap fy Q ->
    var_dist (fdistmap fx (sa_cut_dist (S5Analysis.word_sample secretP L)))
             (fdistmap fy (sa_cut_dist (S5Analysis.word_sample secretP L)))
    <= delta + delta).

(******************************************************************************)
(*     The deterministic checker: the eight typed rows                        *)
(*                                                                            *)
(* One Check per row against AnalysisPathRow, one erefl pin per status       *)
(* field, and one typed check on the model slot: a mandatory family at        *)
(* Sampled and AnalysisBridged, an optional one below. A row whose status or  *)
(* model witness is edited away from the table above fails at its own pin.    *)
(******************************************************************************)

Timeout 60 Check (pgl27_row_exact : AnalysisPathRow).
Timeout 60 Check (apr_model pgl27_row_exact
  : AnalysisModelFamily PGL27Analysis.observed).
Timeout 60 Check (erefl : apr_completion pgl27_row_exact = AnalysisBridged).
Timeout 60 Check (erefl : apr_transfer pgl27_row_exact = StaticExecutedOnly).
Timeout 60 Check
  (erefl : apr_assumptions pgl27_row_exact = BaselineClassicalOnly).

Timeout 60 Check (pgl27_row_word : AnalysisPathRow).
Timeout 60 Check (apr_model pgl27_row_word
  : AnalysisModelFamily PGL27Analysis.observed).
Timeout 60 Check (erefl : apr_completion pgl27_row_word = AnalysisBridged).
Timeout 60 Check (erefl : apr_transfer pgl27_row_word = IdealFinite).
Timeout 60 Check
  (erefl : apr_assumptions pgl27_row_word = BaselineClassicalOnly).

Timeout 60 Check (five_card_row_uniform : AnalysisPathRow).
Timeout 60 Check (apr_model five_card_row_uniform
  : AnalysisModelFamily FiveCardAnalysis.observed).
Timeout 60 Check
  (erefl : apr_completion five_card_row_uniform = AnalysisBridged).
Timeout 60 Check
  (erefl : apr_transfer five_card_row_uniform = StaticExecutedOnly).
Timeout 60 Check
  (erefl : apr_assumptions five_card_row_uniform = BaselineClassicalOnly).

Timeout 60 Check (five_card_row_biased : AnalysisPathRow).
Timeout 60 Check (apr_model five_card_row_biased
  : AnalysisModelFamily FiveCardAnalysis.observed).
Timeout 60 Check
  (erefl : apr_completion five_card_row_biased = AnalysisBridged).
Timeout 60 Check
  (erefl : apr_transfer five_card_row_biased = StaticExecutedOnly).
Timeout 60 Check
  (erefl : apr_assumptions five_card_row_biased = BaselineClassicalOnly).

Timeout 60 Check (five_card_row_repeated : AnalysisPathRow).
Timeout 60 Check (apr_model five_card_row_repeated
  : AnalysisModelFamily FiveCardAnalysis.observed).
Timeout 60 Check (erefl : apr_completion five_card_row_repeated = Sampled).
Timeout 60 Check
  (erefl : apr_transfer five_card_row_repeated = NoModelComparison).
Timeout 60 Check
  (erefl : apr_assumptions five_card_row_repeated = BaselineClassicalOnly).

Timeout 60 Check (s5_row_det : AnalysisPathRow).
Timeout 60 Check (apr_model s5_row_det
  : option (AnalysisModelFamily S5Analysis.observed)).
Timeout 60 Check (erefl : apr_completion s5_row_det = Observed).
Timeout 60 Check (erefl : apr_transfer s5_row_det = NoModelComparison).
Timeout 60 Check
  (erefl : apr_assumptions s5_row_det = AcceptsAxioms [:: AxS5GroupOrder]).

Timeout 60 Check (s5_row_rand : AnalysisPathRow).
Timeout 60 Check (apr_model s5_row_rand
  : AnalysisModelFamily S5Analysis.rand_observed).
Timeout 60 Check (erefl : apr_completion s5_row_rand = AnalysisBridged).
Timeout 60 Check (erefl : apr_transfer s5_row_rand = StaticExecutedOnly).
Timeout 60 Check
  (erefl : apr_assumptions s5_row_rand = AcceptsAxioms [:: AxS5GroupOrder]).

Timeout 60 Check (s5_row_word : AnalysisPathRow).
Timeout 60 Check (apr_model s5_row_word
  : AnalysisModelFamily S5Analysis.observed).
Timeout 60 Check (erefl : apr_completion s5_row_word = AnalysisBridged).
Timeout 60 Check (erefl : apr_transfer s5_row_word = IdealFinite).
Timeout 60 Check (erefl : apr_assumptions s5_row_word
  = AcceptsAxioms [:: AxS5GroupOrder; AxRayleighQ2R]).

(******************************************************************************)
(*     The model families exercised at their index types                      *)
(*                                                                            *)
(* One application per parameterized family pins each family's own index     *)
(* type (a wrong index type is a compile error at the pair), and one         *)
(* application at tt pins a unit family. The generic check below them        *)
(* establishes that every family's adapter is typed at the execution         *)
(* projected from its own row's observed execution, for every row and every  *)
(* family.                                                                   *)
(******************************************************************************)

Timeout 60 Check (fun (R : realType) (p : R.-fdist bool) =>
  amf_sample (apr_model pgl27_row_word) R p).

Timeout 60 Check (fun (R : realType) (secretP : R.-fdist 'I_5) (L : nat) =>
  amf_sample (apr_model s5_row_word) R (secretP, L)).

Timeout 60 Check (fun R : realType =>
  amf_sample (apr_model s5_row_rand) R tt).

Timeout 60 Check (fun (row : AnalysisPathRow)
    (fam : AnalysisModelFamily (apr_observed row)) (R : realType)
    (x : amf_index fam R) =>
  amf_sample fam R x
    : @SampleAdapter R _ (OE.oe_execution (apr_observed row))).

(******************************************************************************)
(*     The executed finite-word theorem family at its spelled types           *)
(*                                                                            *)
(* The S_5 word row names an executed theorem alias, pinned here at its full  *)
(* spelled type, the observer being sa_seat_dist of the interpreter-executed  *)
(* finite-word adapter and the ideal the encoder-image reading.               *)
(******************************************************************************)

Timeout 60 Check (S5Analysis.exec_endpoint_bound :
  forall (R : realType) (secretP : R.-fdist 'I_5) (L : nat)
         (i : 'I_(pi_T' (mp_PI S5Analysis.profile)).+1),
    var_dist
      (sa_seat_dist (S5Analysis.word_sample secretP L) 0 i)
      (S5Analysis.ideal_reading secretP)
    <= Num.sqrt 5%:R * (s5_mixing.s5_alpha_R R) ^+ L).

(******************************************************************************)
(*     Mutation guards: the states the dependent model slot must reject       *)
(*                                                                            *)
(* A Sampled or AnalysisBridged row with no model witness, a family over the *)
(* wrong execution, and an executed word theorem alias reverted to the       *)
(* cut-level type are compile errors, demonstrated by Fail. The fourth guard *)
(* is satisfiable because the executed theorem family exists at the          *)
(* seat-indexed executed type, so reverting it to the cut-level pushforward  *)
(* shape (an ordinary fdistmap of sa_cut_dist) is a real type mismatch and   *)
(* not a vacuous check.                                                      *)
(******************************************************************************)

Fail Check (@MkAnalysisPathRow S5Analysis.observed Sampled None
  NoModelComparison (AcceptsAxioms [:: AxS5GroupOrder])).

Fail Check (@MkAnalysisPathRow S5Analysis.observed Sampled tt
  NoModelComparison (AcceptsAxioms [:: AxS5GroupOrder])).

Fail Check (@MkAnalysisPathRow S5Analysis.rand_observed AnalysisBridged None
  StaticExecutedOnly (AcceptsAxioms [:: AxS5GroupOrder])).

Fail Check (@MkAnalysisPathRow S5Analysis.observed Sampled
  PGL27Analysis.word_family NoModelComparison
  (AcceptsAxioms [:: AxS5GroupOrder])).

(* The fourth mutation: an executed word theorem alias reverted to the
   cut-level type, the executed observer sa_seat_dist not being the
   cut-position pushforward. *)
Fail Check (S5Analysis.exec_endpoint_bound :
  forall (R : realType) (secretP : R.-fdist 'I_5) (L : nat) (s : 'I_5),
    var_dist (fdistmap (fun sigma : {perm 'I_5} => sigma s)
                (sa_cut_dist (S5Analysis.word_sample secretP L)))
             (fdist_uniform (card_ord 5))
    <= Num.sqrt 5%:R * (s5_mixing.s5_alpha_R R) ^+ L).

