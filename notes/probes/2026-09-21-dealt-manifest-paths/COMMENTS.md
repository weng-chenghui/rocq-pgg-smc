# Landed comment text (2026-09-21)

Every block below is copied from the file it now lives in.

## 1. Path 13 and Path 14, as `manifest/pgg_analysis_manifest.v` carries them

```
(*     Path 13: twelve-card chirality instance, dealer-dealt model, colour    *)
(*     observer                                                               *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol family and model | PSL(2,11) twelve-card chirality deck; the    *)
(*                               chirality drawn from a prior on it and the   *)
(*                               cut drawn uniformly over the 660 elements of *)
(*                               the group, the two independent |             *)
(* | profile alias      | PSL211Analysis.profile |                            *)
(* | execution alias    | PSL211Analysis.dealt_exec_plug |                    *)
(* | observed alias     | PSL211Analysis.dealt_observed |                     *)
(* | sample alias       | PSL211Analysis.dealt_sample; the path's typed model *)
(*                        witness is PSL211Analysis.dealt_family, the family  *)
(*                        indexed by the prior on the chirality |             *)
(* | observers          | PSL211Analysis.dealt_colour_of_reading              *)
(*                          : {ffun 'I_12 -> bool}, the colour of the card    *)
(*                            each seat of the coalition holds;               *)
(*                        PSL211Analysis.dealt_static_view                    *)
(*                          : {ffun 'I_12 -> 'I_12}, the card identities the  *)
(*                            colour map is read off;                         *)
(*                        PSL211Analysis.dealt_secret                         *)
(*                          : bool, the chirality the dealer was given, a     *)
(*                            random variable on dealt_prior at the path's    *)
(*                            index |                                         *)
(* | distribution-to-observer bridges | PSL211Analysis.dealt_cut_distE |      *)
(* | bound or certificate | none: the theorem is an independence and carries  *)
(*                          no number |                                       *)
(* | final bridge theorem | PSL211Analysis.dealt_colour_indep |               *)
(* | correctness theorem  | PSL211Analysis.dealt_observed_recovers |          *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | none: the cut this model draws is the uniform law *)
(*                          on the group already, so no idealized model is    *)
(*                          compared and there is no transfer premise to      *)
(*                          lack |                                            *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | StaticExecutedOnly |                              *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed path           | psl211_dealt_colour_path |                        *)
(*                                                                            *)
(* Capabilities, one line per (theorem, distribution, observer, notion):      *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | dealt_colour_indep | the sample law of dealt_sample, which is            *)
(*   dealt_prior secretP, the chirality drawn from secretP and the cut drawn  *)
(*   uniformly over the 660 elements of the shuffle group, the two            *)
(*   independent                                                              *)
(*   | dealt_colour_of_reading at a coalition of at most five of the twelve   *)
(*     seats | exact privacy |                                                *)
(* | dealt_observed_recovers | none, the statement is distribution-free       *)
(*   | the executed endpoint list | correctness |                             *)
(*                                                                            *)
(* Level justification. profile gives Algebraic; dealt_exec_plug is indexed   *)
(* by profile, giving Executable; dealt_observed is the ObservedExecution     *)
(* over that profile and plug, giving Observed; dealt_sample is a             *)
(* SampleAdapter over that plug and dealt_cut_distE identifies its cut        *)
(* distribution with the uniform law on the shuffle group, giving Sampled;    *)
(* dealt_colour_indep is a privacy theorem stated at sa_sampleP               *)
(* (dealt_sample secretP), the model's own sample law, and at the colour      *)
(* observer read off that model's own coalition reader, so the theorem, the   *)
(* distribution and the observer are this path's own, giving AnalysisBridged. *)
(* The transfer status is StaticExecutedOnly, the path comparing no idealized *)
(* model.                                                                     *)
(*                                                                            *)
(* Under these parameters the run argument of the execution IS the chirality, *)
(* so the secret the independence is of is the run argument itself and not a  *)
(* coordinate of a drawn deck description, which is what separates this path  *)
(* from Path 9 over the same instance. The capability is exact privacy at the *)
(* colour observer and at no other: at the card-identity observer             *)
(* dealt_static_view the same independence fails at every prior giving mass   *)
(* to both chiralities, by psl211_dealt_reading_indep_false of                *)
(* instances/psl211/psl211_colour_reading.v, and that is the theorem Path 14  *)
(* below records in its distributional form. The threshold the capability is  *)
(* stated below is the largest one: at the six seats of the mirror            *)
(* representative independence at the colour observer already fails at every  *)
(* prior giving mass to both chiralities, by psl211_colour_reading_dep_k6 of  *)
(* the same file, and six is what the derived profile declares. The program   *)
(* that publishes this path is psl211_colour_exact_published of               *)
(* psl211_tableau_dealt.v in instances/psl211/tableau/.                       *)
(*                                                                            *)
(*     Path 14: twelve-card chirality instance, dealer-dealt model, input     *)
(*     distinguishability                                                     *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol family and model | PSL(2,11) twelve-card chirality deck; the    *)
(*                               chirality drawn from a prior on it and the   *)
(*                               cut drawn uniformly over the 660 elements of *)
(*                               the group, the two independent |             *)
(* | profile alias      | PSL211Analysis.profile |                            *)
(* | execution alias    | PSL211Analysis.dealt_exec_plug |                    *)
(* | observed alias     | PSL211Analysis.dealt_observed |                     *)
(* | sample alias       | PSL211Analysis.dealt_sample; the path's typed model *)
(*                        witness is PSL211Analysis.dealt_family |            *)
(* | observers          | PSL211Analysis.dealt_static_view                    *)
(*                          : {ffun 'I_12 -> 'I_12}, the reading of the deck  *)
(*                            the dealer laid, which static_coalition_obs of  *)
(*                            protocol/pgg_instance.v is at this model |      *)
(* | distribution-to-observer bridges | PSL211Analysis.dealt_cut_distE |      *)
(* | bound or certificate | none: the program over this path publishes an     *)
(*                          obstruction, which carries neither a witness nor  *)
(*                          a certificate |                                   *)
(* | final bridge theorem | PSL211Analysis.dealt_perdeck_reading_ge |         *)
(* | correctness theorem  | PSL211Analysis.dealt_observed_recovers |          *)
(* | model transfer       | none claimed |                                    *)
(* | missing premise      | none: the path's theorem is a limitation. No      *)
(*                          input-indistinguishability proposition holds at   *)
(*                          this model at this observer at a number below     *)
(*                          1/660, in the sum of absolute differences, and    *)
(*                          the advantage of a distinguisher comparing the    *)
(*                          two run arguments that theorem names is at least  *)
(*                          1/1320. The path compares no idealized model, so  *)
(*                          there is no transfer premise to lack |            *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | NegativeTransfer |                                *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed path           | psl211_dealt_obstruction_path |                   *)
(*                                                                            *)
(* Capabilities, one line per (theorem, distribution, observer, notion):      *)
(*                                                                            *)
(* | theorem | distribution | observer | notion |                             *)
(* |---|---|---|---|                                                          *)
(* | dealt_perdeck_reading_ge | the cut law of dealt_sample, which            *)
(*   dealt_cut_distE names as the uniform law on the 660 elements of the      *)
(*   shuffle group                                                            *)
(*   | dealt_static_view at psl211_perdeck_coalition, three of the twelve     *)
(*     seats | input distinguishability at 1/660 |                            *)
(* | dealt_observed_recovers | none, the statement is distribution-free       *)
(*   | the executed endpoint list | correctness |                             *)
(*                                                                            *)
(* Level justification. The first four levels are Path 13's, the two paths    *)
(* naming one execution, one observed execution and one model family.         *)
(* dealt_perdeck_reading_ge is a limitation theorem stated at that cut        *)
(* distribution and at the coalition's own reading of the laid deck, and      *)
(* AnalysisBridged admits a limitation theorem about the same distribution    *)
(* and the same observer, giving AnalysisBridged. The transfer status is      *)
(* NegativeTransfer, which is defined as a theorem transporting an            *)
(* obstruction to the path's observer, and the theorem is that one. Path 13   *)
(* records the same instance, the same execution and the same model, and this *)
(* path differs from it in the observer and in the transfer status: the two   *)
(* describe different theorems about one model, Path 13 the exact             *)
(* independence the colours of a coalition of at most five of the twelve      *)
(* seats have of the chirality, and this path the distance between the        *)
(* readings of the two chiralities at three seats' card identities. Because   *)
(* the run argument is the chirality here, the two run arguments this path's  *)
(* theorem compares are the two values of the secret, so the limitation is    *)
(* about this model's privacy at the card-identity observer and not about     *)
(* two inputs alone. At Path 12 the two run arguments are the two             *)
(* chiralities of one deal, a deck description being a chirality and a deal,  *)
(* so the limitation there is at one fixed deal. The program that publishes   *)
(* this path is psl211_dealt_obstruction_published of psl211_tableau_dealt.v  *)
(* in instances/psl211/tableau/, which certifies no security property.        *)
```

## 2. `manifest/pgg_analysis_manifest.v`: the no-capability row of the PSL(2,11) facade (D14)

```
(*                rand_correct, rand_recovers, word_cut_imageE,               *)
(*                word_transfer_conditional |                                 *)
(* | PSL211Analysis | seat_endpoint, coalition_endpoints, prior, cut_distE,   *)
(*                    exact_coalition_distE, content_traceE, content_trace,   *)
(*                    exact_transfer_status, dealt_prior,                     *)
(*                    dealt_colour_transfer_status,                           *)
```

## 3. `manifest/pgg_analysis_manifest.v`: the banner of the dealer-dealt checker block (D19), and the correctness pin it now carries (D8)

```
  (erefl : PSL211Analysis.dealt_obstruction_transfer_status
           = NegativeTransfer).

(******************************************************************************)
(*     The deterministic checker: the dealer-dealt model of that instance     *)
(*                                                                            *)
(* The same twelve-card instance driven in its other mode. The run argument   *)
(* is the chirality itself, so the aliases below are pinned at a bare bool    *)
(* where the all-decks ones are pinned at a deck description.                 *)
(******************************************************************************)
...
       : R.-fdist (pgg_gT (mp_M PSL211Analysis.profile)))).

Timeout 60 Check (PSL211Analysis.dealt_observed_recovers :
  forall (x : bool) (w0 : pgg_gT (mp_M PSL211Analysis.profile)),
    w0 \in pgg_G (mp_M PSL211Analysis.profile) ->
    exec_decode PSL211Analysis.dealt_exec_plug
      (OE.oe_endpoints_size PSL211Analysis.dealt_observed x w0) = x).

```

## 4. `instances/psl211/psl211_dealt_model.v`: the title (D11), the Definitions index (D9) and the Key-results entry (D10)

```
(* psl211_dealt_model: the dealer-dealt model of the twelve-card chirality    *)
(*                     instance, and the two theorems the analysis manifest's *)
(*                     paths over it name                                     *)
...
(* Definitions:                                                               *)
(*   psl211_dealt_sample       == the fixed-dealer colour model as a sample   *)
(*                                adapter over the dealer-dealt execution     *)
(*   psl211_dealt_family       == that model as an analysis model family, one *)
(*                                member per prior on the chirality           *)
(*   psl211_dealt_decktbl      == the encoder deck of a chirality as a        *)
(*                                twelve-entry position-to-code table         *)
(*   psl211_dealt_view         == the reading giving cards 0, 1 and 6 to      *)
(*                                seats 0, 1 and 2                            *)
(*   psl211_dealt_fiber        == the cuts carrying one encoder deck to it    *)
(*   psl211_colour_of_reading  == the colour map on a coalition's endpoints   *)
...
(*                                under no cut and the other under one        *)
(*   psl211_dealt_massE        == the mass of that reading is the fibre's     *)
(*                                cardinality over the order of the group     *)
(*   psl211_dealt_colour_viewE == the model's colour view of a coalition is   *)
(*                                the colour map of that coalition's          *)
(*                                endpoints                                   *)
(*   psl211_dealt_colour_indep == below the threshold the colour map of a     *)
(*                                coalition's endpoints is independent of the *)
```

## 5. `instances/psl211/psl211_analysis.v`: the facade header's two-dealer paragraph (D12 width, D15 clause)

```
(* Two dealers are aliased here and their aliases are kept apart by name.     *)
(* An unprefixed alias is about the ALL-DECKS dealer, whose run argument is   *)
(* a whole deck description drawn uniformly. An alias whose name begins       *)
(* dealt_ is about the DEALER-DEALT one, whose run argument is the bare       *)
(* chirality, so that at that dealer the two run arguments a limitation       *)
(* theorem compares are the two values of the secret. The two dealers are     *)
(* different executions over one profile and no alias of one is an alias of   *)
(* the other. The alias dealt_secret is the framework's constant of that name *)
(* at this instance's arguments.                                              *)
(*                                                                            *)
```

## 6. `instances/psl211/psl211_analysis.v`: the dealer-dealt Check block's introducing comment and the correctness pin (D8), and the retargeted alias (D21)

```
    chirality the dealer was given, at every chirality and every cut in the
    group. The value the dealer-dealt security lines are about is the value
    that run reconstructs. *)
Definition dealt_observed_recovers := @psl211_dealt_observed_recovers.

...
(* The dealer-dealt aliases at their spelled types. The execution and the
   model keep their dependent indices, recovery keeps its group-membership
   hypothesis, and the two security aliases are pinned at the observers they
   are stated at, the colour map for the first and the framework's static
   reader for the second. *)
Timeout 60 Check (PSL211Analysis.dealt_exec_plug :
  ExecutionPlug PSL211Analysis.profile).

Timeout 60 Check (PSL211Analysis.dealt_observed : OE.ObservedExecution).

Timeout 60 Check (PSL211Analysis.dealt_colour_of_reading :
  {set 'I_12} -> {ffun 'I_12 -> 'I_12} -> {ffun 'I_12 -> bool}).

Timeout 60 Check (PSL211Analysis.dealt_sample :
  forall (R : realType) (secretP : R.-fdist bool),
    SampleAdapter R PSL211Analysis.dealt_exec_plug).

Timeout 60 Check (PSL211Analysis.dealt_family :
  AnalysisModelFamily PSL211Analysis.dealt_observed).

(* 5 Correctness: recovery keeps its group-membership hypothesis and returns
   the chirality the dealer was given. *)
Timeout 60 Check (PSL211Analysis.dealt_observed_recovers :
  forall (x : bool) (w0 : pgg_gT (mp_M PSL211Analysis.profile)),
    w0 \in pgg_G (mp_M PSL211Analysis.profile) ->
    exec_decode PSL211Analysis.dealt_exec_plug
      (OE.oe_endpoints_size PSL211Analysis.dealt_observed x w0) = x).

Timeout 60 Check (PSL211Analysis.dealt_colour_indep :
```

## 7. `instances/psl211/psl211_models.v`: the new theorem, its docstring and its header index entry (D21)

```
(*   psl211_dealt_observed_recovers == the packaged dealer-dealt run decodes  *)
(*                              to the chirality the dealer was given         *)
...

(** psl211_dealt_observed_recovers — the packaged dealer-dealt run decodes to
    the chirality the dealer was given, at every chirality and every cut in
    the group. It is the correctness half of what the dealer-dealt model
    publishes: the chirality a coalition is proved to learn nothing about is
    the one the protocol reconstructs. *)
Theorem psl211_dealt_observed_recovers (x : bool)
    (w0 : pgg_gT psl211_M) (Gw0 : w0 \in pgg_G psl211_M) :
  @exec_decode mpP (instance_exec psl211_dealt_params)
    (@exec_endpoints mpP (instance_exec psl211_dealt_params) x w0 0)
    (OE.oe_endpoints_size psl211_dealt_observed x w0) = x.
Proof. exact: (OE.oe_run_recovers psl211_dealt_observed x w0 Gw0). Qed.

```

## 8. `instances/psl211/psl211_colour_reading.v`: the opening paragraph (D7) and the split proof line (D13)

```
(* The colour theorems of instances/psl211/psl211_secrecy.v are read in       *)
(* psl211P, the law of a chirality bit drawn from a prior together with an    *)
(* independent uniform PSL(2,11) shuffle. A proposition of the Tableau is     *)
(* stated at a sample adapter and at a reading. The adapter over that law is  *)
(* psl211_dealt_sample of instances/psl211/psl211_dealt_model.v, over the     *)
(* dealer-dealt run parameters, whose run argument carrier is the chirality   *)
(* itself. What this file supplies is the reading: the colour reading, which  *)
(* gives each position of a coalition the colour of the card the encoder      *)
(* deck of that chirality puts at the cut image of that position.             *)
...
      (static_coalition_obs C ((psl211_dealt_sample secretP).(sa_arg) u)
         ((psl211_dealt_sample secretP).(sa_cut) u)).
(* The reading record's read function is psl211_colour_of_reading by one iota
   step, so the raw identification is this one at a fixed sample point. *)
Proof.
exact: (congr1 (fun f => f u) (psl211_dealt_colour_viewE secretP C)).
Qed.
```

## 9. `instances/psl211/psl211_reading_constancy.v`: the two file names (D6)

```
(* seats. The dealt statement rules out one named ideal and no certificate.   *)
(* An ideal can be pinned to these parameters through the dealer-dealt sample *)
(* adapter psl211_dealt_sample of instances/psl211/psl211_dealt_model.v,      *)
(* and no certificate is built over it. The dealt parameters read their       *)
(* endpoints through profile_endpointsE, so instances/psl211/psl211_models.v  *)
...
    is 2-transitive and not 3-transitive, where PGL(2,7) proves the same field
    through pgl27_word_view_const. The statement rules out one named ideal and
    no certificate. An ideal can be pinned to these parameters through the
    dealer-dealt sample adapter psl211_dealt_sample of
    instances/psl211/psl211_dealt_model.v, and no certificate is built over
    it. The dealt parameters read their endpoints through profile_endpointsE, so
    instances/psl211/psl211_models.v carries an endpoints statement and an
```

## 10. `instances/psl211/tableau/psl211_tableau_dealt.v`: the path sentences

```
(* The two programs share every line up to the Sampled level, and they must:  *)
(* a reading is a coordinate of the security claim and not of the model, so   *)
(* two programs that differ in the reading alone still name one execution,    *)
(* one model family and one link lemma. The colour program publishes the      *)
(* manifest's thirteenth path, psl211_dealt_colour_path, and the obstruction  *)
(* program its fourteenth, psl211_dealt_obstruction_path, both of             *)
(* manifest/pgg_analysis_manifest.v, and the two _pathE lemmas below decide   *)
(* each equality by conversion.                                               *)
...

(** psl211_dealt_obstruction_published_pathE — the path it publishes is the
    manifest's fourteenth: the dealer-dealt run, the AnalysisBridged level,
    the model family and NegativeTransfer. *)
Lemma psl211_dealt_obstruction_published_pathE :
  published_obstruction_path psl211_dealt_obstruction_published
  = psl211_dealt_obstruction_path.
```

## 11. `instances/psl211/tableau/psl211_tableau_executable.v`: the instance's path list and the dealer-dealt paragraph

```
(* One run mode is named here, the all-decks one, in the supplied-layout mode *)
(* of the framework: the run argument is a whole deck description, a          *)
(* chirality bit with a deal, the layout lays that description as the dealt   *)
(* deck, and the value the run is meant to recover is the chirality bit.      *)
(* Three of the five paths the manifest carries for this instance,            *)
(* psl211_alldecks_path, psl211_word_path and                                 *)
(* psl211_alldecks_obstruction_path, are over this one run. The first two     *)
(* part at the model, and the third parts from the first at the transfer      *)
(* status. The other two, psl211_dealt_colour_path and                        *)
(* psl211_dealt_obstruction_path, are over the dealer-dealt run and not over  *)
(* this one.                                                                  *)
(*                                                                            *)
(* psl211_exec.v carries a second parameter record, psl211_dealt_params, in   *)
(* the dealer-dealt mode, where the run argument is the secret itself. It     *)
(* carries that record's own reconstruction and termination facts. The two    *)
(* programs of psl211_tableau_dealt.v continue from it and publish those      *)
(* other two paths, and the refutation psl211_dealt_constancy_false of        *)
(* psl211_reading_constancy.v is a further statement made at it. It is named  *)
(* here and not built into a value.                                           *)
```

## 12. `instances/psl211/psl211_models.v`: the two recovery docstrings, each carrying its theorem's coalition size and reading (comments-only follow-up)

```
(** psl211_alldecks_observed_recovers — the packaged all-decks run decodes to
    the chirality its input names, at every deck description and every cut in
    the group. This is the correctness half of what the instance publishes:
    the value a coalition of fewer than six seats is proved to learn nothing
    about, the deck description being drawn uniformly, is the value the
    protocol actually reconstructs. *)
Theorem psl211_alldecks_observed_recovers (x : psl211_inputT)
    (w0 : pgg_gT psl211_M) (Gw0 : w0 \in pgg_G psl211_M) :
  @exec_decode mpP eP (@exec_endpoints mpP eP x w0 0)
    (OE.oe_endpoints_size psl211_alldecks_observed x w0) = x.1.
Proof. exact: (OE.oe_run_recovers psl211_alldecks_observed x w0 Gw0). Qed.

(** psl211_dealt_observed_recovers — the packaged dealer-dealt run decodes to
    the chirality the dealer was given, at every chirality and every cut in
    the group. It is the correctness half of what the dealer-dealt model
    publishes: the chirality that a coalition of fewer than six seats is
    proved to learn nothing about from the colours of its cards is the one
    the protocol reconstructs. *)
Theorem psl211_dealt_observed_recovers (x : bool)
    (w0 : pgg_gT psl211_M) (Gw0 : w0 \in pgg_G psl211_M) :
  @exec_decode mpP (instance_exec psl211_dealt_params)
    (@exec_endpoints mpP (instance_exec psl211_dealt_params) x w0 0)
    (OE.oe_endpoints_size psl211_dealt_observed x w0) = x.
```
