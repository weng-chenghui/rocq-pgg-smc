(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGGAlgebraic: the algebraic instance of one card protocol                  *)
(*                                                                            *)
(* An instance of the card-shuffling framework is described by two values     *)
(* and nothing else. PGGAlgebraic holds what the instance is: a generating    *)
(* tuple of deck permutations, a threshold scheme whose shares are deck       *)
(* positions, the seats' starting positions, and the coordinate law that      *)
(* ties the scheme's share indices to the deck action. ExecutionParams holds  *)
(* how one run of it is driven: the run argument type, the input mode, the    *)
(* content readout, the direct computation, the value the run recovers and    *)
(* the interpreter fuel. From these two the interface, the reconstruction     *)
(* plug, the monodromy profile, the execution plug and the observed           *)
(* execution are all derived, so an instance writes down data and the         *)
(* framework writes down the stack.                                           *)
(*                                                                            *)
(* One of the three run obligations is discharged here for every instance,    *)
(* and a second is replaced by a cheaper equivalent. generic_static_recon     *)
(* proves that decoding the static endpoint reading returns the dealt value,  *)
(* from the reconstruction invariance of the plug's scheme and a single       *)
(* coordinate hypothesis; dealt_static_recon supplies that hypothesis from    *)
(* pga_coordE, so a dealer-dealt instance owes no reconstruction proof at     *)
(* all. profile_endpointsE leaves the endpoint obligation with the instance   *)
(* and only makes it cheaper: it carries the endpoint equation from a         *)
(* statement whose content readout is a variable to the statement about the   *)
(* dealt readout. The equation is decided by reduction, and it is reduction   *)
(* of a concrete dealt card that makes that costly, or impossible where an    *)
(* encoding passes through an opaque insub and never reduces at all. Keeping  *)
(* the readout a variable removes the dealt card from the reduction, so one   *)
(* reduction per profile replaces one reduction per plug: measured on         *)
(* 2026-09-14, the PGL(2,7) form closes by vm_compute in 8.8 s with a 3.8 s   *)
(* Qed, and its dealt instance follows by instantiation with no reduction of  *)
(* its own.                                                                   *)
(*                                                                            *)
(* A run is driven in one of three modes, and the modes fall into two         *)
(* families. The sharing family has no committer and the dealer lays the      *)
(* cards itself: dealt_secret_params deals the scheme's own encoding of the   *)
(* secret, and supplied_input_params lays a layout that arrives with the run  *)
(* argument, of which the dealt mode is the case at the canonical encoding.   *)
(* The input family is encoded_input_params alone: the committers hand over   *)
(* their inputs through commit processes and the run recovers an ideal        *)
(* function of them.                                                          *)
(*                                                                            *)
(* Reconstruction is one lemma for the two layout modes, layout_static_recon, *)
(* from the layout being a valid sharing of the value the run recovers; the   *)
(* dealer-dealt mode keeps dealt_static_recon. The endpoint obligation splits *)
(* along the families: the sharing family instantiates                        *)
(* profile_endpoints_stmt, while the input family needs                       *)
(* profile_commit_endpoints_stmt, whose reduction runs the commit processes,  *)
(* and one instance fact, that decoding the payload list returns the input    *)
(* the committers hold.                                                       *)
(*                                                                            *)
(* What an instance owes is termination, instance_terminates_stmt, which has  *)
(* no route through the algebra, and one reduction proof at its own profile:  *)
(* profile_endpoints_stmt in the sharing family, and                          *)
(* profile_commit_endpoints_stmt in the input family.                         *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   PGGAlgebraic             == the algebraic data of one instance           *)
(*   instance_M               == the monodromy representation, a Notation     *)
(*   instance_PI              == the seat interface                           *)
(*   instance_plug            == the reconstruction plug                      *)
(*   instance_profile         == the MonodromyProfile                         *)
(*   ExecutionParams          == the run-level data over an algebra           *)
(*   instance_exec            == the ExecutionPlug of a parameter record      *)
(*   instance_terminates_stmt == every process of the run reaches Finish      *)
(*   instance_endpoints_stmt  == the run's endpoints are the direct           *)
(*                               computation                                  *)
(*   instance_recon_stmt      == static decoding returns the expected value   *)
(*   instance_observed        == the ObservedExecution of a parameter record  *)
(*   dealt_secret_params      == the parameters of a dealer-dealt secret      *)
(*   static_coalition_obs     == a coalition's static endpoint reading        *)
(*   profile_endpoints_stmt   == the endpoint equation with abstract readout  *)
(*   layout_content           == the dealer's readout of a layout             *)
(*   layout_content_obs       == the direct computation over a layout         *)
(*   encoded_input_params     == the input family's parameters                *)
(*   supplied_input_params    == the sharing family's parameters at a         *)
(*                               supplied layout                              *)
(*   profile_commit_endpoints_stmt                                            *)
(*                            == the endpoint equation with committers        *)
(*                                                                            *)
(* Key results:                                                               *)
(*   generic_static_recon       == static decoding returns the dealt value    *)
(*   generic_static_recon_valid == the same for any valid sharing             *)
(*   dealt_static_recon         == the dealer-dealt case, from pga_coordE     *)
(*   layout_static_recon        == decoding the direct computation of a       *)
(*                                 valid layout                               *)
(*   encoded_static_recon       == the input family's case                    *)
(*   supplied_static_recon      == the supplied sharing case                  *)
(*   static_coalition_obsE      == the coalition reading, seat by seat        *)
(*   profile_endpointsE         == abstract readout to the dealt readout      *)
(*   supplied_endpointsE        == abstract readout to the supplied readout   *)
(*   encoded_endpointsE         == commit-mode readout to the committed       *)
(*                                 layout                                     *)
(*   dealt_supplied_paramsE     == the dealt mode is the supplied one         *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum ssralg.
From pgg_smc Require Import smc_interpreter pismc smc_session_types.
From pgg_smc Require Import pgg_interface pgg_session_types card_exchange_pismc.
From pgg_smc Require Import pgg_input_commitment pgg_run pgg_monodromy_profile.
From pgg_smc Require Import pgg_execution_plug pgg_observed_execution.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     The algebraic instance                                                 *)
(******************************************************************************)

(* The algebraic data of one protocol instance: the generators of its shuffle
   group, the threshold scheme it deals with, where the seats start, and the
   law relating share indices to deck positions. The record carries no run,
   no fuel and no probability model, so two instances that differ only in how
   a run is driven share one value of it. Every record of the execution stack
   below is a function of this value. *)
Record PGGAlgebraic := MkPGGAlgebraic {
  (* pga_m and pga_n are the generator count and the deck size in predecessor
     form: pga_m.+1 generating permutations act on pga_n.+2 card positions.
     The successor form is what forbids an empty alphabet and a deck on which
     no two seats can differ. *)
  pga_m       : nat ;
  pga_n       : nat ;
  (* pga_gens generates the shuffle group. No other field constrains the
     group, so the instance's whole algebraic strength is this tuple. *)
  pga_gens    : pga_m.+1.-tuple {perm 'I_pga_n.+2} ;
  (* pga_moves is an optional second alphabet generating the same group,
     carried with the equation that it does; None says the shuffles a step
     may take are pga_gens themselves. Mixing and spectral arguments run on a
     symmetrized or inverse-closed alphabet rather than the presentation
     alphabet, and this field lets one instance name both without
     introducing a second group. *)
  pga_moves   : option { k : nat & { w : k.+1.-tuple {perm 'I_pga_n.+2}
                | (<<[set tnth w i | i : 'I_k.+1]>>
                   = <<[set tnth pga_gens i | i : 'I_pga_m.+1]>>)%G } } ;
  (* pga_secretT is the carrier of the value a run reconstructs, and
     pga_scheme is the threshold scheme dealing it into deck positions. The
     scheme is where the privacy threshold of the instance lives. *)
  pga_secretT : Type ;
  pga_scheme  : ThresholdScheme pga_secretT 'I_pga_n.+2 ;
  (* pga_share_card states that the scheme deals one share per card position.
     It is what lets a share index be read as a deck position, and the
     execution stack transports tuples along it. *)
  pga_share_card : (ts_T' pga_scheme).+1 = pga_n.+2 ;
  (* pga_starts is where the seats begin, one starting position per share,
     and pga_starts_uniq says no two seats begin at the same card. *)
  pga_starts  : (ts_T' pga_scheme).+1.-tuple 'I_pga_n.+2 ;
  pga_starts_uniq : uniq pga_starts ;
  (* pga_content is the readout the dealer applies to a card position before
     dealing it, and it is the readout the reconstruction plug is built from,
     fixed once by the algebra. The run-level ex_content below is a second
     readout, chosen per run and free to depend on committed payloads; a
     reader deciding which one a statement is about reads it off the
     record. *)
  pga_content : 'I_pga_n.+2 -> 'I_pga_n.+2 ;
  (* pga_monodromy is the action of a shuffle on share indices, and
     pga_recon_invariant says reconstruction is unchanged by it: a shuffled
     deck reconstructs to the same secret as the dealt deck. *)
  pga_monodromy : {perm 'I_pga_n.+2} -> {perm 'I_(ts_T' pga_scheme).+1} ;
  pga_recon_invariant :
    @ts_recon_perm_invariant _ (pgg_G (Gen_PGGTypes pga_gens)) _ _
      pga_scheme pga_monodromy ;
  (* pga_coordE fixes seat i's share index under a shuffle to be the deck
     position that shuffle sends seat i's start to. The constant map
     fun _ => 1 satisfies ts_recon_perm_invariant for every scheme, so
     invariance alone leaves the share coordinates unrelated to the card
     action; this equation is what relates them, and it is the only
     hypothesis the static reconstruction lemma below needs. *)
  pga_coordE : forall (w0 : {perm 'I_pga_n.+2}) (i : 'I_(ts_T' pga_scheme).+1),
    pga_monodromy w0 i
    = cast_ord (esym pga_share_card)
        (@pgg_rho (Gen_PGGTypes pga_gens) w0 (tnth pga_starts i)) ;
  (* pga_players is the literal seat list and pga_playersE identifies it with
     the canonical enumeration. An executable run reads the stored list
     because enum 'I_T does not converge under vm_compute, and the equation
     leaves no freedom to drop or reorder a seat. *)
  pga_players  : seq 'I_(ts_T' pga_scheme).+1 ;
  pga_playersE : pga_players = enum 'I_(ts_T' pga_scheme).+1 ;
}.

(* Unset Strict Implicit infers the record argument of a projection whose
   field type binds a later argument mentioning it, which is the case for
   pga_content, pga_monodromy, pga_recon_invariant and pga_coordE; these lines
   keep it explicit. The three arity-one equations that follow mention the
   record only in their conclusion, where no inference is attempted, and are
   listed so that the record is supplied the same way at every projection. *)
Arguments pga_content : clear implicits.
Arguments pga_monodromy : clear implicits.
Arguments pga_recon_invariant : clear implicits.
Arguments pga_coordE : clear implicits.
Arguments pga_playersE : clear implicits.
Arguments pga_starts_uniq : clear implicits.
Arguments pga_share_card : clear implicits.

(* The monodromy representation an instance's generators define: the
   permutation group they generate, acting on the deck by evaluation. This is a
   notation rather than a definition because the isMonodromyRepr and
   hasGenerators structures are registered against the head symbol
   Gen_PGGTypes, and instance resolution finds them only where that head is
   visible. *)
Notation instance_M A := (Gen_PGGTypes (pga_gens A)).

(* The reconstruction plug of an instance: its scheme, its readout, its
   monodromy action and the invariance proof, assembled from the record. The
   reconstruction half of the framework is thereby determined by the algebra
   alone, with no further choice left to the instance. *)
Definition instance_plug (A : PGGAlgebraic)
    : ReconPlug (instance_M A) (pga_secretT A) :=
  @MkReconPlug (instance_M A) (pga_secretT A) (pga_scheme A) (pga_content A)
    (pga_monodromy A) (pga_recon_invariant A).

(* The seat interface of an instance: one seat per share, beginning at the
   recorded starting positions. Taking the seat count from the scheme is what
   makes instance_bridge reflexivity. *)
Definition instance_PI (A : PGGAlgebraic) : PGGInterface (instance_M A) :=
  @MkPGGI (instance_M A) (ts_T' (pga_scheme A)) (pga_starts A)
    (pga_starts_uniq A).

(* The monodromy profile of an instance: its representation, its secret
   carrier, its seat interface and its reconstruction plug. This is the value
   an instance file otherwise writes by hand, and the two are the same term,
   so every theorem about a hand-written profile applies to
   the derived one by conversion. *)
Definition instance_profile (A : PGGAlgebraic) : MonodromyProfile :=
  @MkMonodromyProfile (instance_M A) (pga_secretT A) (instance_PI A)
    (instance_plug A).

(* Seat count and share count agree. The execution plug takes this equation
   as data; here it holds by reflexivity because the interface was built from
   the scheme's own share count, so an instance cannot supply a mismatched
   pair. *)
Definition instance_bridge (A : PGGAlgebraic) :
  pi_T' (mp_PI (instance_profile A))
  = ts_T' (rp_scheme (mp_plug (instance_profile A))) := erefl.

(******************************************************************************)
(*     The execution parameters                                               *)
(******************************************************************************)

(* The input mode of a run: either no party commits an input and the dealer's
   secret is the only input, or each run argument determines a list of commit
   processes. The two modes are the two smart constructors of the execution
   plug, named here so that a parameter record can carry the choice as data. *)
Variant InputProcs (A : PGGAlgebraic) (inputT : Type) : Type :=
  | NoCommit
  | Commits of (inputT -> seq (aproc pgg_dtype (pgg_data (pga_n A).+2))).

(* The process list a mode supplies at each run argument: empty in the
   dealer-dealt mode, the stored list otherwise. Separating the eliminator
   from params_exec is what lets the mode be consumed inside the
   ep_input_procs field rather than at the head of the plug. *)
Definition params_input_procs (A : PGGAlgebraic) (inputT : Type)
    (commits : InputProcs A inputT)
    : inputT -> seq (aproc pgg_dtype (pgg_data (pga_n A).+2)) :=
  match commits with NoCommit => fun _ => [::] | Commits p => p end.

(* The execution plug of an instance at a chosen input mode, content readout
   and fuel. The mode is consumed inside the ep_input_procs field rather than
   at the head of the definition, so the plug remains one constructor
   application and stays convertible with a plug written by a smart
   constructor of pgg_execution_plug.v. *)
Definition params_exec (A : PGGAlgebraic) (inputT : Type)
    (commits : InputProcs A inputT)
    (content : inputT -> seq 'I_(pga_n A).+2
                 -> 'I_(pga_n A).+2 -> 'I_(pga_n A).+2)
    (fuel : nat) : ExecutionPlug (instance_profile A) :=
  @MkExecutionPlug (instance_profile A) inputT (instance_bridge A)
    (pga_players A) (pga_playersE A) content (params_input_procs commits) fuel.

(* The run-level data an instance chooses over its algebra: what a run takes
   as argument, which parties commit, how the dealer reads a card, what a
   seat observes statically, what value the run is meant to recover, and how
   much interpreter fuel it is given. None of it constrains the algebra, so
   one algebra supports several parameter records. *)
Record ExecutionParams (A : PGGAlgebraic) := MkExecutionParams {
  (* ex_inputT is the carrier of one run argument. It need not be the secret
     carrier: a run may take committed bits and reconstruct something else. *)
  ex_inputT   : Type ;
  (* ex_commits selects the input mode, so a parameter record records who
     supplies the input rather than leaving it to the plug that is built. *)
  ex_commits  : InputProcs A ex_inputT ;
  (* ex_content is the readout the dealer runs inside the interpreter, taking
     the run argument and the committed payloads to a card content. *)
  ex_content  : ex_inputT -> seq 'I_(pga_n A).+2
                  -> 'I_(pga_n A).+2 -> 'I_(pga_n A).+2 ;
  (* ex_content_obs is what a seat observes after a shuffle, as a function of
     the run argument and the shuffle alone. It names no interpreter state and
     takes no payload list, which is why it can carry a security statement
     that a trace cannot; instance_endpoints_stmt is the assertion that the
     interpreter's messages compute it. *)
  ex_content_obs : ex_inputT -> pgg_gT (instance_M A) * 'I_(pga_n A).+2
                     -> 'I_(pga_n A).+2 ;
  (* ex_expected is the value the run is meant to recover. It is the
     specification side of correctness, so a run that decodes to something
     else is a failed run rather than a different protocol. *)
  ex_expected : ex_inputT -> pga_secretT A ;
  (* ex_fuel is the interpreter budget. Replacing a sufficient budget by
     another sufficient one leaves every statement below unchanged. *)
  ex_fuel     : nat ;
}.

Arguments ex_content {A} E : rename.
Arguments ex_content_obs {A} E : rename.
Arguments ex_expected {A} E : rename.

(* The plug a parameter record builds: params_exec at the record's own mode,
   readout and fuel. Four of the six fields reach the plug, ex_inputT as its
   run argument type and ex_content, ex_commits and ex_fuel as its readout,
   process list and budget. ex_content_obs and ex_expected do not, because they
   are not execution data, and they enter at instance_observed. Routing the
   plug through the record rather than letting an instance call params_exec is
   what stops a run whose interpreter readout disagrees with the static
   observation its security statements are made about. *)
Definition instance_exec (A : PGGAlgebraic) (E : ExecutionParams A)
    : ExecutionPlug (instance_profile A) :=
  params_exec (ex_commits E) (ex_content E) (ex_fuel E).

(* Every process of the run reaches Finish within the given fuel. The first
   of the three run facts an ObservedExecution requires, and the one the
   algebra says nothing about: it depends on the fuel and on the interpreter,
   so it is decided by reduction at each parameter record. *)
Definition instance_terminates_stmt (A : PGGAlgebraic) (E : ExecutionParams A)
    : Prop :=
  forall (x : ex_inputT E) (w0 : pgg_gT (mp_M (instance_profile A))),
    (@exec_run (instance_profile A) (instance_exec E) x w0 0).1
    = nseq (size (@exec_procs (instance_profile A) (instance_exec E) x w0 0))
           Finish.

(* The endpoints the verifier collects from the executed run are the static
   group-action reading of the same run. The second run fact: it says the
   interpreter's message passing computes the action, which is what lets
   every later security statement be made about the direct computation
   instead of about a trace. *)
Definition instance_endpoints_stmt (A : PGGAlgebraic) (E : ExecutionParams A)
    : Prop :=
  forall (x : ex_inputT E) (w0 : pgg_gT (mp_M (instance_profile A))),
    @exec_endpoints (instance_profile A) (instance_exec E) x w0 0
    = @exec_static_endpoints (instance_profile A) (instance_exec E)
        (ex_content_obs E) x w0.

(* Decoding the static endpoint reading at a shuffle in the group returns the
   value the run is meant to recover. The third run fact, and the one
   dealt_static_recon derives from pga_coordE. *)
Definition instance_recon_stmt (A : PGGAlgebraic) (E : ExecutionParams A)
    : Prop :=
  forall (x : ex_inputT E) (w0 : pgg_gT (mp_M (instance_profile A))),
    w0 \in pgg_G (mp_M (instance_profile A)) ->
    forall sz_ep : size (@exec_static_endpoints (instance_profile A)
                          (instance_exec E) (ex_content_obs E) x w0)
                 = (pi_T' (mp_PI (instance_profile A))).+1,
    @exec_decode (instance_profile A) (instance_exec E)
      (@exec_static_endpoints (instance_profile A) (instance_exec E)
         (ex_content_obs E) x w0) sz_ep
    = ex_expected E x.

(* The observed execution of a parameter record, packed with its three run
   facts. This is the value every downstream analysis consumes, so supplying
   an algebra, a parameter record and the three proofs is the whole of what
   an instance owes the framework. *)
Definition instance_observed (A : PGGAlgebraic) (E : ExecutionParams A)
    (Ht : instance_terminates_stmt E) (He : instance_endpoints_stmt E)
    (Hr : instance_recon_stmt E) : OE.ObservedExecution :=
  @OE.MkObservedExecution (instance_profile A) (instance_exec E) 0
    (ex_content_obs E) (ex_expected E) Ht He Hr.

(******************************************************************************)
(*     The dealer-dealt secret                                                *)
(******************************************************************************)

(* The dealer's readout when the run argument is the secret itself: card j
   carries share j of the canonical encoding, transported along
   pga_share_card. Committed inputs play no part, so the payload list is
   ignored. *)
Definition dealt_content (A : PGGAlgebraic) (x : pga_secretT A)
    (_ : seq 'I_(pga_n A).+2) (j : 'I_(pga_n A).+2) : 'I_(pga_n A).+2 :=
  tnth (tcast (pga_share_card A) (ts_encode (pga_scheme A) x)) j.

(* What a seat starting at position p observes after the shuffle w0: the
   share sitting at the position w0 moves p to. The static counterpart of
   dealt_content, and the observation every dealer-dealt security statement
   is made about. *)
Definition dealt_content_obs (A : PGGAlgebraic) (x : pga_secretT A)
    (p : pgg_gT (instance_M A) * 'I_(pga_n A).+2) : 'I_(pga_n A).+2 :=
  tnth (tcast (pga_share_card A) (ts_encode (pga_scheme A) x))
       (@pgg_rho (instance_M A) p.1 p.2).

(* The parameters of a run that deals a secret and recovers it: the run
   argument is the secret, no party commits, the readout and the static
   observation are the dealt pair above, and the recovered value is the
   argument itself. An instance in this mode supplies only its algebra and a
   fuel. *)
Definition dealt_secret_params (A : PGGAlgebraic) (fuel : nat)
    : ExecutionParams A :=
  @MkExecutionParams A (pga_secretT A) (NoCommit A (pga_secretT A))
    (@dealt_content A) (@dealt_content_obs A) id fuel.

(******************************************************************************)
(*     The layout readout, and the two layout constructors over it            *)
(******************************************************************************)

(* The dealer's readout of a layout: card j carries share j of the layout,
   transported along pga_share_card. The two constructors below are one per
   family and differ in what determines the layout, a committed payload list
   for the input family or the run argument itself for the sharing family;
   they agree on how the dealer reads it once it is determined. *)
Definition layout_content (A : PGGAlgebraic) (inputT : Type)
    (layout : inputT -> (ts_T' (pga_scheme A)).+1.-tuple 'I_(pga_n A).+2)
    (x : inputT) (j : 'I_(pga_n A).+2) : 'I_(pga_n A).+2 :=
  tnth (tcast (pga_share_card A) (layout x)) j.

(* What a seat starting at position p observes after the cut w0: the share the
   layout puts at the position w0 moves p to. It names no interpreter state,
   so it is the direct computation the security statements of both families
   are made about, and instance_endpoints_stmt is the assertion that the
   interpreter's messages compute it. *)
Definition layout_content_obs (A : PGGAlgebraic) (inputT : Type)
    (layout : inputT -> (ts_T' (pga_scheme A)).+1.-tuple 'I_(pga_n A).+2)
    (x : inputT) (p : pgg_gT (instance_M A) * 'I_(pga_n A).+2)
    : 'I_(pga_n A).+2 :=
  layout_content layout x (@pgg_rho (instance_M A) p.1 p.2).

(* The input family's parameters: the committers hand over their inputs
   through commit processes, dec reads the joint input back out of the payload
   list they sent, layout turns it into a sharing, and the value the run
   recovers is the ideal function f. This is the only mode whose run carries a
   committer, and the only one that states an ideal function.

   The argument between layout and dec is the sharing claim of the encoding,
   that the layout is a valid sharing of f x. The record does not store it, so
   it is checked where the statement is written and read back from the
   parameter term by encoded_static_recon; a layout that shares something
   other than f x therefore leaves the reconstruction obligation of the run
   unprovable. *)
Definition encoded_input_params (A : PGGAlgebraic) (inputT : Type)
    (f : inputT -> pga_secretT A)
    (layout : inputT -> (ts_T' (pga_scheme A)).+1.-tuple 'I_(pga_n A).+2)
    (_ : forall x, ts_valid (pga_scheme A) (f x) (layout x))
    (dec : seq 'I_(pga_n A).+2 -> inputT)
    (procs : inputT -> seq (aproc pgg_dtype (pgg_data (pga_n A).+2)))
    (fuel : nat) : ExecutionParams A :=
  @MkExecutionParams A inputT (Commits procs)
    (fun _ committed => layout_content layout (dec committed))
    (layout_content_obs layout) f fuel.
Arguments encoded_input_params : clear implicits.

(* The sharing family's parameters at a supplied layout: no party commits, the
   dealer lays the cards itself from the layout the run argument names, and
   the value the run recovers is the one written beside it. That value is a
   reading of the run argument and not a function of any committer's input,
   which is what keeps this mode in the sharing family. The sharing claim is
   not an argument here, which is what leaves such a run owing a
   reconstruction obligation of its own. *)
Definition supplied_input_params (A : PGGAlgebraic) (inputT : Type)
    (layout : inputT -> (ts_T' (pga_scheme A)).+1.-tuple 'I_(pga_n A).+2)
    (expected : inputT -> pga_secretT A)
    (fuel : nat) : ExecutionParams A :=
  @MkExecutionParams A inputT (NoCommit A inputT)
    (fun x _ => layout_content layout x)
    (layout_content_obs layout) expected fuel.
Arguments supplied_input_params : clear implicits.

(* The dealer-dealt parameters are the sharing family at the canonical
   encoding. The two records are the same term, so a dealt secret is a
   supplied layout whose supplier is the scheme itself. *)
Lemma dealt_supplied_paramsE (A : PGGAlgebraic) (fuel : nat) :
  dealt_secret_params A fuel
  = supplied_input_params A (pga_secretT A) (ts_encode (pga_scheme A)) id fuel.
Proof. by []. Qed.

(* A coalition's static endpoint reading at one run argument and one shuffle:
   the coalition's seats read their own observation, every other seat reads
   ord0. The sample point is an explicit argument and shuffle pair rather
   than a point of a probability space, because a two-secret comparison
   cannot be stated at a space whose sample already contains the secret. *)
Definition static_coalition_obs (A : PGGAlgebraic) (E : ExecutionParams A)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1})
    (x : ex_inputT E) (g : pgg_gT (mp_M (instance_profile A)))
    : {ffun 'I_(pi_T' (mp_PI (instance_profile A))).+1
         -> 'I_(pgg_N' (mp_M (instance_profile A))).+1} :=
  [ffun i => if i \in C
             then ex_content_obs E x
                    (g, tnth (pi_starts (mp_PI (instance_profile A))) i)
             else ord0].

(* Seat i's entry of that reading. The defining equation is proved here, at
   abstract A, so that a downstream proof at a concrete profile reaches the
   entry by rewriting with this lemma instead of unfolding the finite
   function, whose unscoped expansion does not terminate on a concrete
   deck. *)
Lemma static_coalition_obsE (A : PGGAlgebraic) (E : ExecutionParams A)
    (C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1})
    (x : ex_inputT E) (g : pgg_gT (mp_M (instance_profile A)))
    (i : 'I_(pi_T' (mp_PI (instance_profile A))).+1) :
  static_coalition_obs C x g i
  = if i \in C
    then ex_content_obs E x (g, tnth (pi_starts (mp_PI (instance_profile A))) i)
    else ord0.
Proof. by rewrite /static_coalition_obs ffunE. Qed.

(******************************************************************************)
(*     Framework lemma 1: static reconstruction                               *)
(******************************************************************************)

Section generic_static_recon.

Variable mp : MonodromyProfile.
Variable e : ExecutionPlug mp.

Local Notation M  := (mp_M mp).
Local Notation PI := (mp_PI mp).
Local Notation ts := (rp_scheme (mp_plug mp)).

Variable content_obs :
  ep_inputT e -> pgg_gT M * 'I_(pgg_N' M).+1 -> 'I_(pgg_N' M).+1.
Variable expected : ep_inputT e -> mp_secretT mp.

(* The plug's own seat/share bridge in successor form. Both counts are the
   same natural number, so the cast it induces is the identity on indices. *)
Let bridge : (pi_T' PI).+1 = (ts_T' ts).+1 := exec_seat_share_count e.

Hypothesis Hobs :
  forall (x : ep_inputT e) (w0 : pgg_gT M) (i : 'I_(pi_T' PI).+1),
  content_obs x (w0, tnth (pi_starts PI) i)
  = tnth (ts_encode ts (expected x))
      (rp_monodromy (mp_plug mp) w0 (cast_ord bridge i)).

(* Decoding the static endpoint reading at a shuffle in the group returns the
   expected value. The hypothesis is one coordinate correspondence: seat i
   observes the share whose index is the monodromy image of seat i. It
   subsumes both halves an instance would otherwise prove, that the readout
   is the canonical encoding and that the monodromy agrees with the deck
   action on the seat starts, and it needs no relation between seat count and
   deck size, since a share index is never read as a deck position. *)
Lemma generic_static_recon (x : ep_inputT e) (w0 : pgg_gT M) :
  w0 \in pgg_G M ->
  forall sz_ep : size (@exec_static_endpoints mp e content_obs x w0)
               = (pi_T' PI).+1,
  @exec_decode mp e (@exec_static_endpoints mp e content_obs x w0) sz_ep
  = expected x.
Proof.
move=> Gw0 sz_ep; rewrite /exec_decode /run_recover.
have -> : tcast (etrans sz_ep (exec_seat_share_count e))
            (in_tuple (@exec_static_endpoints mp e content_obs x w0))
        = [tuple tnth (ts_encode ts (expected x))
                   (rp_monodromy (mp_plug mp) w0 j) | j < (ts_T' ts).+1].
  apply: eq_from_tnth => j.
  have jlt : (j < (pi_T' PI).+1)%N by rewrite bridge; exact: ltn_ord.
  rewrite tcastE tnth_mktuple (tnth_nth ord0) /=.
  rewrite /exec_static_endpoints (ep_playersE e).
  rewrite (nth_map (Ordinal jlt));
    last by rewrite size_enum_ord; exact: jlt.
  have enumE : nth (Ordinal jlt) (enum 'I_(pi_T' PI).+1) (nat_of_ord j)
             = Ordinal jlt := nth_ord_enum (Ordinal jlt) (Ordinal jlt).
  rewrite enumE Hobs.
  congr (tnth _ (rp_monodromy _ _ _)).
  exact: val_inj.
exact: (@rp_recon_invariant (mp_M mp) (mp_secretT mp) (mp_plug mp) w0
          (expected x) (ts_encode ts (expected x)) Gw0
          (ts_encode_valid ts (expected x))).
Qed.

End generic_static_recon.

Section generic_static_recon_valid.

Variable mp : MonodromyProfile.
Variable e : ExecutionPlug mp.

Local Notation M  := (mp_M mp).
Local Notation PI := (mp_PI mp).
Local Notation ts := (rp_scheme (mp_plug mp)).

Variable content_obs :
  ep_inputT e -> pgg_gT M * 'I_(pgg_N' M).+1 -> 'I_(pgg_N' M).+1.
Variable expected : ep_inputT e -> mp_secretT mp.
(* shares is the layout actually dealt, which need not be ts_encode. *)
Variable shares : ep_inputT e -> ((ts_T' ts).+1).-tuple 'I_(pgg_N' M).+1.

(* The plug's own seat/share bridge in successor form. Both counts are the
   same natural number, so the cast it induces is the identity on indices. *)
Let bridge : (pi_T' PI).+1 = (ts_T' ts).+1 := exec_seat_share_count e.

Hypothesis Hvalid : forall x, ts_valid ts (expected x) (shares x).

Hypothesis HobsV :
  forall (x : ep_inputT e) (w0 : pgg_gT M) (i : 'I_(pi_T' PI).+1),
  content_obs x (w0, tnth (pi_starts PI) i)
  = tnth (shares x) (rp_monodromy (mp_plug mp) w0 (cast_ord bridge i)).

(* Static reconstruction for a sharing that need not be the canonical
   encoding, only a valid one. A run whose layout is drawn from a tape rather
   than produced by ts_encode reconstructs by this form; the canonical case
   above is this one at shares := ts_encode. *)
Lemma generic_static_recon_valid (x : ep_inputT e) (w0 : pgg_gT M) :
  w0 \in pgg_G M ->
  forall sz_ep : size (@exec_static_endpoints mp e content_obs x w0)
               = (pi_T' PI).+1,
  @exec_decode mp e (@exec_static_endpoints mp e content_obs x w0) sz_ep
  = expected x.
Proof.
move=> Gw0 sz_ep; rewrite /exec_decode /run_recover.
have -> : tcast (etrans sz_ep (exec_seat_share_count e))
            (in_tuple (@exec_static_endpoints mp e content_obs x w0))
        = [tuple tnth (shares x)
                   (rp_monodromy (mp_plug mp) w0 j) | j < (ts_T' ts).+1].
  apply: eq_from_tnth => j.
  have jlt : (j < (pi_T' PI).+1)%N by rewrite bridge; exact: ltn_ord.
  rewrite tcastE tnth_mktuple (tnth_nth ord0) /=.
  rewrite /exec_static_endpoints (ep_playersE e).
  rewrite (nth_map (Ordinal jlt));
    last by rewrite size_enum_ord; exact: jlt.
  have enumE : nth (Ordinal jlt) (enum 'I_(pi_T' PI).+1) (nat_of_ord j)
             = Ordinal jlt := nth_ord_enum (Ordinal jlt) (Ordinal jlt).
  rewrite enumE HobsV.
  congr (tnth _ (rp_monodromy _ _ _)).
  exact: val_inj.
exact: (@rp_recon_invariant (mp_M mp) (mp_secretT mp) (mp_plug mp) w0
          (expected x) (shares x) Gw0 (Hvalid x)).
Qed.

End generic_static_recon_valid.

(* The reconstruction obligation of a dealer-dealt run, discharged from the
   algebra alone. The coordinate hypothesis of generic_static_recon is
   pga_coordE read through the plug's seat/share bridge, which casts between
   two copies of the same share count and is therefore the identity on
   indices. *)
Lemma dealt_static_recon (A : PGGAlgebraic) (fuel : nat) :
  instance_recon_stmt (dealt_secret_params A fuel).
Proof.
move=> x w0.
apply: (@generic_static_recon (instance_profile A)
          (instance_exec (dealt_secret_params A fuel))
          (@dealt_content_obs A) id _ x w0).
move=> {}x {}w0 i.
have ci : cast_ord (exec_seat_share_count
                      (instance_exec (dealt_secret_params A fuel))) i = i
  by apply: val_inj.
by rewrite /dealt_content_obs ci pga_coordE tcastE.
Qed.

(* The algebra and the fuel are supplied positionally: both occur in the run
   arguments of the conclusion, which the file-level Unset Strict Implicit
   would otherwise take for a reason to infer them. *)
Arguments dealt_static_recon : clear implicits.

Section layout_static_recon.

Variable A : PGGAlgebraic.
Variable E : ExecutionParams A.
Variable layout :
  ex_inputT E -> (ts_T' (pga_scheme A)).+1.-tuple 'I_(pga_n A).+2.

Hypothesis Hvalid :
  forall x, ts_valid (pga_scheme A) (ex_expected E x) (layout x).
Hypothesis Hobs : ex_content_obs E = layout_content_obs layout.

(* The reconstruction obligation of a run whose direct computation reads a
   layout, from the layout being a valid sharing of the expected value. The
   coordinate hypothesis of generic_static_recon_valid is pga_coordE read
   through the plug's seat/share bridge, which casts between two copies of the
   same share count and is therefore the identity on indices. The two
   hypotheses are what the input family and the supplied sharing mode have in
   common, so the obligation is discharged once for both. *)
Lemma layout_static_recon : instance_recon_stmt E.
Proof.
move=> x w0.
apply: (@generic_static_recon_valid (instance_profile A) (instance_exec E)
          (ex_content_obs E) (ex_expected E) layout Hvalid _ x w0).
move=> {}x {}w0 i.
have ci : cast_ord (exec_seat_share_count (instance_exec E)) i = i
  by apply: val_inj.
by rewrite Hobs /layout_content_obs /layout_content ci pga_coordE tcastE.
Qed.

End layout_static_recon.

(* The algebra, the parameter record and the layout all occur in the run
   arguments of the conclusion, which the file-level Unset Strict Implicit
   would otherwise take for a reason to infer them. *)
Arguments layout_static_recon : clear implicits.

(* The reconstruction obligation of an input-family run, discharged from the
   sharing claim written in its own parameter statement. Every argument occurs
   in the conclusion, so such a run owes no reconstruction proof beyond the
   encoding it already named. *)
Lemma encoded_static_recon (A : PGGAlgebraic) (inputT : Type)
    (f : inputT -> pga_secretT A)
    (layout : inputT -> (ts_T' (pga_scheme A)).+1.-tuple 'I_(pga_n A).+2)
    (Hv : forall x, ts_valid (pga_scheme A) (f x) (layout x))
    (dec : seq 'I_(pga_n A).+2 -> inputT)
    (procs : inputT -> seq (aproc pgg_dtype (pgg_data (pga_n A).+2)))
    (fuel : nat) :
  instance_recon_stmt
    (encoded_input_params A inputT f layout Hv dec procs fuel).
Proof.
exact: (layout_static_recon A
  (encoded_input_params A inputT f layout Hv dec procs fuel) layout Hv erefl).
Qed.

(* The eight arguments of encoded_input_params occur in the statement the
   obligation is made about, so the lemma is written unapplied where the
   obligation is owed. *)
Arguments encoded_static_recon {A inputT f layout Hv dec procs fuel} x w0.

(* The reconstruction obligation of a sharing-family run at a supplied layout,
   from that layout being a valid sharing of the expected value. The sharing
   claim is not part of the parameter statement in this mode, so it is written
   here and
   the algebra is supplied with it: the claim alone leaves the deck size and
   the share count undetermined. *)
Lemma supplied_static_recon (A : PGGAlgebraic) (inputT : Type)
    (layout : inputT -> (ts_T' (pga_scheme A)).+1.-tuple 'I_(pga_n A).+2)
    (expected : inputT -> pga_secretT A) (fuel : nat) :
  (forall x, ts_valid (pga_scheme A) (expected x) (layout x)) ->
  instance_recon_stmt (supplied_input_params A inputT layout expected fuel).
Proof.
move=> Hv.
exact: (layout_static_recon A
  (supplied_input_params A inputT layout expected fuel) layout Hv erefl).
Qed.

(* The algebra is explicit for the reason the comment above gives, and the
   rest is read off the statement the obligation is made about. *)
Arguments supplied_static_recon A {inputT layout expected fuel} Hv x w0.

(******************************************************************************)
(*     Framework lemma 2: the endpoint equation at abstract readout           *)
(******************************************************************************)

(* The endpoint equation of a profile with the content readout left as a
   variable: for every readout, the executed endpoints of the dealer-dealt
   plug are its direct computation. Leaving the readout abstract keeps a
   dealt card out of the reduction, so the equation is decided once per
   profile instead of once per plug. *)
Definition profile_endpoints_stmt (A : PGGAlgebraic) (fuel : nat) : Prop :=
  forall (inputT : Type)
         (content : inputT -> seq 'I_(pga_n A).+2
                      -> 'I_(pga_n A).+2 -> 'I_(pga_n A).+2)
         (x : inputT) (w0 : pgg_gT (instance_M A)),
    @exec_endpoints (instance_profile A) (params_exec (NoCommit A inputT)
                                            content fuel) x w0 0
    = @exec_static_endpoints (instance_profile A)
        (params_exec (NoCommit A inputT) content fuel)
        (fun x p => content x [::] (@pgg_rho (instance_M A) p.1 p.2)) x w0.

(* The endpoint obligation of a dealer-dealt run, read off the profile's own
   abstract-readout equation. Instantiating the variable readout at
   dealt_content gives the dealt direct computation by conversion, so the
   instance-level statement costs no reduction of its own. *)
Lemma profile_endpointsE (A : PGGAlgebraic) (fuel : nat) :
  profile_endpoints_stmt A fuel ->
  instance_endpoints_stmt (dealt_secret_params A fuel).
Proof. by move=> H x w0; exact: (H _ (@dealt_content A) x w0). Qed.

(* The endpoint obligation of a sharing-family run at a supplied layout, read
   off the same abstract-readout equation. The profile statement already
   quantifies over the content readout, so instantiating it at the supplied
   layout costs the run no reduction of its own, and the two modes of the
   sharing family share the profile's one decision. *)
Lemma supplied_endpointsE (A : PGGAlgebraic) (inputT : Type)
    (layout : inputT -> (ts_T' (pga_scheme A)).+1.-tuple 'I_(pga_n A).+2)
    (expected : inputT -> pga_secretT A) (fuel : nat) :
  profile_endpoints_stmt A fuel ->
  instance_endpoints_stmt (supplied_input_params A inputT layout expected fuel).
Proof. by move=> H x w0; exact: (H _ _ x w0). Qed.

(* The endpoint equation of a profile driven with commit processes: for every
   content readout, the executed endpoints of a run whose committers are procs
   are its direct computation, the readout taken at the payload list the
   committers send. The readout stays a variable for the reason it does above,
   and the payload list is named rather than computed because it is what the
   committers put into the run and what the reduction has to produce; the
   commit processes themselves cannot stay variable, since the reduction runs
   them. The algebra and the input carrier are read off procs, so an instance
   states this obligation at its process list where it states the
   dealer-dealt one at its algebra. *)
Definition profile_commit_endpoints_stmt (A : PGGAlgebraic) (inputT : Type)
    (procs : inputT -> seq (aproc pgg_dtype (pgg_data (pga_n A).+2)))
    (payload : inputT -> seq 'I_(pga_n A).+2) (fuel : nat) : Prop :=
  forall (content : inputT -> seq 'I_(pga_n A).+2
                      -> 'I_(pga_n A).+2 -> 'I_(pga_n A).+2)
         (x : inputT) (w0 : pgg_gT (instance_M A)),
    @exec_endpoints (instance_profile A)
      (params_exec (Commits procs) content fuel) x w0 0
    = @exec_static_endpoints (instance_profile A)
        (params_exec (Commits procs) content fuel)
        (fun y p => content y (payload y) (@pgg_rho (instance_M A) p.1 p.2))
        x w0.

(* The endpoint obligation of an input-family run, from the profile's
   commit-mode equation and the single fact that decoding the payload list
   returns the input the committers hold. That decoding fact is the whole of
   what an instance adds: the reduction is spent once at the profile, and this
   lemma is what turns the layout the dealer assembled from the payloads into
   the layout the direct computation reads. *)
Lemma encoded_endpointsE (A : PGGAlgebraic) (inputT : Type)
    (f : inputT -> pga_secretT A)
    (layout : inputT -> (ts_T' (pga_scheme A)).+1.-tuple 'I_(pga_n A).+2)
    (Hv : forall x, ts_valid (pga_scheme A) (f x) (layout x))
    (dec : seq 'I_(pga_n A).+2 -> inputT)
    (procs : inputT -> seq (aproc pgg_dtype (pgg_data (pga_n A).+2)))
    (payload : inputT -> seq 'I_(pga_n A).+2) (fuel : nat) :
  profile_commit_endpoints_stmt procs payload fuel ->
  (forall x, dec (payload x) = x) ->
  instance_endpoints_stmt
    (encoded_input_params A inputT f layout Hv dec procs fuel).
Proof.
move=> H Hdec x w0; rewrite (H _ x w0) /exec_static_endpoints.
by apply: eq_map => i /=; rewrite /layout_content_obs Hdec.
Qed.
