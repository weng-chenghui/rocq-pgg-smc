# Refutations: a program that publishes an obstruction — probe ledger

Probe for `notes/20260921-refutations-probe-design.md` (tracker step 4.2), run
2026-09-21. No production file was touched. Everything below lives in
`notes/probes/2026-09-21-refutations/`.

Every number below is from one ordered pass over the whole set, run after
another agent committed `a91b321`, the landing of the terminals below
`AnalysisBridged` that this probe's record and terminal follow. That commit
turned every probe `.vo` stale mid-run with `makes inconsistent assumptions
over library pgg_smc.pgg_tableau`; the pass was restarted whole. The probe is
unaffected by the commit: every file is green against it.

Compile line, from the repository root, one Rocq process at a time:

```
FLAGS="-Q notes/probes/2026-09-21-refutations refuteprobe <the -R lines of _CoqProject> <its -arg lines, the word -arg dropped>"
<scratchpad>/rocq1 900 8000 rocq compile ${=FLAGS} notes/probes/2026-09-21-refutations/<file>.v
```

## The flow

How the all-decks Sampled program becomes a published obstruction. One step per
line, the trailing comment holding what the program has accumulated after it.

```
start    psl211_algebra                                  // proved: nothing
supplied/execute  psl211_alldecks_prefix                 // + run correctness (three run facts)
sample   psl211_exact_family                             // + link lemma; model: uniform cut on G, |G| = 660
refute   NoCertificateNear (`U psl211_G_pos) eps         // + no certificate with ideal within eps of the uniform cut
     by  psl211_alldecks_obstruction_proof               //   premise discharged: eps + eps < 1/|G|
|>       path (observed, AnalysisBridged, exact_family,  // + the manifest path, NegativeTransfer fixed by the terminal
          NegativeTransfer, BaselineClassicalOnly)       //   published: an obstruction, and no security property
```

Monad verdict: the carrier stays `TableauAt`, the parameterised monad indexed by
completion level that `manifest/pgg_tableau.v` already carries; `refute` is a
terminal out of it and not a step, its result leaving the indexed family, as
`publish_sampled` does.

Interfaces, one per external result:

| result | where it enters | through |
|---|---|---|
| `psl211_alldecks_prefix` | first object of the flow | the three run facts, `psl211_tableau_observed.v` |
| `psl211_exact_family` | the model slot | `sample`, and `sp_f` reads it back |
| `psl211_alldecks_constancy_false_close` | the `refute` line's justification | `no_certificate_near_of_constancy_false` |
| `ic_const` of `IndistinguishabilityCert` | observation change, at no cost | `indistinguishability_cert_reading_constancy` |
| `psl211_G_pos` | the number's side condition | `psl211_alldecks_obstruction_eps_lt` |
| `pgl27_word_cert` | outside the flow | non-vacuity only, `n_pgl27_nonvacuity.v` |

Outside the DSL: the choice of the published number, which is a fraction of
1/|G| and not a quantity the flow accumulates; and the manifest path's prose
table entry, which no term produces.

## Files

| file | what it holds | compiles | seconds |
|---|---|---|---|
| `n_framework.v` | N1, N2 (framework form), N5 | yes | 4 |
| `n_syntax.v` | N7, the rule and the coexistence checks | yes | 4 |
| `n_syntax_keyword.v` | N7, the keyword cost in a second file | yes | 3 |
| `n_pgl27_nonvacuity.v` | N4 (a) | yes | 4 |
| `n_psl211.v` | N2 (at the tree's name), N3, N6 draft, N8 | yes | 66 |
| `n_psl211_number.v` | N9 | yes | 25 |
| `m_n2_nohyp.v` | the N2 mutation, `Fail`-guarded | yes | 4 |
| `m_n2_nohyp_nofail.v` | the same without `Fail` | **no, by design** | 5 |
| `m_n3_noeps.v` | the N3 mutation, `Fail`-guarded | yes | 4 |
| `m_n3_noeps_nofail.v` | the same without `Fail` | **no, by design** | 4 |
| `m_reader_secrecy.v` | N5, `view_secrecy_of` refused, `Fail`-guarded | yes | 5 |
| `m_reader_secrecy_nofail.v` | the same without `Fail` | **no, by design** | 4 |
| `m_reader_property.v` | N5, `security_property_of` refused, `Fail`-guarded | yes | 4 |
| `m_reader_property_nofail.v` | the same without `Fail` | **no, by design** | 4 |

The four `_nofail` files are the twins the procedure demands: a passing `Fail`
prints nothing, so each is compiled once without its guard and the message is
quoted below. No `Admitted`, no `Abort`, no `Axiom` anywhere.

## Ledger

### N1 — GO

`n_framework.v`, `NoIndistinguishabilityCertNear`. Final statement, verbatim:

```coq
Definition NoIndistinguishabilityCertNear (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (U : R.-fdist (pgg_gT (mp_M (instance_profile A)))) (eps : R) : Prop :=
  forall cert : IndistinguishabilityCert sa,
    var_dist U (ic_ideal cert) <= eps -> False.
Arguments NoIndistinguishabilityCertNear {R A E} sa U eps.
```

Monotone downward in `eps`, `Qed`:

```coq
Lemma no_indistinguishability_cert_near_le (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (U : R.-fdist (pgg_gT (mp_M (instance_profile A)))) (eps eps' : R) :
  eps' <= eps ->
  NoIndistinguishabilityCertNear sa U eps ->
  NoIndistinguishabilityCertNear sa U eps'.
```

The `Arguments` line is load-bearing. Without it `Unset Strict Implicit` makes
`sa` implicit, the conclusion delta-reducing to a dependent product in which
`sa` occurs, and the product's own binder takes the first written slot.

### N2 — GO, by conversion

Two forms, both `Qed`.

Framework form, in `n_framework.v`, with the constancy written out because the
standalone name sits above that file:

```coq
Lemma no_indistinguishability_cert_nearP (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (U : R.-fdist (pgg_gT (mp_M (instance_profile A)))) (eps : R) :
  (forall ideal : R.-fdist (pgg_gT (mp_M (instance_profile A))),
     var_dist U ideal <= eps ->
     ~ (forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
          (#|C| < profile_k (instance_profile A))%N ->
          forall x x' : ex_inputT E,
            fdistmap (static_coalition_obs C x) ideal
            = fdistmap (static_coalition_obs C x') ideal)) ->
  NoIndistinguishabilityCertNear sa U eps.
Proof.
move=> H cert Hc.
exact: (H (ic_ideal cert) Hc (@ic_const R A E sa cert)).
Qed.
```

At the tree's own name, in `n_psl211.v`:

```coq
Lemma no_certificate_near_of_constancy_false (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (U : R.-fdist (pgg_gT (mp_M (instance_profile A)))) (eps : R) :
  (forall u : R.-fdist (pgg_gT (mp_M (instance_profile A))),
     var_dist U u <= eps -> ~ coalition_reading_constancy E u) ->
  NoIndistinguishabilityCertNear sa U eps.
```

**Which:** conversion, by delta on `coalition_reading_constancy`, and nothing
else. The identity is compiled in `n_psl211.v` as

```coq
Lemma coalition_reading_constancy_unfoldE (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A)
    (u : R.-fdist (pgg_gT (mp_M (instance_profile A)))) :
  coalition_reading_constancy E u
  = (forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
       (#|C| < profile_k (instance_profile A))%N ->
       forall x x' : ex_inputT E,
         fdistmap (static_coalition_obs C x) u
         = fdistmap (static_coalition_obs C x') u).
Proof. exact: erefl. Qed.
```

and the same identity is visible in the mutation message below, where the
kernel prints the type of `ic_const cert` in full.

**Mutation (N2 without its hypothesis) — NO-GO as required.** Reading: "the
closeness hypothesis" is N2's premise, whose whole content is the refutation
indexed by closeness; deleting the premise leaves the lemma claiming the
obstruction out of nothing. Deleting the closeness *inside* the premise would
instead strengthen the premise and stay provable, which is why that is not the
mutation run. `m_n2_nohyp_nofail.v`, message quoted verbatim:

```
File "./notes/probes/2026-09-21-refutations/m_n2_nohyp_nofail.v", line 32, characters 18-41:
Error:
In environment
R : realType
A : PGGAlgebraic
E : ExecutionParams A
sa : SampleAdapter R (instance_exec E)
U : {fdist pgg_gT (mp_M (instance_profile A))}
eps : R
cert : IndistinguishabilityCert sa
Hc : var_dist U (ic_ideal cert) <= eps
The term "ic_const cert" has type
 "forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
  (#|C| < profile_k (instance_profile A))%N ->
  forall x x' : ex_inputT E,
  fdistmap (static_coalition_obs C x) (ic_ideal cert) =
  fdistmap (static_coalition_obs C x') (ic_ideal cert)"
while it is expected to have type "False".
```

### N3 — GO

`n_psl211.v`. Final statement, verbatim:

```coq
Theorem psl211_alldecks_no_certificate_near (R : realType) (eps : R) :
  eps + eps < (#|pgg_G psl211_M|%:R)^-1 ->
  NoIndistinguishabilityCertNear (amf_sample psl211_exact_family R tt)
    ((`U psl211_G_pos) : R.-fdist cutT) eps.
```

The adapter is the all-decks family's own, `amf_sample psl211_exact_family R tt`
and not `psl211_alldecks_sample R` written beside it. `Print Assumptions`:

```
Axioms:
propositional_extensionality : forall P Q : Prop, P <-> Q -> P = Q
functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
constructive_indefinite_description :
  forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
```

the repository's classical baseline and nothing else, so the path's assumption
status is `BaselineClassicalOnly`.

**Mutation (N3 without `eps + eps < (#|G|)^-1`) — NO-GO as required.**
`m_n3_noeps_nofail.v`, message quoted verbatim:

```
File "./notes/probes/2026-09-21-refutations/m_n3_noeps_nofail.v", line 55, characters 18-71:
Error:
In environment
R : realType
eps : R
u : {fdist pgg_gT (mp_M (instance_profile psl211_algebra))}
Hclose : var_dist (`U psl211_G_pos) u <= eps
The term "psl211_alldecks_constancy_false_close Hclose" has type
 "eps + eps < #|pgg_G psl211_M|%:R^-1 ->
  ~ coalition_reading_constancy psl211_alldecks_params u"
while it is expected to have type
 "~ coalition_reading_constancy psl211_alldecks_params u"
(cannot unify "coalition_reading_constancy psl211_alldecks_params u" and
"is_true (eps + eps < #|pgg_G psl211_M|%:R^-1)").
```

### N4 — GO

**(a) The class is inhabited at another model.** `n_pgl27_nonvacuity.v`. The
eight-card orbit instance's word certificate takes the group-uniform law itself
as its ideal cut, at distance zero, so no number denies the certificates that
near it there:

```coq
Theorem pgl27_word_no_certificate_near_false (R : realType)
    (secretP : R.-fdist bool) (eps : R) :
  0 <= eps ->
  ~ NoIndistinguishabilityCertNear (amf_sample pgl27_word_family R secretP)
      ((`U pgl27_G_pos) : R.-fdist (pgg_gT pgl27_M)) eps.
```

with the corollary at `eps = 0`, where the obstruction is weakest. The distance
is zero by

```coq
Lemma pgl27_word_cert_ideal_uniform (R : realType) (secretP : R.-fdist bool) :
  var_dist ((`U pgl27_G_pos) : R.-fdist (pgg_gT pgl27_M))
    (ic_ideal (@pgl27_word_cert R secretP)) = 0 :> R.
```

which needs one point infotheo does not carry, `var_dist d d = 0`; it is proved
in three tokens beside it and belongs upstream in
`probability/variation_dist.v`, next to `pos_var_dist` and `def_var_dist`.

**(b) Certificates with a far ideal are not refuted.** N3 holds only under
`eps + eps < (#|G|)^-1`, so the class it denies is the certificates whose ideal
sits within less than half of 1/660 of the group-uniform law. Above that the
statement is silent, and `no_indistinguishability_cert_near_le` runs downward
only: from the obstruction at `eps` one gets it at every smaller number and at
no larger one. The excluded range is bounded above for a reason the constancy
theorem makes explicit: its proof moves two masses, zero and 1/660, by at most
`eps` each, and an ideal further away than half their gap leaves them able to
coincide. `instances/psl211/psl211_reading_constancy.v`'s header names the
occupant of the larger range, the uniform law on the whole of `{perm 'I_12}`,
whose distance from `` `U psl211_G_pos `` is `2 * (1 - 660/12!)`; that occupancy
is argued there and not compiled, and this probe did not compile it either.

### N5 — GO

`n_framework.v`. The family, the record and the terminal:

```coq
Variant ObstructionKind (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E)) : Type :=
  | NoCertificateNear of R.-fdist (pgg_gT (mp_M (instance_profile A))) & R.

Definition ObstructionProp (R : realType) (A : PGGAlgebraic)
    (E : ExecutionParams A) (sa : SampleAdapter R (instance_exec E))
    (o : ObstructionKind sa) : Prop :=
  match o with
  | NoCertificateNear U eps => NoIndistinguishabilityCertNear sa U eps
  end.

Definition ObstructionPayload (q : StackAt Sampled) : Type :=
  forall (R : realType) (idx : amf_index (sp_f q) R),
    ObstructionKind (amf_sample (sp_f q) R idx).

Definition ObstructionPropOf (q : StackAt Sampled) (o : ObstructionPayload q)
    : Prop :=
  forall (R : realType) (idx : amf_index (sp_f q) R), ObstructionProp (o R idx).

Definition RefutePayload (q : StackAt Sampled) : Type :=
  { o : ObstructionPayload q & ObstructionPropOf o }.

Definition mk_obstruction (q : StackAt Sampled) (o : ObstructionPayload q)
    (H : ObstructionPropOf o) : RefutePayload q := existT _ o H.

Record PublishedObstruction := MkPublishedObstruction {
  published_obstruction_at   : StackAt Sampled ;
  published_obstruction_path : AnalysisPath ;
  published_obstruction_kind : ObstructionPayload published_obstruction_at ;
  published_obstruction_thm  : StackProp Sampled published_obstruction_at ;
  published_obstruction_pf   : ObstructionPropOf published_obstruction_kind }.

Definition refute (a : AssumptionStatus) (q : StackAt Sampled)
    (pf : StackProp Sampled q) (p : RefutePayload q) : PublishedObstruction :=
  @MkPublishedObstruction q
    (@MkAnalysisPath (sp_obs q) AnalysisBridged (sp_f q) NegativeTransfer a)
    (projT1 p) pf (projT2 p).
Arguments refute : clear implicits.
```

`SecurityEvidence` keeps its three constructors and `StackAt AnalysisBridged` is
unchanged, as the spec's invariant asks; the record's data is at `Sampled` and
carries no evidence at all.

Five path equations, each `exact: erefl`, all `Qed`: `refute_completionE`
(`= AnalysisBridged`), `refute_transferE` (`= NegativeTransfer`),
`refute_modelE` (`= sp_f q`), `refute_observedE` (`= sp_obs q`),
`refute_assumptionsE` (`= a`), and `refute_kindE` (the kind is the one the line
wrote).

Readers: `obstruction_of`, `run_correct_of_obstruction`,
`view_identification_of_obstruction`.

Three `Arguments … : clear implicits` are load-bearing, on
`published_obstruction_kind`, `published_obstruction_thm` and
`published_obstruction_pf`. Without the first, the probe's own
`refute_kindE` was rejected with

```
The term "refute a q pf (mk_obstruction q o H)" has type
 "PublishedObstruction"
while it is expected to have type
 "amf_index (sp_f (published_obstruction_at ?p)) ?R".
```

**No security reader applies.** `m_reader_secrecy_nofail.v`, verbatim:

```
File "./notes/probes/2026-09-21-refutations/m_reader_secrecy_nofail.v", line 29, characters 23-24:
Error:
In environment
r : PublishedObstruction
The term "r" has type "PublishedObstruction"
while it is expected to have type "PublishedAt ?c".
```

`m_reader_property_nofail.v` gives the same message at
`security_property_of r`, characters 28-29. Both readers project out of
`PublishedAt`, and a published obstruction is not one.

### N6 — yes, honest, with one gap in the capability vocabulary

The manifest's own definitions, quoted.

Level, from `manifest/pgg_analysis_manifest.v`:

```
(*   AnalysisBridged + bridge alias to a named security, leakage, mixing or   *)
(*                    limitation theorem about the same distribution and the  *)
(*                    same observer                                           *)
```

and from `manifest/pgg_analysis_status.v`:

```
(* AnalysisBridged is the typed form of the prose label Security-bridged of   *)
(* the earlier manifest banner: a bridged path relates a security, leakage,   *)
(* mixing or limitation theorem to the same distribution and the same         *)
(* observer as its sample, which a negative mixing result also does.          *)
```

Status, from `manifest/pgg_analysis_status.v`:

```
(* NegativeTransfer is a theorem transporting an                              *)
(* obstruction to the path's observer.                                        *)
```

Duty paragraphs, from the manifest header:

```
(* (1) The classical trio propositional_extensionality,                       *)
(* functional_extensionality_dep and constructive_indefinite_description is   *)
(* the repository baseline … A path is                                        *)
(* BaselineClassicalOnly when Print Assumptions reports the trio and nothing  *)
(* else …                                                                     *)
(* (2) Completion levels are cumulative and are stated at the level the       *)
(* theorems actually reach. …                                                 *)
(* (3) A capability line uses the narrowest label the theorem statement       *)
(* supports, from the closed vocabulary correctness, exact privacy,           *)
(* approximate privacy, trace secrecy, conditional entropy, mutual            *)
(* information or endpoint marginal mixing.                                   *)
```

and

```
(* A path records no security property. Which one a published program carries *)
(* is read off that program by security_property_of …                         *)
```

Against those: the level is honest. `psl211_alldecks_no_certificate_near` is a
limitation theorem about the path's own cut law, `` `U psl211_G_pos ``, which
`psl211_alldecks_cut_distE` identifies with the model's `sa_cut_dist`, and about
the path's own static observer `static_coalition_obs`, so it relates a
limitation theorem to the same distribution and the same observer as the
sample. The status is honest: the theorem transports the failure of the
constancy of a reading, an obstruction, to that observer. Duty (1) is met, the
`Print Assumptions` above showing the trio and nothing else. Duty (2) is met,
the theorem reaching `AnalysisBridged` and no higher level existing. That a path
records no security property is exactly why an obstruction can have one: nothing
in `AnalysisPath` claims a program on it certifies anything.

The gap is duty (3). An obstruction supports none of the seven capability
labels, which all name something a path proves about a coalition. Either the
closed vocabulary gains an eighth label, or the path's capability table carries
no line and says so. That is the owner's call and the landing should not settle
it silently.

One consistency point. Two paths over one observed execution and one model
family, differing in the transfer status alone, are two paths and not two
descriptions of one: path 11's bridged theorem is `exact_view_indep`, which
compares no idealized model, and the new path's is the obstruction, which
compares every ideal within `eps` of the uniform cut. The probe compiles both
halves of that:

```coq
Lemma psl211_alldecks_obstruction_path_observedE :
  ap_observed (published_obstruction_path psl211_alldecks_obstruction_published)
  = ap_observed psl211_alldecks_path.
Proof. exact: erefl. Qed.

Lemma psl211_alldecks_obstruction_path_transfer_neq :
  ap_transfer (published_obstruction_path psl211_alldecks_obstruction_published)
  <> ap_transfer psl211_alldecks_path.
Proof. by []. Qed.
```

**Drafted path entry** (drafted, not landed).

Five coordinates, compiled against the facade's vocabulary by

```coq
Lemma psl211_alldecks_obstruction_pathE :
  published_obstruction_path psl211_alldecks_obstruction_published
  = @MkAnalysisPath PSL211Analysis.observed AnalysisBridged
      PSL211Analysis.exact_family NegativeTransfer BaselineClassicalOnly.
Proof. exact: erefl. Qed.
```

so the typed value the manifest would carry is

```coq
Definition psl211_alldecks_obstruction_path : AnalysisPath :=
  @MkAnalysisPath PSL211Analysis.observed AnalysisBridged
    PSL211Analysis.exact_family NegativeTransfer BaselineClassicalOnly.
```

Prose table entry, in the manifest's own shape:

```
(*     Path 12: twelve-card chirality instance, all-decks dealer, the         *)
(*              input-indistinguishability route refuted                      *)
(*                                                                            *)
(* | field | value |                                                          *)
(* |---|---|                                                                  *)
(* | protocol family and model | PSL(2,11) twelve-card deck, deck             *)
(*                               description drawn uniformly and the cut      *)
(*                               drawn uniformly over the 660 elements of the *)
(*                               group, the same model as Path 10 |           *)
(* | profile alias      | PSL211Analysis.profile |                            *)
(* | execution alias    | PSL211Analysis.exec_plug |                          *)
(* | observed alias     | PSL211Analysis.observed |                           *)
(* | sample alias       | PSL211Analysis.exact_sample; the path's typed model *)
(*                        witness is PSL211Analysis.exact_family |            *)
(* | observers          | PSL211Analysis.static_view                          *)
(*                          : {ffun 'I_12 -> 'I_12}, the reading of the laid  *)
(*                            deck at a description and a cut |               *)
(* | distribution-to-observer bridges | PSL211Analysis.cut_distE |            *)
(* | bound or certificate | none: the path denies a class of certificates and *)
(*                          carries none |                                    *)
(* | final bridge theorem | psl211_alldecks_no_certificate_near |             *)
(* | correctness theorem  | PSL211Analysis.observed_recovers |                *)
(* | model transfer       | psl211_alldecks_constancy_false_close, which      *)
(*                          carries the failure of the constancy of a         *)
(*                          coalition's reading from every ideal cut within   *)
(*                          eps of the group-uniform law to this path's       *)
(*                          observer |                                        *)
(* | missing premise      | none |                                            *)
(* | completion level     | AnalysisBridged |                                 *)
(* | transfer status      | NegativeTransfer |                                *)
(* | assumption status    | BaselineClassicalOnly |                           *)
(* | typed path           | psl211_alldecks_obstruction_path |                *)
(*                                                                            *)
(* Capabilities: none. The closed vocabulary of convention (3) labels what a  *)
(* path proves about a coalition, and this path proves that one route to such *)
(* a statement is closed at this model.                                       *)
(*                                                                            *)
(* Level justification. profile gives Algebraic; exec_plug is indexed by      *)
(* profile, giving Executable; observed is the ObservedExecution over that    *)
(* profile and plug, giving Observed; exact_sample is a SampleAdapter over    *)
(* that plug and cut_distE identifies its cut law with the uniform law on the *)
(* group, giving Sampled; psl211_alldecks_no_certificate_near is a limitation *)
(* theorem stated at that law and at this path's own static observer, giving  *)
(* AnalysisBridged. It differs from psl211_alldecks_path in the transfer      *)
(* status alone: that path's theorem compares no idealized model, and this    *)
(* path's compares every ideal cut within eps of the uniform one.             *)
```

### N7 — GO

`n_syntax.v`. The rule:

```coq
Notation "s |> 'refute' a o 'by' pf" :=
  (s ;;; refute a of (mk_obstruction (tableau_at s) o pf))
  (at level 90, left associativity, a at level 0, o at level 0, pf at level 0).
```

Measured as the header of `manifest/pgg_tableau_syntax.v` demands. The rule's
only quoted token is `refute`, and it follows the literal `|>` exactly as
`publish` and `conclude` do, so it reserves no identifier; `by` follows the slot
`o` and is ssreflect's already; `|>` is the surface's existing separator. In the
declaring file `Check refute.` prints the constant. In a second file whose
`Require` lines are `ssreflect` and the probe, `n_syntax_keyword.v`, all three
uses pass:

```
refute
     : pgg_analysis_status.AssumptionStatus ->
       forall q : pgg_tableau.StackAt pgg_analysis_status.Sampled,
       pgg_tableau.StackProp pgg_analysis_status.Sampled q ->
       RefutePayload q -> PublishedObstruction
Constant refuteprobe.n_framework.refute
```

and `Lemma refute_is_a_binder_name (refute : nat) : refute = refute.` compiles,
so `refute` is still a binder name. The nineteen reserved identifiers stay
nineteen.

The existing rules still parse beside it. `n_syntax.v` elaborates all three
terminals in one section and the printer returns the new one in its own surface:

```
s |> publish Sampled tw a : PublishedSampled
     : PublishedSampled
u |> publish t a : Published
     : Published
s |> refute a o by H : PublishedObstruction
     : PublishedObstruction
```

The assumption status leads the obstruction because the transfer status, which
leads in the two `publish` rules, is fixed at `NegativeTransfer` by this
terminal and is not a payload.

**What misled me here.** `ideal` is one of the nineteen reserved identifiers,
and the first draft of `n_psl211.v` used it as a binder name, as
`instances/psl211/psl211_reading_constancy.v` does. That file does not require
the surface; any file that does cannot bind `ideal`. The error is
`Syntax error: [name] expected after '(' (in [closed_binder])` and names the
binder's column, not the keyword. The binder is `u` in the probe, which is what
`mk_indistinguishability` already calls the ideal cut.

### N8 — GO

`n_psl211.v`. The program, in the surface:

```coq
Definition psl211_alldecks_obstruction_published : PublishedObstruction :=
  psl211_exact_sampled
    |> refute BaselineClassicalOnly psl211_alldecks_obstruction
       by psl211_alldecks_obstruction_proof.
```

over the named Sampled value of
`instances/psl211/tableau/psl211_tableau_sampled.v`, with

```coq
Definition psl211_alldecks_obstruction_eps (R : realType) : R :=
  (#|pgg_G psl211_M|%:R)^-1 / 4%:R.

Definition psl211_alldecks_obstruction
  : ObstructionPayload (tableau_at psl211_exact_sampled) :=
  fun (R : realType) (idx : unit) =>
    @NoCertificateNear R psl211_algebra psl211_alldecks_params
      (amf_sample psl211_exact_family R idx)
      ((`U psl211_G_pos) : R.-fdist cutT)
      (psl211_alldecks_obstruction_eps R).
```

The number is a choice the flow does not force: N3 holds at every `eps` with
`eps + eps < 1/|G|`, the strict inequality leaving half of 1/|G| out, and a
program names one. A quarter of 1/|G| is inside the range and its side
condition, `psl211_alldecks_obstruction_eps_lt`, needs only `psl211_G_pos`.

The reader gives N3's statement back:

```coq
Theorem psl211_alldecks_published_no_certificate_near (R : realType) :
  NoIndistinguishabilityCertNear (amf_sample psl211_exact_family R tt)
    ((`U psl211_G_pos) : R.-fdist cutT) (psl211_alldecks_obstruction_eps R).
Proof.
exact: (obstruction_of psl211_alldecks_obstruction_published R tt).
Qed.
```

`Print Assumptions` of the reader's theorem and of the program itself is the
classical trio and nothing else, equal to N3's, so all three
`Print Assumptions` in the file agree.

### N9 — GO, and it is the stronger statement

`n_psl211_number.v`. The optional row was attempted and closed. It does not
deny a class of certificates; it denies the input-indistinguishability
proposition itself below a number, at the model and at no certificate in
particular. Final statement, verbatim:

```coq
Theorem psl211_alldecks_indistinguishability_number_ge (R : realType)
    (cert : IndistinguishabilityCert (amf_sample psl211_exact_family R tt))
    (c : R) :
  IndistinguishabilityPropAt cert c -> (#|pgg_G psl211_M|%:R)^-1 <= c.
```

Read as an obstruction: no input-indistinguishability program over the
all-decks model publishes a number below 1/660, whatever its certificate's
five fields are. The two supporting lemmas fix the two masses at the
framework's own static reader, in term mode as
`instances/psl211/psl211_reading_constancy.v` fixes them:

```coq
Lemma psl211_perdeck_static_mass_true (R : realType) :
  (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
       psl211_perdeck_coalition (true, psl211_perdeck_deal))
     ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view = 0 :> R.

Lemma psl211_perdeck_static_mass_false (R : realType) :
  (fdistmap (@static_coalition_obs psl211_algebra psl211_alldecks_params
       psl211_perdeck_coalition (false, psl211_perdeck_deal))
     ((`U psl211_G_pos) : R.-fdist cutT)) psl211_perdeck_view
  = (#|pgg_G psl211_M|%:R)^-1 :> R.
```

`Print Assumptions` is the classical trio and nothing else.

How it relates to N3. N3 denies certificates whose ideal is near the uniform
cut; N9 denies the published number, whatever the ideal. Neither implies the
other as stated: N3 says nothing about a certificate with a far ideal, and N9
says nothing about a number at or above 1/660. Together they close the two
shapes an input-indistinguishability program over this model could take. As a
second member of the family N9 would be a second `ObstructionKind`
constructor, carrying the number alone and no law; the probe did not add it,
the spec fixing one member for this batch.

**Cost.** The first version of this file compiled in 251 s, of which one
sentence held 228. The sentence is identified and removed at the end of this
ledger; the file now compiles in 25 s, of which about 21 is its own
`Print Assumptions`.

## Departures from the spec

1. **`n_syntax_keyword.v` is a file the Procedure does not name.** The measured
   keyword rule of `manifest/pgg_tableau_syntax.v` is measured across two files,
   and `n_syntax.v` is the declaring one; the second file is the measurement.
2. **`n_psl211.v` carries N2 as well as N3, N6 and N8.** The spec's N2 is a
   general lemma, but `coalition_reading_constancy` sits in
   `instances/psl211/psl211_reading_constancy.v`, above the framework. The
   framework file therefore carries the same lemma with the constancy written
   out, and the psl211 file carries it at the tree's name together with the
   compiled identity between the two.
3. **`m_*.v` are eight files rather than one set of "message files".** Each
   `Fail` has its own no-`Fail` twin, as the procedure requires, and a twin can
   hold only one probe because the compile stops at the first error.
4. **N4 (a) needed one lemma infotheo does not carry**, `var_dist d d = 0`. It
   is proved locally in `n_pgl27_nonvacuity.v`. A landing should either keep it
   local or send it upstream; the probe does not decide.
5. **The published number of N8 is a design choice the spec did not fix.** It
   is recorded above with its reason.

## What was recorded as misleading

- `ideal` is a reserved identifier of the surface, and the error it causes
  names the binder's column and not the keyword. See N7.
- `Unset Strict Implicit` made `sa` implicit in `NoIndistinguishabilityCertNear`
  and the record's field `published_obstruction_kind` implicit in its own
  record, because both conclusions delta-reduce to dependent products. The
  second was caught only by `refute_kindE`, whose error named
  `amf_index (sp_f (published_obstruction_at ?p)) ?R` as the expected type.
- `pgl27_word_cert`'s real field is implicit, `R` occurring in `secretP`'s type;
  `pgl27_word_cert R secretP` is rejected with `The term "R" has type
  "realType" while it is expected to have type "{fdist bool}"`.
- `eps` is a conclusion-only argument of
  `pgl27_word_no_certificate_near_false`, so `Unset Strict Implicit` makes it
  implicit and a positional `exact:` mis-assigns the hypothesis, reporting only
  `Cannot apply lemma (…)`. The goal fixes it under `apply:`.
- `Require Import` is not transitive here: `n_syntax_keyword.v` requiring only
  `n_syntax` reported `The reference refute was not found in the current
  environment`, which would have been a false measurement of the keyword cost.
- `lexx` and `le_trans` are not in `Num.Theory`; they are
  `Order.POrderTheory.lexx` and `Order.POrderTheory.le_trans`.
- A rewrite naming one chirality's reader in a goal that holds both cost 228 s
  and looked like an ordinary line. It was found only by `-time`, the file
  having compiled green. See the last section.
- Midway through the run another agent rebuilt `manifest/pgg_tableau.v` and
  every probe `.vo` went stale, reported as `Compiled library
  refuteprobe.n_framework … makes inconsistent assumptions over library
  pgg_smc.pgg_tableau`. The whole ordered pass was restarted, as the
  procedure requires; retrying the one file would not have converged.

## Verdicts

| id | verdict |
|---|---|
| N1 | GO |
| N2 | GO, the two propositions identical by conversion (delta); mutation rejected as required |
| N3 | GO, assumption status `BaselineClassicalOnly`; mutation rejected as required |
| N4 | GO, both halves |
| N5 | GO, six path and kind equations by `erefl`, both security readers refused |
| N6 | yes, honest, except that the capability vocabulary has no label for an obstruction; path drafted |
| N7 | GO, no identifier reserved, existing rules unaffected |
| N8 | GO, `Print Assumptions` equal to N3's |
| N9 | GO, and stronger than N3 in a direction N3 does not cover |

## What is left

- **Two audits before a landing plan**, which the spec's Procedure asks for and
  this probe did not run.
- **The capability vocabulary** of convention (3). An owner decision, not a
  compile question. Until it is settled the drafted Path 12 carries no
  capability line.
- **Where the framework lands.** `manifest/pgg_tableau.v` is 1283 lines and the
  probe's framework half is about 130. A leaf file above it would need
  `AnalysisPath`, so it would sit between `pgg_analysis_manifest.v` and the
  instance phase directories; the audits decide.
- **Whether `coalition_reading_constancy` moves.** The probe keeps the
  framework lemma's hypothesis written out because that definition lives in
  `instances/psl211/psl211_reading_constancy.v`, whose own header already calls
  it framework-level. If it moves down beside `IndistinguishabilityCert`, the
  two forms of N2 collapse into one.
- **`var_dist d d = 0` upstream or local.** See departure 4.
- **N9's second constructor.** The probe proves N9 and does not add it to
  `ObstructionKind`; a landing that wants both members published needs a second
  constructor carrying a number alone.
- **The published number of N8.** A quarter of 1/|G| is one choice inside the
  range; the owner may prefer another.
- **The 251 s cost of `n_psl211_number.v`**, measured below.

## The slow sentence of `n_psl211_number.v`, found and removed

The first version of `psl211_alldecks_indistinguishability_number_ge` closed
with

```coq
move: T.
rewrite psl211_perdeck_static_mass_true psl211_perdeck_static_mass_false.
```

Per-sentence timings of that version, `rocq compile -time`, longest first:

```
Chars 6615 - 6680 [Print~Assumptions~psl211_allde...]  21.273 secs
Chars 6463 - 6536 [rewrite~psl211_perdeck_static_...] 227.946 secs
Chars 6582 - 6608 [by~rewrite~invr_ge0~ler0n.]          0.001 secs
Chars 6537 - 6581 [rewrite~sub0r~normrN~ger0_norm...]   0.003 secs
Chars 6454 - 6462 [move~:~T~.]                          0.001 secs
Chars 6371 - 6453 [have~T~:=~~Order.POrderTheory....]   0.003 secs
Chars 6353 - 6370 [rewrite~Hd~in~~~H0.]                 0.001 secs
Chars 6215 - 6352 [have~Hd:~~sa_cut_dist~(amf_sam...]   0.    secs
Chars 6080 - 6214 [have~H0~:=~~Hprop~psl211_perde...]   0.003 secs
```

One sentence holds 228 of the 251 seconds. It is the cross-reader rewrite that
`instances/psl211/psl211_reading_constancy.v` already warns about in its own
proofs: the goal at that point holds both chiralities' readers, and a rewrite
whose pattern names one of them tests the pattern against the other too, a
mismatch decided by conversion on the two twelve-entry deck tables.

The fix is the discipline that file states and this probe's own supporting
lemmas already follow: substitute each mass by one `congr1` in term mode and
transport the inequality with `eq_ind`. The rewrite is gone from the file; the
comment beside the replacement carries the measurement.

A landing that puts N9 in a phase file should keep the term-mode form. The
remaining 21 s of the file is one `Print Assumptions`, which a landing would
not carry.
