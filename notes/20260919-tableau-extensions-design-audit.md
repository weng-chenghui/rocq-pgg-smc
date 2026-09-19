# Design audit: extending the Tableau to hold what the repository has found

DESIGN NO-GO for starting a compile probe on this placement.

Date: 2026-09-19. Independent design audit of
`notes/20260919-tableau-three-extensions-probe-design.md`, read against the
real infrastructure. Read-only: nothing was compiled and no file of the tree
was edited. This file is the only new file.

The mathematics the design wants is right and the repository wants it. The
placement of finding 1 is not, and the first file a probe would write from
this spec cannot typecheck at two of its three pinned instances. Findings 2, 3
and 4 each sit at the right phase but each rests on one statement about the
infrastructure that is false. Every correction below is concrete enough to
restart from.

The single strongest fact the design does not know: **the proposition finding 1
wants is already a landed theorem at PGL(2,7)**, `pgl27_view_mixing`
(`instances/pgl27/pgl27_word_privacy.v:233-239`), already named in the
manifest's own capability table
(`manifest/pgg_analysis_manifest.v:201-203`) and already aliased by the facade
(`instances/pgl27/pgl27_analysis.v:263`). It is carried by no row. Its shape is
a certificate and a proposition about one model. It is not an edge between two
rows, and its ideal is not the exact row's model.

---

## Per-finding verdicts

| # | Finding | Verdict | Recommended change | Evidence |
|---|---|---|---|---|
| 1 | ideal/actual relation as a step consuming a finished exact row | **change** | Make it a third `SecurityPort` arm at `AnalysisBridged`, not a step between rows. Its certificate carries an ideal `SampleAdapter` over the same execution, that ideal's `ExactWitness`, the actual model's secret at the same `finType`, and one distance on the joint reading-and-secret carrier. Drop PGL(2,7)'s exact row as the ideal and build a prior-indexed ideal family instead. Drop the Kim half. | `manifest/pgg_tableau.v:149-152`, `:179-186`, `:377-381`; `instances/pgl27/pgl27_models.v:410-412` vs `:417-419`; `instances/pgl27/pgl27_word_privacy.v:233-239` |
| 2 | leakage in bits at the full reveal, a second claim on one row | **change** | Phase is right. The stated reason is wrong: the leakage observer is not an observer the `Sampled` phase knows. Carry the second claim in the **proposition family** of `TableauAt`, not in the data slot of `StackAt AnalysisBridged`. Generalize `PublishedRowAt` by that family so a published row displays its claims in its type. | `manifest/pgg_tableau.v:286-296`, `:410-416`, `:638-645`, `:678-686`; `instances/kim2025/five_card_rows.v:516-529`; `instances/kim2025/five_card_models.v:284-288` |
| 3 | conclude with an inequality | **keep**, one correction | Needed, and for a reason the design states imprecisely. `restate` already publishes a weaker number as a proposition. What it cannot do is publish a **manifest row** at that number, because `RestatedTableau` holds no `AnalysisPathRow`. Say that. Also drop ledger row F3.2, whose evidence does not test what it claims. | `manifest/pgg_tableau.v:610-616`, `:652-672`, `:678-686`; `instances/pgl27/pgl27_rows.v:417-454`, `:389-394` |
| 4 | refutations publishing `NegativeTransfer` | **change** | Phase `AnalysisBridged` is right and is backed verbatim by the status file. But `psl211_fixed_deal_view_dep` is not stated at any observed execution's observer, so no row can take it today and `NegativeTransfer` as documented does not describe it. The first deliverable is a fixed-deck `AnalysisModelFamily` over `psl211_alldecks_observed` and the bridge lemma. The port is the last step, not the first. | `manifest/pgg_analysis_status.v:14-17`, `:68-69`; `instances/psl211/psl211_models.v:1158-1166`; `instances/psl211/psl211_rows.v:17-18`, `:40-46`; `manifest/pgg_analysis_manifest.v:628-631` |

---

## b. Feasibility of finding 1 against the real types

### b.1 A payload can mention another row's data, and the prefix can be forced by type

`tableau_bind` takes a payload family `P : StackAt a -> Type`
(`manifest/pgg_tableau.v:428-432`). The family may mention the incoming stack
freely, so nothing forbids a payload that carries a second model or a whole
second row. The design's F1.3 is not blocked by the carrier.

There are two ways to force the shared prefix, and only one of them is free of
transport.

**The equation route, not recommended.** Take the payload to be a value
`r : Tableau AnalysisBridged` together with `ab_obs (tableau_at r) = sp_obs x`.
That equation is a propositional identity between two `OE.ObservedExecution`
records built from three proof terms
(`manifest/pgg_tableau.v:169-178`, `:206-207`, `:236-237`). The tail lemma
would then have to transport an `ExactProp` along it, and `ExactProp` mentions
the adapter, the profile and the execution
(`manifest/pgg_tableau.v:304-325`). In practice two rows over one prefix are
definitionally equal, which is why `five_card_row_repeated_prefixE` closes by
`by split` (`instances/kim2025/five_card_rows.v:418-425`). Paying for a
transport that is always `erefl` is the wrong trade.

**The reconstruction route, recommended.** Note that `StackAt AnalysisBridged`
differs from `StackAt Sampled` by exactly two components, the family and the
port (`manifest/pgg_tableau.v:173-186`). So from `x : StackAt Sampled` and a
pair

```
g  : AnalysisModelFamily (sp_obs x)
w  : forall (R : realType) (idx : amf_index g R), ExactWitness (amf_sample g R idx)
```

the term

```
existT _ (projT1 x) (existT _ (projT1 (projT2 x))
  (existT _ (sp_Ht x) (existT _ (sp_He x) (existT _ (sp_Hr x)
    (existT _ g (fun R idx => ExactIndependence (w R idx)))))))
```

is a `StackAt AnalysisBridged` whose `ab_Ht`, `ab_He`, `ab_Hr` and `ab_obs`
reduce to `sp_Ht x`, `sp_He x`, `sp_Hr x` and `sp_obs x` by `iota`, because
those accessors are plain `projT` chains (`manifest/pgg_tableau.v:212-222`,
`:228-240`). The shared prefix is therefore forced by construction, with no
equation and no transport. The pair `(g, w)` is exactly the data of a finished
exact row over `x`'s own prefix: the Observed stack can be rebuilt from `x` the
same way, `sample_step` applied to it at `g` gives the Sampled row, and
`certify_exact` at `w` finishes it (`manifest/pgg_tableau.v:502-511`,
`:577-584`). A probe can exhibit that row by `erefl` as a side lemma without
making the statement consume it.

So the design's stated benefit, "the types force the two rows to share the
algebra, the run and the observed execution", is available. It does not require
a new notion of an arrow between rows.

### b.2 But a certificate cannot hold a family, and does not need to

`SecurityPort` is parameterised by `(R, A, E, sa)` only
(`manifest/pgg_tableau.v:149-152`). It does not know the observed execution or
the family, so a new certificate record cannot have a field of type
`AnalysisModelFamily (sp_obs x)`. It can have a field of type
`SampleAdapter R (instance_exec E)`, which is the type of every member of every
family over an observed execution built from `E`. That is enough: the ideal
enters a certificate as one adapter per real field and index, which is what
`ExactPayload` and `SpectralPayload` already are
(`manifest/pgg_tableau.v:518-528`).

This matters for the design's own framing. `SpectralCert` already carries an
ideal, `sc_ideal`, a bare law on the cut carrier
(`manifest/pgg_tableau.v:136`). The design's complaint is that it is a bare law
and not a model. Upgrading it from a law to an adapter with a witness is a
change of the same kind at the same phase, and it delivers what the design
asked for.

### b.3 No universe or elaboration hazard is visible, and one is confirmed absent

`SecurityPort` is in `Type`, `ExactWitness` and `SpectralCert` are records in
`Type` over a `finType` and an `fdist`, and `StackAt` is a chain of `sigT` in
`Type`. A new record of the same shape adds no universe level. The quantifier
`forall (R : realType) (idx : amf_index f R)` is already crossed six times in
the file and once in each instance payload. The one recorded mechanical trap in
this area is the reprice payload's missing per-index abstraction, which the
Kim batch reproduced and diagnosed: the obligation is
`forall R, forall idx, match ab_port ... with ... end`, and a bare field-level
identity at every field does not fit. That is a payload-shape trap, not a
universe trap.

### b.4 What "the distance between the two sampled laws" can mean

This is where the design is thinnest, and the answer is forced by the types.

`ep_inputT : Type` (`protocol/pgg_execution_plug.v:62`). It is **not** a
`finType`. Therefore `sa_arg` cannot be pushed forward to an `fdist`
(`security/pgg_sample_adapter.v:119-120`), and there is no such thing as "the
joint law of the argument and the cut" in this development. The only carriers
on which two adapters over one execution can be compared are:

| carrier | pushforward | availability |
|---|---|---|
| `pgg_gT (mp_M mp)` | `sa_cut_dist` (`security/pgg_sample_adapter.v:196`) | always |
| `{ffun seatT -> cardT}` | `sa_coalition_dist ... 0 C` (`:185`), per coalition | always |
| `{ffun seatT -> cardT} * secretT` | joint of the reading and a secret random variable | needs a secret on each side at one common `finType` |
| `ep_inputT` | none | impossible |

The three instances differ sharply, and the design treats them as if they did
not.

**Kim, biased row: the easy case, and the only one where the two sample spaces
coincide.** `kim_single_sample` has "carrier and both maps exactly those of
`five_card_sample`; only the distribution differs"
(`instances/kim2025/five_card_models.v:137-142`, against
`instances/kim2025/five_card_exec.v:624-626`). Both are `five_card_leakage.Omega`
with `five_card_sample_arg` and `five_card_sample_cut`. So the distance is
`var_dist (kim_input_dist ...) (P R)` on one finite sample space, and every
downstream distance, the reading's, the secret's, the joint's, follows by
`var_dist_fdistmap` (`security/pgg_collusion_bound.v:126`) with no further
hypothesis. This is the instance a probe should start at, not PGL(2,7).

**Kim, repeated row: different carrier.** `kim_repeated_sampleT` is
`(bool * bool) * L.-tuple 'I_5` (`instances/kim2025/five_card_models.v:146-147`).
The common carrier is the cut carrier or the joint reading-and-secret carrier.

**PGL(2,7): different carrier, and the pinned ideal is the wrong one.**
`pgl27_exact_family` is indexed by `unit` with law `pgl27P R`, uniform secret
times uniform cut (`instances/pgl27/pgl27_models.v:410-412`;
`instances/pgl27/pgl27_secrecy.v:66-67`). `pgl27_word_family` is indexed by
`R.-fdist bool` with law `secretP `x pgl27_word_wordP`
(`instances/pgl27/pgl27_models.v:417-419`;
`instances/pgl27/pgl27_exec.v:536-537`). Their `(secret, cut)` pushforwards are
`pgl27P_word_gen secretP = secretP `x rho_word` and
`pgl27P R = uniform `x U` (`instances/pgl27/pgl27_word_privacy.v:96-103`).
The variation distance between those two is at least the distance between the
secret marginals, `var_dist secretP uniform`, which is not small and is not
bounded by `pgl27_word_mixing`. The word row is quantified over every prior. So
the design's F1.4, "each consuming its instance's existing exact program
unchanged", is **false at PGL(2,7) for every non-uniform prior**, and the index
types do not even match, `unit` against `R.-fdist bool`.

The ideal PGL(2,7) actually needs is `pgl27P_gen secretP = secretP `x U`
(`instances/pgl27/pgl27_word_privacy.v:96-97`), the same prior with the exact
cut. That adapter and that family do not exist in the tree. Building them is a
named, small deliverable, and it should replace the pinned carrier.

**PSL(2,11): no word model at all.** The exact family is unit-indexed over
`psl211_inputT * pgg_gT psl211_M` with the uniform deck description times the
uniform cut (`instances/psl211/psl211_models.v:192-205`, `:222-227`, `:516-518`).
The design's pinned word model on the same carrier with
`rho_from_words_weighted` is the right shape. Its distance payload is named as
`psl211_joint_mixing`, which is stated at `secretP : R.-fdist bool`
(`instances/psl211/psl211_mixing.v:595-604`) and so does not apply at
`R.-fdist psl211_inputT`. The generic ingredient is `var_dist_prodR`
(`instances/psl211/psl211_mixing.v:577-588`), which is polymorphic in the first
factor and gives the right statement in one line. Two corrections follow: the
design's cited object is wrong, and the replacement is declared `Local`, so a
probe file importing `psl211_mixing` cannot name it and has to restate it. Both
belong in the spec so the probe does not chase them.

### b.5 The honest statement, given all of the above

Not a coupling map, not a common sample space in general, and not the distance
of two sample laws. The honest and instance-agnostic form is a distance on the
**joint reading-and-secret carrier, per coalition below the threshold**:

```
forall (C : {set seatT}), (#|C| < profile_k ...)%N ->
  var_dist (fdistmap (fun u => (sa_coalition_view sa 0 C u, secret_actual u))
                     (sa_sampleP sa))
           (fdistmap (fun u => (sa_coalition_view ideal 0 C u, ew_secret w u))
                     (sa_sampleP ideal))
  <= eps
```

Every term is on a `finType`. Each instance discharges it in its own way: Kim's
biased row by data processing from one sample-law distance, PGL(2,7) by
`pgl27_view_mixing` restated, PSL(2,11) by the generalized `var_dist_prodR`
plus `psl211_word_mixing`. This is the form that fits the phase meaning, and it
is the one most likely to elaborate, because it names no carrier that is not
already a `finType` in the file.

---

## c. What the proposition should be

Write `V` for the coalition's reading, `S` for the secret, `J` for their joint
law under the actual model, `M` and `P_S` for `J`'s own marginals.

The four candidates:

- **(A)** `var_dist J (M `x P_S) <= k * eps`. The design's proposal.
- **(B)** `var_dist J J_ideal <= eps` together with `J_ideal = M_ideal `x P_S_ideal`.
- **(C)** for every pair of secret values `s, s'`, `var_dist (V | s) (V | s') <= c`.
- **(D)** `I(S ; V) <= f(eps)`.

**Which is strongest.** (C) is strongest. It implies (A) with constant 1, by
`var_dist J (M `x P_S) = E_s [ var_dist (V|s) M ]` and
`M = sum_{s'} p(s') (V|s')`, so each inner distance is at most the maximum over
pairs. The converse costs a factor `1/p_min`: (A) at bound `d` gives
`var_dist (V|s) M <= d / p(s)`, hence
`var_dist (V|s) (V|s') <= d/p(s) + d/p(s')`, which is `4d` at a uniform bit. So
(C) is strictly stronger, and prior-free, which (A) is not.

**Which is statistical privacy.** (C) is the statement a cryptographer reads as
statistical privacy of a threshold scheme: below the threshold, two secrets are
statistically indistinguishable to the coalition. (A) is the weaker
prior-dependent form, usually called `eps`-independence or approximate
independence. (B) is a hybrid step and not a conclusion: on its own it says
nothing until the ideal's independence is used, which is why the design is
right to make the published proposition mention the actual model only.

**Which can be derived from which.** (B) plus the ideal's independence gives (A)
with `k = 2` when the two secret marginals agree and `k = 3` otherwise, by the
triangle inequality and two applications of `var_dist_fdistmap`
(`security/pgg_collusion_bound.v:126`) for the marginals. The design's F1.2
constant analysis is therefore correct as stated. (D) is derivable from (A) only
through a distance-to-divergence inequality, which the design has correctly put
out of scope.

**The existing spectral arm already states (C).** `SpectralPropAt`
(`manifest/pgg_tableau.v:331-339`) is exactly (C), with one caveat: it pushes
`static_coalition_obs C x` forward along `sa_cut_dist sa`, which is the
conditional law of the reading given argument `x` **only if the cut is
independent of the argument** under `sa_sampleP`. That premise holds at every
instance in the tree, all three model laws being products
(`instances/pgl27/pgl27_exec.v:536-537`,
`instances/kim2025/kim_input_privacy.v:58-60`,
`instances/psl211/psl211_models.v:200-201`), but the Tableau nowhere requires
it, so `SpectralPropAt` is literally a statement about a synthetic law. The
probe should state that premise where it uses it rather than leave it implicit.

**Does `ExactWitness` carry what is needed.** Partly. `ew_secretT` is a
`finType` and `ew_secret : {RV (sa_sampleP sa) -> ew_secretT}`
(`manifest/pgg_tableau.v:117-118`), so the ideal's secret is a random variable
on the **ideal** sample space. There is no secret on the actual sample space
anywhere in the Tableau: the spectral arm has none, and the actual row never
reaches `certify_exact`. So the new certificate must carry the actual secret as
its own field, typed at `ew_secretT` of the ideal witness so the two joint laws
live on one carrier. That field is the one piece of new data finding 1 genuinely
needs, and the design does not mention it.

---

## d. Relation to what already exists

**Finding 1 against `SpectralDecay`.** The two propositions genuinely differ,
and neither subsumes the other in general.

- (C) implies (A) with constant 1 whenever the cut is independent of the
  argument. So wherever the spectral arm closes, finding 1's claim adds no
  mathematical content. The Kim batch just closed it for **both** Kim rows,
  with `sc_ideal` the uniform rotation law and all five certificate fields
  reached by `Qed`. The design's pinned carriers for finding 1 include exactly
  those two rows. That half of finding 1 is redundant and should be dropped
  rather than probed.
- (A) does not imply (C): averaging over the argument destroys the per-argument
  statement. This is the real gap, and PSL(2,11) is where it bites. `sc_const`
  asks for constancy of the ideal's reading at **every pair of run arguments**
  (`manifest/pgg_tableau.v:138-142`), and under the all-decks dealer the run
  argument is the whole public deck description, of which the secret is one
  coordinate. The probe refutations show the field fails there, and at a
  measured floor of roughly `10/11`, while the exact arm's averaged
  independence holds. So the expressiveness gap is precisely **that no arm can
  say "constant in the secret coordinate, averaged over the public ones"**.

That is a much better statement of the problem than "the ideal and the actual
model are related", and it should replace the design's opening. The ideal model
is a proof device for reaching (A); the claim itself mentions one model, as the
design's own F1.3 admits.

**Dealt mode.** In dealt mode `ex_inputT` is the secret itself
(`manifest/pgg_tableau.v:465-469`), so (C) at the argument is (C) at the
secret, and the two propositions are equivalent up to a factor of at most 4 for
a uniform bit. PGL(2,7) is a dealt row (`instances/pgl27/pgl27_rows.v:124-129`),
so there the spectral arm and finding 1 say the same thing twice.

The design should say: **the spectral arm is the argument-level statement, and
the new arm the secret-level averaged one; they coincide up to constants
exactly when the run argument carries nothing but the secret.** Note this is
not the same as "the dealt-mode special case": Kim's encoded run has argument
`bool * bool` while its exact-arm secret is the conjunction
(`instances/kim2025/five_card_rows.v:321-325`), so there the spectral arm is
strictly stronger than the secret-level claim, which is why
`five_card_static_obs_const` was provable at all four layouts.

**Finding 3 against `restate`.** `restate` already allows a weaker number: its
payload is `StackProp AnalysisBridged q -> Q` for an arbitrary `Q`
(`manifest/pgg_tableau.v:652-654`), and `pgl27_word_bridge` already uses it to
hand over a statement at `2^-39`
(`instances/pgl27/pgl27_rows.v:417-429`). What `restate` cannot do is publish:
`RestatedTableau` has two fields and neither is an `AnalysisPathRow`
(`manifest/pgg_tableau.v:660-663`), while `PublishedRowAt` has three and one is
(`:678-682`). So the change is needed, and the correct statement of the problem
is that `conclude` is the only terminal that keeps the manifest row and its
obligation is an equality (`:610-616`), not that a weaker number is unreachable.

Ledger row F3.2 should be dropped or rewritten. With an inequality obligation a
number below the proved one fails because the obligation is unprovable, and
unprovability is not a `Fail`. The cited witness `pgl27_row_word39_bare`
(`instances/pgl27/pgl27_rows.v:389-394`) fails for an unrelated reason, the
missing per-index abstraction, so it tests nothing about the direction of the
inequality.

**Finding 4 against `NegativeTransfer`.** The documented meaning is "a theorem
transporting an obstruction to the path's observer"
(`manifest/pgg_analysis_status.v:68-69`).
`psl211_fixed_deal_view_dep` is a negated independence at
`dealer_shuffle_view ... (psl211_dealer_view psl211_perdeck_coalition)` over the
law `psl211_fixed_dealP` on `bool * (psl211_deal * cutT)`
(`instances/psl211/psl211_models.v:1143-1166`). That observer is a dealer-model
reader, not `static_coalition_obs`, and that law is not the law of any
`SampleAdapter` over any `ExecutionPlug`. So today it is **not** a theorem at
the path's observer, and a row publishing `NegativeTransfer` on it would
misdescribe itself. The repository has already recorded this twice, in the row
file's own header (`instances/psl211/psl211_rows.v:17-18`) and in the manifest's
row-9 justification (`manifest/pgg_analysis_manifest.v:630-632`).

The level is right, and for a reason the design does not cite: the status file
says in its own words that a bridged path relates "a security, leakage, mixing
or limitation theorem to the same distribution and the same observer as its
sample, **which a negative mixing result also does**"
(`manifest/pgg_analysis_status.v:14-17`). So `AnalysisBridged` admits a
refutation by the file's own definition. What is missing is the model and the
bridge, and there is a favourable fact the design misses: the fixed-deck dealer
needs **no new run**. `psl211_alldecks_params` drives a supplied-layout run
whose argument is the deck description
(`instances/psl211/psl211_rows.v:126-134`,
`instances/psl211/psl211_models.v:210-216`), so a fixed deck is a point mass on
that argument and a new `SampleAdapter` over the same
`psl211_alldecks_observed` suffices. That reuse should be the spec's first
deliverable for finding 4, and F4.2's "if the landed theorem is stated on a
carrier the row cannot use" should be resolved to "it is, and here is the
bridge".

---

## e. A second claim on one row

### What the real types allow

`StackAt AnalysisBridged` holds exactly one port per field and index
(`manifest/pgg_tableau.v:179-186`). `StackProp AnalysisBridged` is
`BridgedProp no_reprice` (`:398`), a left-nested conjunction whose right
conjunct quantifies over `R` and `idx` and applies `PortProp`
(`:377-381`). `PortProp` matches on the port (`:363-369`). `RepricePayload`
matches on it again (`:610-615`), `port_reprice` cases on it (`:622-631`), and
the four projections are `proj1`/`proj2` chains into that conjunction
(`:700-722`).

**Option 1, a list of ports.** Change the last component of
`StackAt AnalysisBridged` to a `seq (SecurityPort ...)`. What breaks:
`certify_exact` and `certify_spectral` build a bare constructor
(`:583`, `:598`), `ab_port`'s type (`:241-245`), both `match`es, and, worst,
the four projections. `view_secrecy_of` currently returns
`forall R idx, PortProp ...`, which reduces to `ExactProp` at an exact row, and
`pgl27_exact_view_secrecy` closes by `exact: (view_secrecy_of ... R tt C HC)`
(`instances/pgl27/pgl27_rows.v:539`). With a list the projection returns an
`all` over a list and that `exact:` fails at all four instances
(`instances/pgl27/pgl27_rows.v:539`,
`instances/kim2025/five_card_rows.v:377`,
`instances/s5/s5_rows.v:318`,
`instances/psl211/psl211_rows.v:221`). G1 fails.

**Option 2, a product constructor.** Add `BothPorts of SecurityPort & SecurityPort`.
Existing programs survive by conversion, the two `match`es gain one branch, and
the projections still reduce at one-port rows. This is the least disruptive
**data** change. It is also the shape the owner rejected once, and it has a
real defect: it fixes the arity at two and gives no way to say which claim is
which, so a reader of a published row cannot tell the leakage claim from the
privacy claim.

**Option 3, a repeatable `certify` at `AnalysisBridged`, in the proposition
family. This is the recommendation.** `TableauAt` is already indexed by an
arbitrary proposition family `Q : StackAt b -> Prop`
(`manifest/pgg_tableau.v:410-416`), and `conclude` already exploits exactly
that, returning `TableauAt AnalysisBridged (BridgedProp c)` rather than a
`Tableau` (`:638-645`). So a second claim can be adjoined as

```
certify_more : forall (q : StackAt AnalysisBridged),
  StackProp AnalysisBridged q -> NewPayload q ->
  TableauAt AnalysisBridged (fun q' => StackProp AnalysisBridged q' /\ NewProp q')
```

with **zero** change to `StackAt`, `StackProp`, `SecurityPort`, `PortProp`,
`RepricePayload`, `port_reprice`, `ab_port` or any existing program or
projection. The claim's own data, its observer and its bound, rides in
`NewPayload` and is named in `NewProp`. The statement is repeatable because the
family it returns is itself an argument.

**What breaks in option 3, and how to fix it.** Only `publish`. It takes
`pf : BridgedProp c q` and `PublishedRowAt` stores
`published_thm : BridgedProp c published_at`
(`manifest/pgg_tableau.v:678-682`, `:691-696`), so the second conjunct is
dropped at the terminal. The fix is parametric and small: generalize the record
to a proposition family,

```
Record PublishedRowAtQ (Q : StackAt AnalysisBridged -> Prop) := ...
Notation PublishedRowAt c := (PublishedRowAtQ (BridgedProp c)).
Notation PublishedRow    := (PublishedRowAt no_reprice).
```

Both existing notations survive, so every `PublishedRow` ascription in the four
rows files and every projection keeps its type.

### How a published row shows which claims it carries

`AnalysisPathRow` has five fields and none names an arm
(`manifest/pgg_analysis_manifest.v:707-725`). It cannot show this, and the
design is right that the manifest record must not be edited.

Under option 3 it does not have to. The proposition family `Q` is an **index of
the published row's type**, so a row carrying two claims has a visibly different
type from a row carrying one, and the difference is checked by the kernel at
every ascription. That answers F2.4 in the affirmative and without touching the
manifest: the arm is displayed by the Tableau's own record, and
`AnalysisPathRow` keeps describing the path rather than the proof.

### The phase reason the design gives for finding 2 is wrong

The design says the `Sampled` phase "already identifies the executed reader with
the static one at every set of seats, with no threshold, so the full reveal is an
observer the row already knows". `sampled_viewE_prop` quantifies over
`C : {set seatT}` and identifies `sa_coalition_view` with the static reading,
valued in `{ffun seatT -> cardT}` (`manifest/pgg_tableau.v:286-296`). Kim's
leakage bound observes `five_card_exec_colour_view A` for `A : seq nat`, a list
of **card positions**, valued in `(size A).-tuple bool`
(`instances/kim2025/five_card_models.v:284-288`,
`instances/kim2025/five_card_rows.v:516-529`). Different index, different
carrier. The `Sampled` link lemma does not reach it.

There is a second, larger mismatch the design does not mention at all. Kim's
quantity is a **conditional** mutual information of a triple, the input pair,
the reading, and the output `a && b`
(`instances/kim2025/five_card_rows.v:517-528`). The Tableau's exact arm has one
secret random variable and no conditioning
(`manifest/pgg_tableau.v:114-122`, `:304-325`). So finding 2 is not "the same
phase with a wider observer". It is a different secrecy notion, input privacy
given the output, for which the Tableau has no vocabulary at any phase. The
spec should say so, because it changes what the header sentence at
`manifest/pgg_tableau.v:23-24` has to become, and the design's G3 currently
promises only to weaken the threshold clause.

Ledger row F2.2 already anticipates the observer mismatch, so the correction is
to the Placement prose and not to the probe's plan.

---

## f. What the repository has found that still has no place after all four extensions

Each item with the phase it would belong to. These are listed, not designed.

1. **`pgl27_view_mixing`** (`instances/pgl27/pgl27_word_privacy.v:233-239`).
   The joint law of the reading and the secret under the word shuffle, within
   `2^-40` of the product of the exact-shuffle marginals, at every prior and
   every coalition below the threshold. Already in the manifest capability
   table (`manifest/pgg_analysis_manifest.v:201-203`) and in the facade
   (`instances/pgl27/pgl27_analysis.v:263`). Phase: `AnalysisBridged`. Finding 1
   would hold it, at the corrected ideal.
2. **Trace-observer results at PGL(2,7)**: `pgl27_coalition_trace_secrecy`
   (`instances/pgl27/pgl27_trace.v:429`), `pgl27_word_trace_indist`
   (`instances/pgl27/pgl27_word_privacy.v:208`), `pgl27_exec_trace_indist`
   (`instances/pgl27/pgl27_models.v:335`). The observer is the content trace,
   not `sa_coalition_view`, and `sampled_viewE_prop` names only the latter.
   Phase: `AnalysisBridged` with a second observer.
3. **`pgl27_view_leakage_le`** (`instances/pgl27/pgl27_secrecy.v:98`). Leakage
   is monotone in the coalition, at every size including above the threshold.
   No arm states anything at or above the threshold except the existential
   `ExactLeakAt` annotation at one size
   (`manifest/pgg_tableau_syntax.v:260-269`). Phase: `AnalysisBridged`.
4. **One-seat endpoint marginal bounds**: `five_card_row_repeated_endpoint_lt`
   (`instances/kim2025/five_card_rows.v:488-493`) and
   `S5Analysis.exec_endpoint_bound` (`manifest/pgg_analysis_manifest.v:1863-1869`).
   Neither quantifies over a coalition. The manifest puts `s5_row_word` at
   `AnalysisBridged` on the strength of one of them. Phase: `AnalysisBridged`,
   no arm takes it.
5. **`s5_row_word` as a program** (`instances/s5/s5_rows.v:54-73`). Two of the
   five `SpectralCert` fields are out of reach, one for a reason the file
   records as removable by no proof. Phase: `AnalysisBridged`.
6. **The PSL(2,11) mixing family**: `psl211_word_mixing`,
   `psl211_endpoint_mixing`, `psl211_joint_mixing`
   (`instances/psl211/psl211_mixing.v:545`, `:564`, `:595`). No PSL(2,11) model
   draws a word cut, so there is no row for any of them. Phase: `Sampled` and
   `AnalysisBridged`.
7. **Trace secrecy generally.** "Trace secrecy is not a field of an
   `AnalysisPathRow`, so no trace row is written"
   (`instances/psl211/psl211_rows.v:44-46`). Phase: `AnalysisBridged`.
8. **`ExactLeakAt 6` at PSL(2,11)** (`instances/psl211/psl211_rows.v:46-48`).
   The surface exists; the six-seat separation is a numeric check and not a
   theorem, so the blockage is at the instance and not at the Tableau.
9. **The PSL(2,11) deck parametrization** (`instances/psl211/psl211_rows.v:48-55`).
   Checked numerically, not in Rocq. Phase: `Sampled`, a fact about the model's
   index.
10. **The dealer-model impossibility family**:
    `psl211_dealer_view_indep_of_deck_unsat`
    (`instances/psl211/psl211_models.v:1116-1123`), `psl211_perdeck_law_neq`,
    and `psl211_fixed_deal_view_dep` (`:1158`). All stated below the execution
    layer, at `dealer_shuffleP` and not at any `SampleAdapter`. Phase: none
    today. Finding 4 would reach the third only after a new model and a bridge.
11. **`realises_expected` at all four instances**
    (`instances/pgl27/pgl27_rows.v:609`,
    `instances/kim2025/five_card_rows.v:579`, `instances/s5/s5_rows.v:356`,
    `:381`). The specification a run meets has no place in the accumulated
    proposition, by an explicit design choice
    (`manifest/pgg_tableau_syntax.v:170-186`). Phase: `Observed`.
12. **Three of the nine manifest rows have no publishable program**, because
    `publish` is defined only at `AnalysisBridged`
    (`manifest/pgg_tableau.v:691-696`): `five_card_row_repeated` at `Sampled`
    (`manifest/pgg_analysis_manifest.v:1787`), `five_card_row_biased` whose
    program stops at `Sampled` against an `AnalysisBridged` row
    (`instances/kim2025/five_card_rows.v:465-475`), and `s5_row_det` at
    `Observed` (`manifest/pgg_analysis_manifest.v:1796`). Phase: `Observed` and
    `Sampled` each need their own terminal. None of the four extensions supplies
    one.
13. **A restated statement cannot be published.** `RestatedTableau` carries no
    `AnalysisPathRow` (`manifest/pgg_tableau.v:660-663`), so
    `pgl27_word_view_indist_restated` at `2^-39`
    (`instances/pgl27/pgl27_rows.v:448-454`) exists only beside its row. Phase:
    the terminals. Finding 3 addresses the number and not this.
14. **Privacy under alternative dealer laws at PGL(2,7)**:
    `pgl27_view_indep_alldecks`, `pgl27_view_indep_deck`,
    `pgl27_view_indep_deck_prior` (`instances/pgl27/pgl27_secrecy.v:215`,
    `:232`, `:249`). Each would need its own model family over the same
    observed execution. Phase: `Sampled` and `AnalysisBridged`.

---

## g. The Structure paragraph

Three claims, one accurate, one false, one decorative.

**"A parameterised monad indexed by the completion level before and after a
statement."** Roughly accurate as a description of the indexing, generous as a
description of the structure. `tableau_bind` is a dependent application:
`f (tableau_at s) (tableau_thm s) p` (`manifest/pgg_tableau.v:428-431`). The
continuation type `T` is an arbitrary `Type`, not a level-indexed carrier, so
nothing constrains a statement to land at a level at all, and the level
discipline is enforced only by each statement's written return type. One law is
stated, `tableau_left_unit`, and it holds by `erefl` (`:452-456`). No
associativity law is stated, and none is needed, because with an arbitrary `T`
associativity is function application. There is no polymorphic unit;
`tableau_start` is one specific element at one level (`:445-446`). What is
really there is a pre-and-post-indexed family of statements that compose by
application, with a definitional left unit. Closer to a parameterised reader
than to a monad, and the file's own header is more careful than the design's
paragraph: it says "sequencing", not "monad".

**"Now also graded by the accumulated bound."** False. No type and no
proposition accumulates a bound. `Reprice` is chosen by the caller of the
terminal and is a parameter of the proposition family
(`manifest/pgg_tableau.v:353-357`, `:363-369`), not a grade that composes.
`ExactProp` mentions no number at all (`:304-325`), so every exact row would
have to be graded by something that does not occur in it. And nothing adds two
bounds: `cert_eps` is the certificate's own `eps` written twice (`:345-347`),
which is the transfer inequality's two crossings and not an accumulation across
lines. If a grade is wanted it has to be built, and building it is a larger
change than any of the four findings.

**"Rows form the objects of a small category and that step is an arrow from the
ideal row to the actual one."** Decoration. The proposed step starts at
`Sampled` on the actual row and ends at `AnalysisBridged` on the actual row.
The ideal row is data inside the payload. No two such steps compose, there is
no identity arrow at a row, and no associativity is claimed or provable. Under
the recommendation of section b the ideal is a certificate field and the
question does not arise.

What is true and worth saying instead: the statements form an indexed family
over `CompletionLevel` whose composition is application and whose left unit is
definitional; the propositions grow by one conjunct on the right from `Sampled`
upward, which is what makes the named projections `proj` chains; and the
published bound is a parameter of the proposition family rather than an
accumulated quantity.

---

## Recommended shape for finding 1

Make finding 1 a third `SecurityPort` arm at `AnalysisBridged`, not a step
between rows, because the claim it publishes is a claim about one model, which
is what that phase holds. Its certificate carries four things: an ideal
`SampleAdapter R (instance_exec E)` over the row's own execution, that ideal's
`ExactWitness`, the actual model's secret random variable typed at the ideal
witness's own `ew_secretT`, and one distance bound on the joint
reading-and-secret carrier, quantified over coalitions below the threshold. The
ideal adapter together with its witness is exactly the data of a finished exact
row over the shared observed prefix, and the probe can exhibit that row by
`erefl` as a side lemma, so the design's stated benefit is kept without a new
notion of an arrow between rows and without any equation to transport along.
The composition law, in the place of `exact_tail` and `spectral_tail`, derives
the published proposition, the actual joint law within `k * eps` of the product
of its own marginals, from the ideal's independence by one triangle inequality
and two applications of `var_dist_fdistmap`, with `k = 2` when the two secret
marginals agree and `k = 3` otherwise.

## Order the probe should run in

Not the design's F3, F1, F2, F4. Start at Kim's biased row, the one instance
where the ideal and the actual adapter share a sample carrier and differ only
in the law, so that the arm's shape is settled before any carrier work. Then
PGL(2,7), where the prior-indexed exact family has to be built first and
`pgl27_view_mixing` is the target to reproduce. Then PSL(2,11)'s word model,
which is the only case that motivates the arm at all. Finding 3 is independent
of all of this and can run first or last. Findings 2 and 4 each need one bridge
lemma before any Tableau work, and should not be started until those lemmas are
probed.

## Three largest risks

1. **The Kim half of finding 1 is already done by the spectral arm.** Both Kim
   rows now carry a `SpectralCert` whose `sc_ideal` is the uniform rotation law
   and whose five fields are all reached. Probing finding 1 at those two rows
   spends the batch reproving a weaker statement. Drop them and keep PSL(2,11)
   as the motivation.
2. **The pinned PGL(2,7) carrier cannot work.** `pgl27_exact_family` is
   `unit`-indexed at a uniform secret and `pgl27_word_family` is indexed by the
   prior, and the distance between their sample laws is bounded below by the
   distance between the secret marginals. F1.4 as written is false. The probe
   must build a prior-indexed exact family at `pgl27P_gen secretP` first, and
   the spec must say so.
3. **Finding 4's payload is not stated at any row's observer.** The refutation
   lives on the dealer-law carrier, and two places in the tree already record
   that it is not a row. Without the new fixed-deck family over
   `psl211_alldecks_observed` and the bridge to `static_coalition_obs`, a row
   publishing `NegativeTransfer` would assert a status the status file does not
   support.

Smaller, still worth carrying: `var_dist_le2`, cited by F1.5 and by soundness
invariant 6, exists only inside the Kim probe directory and not in the
permanent tree or in infotheo, so the new probe redefines it rather than
importing it; and `psl211_joint_mixing` is stated at a Boolean prior and does
not apply at the deck-description carrier the PSL(2,11) word model needs, while
the generic lemma that would apply is declared `Local` and has to be restated.
