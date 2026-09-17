# Style audit C: lib/support_posterior.v, reconstruct/coalition_view_transport.v

Auditor: rocq-auditor on Opus, read-only, 2026-09-17. Verdict: PASS-WITH-FIXES.
0 blocking, 8 should, 10 nit, 2 info. No duplicate of an infotheo or lib lemma.

| ID | Where | Finding | Coordinator ruling |
|---|---|---|---|
| SP1 | support_posterior 148-150 | "the only place where the hypothesis is used" is proof bookkeeping | APPLY text SP1 |
| SP2 | 69-70 | "the adversary is measured against" is garbled | APPLY text SP2 |
| SP3 | file-wide | "observation" and "view" name one object | APPLY: "view" throughout, header text SP3, six in-body substitutions |
| SP4 | 230 | support_compatible_secret_cardE misspells its main symbol | RENAME to support_compatible_secrets_cardE |
| SP5 | 197, 216 | Equations without the equation suffix | RENAME support_posterior_secret_uniform to support_posterior_secret_uniformE and support_posterior_secret_zero to support_posterior_secret_eq0 |
| SP6 | 35-38 | finalg, zmodp redundant; fingroup, lra, boolp, graphoid, jfdist_cond likely unused | APPLY, build-checked; re-add whatever the build asks for |
| SP7 | 48 | reals_ext_scope unused | APPLY, build-checked |
| SP8 | 56 | Carrier named G reads as the monodromy group | RENAME the section variable G to T |
| SP9 | 62-64 | "below" is a layout reference | APPLY text SP9 |
| SP10 | 227-229 | "It is the step that" narrates proof order | APPLY text SP10 |
| SP11 | 22 | "Key results" label | KEEP. It is the header grammar of every file in the repo |
| CT1, CT3 | transport 43-90, 110-128 | Generic helpers live in a pgg_reconstruct file | APPLY with a NEW file lib/mutual_info_recoding.v. lib/proba_entropy_ext.v must NOT be edited, its rebuild invalidates expensive .vo files. The translation lemma is generalized from bool to any finType T as the auditor wrote |
| CT2 | 71-88 | mutual_info_RV_comp_inj goes through view_mutual_info_le | APPLY: reprove from infotheo entropy_fdistmap, injective_joint_entropy and mutual_infoEjoint_entropy. If that route does not close after honest diagnosis, keep the current proof, leave this one lemma in the transport file, and report |
| CT4 | 110 | `mulgl` is not a MathComp token | RENAME to fdistmap_prod_uniform_Ml |
| CT5 | 130-139 and header 23-25 | A coalition's VIEW shares mutual information; shuffle group vs monodromy group drift | APPLY text CT5 with the theorem's real name |
| CT6 | 140 | Asks for an E suffix on coalition_view_mutual_info_imset | REJECT. MathComp's card_imset and infotheo's entropy_fdistmap carry no E, and audit A accepted pgl27_view_mutual_info_imset on that precedent |
| CT7 | 30-39 | action, div, prime, Num.Theory likely unused | APPLY, build-checked |
| CT8 | 49-53 | "below" layout reference | APPLY text CT8 |

## Replacement texts

### SP1
```
(** At a fixed secret, restricted injectivity makes the supported fibre of the
    view map over [v] empty or a singleton, according to whether that secret is
    compatible with [v]. Injectivity on [A] is the assumption that no secret
    reaches one view from two distinct elements of [A], so the weight a view
    puts on a secret is a compatibility bit and never a multiplicity. *)
```
### SP2
```
(** The secret is the Boolean component of a sample. It is the quantity whose
    residual uncertainty given the adversary's view the posterior entropy
    measures, so secrecy of the scheme is a statement about this variable. *)
```
### SP3 header, replaces header lines 4-31
```
(* support_posterior: posterior entropy of a Boolean secret behind a view     *)
(*                    injective on a support set                              *)
(*                                                                            *)
(* A uniform Boolean secret is drawn independently of a uniform element of a  *)
(* nonempty subset A of a finite type, and the adversary sees a map indexed   *)
(* by the secret that is injective on A for each secret. Every view that      *)
(* occurs at all is then produced by at most one element of A per secret, so  *)
(* it leaves one or two compatible secrets and its posterior entropy is the   *)
(* indicator of that ambiguity.                                               *)
(*                                                                            *)
(* Definitions:                                                               *)
(*   support_posteriorP == the joint law of a uniform Boolean secret and a    *)
(*                         uniform element of A                               *)
(*   support_posterior_secret == the Boolean secret of a sample               *)
(*   support_posterior_view == the view of a sample                           *)
(*   support_compatible_secrets v == the secrets that produce v from A        *)
(*   support_ambiguous_view v == both secrets produce v from A                *)
(*                                                                            *)
(* Key results:                                                               *)
(*   support_posterior_secret_uniformE == at a reachable view the posterior   *)
(*     is uniform on the compatible secrets                                   *)
(*   support_compatible_secrets_cardE == a reachable view has two compatible  *)
(*     secrets when it is ambiguous and one otherwise                         *)
(*   support_posterior_entropy_ambiguousE == the posterior entropy of a       *)
(*     reachable view is the indicator of its ambiguity                       *)
(*                                                                            *)
(* The statements concern one pre-reveal view of a single execution, before   *)
(* any value is published.                                                    *)
```
In-body: "The observation applies" to "The view applies"; "the observation [v]"
to "the view [v]"; "An observation is ambiguous ... Such an observation" to
"A view is ambiguous ... Such a view"; "the observation still allows" to "the
view still allows"; "The observation thus rules out" to "The view thus rules
out"; "per-observation" to "per-view"; "the observation map" to "the view map".
### SP9
```
(** The source is the independent product of a uniform Boolean secret with a
    uniform draw from [A]. It is the law under which the adversary's posterior
    about the secret is taken. *)
```
### SP10
```
(** A reachable view has two compatible secrets exactly when it is ambiguous,
    and one otherwise. The posterior support of a reachable view is therefore
    a two-valued quantity, which is what makes its entropy a Boolean
    indicator. *)
```
### CT3 generalized statement
```
Lemma fdistmap_prod_uniform_Ml (R : realType) (gT : finGroupType)
    (G : {group gT}) (HG : (0 < #|G|)%N) (T : finType) (P : R.-fdist T)
    (h : gT) : h \in G ->
  fdistmap (fun u : T * gT => (u.1, (h * u.2)%g)) (P `x (`U HG))
    = P `x (`U HG).
```
### CT5
```
(** The view of a coalition seated at the relabelled positions rho g C shares
    exactly the same mutual information with the dealt secret as the view of
    the coalition seated at C, for every g in the monodromy group. Which
    positions a coalition occupies therefore matters only up to the monodromy
    group: relabelling the positions by a group element is absorbed by the
    uniform shuffle, so leakage about the secret is a function of the orbit of
    the coalition rather than of the coalition. The equality is exact and
    assumes no transitivity, so it transports leakage values at coalition
    sizes at and above the privacy threshold as well as below it. *)
```
### CT8
```
(** Two maps that agree wherever a law charges push that law forward to the
    same law: fdistmap f d = fdistmap g d as soon as f and g agree on
    fdist_supp d. A coalition view identity that holds only at samples whose
    shuffle lies in the monodromy group is available in this
    support-restricted form and in no pointwise one. *)
```
