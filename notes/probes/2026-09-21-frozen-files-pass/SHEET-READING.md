# SHEET-READING: proposed comment changes for the word "reading"

Read-only pass, 2026-09-21, HEAD c7f9991. No `.v` file was edited and nothing was
compiled. Every "current" block below was copied out of the working tree
mechanically and is byte-for-byte; every replacement was laid out to the
paragraph's own width and checked to be at most 80 bytes a line, to hold no
quotation mark and no comment delimiter, and to hold none of the barred words.

## The rule applied

Since the landing of `CoalitionReading A` (`manifest/pgg_tableau.v`), a READING is
what a coalition is granted to see of its endpoints, a function of them; the
default is `coalition_endpoint_reading`, the identity and the finest, and
`psl211_colour_reading` is a coarser one. In a comment the word must name a
reading in that sense: the record, a named reading, or the established phrase for
the default. It must not name the value read, a random variable, a law, or a
generic act of reading.

The replacements use one word per concept, all of them already in the tree:

- **endpoints** for `static_coalition_obs` and for what a coalition's seats hold,
  which the landing's own fix pass already uses ("the framework's direct
  computation of a coalition's endpoints").
- **view** for an instance's own function of the deal, which is its own name for
  it: `psl211_alldecks_view`, `pgl27_view`, `static_view`, `colour_view`, and for
  one value of such a function in the counting sections.
- **executed coalition view** for `sa_coalition_view`, the code's own name.
- **law** for a pushforward, which is what a distance is taken between.
- **read-off statement** for a theorem read off a published program, where the
  headers of the four AnalysisBridged files wrote "the reading X".

## Scope

Comments of the tracked `.v` files outside `notes/` and `legacy/`, less the 35
frozen modules of `FROZEN_MODULES` and less the paragraph at
`manifest/pgg_tableau_security_property_relations.v:466-470`, which another agent
holds. The whole-word scan over comments found 779 occurrences of
reading/readings, 51 of them in frozen files.

**273 sites in 40 files.** Barred from every replacement, and absent from all of
them: apex; gate and its forms; posit and its forms; arm; port; "row" for a
program or a manifest path; the letter-and-digit norm abbreviation; spend, price,
pay, budget, buy, owe, cost, currency and their inflections; the abbreviation of
indistinguishability; "observer" for the party.

---

# Part 1. SITES

### lib/fdist_prod_cst_cond.v

**V1** &nbsp; `lib/fdist_prod_cst_cond.v:7-18`

current:
```
(* A model that draws two coordinates apart and shows a function of the pair  *)
(* tells an observer nothing about the first coordinate when the reading's    *)
(* conditional law does not move with that coordinate.                        *)
(* fdistmap_pair_fst_prodE states the direction a privacy argument uses: from *)
(* constancy of the conditional law to a joint law of the reading and the     *)
(* first coordinate that is the product of its two marginals. That product is *)
(* the right-hand side an ideal-proximity comparison is stated against, and   *)
(* an ideal model built by drawing a run argument apart from a cut is where   *)
(* it is applied. The three equations before it are the mass computations of  *)
(* its proof: the fibre of the reading over one value of the first            *)
(* coordinate, the joint mass there, and the law of the reading alone as a    *)
(* mixture of its conditional laws.                                           *)
```
replacement:
```
(* A model that draws two coordinates apart and shows a function of the pair  *)
(* tells nothing about the first coordinate when that function's conditional  *)
(* law does not move with that coordinate. fdistmap_pair_fst_prodE states the *)
(* direction a privacy argument uses: from constancy of the conditional law   *)
(* to a joint law of the function and the first coordinate that is the        *)
(* product of its two marginals. That product is the right-hand side an       *)
(* ideal-proximity comparison is stated against, and an ideal model built by  *)
(* drawing a run argument apart from a cut is where it is applied. The three  *)
(* equations before it are the mass computations of its proof: the fibre of   *)
(* the function over one value of the first coordinate, the joint mass there, *)
(* and the law of the function alone as a mixture of its conditional laws.    *)
```
reason: reading names the random variable fun z => f z.1 z.2, not a CoalitionReading; observer for the party is barred

**V2** &nbsp; `lib/fdist_prod_cst_cond.v:20-24`

current:
```
(* inde_RV_cst is the same conclusion in the case where the coordinate the    *)
(* reading is compared against is one value. A constant random variable is    *)
(* independent of every other, so a constant secret satisfies the             *)
(* independence field of an exact witness over any model whatever, and        *)
(* carrying such a witness is by itself no statement about the model.         *)
```
replacement:
```
(* inde_RV_cst is the same conclusion in the case where the coordinate the    *)
(* function is compared against is one value. A constant random variable is   *)
(* independent of every other, so a constant secret satisfies the             *)
(* independence field of an exact witness over any model whatever, and        *)
(* carrying such a witness is by itself no statement about the model.         *)
```
reason: reading names the random variable

**V3** &nbsp; `lib/fdist_prod_cst_cond.v:30-37`

current:
```
(*   sum_prod_fibreE         == the mass of one value of the reading and one  *)
(*                              value of the first coordinate under a product *)
(*   fdistmap_pair_fst_condE == the joint law of the reading and the first    *)
(*                              coordinate under a product law                *)
(*   fdistmap_prod_mixtureE  == the law of the reading alone is the mixture   *)
(*                              of its conditional laws                       *)
(*   fdistmap_pair_fst_prodE == a reading whose conditional law is one law is *)
(*                              independent of the first coordinate           *)
```
replacement:
```
(*   sum_prod_fibreE         == the mass of one value of the function and     *)
(*                              one value of the first coordinate under a     *)
(*                              product                                       *)
(*   fdistmap_pair_fst_condE == the joint law of the function and the first   *)
(*                              coordinate under a product law                *)
(*   fdistmap_prod_mixtureE  == the law of the function alone is the mixture  *)
(*                              of its conditional laws                       *)
(*   fdistmap_pair_fst_prodE == a function whose conditional law is one law   *)
(*                              is independent of the first coordinate        *)
```
reason: index block, edited line by line; reading names the random variable

**V4** &nbsp; `lib/fdist_prod_cst_cond.v:82-82`

current:
```
(*     A reading of a product law with a constant conditional law             *)
```
replacement:
```
(*     A function of a product law with a constant conditional law            *)
```
reason: banner; reading names the random variable

**V5** &nbsp; `lib/fdist_prod_cst_cond.v:90-92`

current:
```
(** The mass a product law puts on one value of the reading together with one
    value of the first coordinate: the mass of that coordinate times the mass
    its own conditional reading law puts on the value. *)
```
replacement:
```
(** The mass a product law puts on one value of the function together with one
    value of the first coordinate: the mass of that coordinate times the mass
    its own conditional law puts on the value. *)
```
reason: reading names the random variable and its conditional law

**V6** &nbsp; `lib/fdist_prod_cst_cond.v:103-104`

current:
```
(** The joint law of the reading and the first coordinate under a product
    law, point by point. *)
```
replacement:
```
(** The joint law of the function and the first coordinate under a product law,
    point by point. *)
```
reason: reading names the random variable

**V7** &nbsp; `lib/fdist_prod_cst_cond.v:114-116`

current:
```
(** The law of the reading alone under a product law: the mixture of its
    conditional laws over the first coordinate, weighted by that
    coordinate's own law. *)
```
replacement:
```
(** The law of the function alone under a product law: the mixture of its
    conditional laws over the first coordinate, weighted by that coordinate's
    own law. *)
```
reason: reading names the random variable

**V8** &nbsp; `lib/fdist_prod_cst_cond.v:130-135`

current:
```
(** A reading whose conditional law does not move with the first coordinate
    is independent of that coordinate: the joint law of the two is the
    product of its two marginals. On an ideal model that draws a run argument
    apart from a cut, the constancy hypothesis is the ideal reading's
    constancy in the run argument, and the conclusion is the product the
    ideal-proximity proposition compares an actual joint law against. *)
```
replacement:
```
(** A function whose conditional law does not move with the first coordinate is
    independent of that coordinate: the joint law of the two is the product of
    its two marginals. On an ideal model that draws a run argument apart from a
    cut, the constancy hypothesis is the constancy in the run argument of what
    that ideal model shows a coalition, and the conclusion is the product the
    ideal-proximity proposition compares an actual joint law against. *)
```
reason: reading names the random variable, and the ideal reading names its law

### lib/var_dist_supp.v

**V9** &nbsp; `lib/var_dist_supp.v:6-18`

current:
```
(* var_dist_fdistmap_inj, the equality case of the data processing inequality *)
(* var_dist_fdistmap, asks that the reader be injective on the whole domain.  *)
(* A reader of the form sigma |-> sigma s on a permutation group is not, so   *)
(* that case carries no distance between two laws on the group back from a    *)
(* bound on the reading of one card position. Weakening the hypothesis to the *)
(* union of the two supports restores the transport, and that is the form in  *)
(* which a per-position number becomes a number about the group. Beside it    *)
(* sit the scale a published variation distance is read against, the          *)
(* invariance of a uniform law under an injective endomap, the fact that a    *)
(* pushforward is supported in the image, and the distance between the point  *)
(* mass at true on the booleans and the uniform law there.                    *)
(* security/var_dist_joint_law.v carries the distance between two joint laws  *)
(* of a reading and a secret.                                                 *)
```
replacement:
```
(* var_dist_fdistmap_inj, the equality case of the data processing inequality *)
(* var_dist_fdistmap, asks that the reader be injective on the whole domain.  *)
(* A reader of the form sigma |-> sigma s on a permutation group is not, so   *)
(* that case carries no distance between two laws on the group back from a    *)
(* bound on the card at one position. Weakening the hypothesis to the union   *)
(* of the two supports restores the transport, and that is the form in which  *)
(* a per-position number becomes a number about the group. Beside it sit the  *)
(* scale a published variation distance is read against, the invariance of a  *)
(* uniform law under an injective endomap, the fact that a pushforward is     *)
(* supported in the image, and the distance between the point mass at true on *)
(* the booleans and the uniform law there. security/var_dist_joint_law.v      *)
(* carries the distance between two joint laws of a coalition's endpoints and *)
(* a secret.                                                                  *)
```
reason: reading names the value read at a position and the random variable paired with the secret

**V10** &nbsp; `lib/var_dist_supp.v:51-56`

current:
```
(** The variation distance between two laws on a finite carrier is at most
    two, since it is the sum of the absolute differences and each law sums to
    one. It is the scale a published number is read against: a certificate
    says something about a coalition's two readings exactly in so far as its
    number is below two, and the total variation distance of the literature
    is half of this quantity. *)
```
replacement:
```
(** The variation distance between two laws on a finite carrier is at most two,
    since it is the sum of the absolute differences and each law sums to one.
    It is the scale a published number is read against: a certificate says
    something about the two laws a coalition sees exactly in so far as its
    number is below two, and the total variation distance of the literature is
    half of this quantity. *)
```
reason: a coalition's two readings names the two laws compared, not two CoalitionReadings

**V11** &nbsp; `lib/var_dist_supp.v:78-84`

current:
```
(** A reader that separates the points carrying mass transports the
    variation distance exactly. It is var_dist_fdistmap_inj, the equality
    case of the data processing inequality var_dist_fdistmap, with
    injectivity weakened from the whole domain to the union of the two
    supports. The weakening is what a cut law needs: the inequality runs from
    the group to the reading, and a certificate states its bound on the
    reading and must establish it on the group. *)
```
replacement:
```
(** A reader that separates the points carrying mass transports the variation
    distance exactly. It is var_dist_fdistmap_inj, the equality case of the
    data processing inequality var_dist_fdistmap, with injectivity weakened
    from the whole domain to the union of the two supports. The weakening is
    what a cut law needs: the inequality runs from the group to what is read,
    and a certificate states its bound on what is read and must establish it on
    the group. *)
```
reason: reading names the value read

**V12** &nbsp; `lib/var_dist_supp.v:164-167`

current:
```
(** A pushforward gives no mass to a point outside the image of its map. It is
    the contrapositive of fdistmap_neq0_codom: a reading that never returns a
    value leaves that value with mass zero, which is how two laws are shown to
    carry mass at no common point. *)
```
replacement:
```
(** A pushforward gives no mass to a point outside the image of its map. It is
    the contrapositive of fdistmap_neq0_codom: a map that never returns a value
    leaves that value with mass zero, which is how two laws are shown to carry
    mass at no common point. *)
```
reason: reading names the map g

**V13** &nbsp; `lib/var_dist_supp.v:206-212`

current:
```
(** The distance between the point mass at true on the booleans and the
    uniform law on the booleans, in the sum of absolute differences: one.
    Pushing two joint laws of a reading and a secret along the secret
    coordinate leaves the two laws of the secret and can only shorten the
    distance, so a proximity number between two models whose secrets are
    drawn from these two laws is at least one, whatever the rest of the two
    executions does. *)
```
replacement:
```
(** The distance between the point mass at true on the booleans and the uniform
    law on the booleans, in the sum of absolute differences: one. Pushing two
    joint laws of a coalition's endpoints and a secret along the secret
    coordinate leaves the two laws of the secret and can only shorten the
    distance, so a proximity number between two models whose secrets are drawn
    from these two laws is at least one, whatever the rest of the two
    executions does. *)
```
reason: reading names the random variable paired with the secret

### security/var_dist_joint_law.v

**V14** &nbsp; `security/var_dist_joint_law.v:6-12`

current:
```
(* A shuffle bound is proved on the cut group. What a coalition is shown is a *)
(* bound on the pair of its reading and the secret. The two carriers are not  *)
(* the same, and the lemmas here are the steps between them. Each distance    *)
(* step is stated on the sum of the absolute differences of two laws, which   *)
(* is twice the total variation distance of the literature and bounds twice a *)
(* distinguisher's advantage. fdist_prod_snd is the marginal identity those   *)
(* steps consume.                                                             *)
```
replacement:
```
(* A shuffle bound is proved on the cut group. What a coalition is shown is a *)
(* bound on the pair of its endpoints and the secret. The two carriers are    *)
(* not the same, and the lemmas here are the steps between them. Each         *)
(* distance step is stated on the sum of the absolute differences of two      *)
(* laws, which is twice the total variation distance of the literature and    *)
(* bounds twice a distinguisher's advantage. fdist_prod_snd is the marginal   *)
(* identity those steps consume.                                              *)
```
reason: reading names the random variable paired with the secret; first paragraph only, lines 14-24 unchanged

note: EDIT ONLY lines 6-12 of this box; lines 14-24 are a second paragraph and stay as they are, except V15

**V15** &nbsp; `security/var_dist_joint_law.v:14-24`

current:
```
(* Downward, var_dist_fdistmap_pair carries a bound from any common carrier   *)
(* to the pair, because a coalition's reading and the secret are both         *)
(* functions of one sample point. Upward, var_dist_prodR and var_dist_prodL   *)
(* carry a bound from one factor of a product to the product, because a model *)
(* whose run argument is drawn independently of its cut has a joint law of    *)
(* argument and cut that is a product, and tensoring with a common factor     *)
(* neither creates nor destroys the sum. fdist_prod_snd names the second      *)
(* marginal of such a product. var_dist_own_marginals removes the second      *)
(* model from the comparison: a joint law within a number of some product is  *)
(* within three times that number of the product of its own two marginals, so *)
(* a statement comparing two models becomes a statement about one.            *)
```
replacement:
```
(* Downward, var_dist_fdistmap_pair carries a bound from any common carrier   *)
(* to the pair, because a coalition's endpoints and the secret are both       *)
(* functions of one sample point. Upward, var_dist_prodR and var_dist_prodL   *)
(* carry a bound from one factor of a product to the product, because a model *)
(* whose run argument is drawn independently of its cut has a joint law of    *)
(* argument and cut that is a product, and tensoring with a common factor     *)
(* neither creates nor destroys the sum. fdist_prod_snd names the second      *)
(* marginal of such a product. var_dist_own_marginals removes the second      *)
(* model from the comparison: a joint law within a number of some product is  *)
(* within three times that number of the product of its own two marginals, so *)
(* a statement comparing two models becomes a statement about one.            *)
```
reason: reading names the random variable paired with the secret

**V16** &nbsp; `security/var_dist_joint_law.v:32-34`

current:
```
(*   var_dist_fdistmap_pair     == two laws on one sample space stay within   *)
(*                                 their bound when read as a reading and a   *)
(*                                 secret                                     *)
```
replacement:
```
(*   var_dist_fdistmap_pair     == two laws on one sample space stay within   *)
(*                                 their bound when read as a coalition's     *)
(*                                 endpoints and a secret                     *)
```
reason: index block; reading names the random variable

**V17** &nbsp; `security/var_dist_joint_law.v:64-64`

current:
```
(*     Down to the pair of a reading and a secret                             *)
```
replacement:
```
(*     Down to the pair of a coalition's endpoints and a secret               *)
```
reason: banner; reading names the random variable

**V18** &nbsp; `security/var_dist_joint_law.v:67-73`

current:
```
(** Two laws on one sample space, within d of each other, stay within d when
    each is read as the pair of a coalition's reading and the secret. It is
    data processing along the map pairing the two readers, and it is the step
    by which a proximity certificate's ipc_close field is discharged: the
    actual and the ideal model of one execution differ only in the law they
    draw a sample point from, and the pair ipc_close compares is a
    deterministic function of that point. *)
```
replacement:
```
(** Two laws on one sample space, within d of each other, stay within d when
    each is read as the pair of a coalition's endpoints and the secret. It is
    data processing along the map pairing the two readers, and it is the step
    by which a proximity certificate's ipc_close field is discharged: the
    actual and the ideal model of one execution differ only in the law they
    draw a sample point from, and the pair ipc_close compares is a
    deterministic function of that point. *)
```
reason: reading names the random variable paired with the secret

**V19** &nbsp; `security/var_dist_joint_law.v:141-141`

current:
```
(*     One reading of two products sharing their left factor                  *)
```
replacement:
```
(*     One map applied to two products sharing their left factor              *)
```
reason: banner; reading names the map h

**V20** &nbsp; `security/var_dist_joint_law.v:144-150`

current:
```
(** One map applied to two product laws sharing their left factor gives two
    laws no further apart than the two right factors. It is the general core
    of the step that carries a bound on a model's cut law to a bound on the
    joint law of a coalition's reading and the model's run argument: the
    shared left factor is the prior on the run argument, the two right
    factors are the actual and the ideal cut law, and the map is the pair of
    the reading and the argument, a deterministic function of the pair. *)
```
replacement:
```
(** One map applied to two product laws sharing their left factor gives two
    laws no further apart than the two right factors. It is the general core of
    the step that carries a bound on a model's cut law to a bound on the joint
    law of a coalition's endpoints and the model's run argument: the shared
    left factor is the prior on the run argument, the two right factors are the
    actual and the ideal cut law, and the map is the pair of the endpoints and
    the argument, a deterministic function of the pair. *)
```
reason: reading names the random variable and the map

### security/pgg_sample_adapter.v

**V21** &nbsp; `security/pgg_sample_adapter.v:11-18`

current:
```
(* Section sample_layers derives the three layers of the sample space. Layer  *)
(* one is the interpreter run at a sample point. Layer two is a seat's or a   *)
(* coalition's endpoint reading as a random variable on the sample space.     *)
(* Layer three is the pushforward of the sample distribution along a          *)
(* layer-two reader or along the cut map. Its inner section                   *)
(* sample_of_static_observation replaces, from a pointwise endpoint equation, *)
(* every executed reader by the static group-action observation, at the level *)
(* of the random variables and at the level of their distributions.           *)
```
replacement:
```
(* Section sample_layers derives the three layers of the sample space. Layer  *)
(* one is the interpreter run at a sample point. Layer two is a seat's or a   *)
(* coalition's endpoints as a random variable on the sample space. Layer      *)
(* three is the pushforward of the sample distribution along a layer-two      *)
(* reader or along the cut map. Its inner section                             *)
(* sample_of_static_observation replaces, from a pointwise endpoint equation, *)
(* every executed reader by the static group-action observation, at the level *)
(* of the random variables and at the level of their distributions.           *)
```
reason: a coalition's endpoint reading is now the established name of the default CoalitionReading; here it is the random variable

**V22** &nbsp; `security/pgg_sample_adapter.v:27-28`

current:
```
(*   sa_coalition_dist       == layer 3: the distribution of a coalition's    *)
(*                              reading                                       *)
```
replacement:
```
(*   sa_coalition_dist       == layer 3: the distribution of a coalition's    *)
(*                              endpoints                                     *)
```
reason: index block; matches the sa_coalition_view entry above it

**V23** &nbsp; `security/pgg_sample_adapter.v:154-156`

current:
```
(** sa_coalition_view — a coalition's endpoint readings as a random
    variable: the sample point mapped to exec_coalition_endpoints at its
    argument and cut. *)
```
replacement:
```
(** sa_coalition_view — a coalition's endpoints as a random variable: the
    sample point mapped to exec_coalition_endpoints at its argument and cut. *)
```
reason: endpoint readings names the random variable, colliding with the default reading's established name

**V24** &nbsp; `security/pgg_sample_adapter.v:183-184`

current:
```
(** sa_coalition_dist — the distribution of a coalition's endpoint
    readings: the pushforward of sa_sampleP along sa_coalition_view C. *)
```
replacement:
```
(** sa_coalition_dist — the distribution of a coalition's endpoints: the
    pushforward of sa_sampleP along sa_coalition_view C. *)
```
reason: endpoint readings names the random variable

### instances/kim2025/five_card_analysis.v

**V25** &nbsp; `instances/kim2025/five_card_analysis.v:13-21`

current:
```
(* A bound sub-block sits beside section 6 and carries the endpoint marginal  *)
(* bounds of the repeated and seven-cut models. Those are not privacy or      *)
(* security statements and are not aliased under the security heading.        *)
(* Section 7 carries the base premises Kim's one-cut and seven-cut programs   *)
(* rest on, the distance of each cut law from the uniform rotation law and    *)
(* the constancy, at every coalition of at most one of the five seats, of     *)
(* that coalition's reading of the uniform rotation law. Beside them it       *)
(* carries the coalition bound each pair of premises gives, and one typed     *)
(* transfer status per analysis path.                                         *)
```
replacement:
```
(* A bound sub-block sits beside section 6 and carries the endpoint marginal  *)
(* bounds of the repeated and seven-cut models. Those are not privacy or      *)
(* security statements and are not aliased under the security heading.        *)
(* Section 7 carries the base premises Kim's one-cut and seven-cut programs   *)
(* rest on, the distance of each cut law from the uniform rotation law and    *)
(* the constancy, at every coalition of at most one of the five seats, of the *)
(* law of that coalition's endpoints under the uniform rotation law. Beside   *)
(* them it carries the coalition bound each pair of premises gives, and one   *)
(* typed transfer status per analysis path.                                   *)
```
reason: that coalition's reading of the uniform rotation law names the law of the endpoints, not a CoalitionReading

**V26** &nbsp; `instances/kim2025/five_card_analysis.v:66-69`

current:
```
(*   ideal reading constancy                  -> static_obs_const             *)
(*   coalition reading bound at two pairs                                     *)
(*     -> centi_static_obs_indistinguishability,                              *)
(*        biased_static_obs_indistinguishability                              *)
```
replacement:
```
(*   ideal endpoint constancy                 -> static_obs_const             *)
(*   coalition endpoint bound at two pairs                                    *)
(*     -> centi_static_obs_indistinguishability,                              *)
(*        biased_static_obs_indistinguishability                              *)
```
reason: two rows of a two-column table, edited line by line; reading names the value read

note: TABLE: the arrow column is fixed; only the left cell of the first two rows changes

**V27** &nbsp; `instances/kim2025/five_card_analysis.v:145-150`

current:
```
(* Seven carriers, kept distinct: a message list for the raw traces, the card *)
(* position 'I_5 for the participant and input-party content readers,         *)
(* bool * bool for the dealer content reader, a list of card positions for    *)
(* the verifier endpoints, (size A).-tuple bool for the decoded colour        *)
(* sequence, {ffun 'I_5 -> 'I_5} for a coalition's static reading of the      *)
(* endpoint card positions, and bool for the evaluated secret.                *)
```
replacement:
```
(* Seven carriers, kept distinct: a message list for the raw traces, the card *)
(* position 'I_5 for the participant and input-party content readers, bool *  *)
(* bool for the dealer content reader, a list of card positions for the       *)
(* verifier endpoints, (size A).-tuple bool for the decoded colour sequence,  *)
(* {ffun 'I_5 -> 'I_5} for a coalition's static endpoint card positions, and  *)
(* bool for the evaluated secret.                                             *)
```
reason: a coalition's static reading of the endpoint card positions names the value read

**V28** &nbsp; `instances/kim2025/five_card_analysis.v:380-388`

current:
```
(* The generic bound var_dist_fdistmap_transfer runs from a distance between  *)
(* two laws on the cut carrier to a distance between two readings of them,    *)
(* and asks for that distance and for an equality of the two readings under   *)
(* an ideal law. Both hold at this development. Each of Kim's two cut laws    *)
(* is within its own number of the uniform rotation law on the cut group,     *)
(* and a coalition of at most one seat reads that ideal law alike at both     *)
(* committed pairs. The three theorems are aliased here. The section also     *)
(* carries one typed transfer status per analysis path: the uniform           *)
(* exact-cut path, the single-biased path and the repeated-cut path.          *)
```
replacement:
```
(* The generic bound var_dist_fdistmap_transfer runs from a distance between  *)
(* two laws on the cut carrier to a distance between two pushforwards of      *)
(* them, and asks for that distance and for an equality of the two            *)
(* pushforwards under an ideal law. Both hold at this development. Each of    *)
(* Kim's two cut laws is within its own number of the uniform rotation law on *)
(* the cut group, and a coalition of at most one seat reads that ideal law    *)
(* alike at both committed pairs. The three theorems are aliased here. The    *)
(* section also carries one typed transfer status per analysis path: the      *)
(* uniform exact-cut path, the single-biased path and the repeated-cut path.  *)
```
reason: two readings of them names two laws

### instances/kim2025/five_card_mixing.v

**V29** &nbsp; `instances/kim2025/five_card_mixing.v:53-55`

current:
```
(*   kim_centi_static_obs_indistinguishability                                *)
(*     == the two readings of the seven-cut law at two committed pairs are    *)
(*        within twice that number of each other                              *)
```
replacement:
```
(*   kim_centi_static_obs_indistinguishability                                *)
(*     == the laws of a coalition's endpoints at two committed pairs under    *)
(*        the seven-cut law are within twice that number of each other        *)
```
reason: index block; the two readings of the seven-cut law names two laws

**V30** &nbsp; `instances/kim2025/five_card_mixing.v:59-60`

current:
```
(*   kim_biased_static_obs_indistinguishability                               *)
(*     == the same reading statement at word length one                       *)
```
replacement:
```
(*   kim_biased_static_obs_indistinguishability                               *)
(*     == the same statement at word length one                               *)
```
reason: index block; reading statement reads as a statement at a reading

**V31** &nbsp; `instances/kim2025/five_card_mixing.v:236-240`

current:
```
(** fc_arrange_countE — counting a colour in den Boer's dealt row gives the
    same number at every committed pair: three hearts and two clubs. The
    colour census is the coarsening of the deal that the two bits leave
    fixed, and the level at which a single seat's reading stops depending on
    them. *)
```
replacement:
```
(** fc_arrange_countE — counting a colour in den Boer's dealt row gives the
    same number at every committed pair: three hearts and two clubs. The colour
    census is the coarsening of the deal that the two bits leave fixed, and the
    level at which what a single seat reads stops depending on them. *)
```
reason: a single seat's reading names the value read

**V32** &nbsp; `instances/kim2025/five_card_mixing.v:292-292`

current:
```
(*     The ideal cut's reading does not depend on the committed pair          *)
```
replacement:
```
(*     What is read under the ideal cut does not depend on the committed pair *)
```
reason: banner; the ideal cut's reading names the value read

**V33** &nbsp; `instances/kim2025/five_card_mixing.v:295-301`

current:
```
(** five_card_static_obs_const — the privacy threshold is two, so a coalition
    below it is empty or holds one seat. At every such coalition the static
    endpoint reading of the uniform rotation law has the same law at both
    committed pairs. One seat reads one card of a deck whose colour census
    den Boer's encoding fixes at three hearts and two clubs, so the reading
    cannot separate the pairs. This is the constancy field of the spectral
    certificate, and it is exact. It appeals to no mixing bound. *)
```
replacement:
```
(** five_card_static_obs_const — the privacy threshold is two, so a coalition
    below it is empty or holds one seat. At every such coalition the static
    endpoints have the same law under the uniform rotation law at both
    committed pairs. One seat reads one card of a deck whose colour census den
    Boer's encoding fixes at three hearts and two clubs, so what it reads
    cannot separate the pairs. This is the constancy field of the spectral
    certificate, and it is exact. It appeals to no mixing bound. *)
```
reason: the static endpoint reading names the random variable, and the reading names the value read

**V34** &nbsp; `instances/kim2025/five_card_mixing.v:397-408`

current:
```
(** kim_centi_static_obs_indistinguishability — at every coalition of at most
    one seat and every two committed pairs, the law of what that coalition reads
    off the static endpoints under the seven-cut law, which kim_centi_cut_distE
    identifies with the cut the seven-cut adapter draws, is within twice the
    bundle's spectral number of the same law at the other pair, in variation
    distance. This is the security statement of Kim's seven-cut analysis path,
    and it is what the two premises above are for: the attacker is that
    coalition, seeing only static endpoint colours, and the number bounds every
    advantage it has in telling the two pairs apart. The number is the bundle's
    spectral one lost at one hop for each pair, so the only inexact quantity is
    that mixing distance; the constancy of the ideal reading is exact and adds
    nothing. *)
```
replacement:
```
(** kim_centi_static_obs_indistinguishability — at every coalition of at most
    one seat and every two committed pairs, the law of what that coalition
    reads off the static endpoints under the seven-cut law, which
    kim_centi_cut_distE identifies with the cut the seven-cut adapter draws, is
    within twice the bundle's spectral number of the same law at the other
    pair, in variation distance. This is the security statement of Kim's
    seven-cut analysis path, and it is what the two premises above are for: the
    attacker is that coalition, seeing only static endpoint colours, and the
    number bounds every advantage it has in telling the two pairs apart. The
    number is the bundle's spectral one lost at one hop for each pair, so the
    only inexact quantity is that mixing distance; the constancy of what is
    read under the ideal cut is exact and adds nothing. *)
```
reason: the ideal reading names the value read under the ideal cut

### instances/kim2025/five_card_exec.v

**V35** &nbsp; `instances/kim2025/five_card_exec.v:81-84`

current:
```
(*   five_card_exec_coalition_endpointsE     == a coalition's endpoint        *)
(*                                              readings are the layout       *)
(*                                              entries at the cut images of  *)
(*                                              its seats                     *)
```
replacement:
```
(*   five_card_exec_coalition_endpointsE     == a coalition's endpoints are   *)
(*                                              the layout entries at the     *)
(*                                              cut images of its seats       *)
```
reason: index block; endpoint readings names the values, colliding with the default reading's name

note: the replacement is three lines where the current block is four

**V36** &nbsp; `instances/kim2025/five_card_exec.v:85-86`

current:
```
(*   five_card_exec_coalition_endpoints_seqE == the same reading in seat      *)
(*                                              order                         *)
```
replacement:
```
(*   five_card_exec_coalition_endpoints_seqE == the same endpoints in seat    *)
(*                                              order                         *)
```
reason: index block; the same reading names the values

**V37** &nbsp; `instances/kim2025/five_card_exec.v:103-103`

current:
```
(*   five_card_sample_coalition_distE == the same for a coalition's readings  *)
```
replacement:
```
(*   five_card_sample_coalition_distE == the same for a coalition's           *)
(*                                       endpoints                            *)
```
reason: index block; a coalition's readings names the values

note: the replacement is two lines where the current block is one

**V38** &nbsp; `instances/kim2025/five_card_exec.v:336-338`

current:
```
(** five_card_exec_coalition_endpointsE — a coalition's endpoint readings are
    the layout entries at the cut images of its seats, reading ord0 for every
    seat outside the coalition. *)
```
replacement:
```
(** five_card_exec_coalition_endpointsE — a coalition's endpoints are the
    layout entries at the cut images of its seats, reading ord0 for every seat
    outside the coalition. *)
```
reason: endpoint readings names the values; the second reading is the ordinary gerund and stays

**V39** &nbsp; `instances/kim2025/five_card_exec.v:640-642`

current:
```
(** five_card_sample_coalition_view — layer 2 at the den Boer space: a
    coalition's readings, sa_coalition_view at five_card_sample, the
    coalition endpoint reader as a random variable on P. *)
```
replacement:
```
(** five_card_sample_coalition_view — layer 2 at the den Boer space: a
    coalition's endpoints, sa_coalition_view at five_card_sample, the coalition
    endpoint reader as a random variable on P. *)
```
reason: a coalition's readings names the values

### instances/kim2025/five_card_proximity.v

**V40** &nbsp; `instances/kim2025/five_card_proximity.v:13-20`

current:
```
(* The bound is the closeness field of the proximity certificate: at every    *)
(* coalition, the joint law of that coalition's reading with the conjunction  *)
(* of the committed bits under Kim's one biased cut is within one fiftieth of *)
(* the same joint law under the uniform rotation. The number is the bound     *)
(* kim_biased_cut_mixing_exact proves on the cut group's own distance. Two is *)
(* the threshold the derived profile declares, and this bound is proved at    *)
(* every coalition of the five seats and not only below it, the threshold     *)
(* entering the ideal-proximity proposition and not the bound.                *)
```
replacement:
```
(* The bound is the closeness field of the proximity certificate: at every    *)
(* coalition, the joint law of that coalition's endpoints with the            *)
(* conjunction of the committed bits under Kim's one biased cut is within one *)
(* fiftieth of the same joint law under the uniform rotation. The number is   *)
(* the bound kim_biased_cut_mixing_exact proves on the cut group's own        *)
(* distance. Two is the threshold the derived profile declares, and this      *)
(* bound is proved at every coalition of the five seats and not only below    *)
(* it, the threshold entering the ideal-proximity proposition and not the     *)
(* bound.                                                                     *)
```
reason: that coalition's reading names the random variable static_coalition_obs

**V41** &nbsp; `instances/kim2025/five_card_proximity.v:27-35`

current:
```
(* Three laws carry that proof. The uniform law on the pair of committed bits *)
(* is one law under either of the two cardinality proofs the tree holds for   *)
(* that pair, which is what gives the product step below one common left      *)
(* factor. The pair of a coalition's reading and the secret factors through   *)
(* the pair of the committed bits and the cut, which is the carrier on which  *)
(* the two models are compared. And at a product law on the sample space that *)
(* pair's joint law is the uniform pair tensored with the model's cut law, so *)
(* the distance between the two models on the cut group is the distance       *)
(* between their two joint laws.                                              *)
```
replacement:
```
(* Three laws carry that proof. The uniform law on the pair of committed bits *)
(* is one law under either of the two cardinality proofs the tree holds for   *)
(* that pair, which is what gives the product step below one common left      *)
(* factor. The pair of a coalition's endpoints and the secret factors through *)
(* the pair of the committed bits and the cut, which is the carrier on which  *)
(* the two models are compared. And at a product law on the sample space that *)
(* pair's joint law is the uniform pair tensored with the model's cut law, so *)
(* the distance between the two models on the cut group is the distance       *)
(* between their two joint laws.                                              *)
```
reason: a coalition's reading names the random variable

**V42** &nbsp; `instances/kim2025/five_card_proximity.v:45-48`

current:
```
(*   five_card_reading_secretE                                                *)
(*                           == a coalition's reading and the secret factor   *)
(*                              through the pair of the committed bits and    *)
(*                              the cut                                       *)
```
replacement:
```
(*   five_card_reading_secretE                                                *)
(*                           == a coalition's endpoints and the secret        *)
(*                              factor through the pair of the committed      *)
(*                              bits and the cut                              *)
```
reason: index block; a coalition's reading names the random variable

**V43** &nbsp; `instances/kim2025/five_card_proximity.v:52-55`

current:
```
(*   kim_biased_proximity_close                                               *)
(*                           == at every coalition, the two models' joint     *)
(*                              laws of reading and secret are within one     *)
(*                              fiftieth                                      *)
```
replacement:
```
(*   kim_biased_proximity_close                                               *)
(*                           == at every coalition, the two models' joint     *)
(*                              laws of the endpoints and the secret are      *)
(*                              within one fiftieth                           *)
```
reason: index block; laws of reading and secret names the random variables

**V44** &nbsp; `instances/kim2025/five_card_proximity.v:99-102`

current:
```
(** The pair of a coalition's reading and the secret, as a reading of the pair
    of the committed bits and the cut. Both readers of a five-card sample
    point factor through that pair, which is the carrier on which the two
    models are compared. *)
```
replacement:
```
(** The pair of a coalition's endpoints and the secret, as a function of the
    pair of the committed bits and the cut. Both readers of a five-card sample
    point factor through that pair, which is the carrier on which the two
    models are compared. *)
```
reason: a coalition's reading names the random variable and a reading of the pair names the map

**V45** &nbsp; `instances/kim2025/five_card_proximity.v:134-143`

current:
```
(** At every coalition, the joint law of that coalition's reading with the
    secret under Kim's one biased cut is within one fiftieth of the same joint
    law under the uniform rotation. It is the closeness field of the proximity
    certificate at this instance: the two models differ only in the law of
    the rotation, the committed bits are drawn uniformly and independently of
    it in both, so the distance on the cut group is the distance of the two
    joint laws of the bits and the cut, and the pair of a reading and the
    secret is a deterministic function of those. The bound holds at every
    coalition and not only below the threshold; the threshold enters the
    ideal-proximity proposition and not this distance. *)
```
replacement:
```
(** At every coalition, the joint law of that coalition's endpoints with the
    secret under Kim's one biased cut is within one fiftieth of the same joint
    law under the uniform rotation. It is the closeness field of the proximity
    certificate at this instance: the two models differ only in the law of the
    rotation, the committed bits are drawn uniformly and independently of it in
    both, so the distance on the cut group is the distance of the two joint
    laws of the bits and the cut, and the pair of the endpoints and the secret
    is a deterministic function of those. The bound holds at every coalition
    and not only below the threshold; the threshold enters the ideal-proximity
    proposition and not this distance. *)
```
reason: that coalition's reading and a reading name the random variable

### instances/kim2025/tableau/five_card_tableau_sampled.v

**V46** &nbsp; `instances/kim2025/tableau/five_card_tableau_sampled.v:6-12`

current:
```
(* The Sampled level adjoins a probability model to a run, and what it adds   *)
(* to run correctness is the identification of the two readings of a          *)
(* coalition: at every real field and every index of the family, the reader   *)
(* built from the interpreter's own endpoints is the one computed directly    *)
(* from the run argument and the cut. That identification is what turns a     *)
(* claim about the messages a run exchanges into a claim about a group        *)
(* action, and it is the last thing proved before the certify statement.      *)
```
replacement:
```
(* The Sampled level adjoins a probability model to a run, and what it adds   *)
(* to run correctness is the identification of the two computations of a      *)
(* coalition's endpoints: at every real field and every index of the family,  *)
(* the reader built from the interpreter's own endpoints is the one computed  *)
(* directly from the run argument and the cut. That identification is what    *)
(* turns a claim about the messages a run exchanges into a claim about a      *)
(* group action, and it is the last thing proved before the certify           *)
(* statement.                                                                 *)
```
reason: the two readings of a coalition names two computations of the endpoints, not two CoalitionReadings

**V47** &nbsp; `instances/kim2025/tableau/five_card_tableau_sampled.v:29-49`

current:
```
(* Three of the statements here are about neither a program nor the           *)
(* manifest's path for it, and no certify statement takes a payload of any    *)
(* of those kinds. five_card_repeated_endpoint_lt is one starting position's  *)
(* endpoint marginal under the repeated model's cut law, a statement about    *)
(* where a single position is sent and not about what any set of seats        *)
(* reads, and five_card_repeated_cut_marginal is that comparison as the       *)
(* one-position marginal bound of manifest/pgg_tableau_marginal_bounds.v,     *)
(* which mentions no coalition, no second run argument and no secret.         *)
(* five_card_biased_leak_bound is Kim's input-privacy bound, an upper bound   *)
(* on the conditional mutual information between the two committed inputs and *)
(* the executed colour reading at a list of card positions, given the         *)
(* conjunction the run computes, under the law the one-cut model samples; it  *)
(* is about a reading at a list of card positions and not about a coalition   *)
(* of seats, and it is a bound and not a vanishing. Of the statements this    *)
(* directory makes it is the one security statement below AnalysisBridged,    *)
(* and it is of this level for two reasons: its subject is the law the named  *)
(* Sampled model samples, and the three statements of certify take an         *)
(* ExactWitness, an IndistinguishabilityCert and an IdealProximityCert, none  *)
(* of them a conditional mutual information. The distance                     *)
(* kim_biased_proximity_close of five_card_proximity.v is at no level and is  *)
(* not counted here.                                                          *)
```
replacement:
```
(* Three of the statements here are about neither a program nor the           *)
(* manifest's path for it, and no certify statement takes a payload of any of *)
(* those kinds. five_card_repeated_endpoint_lt is one starting position's     *)
(* endpoint marginal under the repeated model's cut law, a statement about    *)
(* where a single position is sent and not about what any set of seats reads, *)
(* and five_card_repeated_cut_marginal is that comparison as the one-position *)
(* marginal bound of manifest/pgg_tableau_marginal_bounds.v, which mentions   *)
(* no coalition, no second run argument and no secret.                        *)
(* five_card_biased_leak_bound is Kim's input-privacy bound, an upper bound   *)
(* on the conditional mutual information between the two committed inputs and *)
(* the executed colour view at a list of card positions, given the            *)
(* conjunction the run computes, under the law the one-cut model samples; it  *)
(* is about a view at a list of card positions and not about a coalition of   *)
(* seats, and it is a bound and not a vanishing. Of the statements this       *)
(* directory makes it is the one security statement below AnalysisBridged,    *)
(* and it is of this level for two reasons: its subject is the law the named  *)
(* Sampled model samples, and the three statements of certify take an         *)
(* ExactWitness, an IndistinguishabilityCert and an IdealProximityCert, none  *)
(* of them a conditional mutual information. The distance                     *)
(* kim_biased_proximity_close of five_card_proximity.v is at no level and is  *)
(* not counted here.                                                          *)
```
reason: the executed colour reading names the random variable colour_view, and a reading at a list of card positions names its value

**V48** &nbsp; `instances/kim2025/tableau/five_card_tableau_sampled.v:277-286`

current:
```
(** The conditional mutual information between the two committed inputs and
    the executed colour reading at a list of card positions, given the
    conjunction the run computes, is at most kim_leak_bound at bias one
    hundredth, under the law the biased program samples. It is
    five_card_colour_view_leak_bound with every random variable typed at that
    law, which is what sa_sampleP of the family's member is by conversion. The
    statement is a numeric upper bound on that information and not the
    assertion that the information vanishes, it is about a reading at a list
    of card positions and not about a coalition of seats, and it is carried
    beside the program above rather than by it. *)
```
replacement:
```
(** The conditional mutual information between the two committed inputs and the
    executed colour view at a list of card positions, given the conjunction the
    run computes, is at most kim_leak_bound at bias one hundredth, under the
    law the biased program samples. It is five_card_colour_view_leak_bound with
    every random variable typed at that law, which is what sa_sampleP of the
    family's member is by conversion. The statement is a numeric upper bound on
    that information and not the assertion that the information vanishes, it is
    about a view at a list of card positions and not about a coalition of
    seats, and it is carried beside the program above rather than by it. *)
```
reason: the executed colour reading names the random variable and a reading names its value

### instances/pgl27/pgl27_exec.v

**V49** &nbsp; `instances/pgl27/pgl27_exec.v:62-64`

current:
```
(*   pgl27_exec_coalition_endpointsE     == a coalition's endpoint readings   *)
(*                                          are the shares at the cut images  *)
(*                                          of its seats                      *)
```
replacement:
```
(*   pgl27_exec_coalition_endpointsE     == a coalition's endpoints are the   *)
(*                                          shares at the cut images of its   *)
(*                                          seats                             *)
```
reason: index block; endpoint readings names the values, colliding with the default reading's name

**V50** &nbsp; `instances/pgl27/pgl27_exec.v:65-65`

current:
```
(*   pgl27_exec_coalition_endpoints_seqE == the same reading in seat order    *)
```
replacement:
```
(*   pgl27_exec_coalition_endpoints_seqE == the same endpoints in seat order  *)
```
reason: index line; the same reading names the values

**V51** &nbsp; `instances/pgl27/pgl27_exec.v:73-73`

current:
```
(*   pgl27_sample_coalition_distE == the same for a coalition's readings      *)
```
replacement:
```
(*   pgl27_sample_coalition_distE == the same for a coalition's endpoints     *)
```
reason: index line; a coalition's readings names the values

**V52** &nbsp; `instances/pgl27/pgl27_exec.v:82-83`

current:
```
(*   pgl27_word_sample_coalition_distE == the same for a coalition's          *)
(*                                        readings                            *)
```
replacement:
```
(*   pgl27_word_sample_coalition_distE == the same for a coalition's          *)
(*                                        endpoints                           *)
```
reason: index block; a coalition's readings names the values

**V53** &nbsp; `instances/pgl27/pgl27_exec.v:262-265`

current:
```
(** pgl27_exec_coalition_endpointsE — a coalition's endpoint readings are the
    shares at the cut images of its seats. The finfun sends a seat in C to the
    share of s at the cut image of that seat's start, and every seat outside C
    to ord0. *)
```
replacement:
```
(** pgl27_exec_coalition_endpointsE — a coalition's endpoints are the shares
    at the cut images of its seats. The finfun sends a seat in C to the share
    of s at the cut image of that seat's start, and every seat outside C to
    ord0. *)
```
reason: endpoint readings names the values

**V54** &nbsp; `instances/pgl27/pgl27_exec.v:274-277`

current:
```
(** pgl27_exec_coalition_endpoints_seqE — the coalition's endpoint readings in
    seat order are the shares at the cut images of its seats. Mapping the
    endpoint reading over enum C gives the same list as mapping the share of s
    at the cut image of the start over enum C. *)
```
replacement:
```
(** pgl27_exec_coalition_endpoints_seqE — the coalition's endpoints in seat
    order are the shares at the cut images of its seats. Mapping the endpoint
    map over enum C gives the same list as mapping the share of s at the cut
    image of the start over enum C. *)
```
reason: endpoint readings names the values and the endpoint reading names the finfun

**V55** &nbsp; `instances/pgl27/pgl27_exec.v:380-384`

current:
```
(** pgl27_profile_endpoints — at every content readout, the executed
    endpoints of a dealer-dealt run over this profile are its static
    group-action reading.  Keeping the readout a variable removes the dealt
    card from the reduction, so one decision at the profile serves every run
    driven over it. *)
```
replacement:
```
(** pgl27_profile_endpoints — at every content readout, the executed
    endpoints of a dealer-dealt run over this profile are its static
    group-action observation. Keeping the readout a variable removes the dealt
    card from the reduction, so one decision at the profile serves every run
    driven over it. *)
```
reason: the static group-action reading names the observation; observation is the framework's word for it

note: this paragraph uses two spaces after a sentence stop; the replacement keeps them

**V56** &nbsp; `instances/pgl27/pgl27_exec.v:397-402`

current:
```
(** pgl27_dealt_recon — decoding the static endpoint reading at a shuffle in
    the group returns the dealt secret.  The statement is convertible with
    pgl27_exec_recon, which proves it through the interpreter; this one is
    dealt_static_recon, which the framework derives from the algebra's
    coordinate law alone, so reconstruction correctness of this instance is a
    consequence of that law and needs no further proof. *)
```
replacement:
```
(** pgl27_dealt_recon — decoding the static endpoints at a shuffle in the
    group returns the dealt secret. The statement is convertible with
    pgl27_exec_recon, which proves it through the interpreter; this one is
    dealt_static_recon, which the framework derives from the algebra's
    coordinate law alone, so reconstruction correctness of this instance is a
    consequence of that law and needs no further proof. *)
```
reason: the static endpoint reading names the values decoded

**V57** &nbsp; `instances/pgl27/pgl27_exec.v:457-459`

current:
```
(** pgl27_sample_coalition_view — layer 2 at pgl27P: a coalition's readings.
    This is sa_coalition_view at pgl27_sample, the coalition endpoint reader
    as a random variable on pgl27P. *)
```
replacement:
```
(** pgl27_sample_coalition_view — layer 2 at pgl27P: a coalition's endpoints.
    This is sa_coalition_view at pgl27_sample, the coalition endpoint reader as
    a random variable on pgl27P. *)
```
reason: a coalition's readings names the values

**V58** &nbsp; `instances/pgl27/pgl27_exec.v:468-470`

current:
```
(** pgl27_sample_coalition_dist — layer 3 at pgl27P: the distribution of a
    coalition's readings. The pushforward of pgl27P along
    pgl27_sample_coalition_view C. *)
```
replacement:
```
(** pgl27_sample_coalition_dist — layer 3 at pgl27P: the distribution of a
    coalition's endpoints. The pushforward of pgl27P along
    pgl27_sample_coalition_view C. *)
```
reason: a coalition's readings names the values

**V59** &nbsp; `instances/pgl27/pgl27_exec.v:474-477`

current:
```
(** pgl27_sample_seat_distE — the executed seat distribution at pgl27P is the
    distribution of the orbit share at the cut image of the seat's start.  The
    executed reading has the law of the direct computation, so a bound proved
    about the static observable holds of what the run produces. *)
```
replacement:
```
(** pgl27_sample_seat_distE — the executed seat distribution at pgl27P is the
    distribution of the orbit share at the cut image of the seat's start. The
    executed endpoint has the law of the direct computation, so a bound proved
    about the static observable holds of what the run produces. *)
```
reason: the executed reading names the random variable

### instances/pgl27/pgl27_analysis.v

**V60** &nbsp; `instances/pgl27/pgl27_analysis.v:111-114`

current:
```
(* Five carriers, kept distinct: a message list for the raw traces, the card  *)
(* position 'I_8 for one seat's endpoint, a finfun of card positions for a    *)
(* coalition's endpoints and for the content reading of a coalition's rows,   *)
(* and bool for the orbit secret.                                             *)
```
replacement:
```
(* Five carriers, kept distinct: a message list for the raw traces, the card  *)
(* position 'I_8 for one seat's endpoint, a finfun of card positions for a    *)
(* coalition's endpoints and for the content trace of a coalition's rows, and *)
(* bool for the orbit secret.                                                 *)
```
reason: the content reading of a coalition's rows names the content trace

### instances/pgl27/pgl27_models.v

**V61** &nbsp; `instances/pgl27/pgl27_models.v:14-20`

current:
```
(* The executed observations of a coalition come in two forms: the endpoint   *)
(* readings exec_coalition_endpoints and the interpreter rows read through    *)
(* content_of. Both are shown equal to the static coalition observations      *)
(* pgl27_view and pgl27_coalition_trace, so the word-shuffle coalition        *)
(* bounds of pgl27_word_privacy.v hold of the executed run, and the exact     *)
(* model's coalition observation is independent of the orbit secret at three  *)
(* cards.                                                                     *)
```
replacement:
```
(* The executed observations of a coalition come in two forms: the endpoints  *)
(* exec_coalition_endpoints and the interpreter rows read through content_of. *)
(* Both are shown equal to the static coalition observations pgl27_view and   *)
(* pgl27_coalition_trace, so the word-shuffle coalition bounds of             *)
(* pgl27_word_privacy.v hold of the executed run, and the exact model's       *)
(* coalition observation is independent of the orbit secret at three cards.   *)
```
reason: the endpoint readings names the values

### instances/pgl27/pgl27_proximity.v

**V62** &nbsp; `instances/pgl27/pgl27_proximity.v:4-5`

current:
```
(* pgl27_proximity: the instance's reading of a coalition, and the distances  *)
(* between its two laws of the cut                                            *)
```
replacement:
```
(* pgl27_proximity: the instance's view of a coalition, and the distances     *)
(* between its two laws of the cut                                            *)
```
reason: the instance's reading of a coalition names pgl27_view, the instance's own word for which is view

**V63** &nbsp; `instances/pgl27/pgl27_proximity.v:13-19`

current:
```
(* One bound is the closeness field of the proximity certificate: below the   *)
(* four-seat threshold, the joint law of a coalition's reading with the dealt *)
(* secret under the walk is within 2^-40 of the same joint law under the      *)
(* uniform cut at the same law of the secret. The number is the walk's        *)
(* single-card marginal number, and it rests on pgl27_word_mixing, the bound  *)
(* by that same number on the distance between the walk and the uniform cut   *)
(* on the group.                                                              *)
```
replacement:
```
(* One bound is the closeness field of the proximity certificate: below the   *)
(* four-seat threshold, the joint law of a coalition's endpoints with the     *)
(* dealt secret under the walk is within 2^-40 of the same joint law under    *)
(* the uniform cut at the same law of the secret. The number is the walk's    *)
(* single-card marginal number, and it rests on pgl27_word_mixing, the bound  *)
(* by that same number on the distance between the walk and the uniform cut   *)
(* on the group.                                                              *)
```
reason: a coalition's reading names the random variable

**V64** &nbsp; `instances/pgl27/pgl27_proximity.v:36-43`

current:
```
(* The identification of the framework's static reading of a coalition with   *)
(* pgl27_view opens the file, because the distance proof rewrites with it     *)
(* twice and because its subject is the run parameter record and no program   *)
(* value. The two sides are not the same term, the framework reading seat i   *)
(* at tnth (pi_starts _) i and the instance at i, and they agree because this *)
(* instance's seats start at the eight card positions in order. A             *)
(* coalition's content trace is that same finite map again, so the trace      *)
(* theorems and the reading theorems of this instance are one statement each. *)
```
replacement:
```
(* The identification of the framework's static computation of a coalition's  *)
(* endpoints with pgl27_view opens the file, because the distance proof       *)
(* rewrites with it twice and because its subject is the run parameter record *)
(* and no program value. The two sides are not the same term, the framework   *)
(* reading seat i at tnth (pi_starts _) i and the instance at i, and they     *)
(* agree because this instance's seats start at the eight card positions in   *)
(* order. A coalition's content trace is that same finite map again, so the   *)
(* trace theorems and the view theorems of this instance are one statement    *)
(* each.                                                                      *)
```
reason: the framework's static reading names the computation and the reading theorems names the theorems about pgl27_view; the framework reading seat i is the ordinary verb and stays

**V65** &nbsp; `instances/pgl27/pgl27_proximity.v:54-54`

current:
```
(*   pgl27_static_obsE       == the framework's reading is the instance's     *)
```
replacement:
```
(*   pgl27_static_obsE       == the framework's endpoints are the instance's  *)
(*                              view                                          *)
```
reason: index line; the framework's reading names the computation

note: the replacement is two lines where the current block is one

**V66** &nbsp; `instances/pgl27/pgl27_proximity.v:56-58`

current:
```
(*   pgl27_coalition_trace_static_obsE                                        *)
(*                           == a coalition's content trace is its static     *)
(*                              reading                                       *)
```
replacement:
```
(*   pgl27_coalition_trace_static_obsE                                        *)
(*                           == a coalition's content trace is its static     *)
(*                              endpoints                                     *)
```
reason: index block; its static reading names the values

**V67** &nbsp; `instances/pgl27/pgl27_proximity.v:59-62`

current:
```
(*   pgl27_word_proximity_close                                               *)
(*                           == below the four-seat threshold, the two        *)
(*                              models' joint laws of reading and secret are  *)
(*                              within 2^-40                                  *)
```
replacement:
```
(*   pgl27_word_proximity_close                                               *)
(*                           == below the four-seat threshold, the two        *)
(*                              models' joint laws of the endpoints and the   *)
(*                              secret are within 2^-40                       *)
```
reason: index block; joint laws of reading and secret names the random variables

**V68** &nbsp; `instances/pgl27/pgl27_proximity.v:96-96`

current:
```
(*     The instance-side reading of a coalition                               *)
```
replacement:
```
(*     The instance-side view of a coalition                                  *)
```
reason: banner; the instance-side reading names pgl27_view

**V69** &nbsp; `instances/pgl27/pgl27_proximity.v:99-105`

current:
```
(** Seat i's entry of the framework's static coalition reading is seat i's
    entry of the instance's coalition view. The two are not the same term: the
    framework reads seat i at tnth (pi_starts _) i and the instance reads it at
    i, and they agree because this instance's seats start at the eight card
    positions in order. Every security statement of a program is made about the
    left-hand side and every theorem of this instance about the right, so this
    equation is the whole of what carries one to the other. *)
```
replacement:
```
(** Seat i's entry of the framework's static computation of a coalition's
    endpoints is seat i's entry of the instance's coalition view. The two are
    not the same term: the framework reads seat i at tnth (pi_starts _) i and
    the instance reads it at i, and they agree because this instance's seats
    start at the eight card positions in order. Every security statement of a
    program is made about the left-hand side and every theorem of this instance
    about the right, so this equation is the whole of what carries one to the
    other. *)
```
reason: the framework's static coalition reading names the computation

**V70** &nbsp; `instances/pgl27/pgl27_proximity.v:116-119`

current:
```
(** The same identification with the cut left free, as an equality of
    functions of the cut. The input-indistinguishability proposition compares
    two laws obtained by pushing a reading forward along a distribution on
    cuts, so it needs the reading as one function and not as its values. *)
```
replacement:
```
(** The same identification with the cut left free, as an equality of functions
    of the cut. The input-indistinguishability proposition compares two laws
    obtained by pushing a coalition's view forward along a distribution on
    cuts, so it needs that view as one function and not as its values. *)
```
reason: a reading names the map pushed forward

**V71** &nbsp; `instances/pgl27/pgl27_proximity.v:125-132`

current:
```
(** A coalition's content trace at this instance is its static coalition
    reading, at every dealt secret and every cut. The trace records the card
    each member's interpreter row carries and the reading records the card
    each member's seat holds after the shuffle, and at this instance's eight
    seats the two are one finite map. Every theorem this instance publishes
    about the trace and every theorem it publishes about the reading are
    therefore one statement each, and the two numbers 2^-39 the tree
    publishes, one at the trace and one at the reading, are one number. *)
```
replacement:
```
(** A coalition's content trace at this instance is its static coalition
    endpoints, at every dealt secret and every cut. The trace records the card
    each member's interpreter row carries and the endpoint records the card
    each member's seat holds after the shuffle, and at this instance's eight
    seats the two are one finite map. Every theorem this instance publishes
    about the trace and every theorem it publishes about the endpoints are
    therefore one statement each, and the two numbers 2^-39 the tree publishes,
    one at the trace and one at the endpoints, are one number. *)
```
reason: static coalition reading and the reading name the values

**V72** &nbsp; `instances/pgl27/pgl27_proximity.v:159-170`

current:
```
(** At every coalition of fewer than four seats and at every prior, the joint
    law of that coalition's reading with the dealt secret under the
    two-hundred-letter word walk is within 2^-40 of the same joint law under
    the uniform cut at the same prior. It is the closeness field of the
    proximity certificate at this instance: the two models differ in the law of
    the cut alone, the secret is drawn from the same prior and independently of
    the cut in both, and the pair of a reading and the secret is a
    deterministic function of the pair of the secret and the cut. The premise is
    the ideal-proximity proposition's threshold at this instance, four seats.
    pgl27_word_mixing, the bound on the cut group's own distance, carries no
    coalition premise, so the same bound is reachable at every coalition by a
    route this proof does not take. *)
```
replacement:
```
(** At every coalition of fewer than four seats and at every prior, the joint
    law of that coalition's endpoints with the dealt secret under the
    two-hundred-letter word walk is within 2^-40 of the same joint law under
    the uniform cut at the same prior. It is the closeness field of the
    proximity certificate at this instance: the two models differ in the law of
    the cut alone, the secret is drawn from the same prior and independently of
    the cut in both, and the pair of the endpoints and the secret is a
    deterministic function of the pair of the secret and the cut. The premise
    is the ideal-proximity proposition's threshold at this instance, four
    seats. pgl27_word_mixing, the bound on the cut group's own distance,
    carries no coalition premise, so the same bound is reachable at every
    coalition by a route this proof does not take. *)
```
reason: that coalition's reading and a reading name the random variable

**V73** &nbsp; `instances/pgl27/pgl27_proximity.v:187-192`

current:
```
(* The word side is rewritten as a reading of the pair of the secret and the
   evaluated cut, which is the carrier pgl27_view_mixing is stated on; the
   ideal side is that same reading under the uniform cut, turned into the
   product of its marginals by the ideal witness's own independence. The
   threshold is used twice, once for the ideal witness's independence and
   once for pgl27_view_mixing. *)
```
replacement:
```
(* The word side is rewritten as a function of the pair of the secret and the
   evaluated cut, which is the carrier pgl27_view_mixing is stated on; the
   ideal side is that same function under the uniform cut, turned into the
   product of its marginals by the ideal witness's own independence. The
   threshold is used twice, once for the ideal witness's independence and once
   for pgl27_view_mixing. *)
```
reason: a reading of the pair names the map

**V74** &nbsp; `instances/pgl27/pgl27_proximity.v:248-256`

current:
```
(** The closeness field of a proximity certificate is false, and not merely
    unwritable, when the ideal is the uniform-secret member of the tree's exact
    family and the actual model is the word walk at the point-mass prior.
    Pushing both joint laws forward along the secret coordinate leaves the two
    priors themselves, one apart, and 2^-40 is below that, so the two models are
    separated by their secrets alone and no reading of the cut can bring them
    together. It says nothing at a prior near the uniform one, where the same
    lower bound is small. It is stated at every coalition and not only below
    four seats, so it refutes more than the field asks. *)
```
replacement:
```
(** The closeness field of a proximity certificate is false, and not merely
    unwritable, when the ideal is the uniform-secret member of the tree's exact
    family and the actual model is the word walk at the point-mass prior.
    Pushing both joint laws forward along the secret coordinate leaves the two
    priors themselves, one apart, and 2^-40 is below that, so the two models
    are separated by their secrets alone and no view of the cut can bring them
    together. It says nothing at a prior near the uniform one, where the same
    lower bound is small. It is stated at every coalition and not only below
    four seats, so it refutes more than the field asks. *)
```
reason: no reading of the cut names a function of the cut

### instances/pgl27/tableau/pgl27_tableau_sampled.v

**V75** &nbsp; `instances/pgl27/tableau/pgl27_tableau_sampled.v:6-12`

current:
```
(* The Sampled level adjoins a probability model to a run, and what it adds   *)
(* to run correctness is the identification of the two readings of a          *)
(* coalition: at every real field and every index of the family, the reader   *)
(* built from the interpreter's own endpoints is the one computed directly    *)
(* from the run argument and the cut. That identification is what turns a     *)
(* claim about the messages a run exchanges into a claim about a group        *)
(* action, and it is the last thing proved before the certify statement.      *)
```
replacement:
```
(* The Sampled level adjoins a probability model to a run, and what it adds   *)
(* to run correctness is the identification of the two computations of a      *)
(* coalition's endpoints: at every real field and every index of the family,  *)
(* the reader built from the interpreter's own endpoints is the one computed  *)
(* directly from the run argument and the cut. That identification is what    *)
(* turns a claim about the messages a run exchanges into a claim about a      *)
(* group action, and it is the last thing proved before the certify           *)
(* statement.                                                                 *)
```
reason: the two readings of a coalition names two computations of the endpoints

### instances/pgl27/tableau/pgl27_tableau_executable.v

**V76** &nbsp; `instances/pgl27/tableau/pgl27_tableau_executable.v:23-27`

current:
```
(* The two identifications of the framework's static reading of a coalition   *)
(* with pgl27_view are statements about this parameter record and about no    *)
(* program value, and they are in instances/pgl27/pgl27_proximity.v beside    *)
(* the distance whose proof rewrites with them, so that the mathematics       *)
(* requires no tableau module.                                                *)
```
replacement:
```
(* The two identifications of the framework's static computation of a         *)
(* coalition's endpoints with pgl27_view are statements about this parameter  *)
(* record and about no program value, and they are in                         *)
(* instances/pgl27/pgl27_proximity.v beside the distance whose proof rewrites *)
(* with them, so that the mathematics requires no tableau module.             *)
```
reason: the framework's static reading names the computation

### instances/pgl27/tableau/pgl27_tableau_checks.v

**V77** &nbsp; `instances/pgl27/tableau/pgl27_tableau_checks.v:206-212`

current:
```
(** The security properties are different statements, and the difference is
    visible in what a program's projection takes after the coalition. A program
    certifying input indistinguishability is asked here for a threshold proof in
    the position where it expects the first of two dealt secrets, and is
    rejected: what the word program proves at a coalition is a distance between
    the readings of two secrets, so the two secrets come before the threshold
    proof. *)
```
replacement:
```
(** The security properties are different statements, and the difference is
    visible in what a program's projection takes after the coalition. A program
    certifying input indistinguishability is asked here for a threshold proof
    in the position where it expects the first of two dealt secrets, and is
    rejected: what the word program proves at a coalition is a distance between
    the laws at two secrets, so the two secrets come before the threshold
    proof. *)
```
reason: the readings of two secrets names two laws

### instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v

**V78** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:7-13`

current:
```
(* The AnalysisBridged level adjoins security evidence to a Sampled value at  *)
(* every real field and index, and the proposition it carries is the one that *)
(* evidence proves, on top of run correctness and of the identification of    *)
(* the two readings of a coalition. A publish terminal then turns the value   *)
(* into a Published. Every payload this instance gives a certify statement is *)
(* here, every program it publishes is here, and every statement whose        *)
(* subject is a payload or a program is here.                                 *)
```
replacement:
```
(* The AnalysisBridged level adjoins security evidence to a Sampled value at  *)
(* every real field and index, and the proposition it carries is the one that *)
(* evidence proves, on top of run correctness and of the identification of    *)
(* the two computations of a coalition's endpoints. A publish terminal then   *)
(* turns the value into a Published. Every payload this instance gives a      *)
(* certify statement is here, every program it publishes is here, and every   *)
(* statement whose subject is a payload or a program is here.                 *)
```
reason: the two readings of a coalition names two computations of the endpoints

**V79** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:15-23`

current:
```
(* All three security properties are certified over the one dealer-dealt run. *)
(* Certifying exact independence takes an ExactWitness, whose one field is    *)
(* independence of a coalition's endpoints from the dealt secret; at the      *)
(* uniform cut this is three-transitivity of PGL(2,7) on the eight points     *)
(* read as a privacy statement, and it is exact, with no number in it.        *)
(* Certifying input indistinguishability takes a certificate comparing the    *)
(* readings of two dealt secrets under one model. Certifying ideal proximity  *)
(* takes a certificate comparing one model with an ideal one at the same      *)
(* index.                                                                     *)
```
replacement:
```
(* All three security properties are certified over the one dealer-dealt run. *)
(* Certifying exact independence takes an ExactWitness, whose one field is    *)
(* independence of a coalition's endpoints from the dealt secret; at the      *)
(* uniform cut this is three-transitivity of PGL(2,7) on the eight points     *)
(* read as a privacy statement, and it is exact, with no number in it.        *)
(* Certifying input indistinguishability takes a certificate comparing the    *)
(* laws at two dealt secrets under one model. Certifying ideal proximity      *)
(* takes a certificate comparing one model with an ideal one at the same      *)
(* index.                                                                     *)
```
reason: the readings of two dealt secrets names two laws

**V80** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:59-62`

current:
```
(* pgl27_exact_published, under The exact and the word program:               *)
(*     pgl27_exact_published_sampledE, pgl27_exact_published_pathE,           *)
(*     pgl27_exact_published_propertyE, and the readings                      *)
(*     pgl27_exec_exact_view_indep_restated and pgl27_exact_view_secrecy.     *)
```
replacement:
```
(* pgl27_exact_published, under The exact and the word program:               *)
(*     pgl27_exact_published_sampledE, pgl27_exact_published_pathE,           *)
(*     pgl27_exact_published_propertyE, and the read-off statements           *)
(*     pgl27_exec_exact_view_indep_restated and pgl27_exact_view_secrecy.     *)
```
reason: hanging-indent list, edited line by line; the readings names the theorems read off the program

note: LIST: the hanging indent of four spaces is fixed; only the third line changes

**V81** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:63-66`

current:
```
(* pgl27_word_published, under the same banner:                               *)
(*     pgl27_word_published_sampledE, pgl27_word_published_pathE,             *)
(*     pgl27_word_published_propertyE, and the reading                        *)
(*     pgl27_word_view_indistinguishability_restated.                         *)
```
replacement:
```
(* pgl27_word_published, under the same banner:                               *)
(*     pgl27_word_published_sampledE, pgl27_word_published_pathE,             *)
(*     pgl27_word_published_propertyE, and the read-off statement             *)
(*     pgl27_word_view_indistinguishability_restated.                         *)
```
reason: hanging-indent list; the reading names the theorem read off the program

**V82** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:67-68`

current:
```
(* pgl27_word_published39, under The word program concluded at 2^-39:         *)
(*     pgl27_word_published39_propertyE, and no reading of its own.           *)
```
replacement:
```
(* pgl27_word_published39, under The word program concluded at 2^-39:         *)
(*     pgl27_word_published39_propertyE, and no read-off statement of its     *)
(*     own.                                                                   *)
```
reason: hanging-indent list; no reading of its own names the absence of such a theorem

note: the replacement is three lines where the current block is two

**V83** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:78-82`

current:
```
(* pgl27_word_proximity_published, under One model, two claims, two programs: *)
(*     written from pgl27_word_sampled, so no _sampledE,                      *)
(*     pgl27_word_proximity_published_pathE,                                  *)
(*     pgl27_word_proximity_published_propertyE, and the reading              *)
(*     pgl27_word_view_proximity.                                             *)
```
replacement:
```
(* pgl27_word_proximity_published, under One model, two claims, two           *)
(*     programs: written from pgl27_word_sampled, so no _sampledE,            *)
(*     pgl27_word_proximity_published_pathE,                                  *)
(*     pgl27_word_proximity_published_propertyE, and the read-off statement   *)
(*     pgl27_word_view_proximity.                                             *)
```
reason: hanging-indent list; the reading names the theorem read off the program

**V84** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:95-100`

current:
```
(* This file requires instances/pgl27/pgl27_proximity.v, which holds the      *)
(* reading and the distance mathematics the certificates are built from: the  *)
(* two identifications of the framework's static reading of a coalition with  *)
(* pgl27_view, the dealt secret on the word sample space, the distance        *)
(* between the two models' joint laws, and the two arithmetic facts about     *)
(* 2^-40 the conclude obligation is proved with.                              *)
```
replacement:
```
(* This file requires instances/pgl27/pgl27_proximity.v, which holds the view *)
(* and the distance mathematics the certificates are built from: the two      *)
(* identifications of the framework's static computation of a coalition's     *)
(* endpoints with pgl27_view, the dealt secret on the word sample space, the  *)
(* distance between the two models' joint laws, and the two arithmetic facts  *)
(* about 2^-40 the conclude obligation is proved with.                        *)
```
reason: the reading names pgl27_view and the framework's static reading names the computation

**V85** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:143-144`

current:
```
(*   pgl27_word_view_const   == below the four-seat threshold, two secrets    *)
(*                              give one reading of the ideal cut             *)
```
replacement:
```
(*   pgl27_word_view_const   == below the four-seat threshold, two secrets    *)
(*                              give one law under the ideal cut              *)
```
reason: index block; one reading of the ideal cut names one law

**V86** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:189-191`

current:
```
(*   pgl27_prior_viewE       == the framework's reading of a coalition at the *)
(*                              prior-indexed exact shuffle is the instance's *)
(*                              own reading pgl27_view                        *)
```
replacement:
```
(*   pgl27_prior_viewE       == the framework's endpoints of a coalition at   *)
(*                              the prior-indexed exact shuffle are the       *)
(*                              instance's own view pgl27_view                *)
```
reason: index block; the framework's reading names the computation and its own reading names pgl27_view

**V87** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:331-336`

current:
```
(** Two dealt secrets give a coalition of fewer than four seats the same
    reading of the ideal uniform cut. It is pgl27_view_law_const, which is
    three-transitivity of PGL(2,7) read as a privacy statement, carried to
    the framework's reader at each of the two secrets; the statement is
    exact, and it is the half of the input-indistinguishability certificate
    that appeals to no mixing bound. *)
```
replacement:
```
(** Two dealt secrets give a coalition of fewer than four seats the same law
    under the ideal uniform cut. It is pgl27_view_law_const, which is
    three-transitivity of PGL(2,7) read as a privacy statement, carried to the
    framework's reader at each of the two secrets; the statement is exact, and
    it is the half of the input-indistinguishability certificate that appeals
    to no mixing bound. *)
```
reason: the same reading of the ideal uniform cut names one law

**V88** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:407-413`

current:
```
(** The word program: the same prefix, the two-hundred-letter word model, the
    certificate above, and the manifest path at transfer status IdealFinite,
    which records that a finite walk is being compared with the ideal uniform
    cut. What the finished program carries is a variation distance between the
    readings of two dealt secrets, bounded by 2^-40 + 2^-40: the framework's
    transfer inequality crosses from the walk to the ideal cut and back again,
    and each of the two hops loses the same mixing bound. *)
```
replacement:
```
(** The word program: the same prefix, the two-hundred-letter word model, the
    certificate above, and the manifest path at transfer status IdealFinite,
    which records that a finite walk is being compared with the ideal uniform
    cut. What the finished program carries is a variation distance between the
    laws at two dealt secrets, bounded by 2^-40 + 2^-40: the framework's
    transfer inequality crosses from the walk to the ideal cut and back again,
    and each of the two hops loses the same mixing bound. *)
```
reason: the readings of two dealt secrets names two laws

**V89** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:460-464`

current:
```
(** The security property this program carries, at every real field and index,
    is exact independence: independence of the coalition's view from the secret,
    and not a distance between two readings. The program's certify statement
    settles which property that is, through certify_exact_propertyE and
    publish_propertyE. *)
```
replacement:
```
(** The security property this program carries, at every real field and index,
    is exact independence: independence of the coalition's view from the
    secret, and not a distance between two laws. The program's certify
    statement settles which property that is, through certify_exact_propertyE
    and publish_propertyE. *)
```
reason: a distance between two readings names two laws

**V90** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:470-473`

current:
```
(** The security property the word program carries. The two programs publish
    different manifest paths here, but a reader of the manifest alone could not
    tell independence of the view from a distance between two readings, and this
    pair of equations is what separates them. *)
```
replacement:
```
(** The security property the word program carries. The two programs publish
    different manifest paths here, but a reader of the manifest alone could not
    tell independence of the view from a distance between two laws, and this
    pair of equations is what separates them. *)
```
reason: a distance between two readings names two laws

**V91** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:641-645`

current:
```
(** The exact family's published statement, as a proposition: at fewer than
    four seats, the joint law of the executed coalition reading and the dealt
    secret is the product of its two marginals. It is the product form of
    independence, which is what a reader comparing this instance with an ideal
    execution wants to see. *)
```
replacement:
```
(** The exact family's published statement, as a proposition: at fewer than
    four seats, the joint law of the executed coalition view and the dealt
    secret is the product of its two marginals. It is the product form of
    independence, which is what a reader comparing this instance with an ideal
    execution wants to see. *)
```
reason: the executed coalition reading names the random variable sa_coalition_view

**V92** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:686-689`

current:
```
(** At fewer than four seats the executed coalition reading of the exact model
    and the dealt secret have a product joint law. The statement is that of
    pgl27_exec_exact_view_indep, re-proved by reading the restated program's
    theorem field and applying it. *)
```
replacement:
```
(** At fewer than four seats the executed coalition view of the exact model and
    the dealt secret have a product joint law. The statement is that of
    pgl27_exec_exact_view_indep, re-proved by reading the restated program's
    theorem field and applying it. *)
```
reason: the executed coalition reading names the random variable; the second reading is the ordinary gerund and stays

**V93** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:702-710`

current:
```
(** The exact program's view secrecy at this instance: at fewer than four
    colluding seats the executed coalition reading is independent of the dealt
    secret, carries zero mutual information with it, leaves the secret's entropy
    unchanged under conditioning, and stays independent of it under every
    deterministic function of the seat-to-card map. The four conjuncts are the
    whole content of the exact-independence proposition at this instance; the
    proof is the program's security projection applied, so a reader who wants
    the information-theoretic reading of the program needs no further
    derivation. *)
```
replacement:
```
(** The exact program's view secrecy at this instance: at fewer than four
    colluding seats the executed coalition view is independent of the dealt
    secret, carries zero mutual information with it, leaves the secret's
    entropy unchanged under conditioning, and stays independent of it under
    every deterministic function of the seat-to-card map. The four conjuncts
    are the whole content of the exact-independence proposition at this
    instance; the proof is the program's security projection applied, so a
    reader who wants the information-theoretic content of the program needs no
    further derivation. *)
```
reason: the executed coalition reading names the random variable and the information-theoretic reading names the content of the conclusion

**V94** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:766-770`

current:
```
(** The framework's static reading of a coalition at this model is the
    instance's own reading pgl27_view, with the secret left inside the sample
    point. Every security statement of a program is made about the left-hand
    side and every theorem of the instance about the right, so this equation is
    the whole of what carries one to the other at the prior-indexed model. *)
```
replacement:
```
(** The framework's static computation of a coalition's endpoints at this model
    is the instance's own view pgl27_view, with the secret left inside the
    sample point. Every security statement of a program is made about the
    left-hand side and every theorem of the instance about the right, so this
    equation is the whole of what carries one to the other at the prior-indexed
    model. *)
```
reason: the framework's static reading names the computation and its own reading names pgl27_view

**V95** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:944-956`

current:
```
(** The word model certified for ideal proximity and concluded at 2^-39, the
    constant the input-indistinguishability program of the same model publishes
    and the one the published reading statement pgl27_word_view_proximity
    carries. The certificate's own number is 2^-40, half of that. Below four
    seats its distance field, pgl27_word_proximity_close, puts the joint law of
    a coalition's endpoints with the dealt secret within that number of the same
    joint law under the prior-indexed exact execution, where those endpoints and
    the secret are independent outright, so the ideal side is the product of its
    two marginals. The proximity certificate's closeness field is one hop to the
    ideal, so that number is lost once, where the input-indistinguishability
    tail makes two hops. Its transfer status is IdealFinite, the same the
    input-indistinguishability program carries, and the two certificates compare
    against the same ideal cut. *)
```
replacement:
```
(** The word model certified for ideal proximity and concluded at 2^-39, the
    constant the input-indistinguishability program of the same model publishes
    and the one the published statement pgl27_word_view_proximity carries. The
    certificate's own number is 2^-40, half of that. Below four seats its
    distance field, pgl27_word_proximity_close, puts the joint law of a
    coalition's endpoints with the dealt secret within that number of the same
    joint law under the prior-indexed exact execution, where those endpoints
    and the secret are independent outright, so the ideal side is the product
    of its two marginals. The proximity certificate's closeness field is one
    hop to the ideal, so that number is lost once, where the
    input-indistinguishability tail makes two hops. Its transfer status is
    IdealFinite, the same the input-indistinguishability program carries, and
    the two certificates compare against the same ideal cut. *)
```
reason: the published reading statement names the theorem read off the program

**V96** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:976-978`

current:
```
(** The security property this program carries, at every real field and prior,
    is ideal proximity: the distance to a private ideal model, and not the
    distance between two readings of one model. *)
```
replacement:
```
(** The security property this program carries, at every real field and prior,
    is ideal proximity: the distance to a private ideal model, and not the
    distance between two laws of one model. *)
```
reason: two readings of one model names two laws

**V97** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:1018-1024`

current:
```
(** The proximity program's security statement at the eight-card orbit instance:
    at fewer than four colluding seats and at every prior on the dealt secret,
    the joint law of the executed coalition reading and that secret under the
    two-hundred-letter word walk is within 2^-39 of the product of the two
    marginals of the exact execution at the same prior. The proof is the
    program's security projection applied, so the program and this statement are
    one theorem. *)
```
replacement:
```
(** The proximity program's security statement at the eight-card orbit
    instance: at fewer than four colluding seats and at every prior on the
    dealt secret, the joint law of the executed coalition view and that secret
    under the two-hundred-letter word walk is within 2^-39 of the product of
    the two marginals of the exact execution at the same prior. The proof is
    the program's security projection applied, so the program and this
    statement are one theorem. *)
```
reason: the executed coalition reading names the random variable

**V98** &nbsp; `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:1059-1068`

current:
```
(** pgl27_word_input_distinguishability_false — the two-hundred-letter word
    model of the eight-card orbit instance is not input distinguishable at any
    number above 2^-39. Below four colluding seats the published program
    pgl27_word_published39 bounds the distance between the readings of every
    two dealt secrets under this model's own cut law by 2^-39, so no pair of
    run arguments separates them further and the existential the proposition
    asserts has no witness. The obstruction that
    psl211_alldecks_obstruction_published carries is therefore a statement
    about the twelve-card chirality model and not a proposition every model
    satisfies.
```
replacement:
```
(** pgl27_word_input_distinguishability_false — the two-hundred-letter word
    model of the eight-card orbit instance is not input distinguishable at any
    number above 2^-39. Below four colluding seats the published program
    pgl27_word_published39 bounds the distance between the laws at every two
    dealt secrets under this model's own cut law by 2^-39, so no pair of run
    arguments separates them further and the existential the proposition
    asserts has no witness. The obstruction that
    psl211_alldecks_obstruction_published carries is therefore a statement
    about the twelve-card chirality model and not a proposition every model
    satisfies.
```
reason: the readings of every two dealt secrets names two laws

### instances/psl211/psl211_alldecks.v

**V99** &nbsp; `instances/psl211/psl211_alldecks.v:17-26`

current:
```
(* The counting half of the file says what a coalition of at most five seats  *)
(* learns from the codes it reads: at every cut and every reading, the deck   *)
(* descriptions of one chirality producing that reading are exactly as many   *)
(* as those of the other.  The deals of class b producing a reading are       *)
(* indexed by the blocks of the class's Steiner system meeting the cut image  *)
(* of the coalition in the reading's heart pattern, times one extension       *)
(* count for the heart labelling and one for the club labelling; the block    *)
(* counts agree because both tables are S(5,6,12) designs and the pattern has *)
(* at most five points, and the two extension counts do not mention the       *)
(* class.                                                                     *)
```
replacement:
```
(* The counting half of the file says what a coalition of at most five seats  *)
(* learns from the codes it reads: at every cut and every view, the deck      *)
(* descriptions of one chirality producing that view are exactly as many as   *)
(* those of the other.  The deals of class b producing a view are indexed by  *)
(* the blocks of the class's Steiner system meeting the cut image of the      *)
(* coalition in the view's heart pattern, times one extension count for the   *)
(* heart labelling and one for the club labelling; the block counts agree     *)
(* because both tables are S(5,6,12) designs and the pattern has at most five *)
(* points, and the two extension counts do not mention the class.             *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V100** &nbsp; `instances/psl211/psl211_alldecks.v:79-80`

current:
```
(*   psl211_alldecks_per_cut_count  == at one cut the two chiralities have    *)
(*                                 equally many deals producing a reading     *)
```
replacement:
```
(*   psl211_alldecks_per_cut_count  == at one cut the two chiralities have    *)
(*                                 equally many deals producing a view        *)
```
reason: index block; reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V101** &nbsp; `instances/psl211/psl211_alldecks.v:635-640`

current:
```
(** psl211_perm_ext_count — a labelling of the six codes of one colour that is
    prescribed on a set K of ranks, injectively, extends in exactly
    (6 - |K|)! ways.  This is the labelling factor of the deal count: a
    reading pins the labelling on the ranks the coalition sees and leaves the
    rest free, and the factor depends on the size of K alone, so it is the
    same on both sides of the class comparison. *)
```
replacement:
```
(** psl211_perm_ext_count — a labelling of the six codes of one colour that
    is prescribed on a set K of ranks, injectively, extends in exactly (6 -
    |K|)! ways.  This is the labelling factor of the deal count: a view pins
    the labelling on the ranks the coalition sees and leaves the rest free, and
    the factor depends on the size of K alone, so it is the same on both sides
    of the class comparison. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V102** &nbsp; `instances/psl211/psl211_alldecks.v:646-649`

current:
```
(** psl211_perm_ext_count0 — a prescription that is not injective on K has no
    extension at all.  This is the colour-inconsistent branch of the deal
    count: a reading that names one code at two ranks is produced by no deal
    of either class. *)
```
replacement:
```
(** psl211_perm_ext_count0 — a prescription that is not injective on K has no
    extension at all.  This is the colour-inconsistent branch of the deal
    count: a view that names one code at two ranks is produced by no deal of
    either class. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V103** &nbsp; `instances/psl211/psl211_alldecks.v:656-656`

current:
```
(* The coalition's reading and the positions it covers.                       *)
```
replacement:
```
(* The coalition's view and the positions it covers.                          *)
```
reason: rule-bounded heading; reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V104** &nbsp; `instances/psl211/psl211_alldecks.v:671-676`

current:
```
(** psl211_alldecks_view C x g — the coalition's reading of the all-decks
    deck, written on the instance's own side: seat i in C reads the card the
    laid deck puts at the shuffle image of i, every other seat reads ord0.
    The counting argument is stated about this function; the framework's
    static_coalition_obs is the same reading in the framework's own
    spelling. *)
```
replacement:
```
(** psl211_alldecks_view C x g — the coalition's view of the all-decks deck,
    written on the instance's own side: seat i in C reads the card the laid
    deck puts at the shuffle image of i, every other seat reads ord0. The
    counting argument is stated about this function; the framework's
    static_coalition_obs is the same function in the framework's own spelling.
    *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V105** &nbsp; `instances/psl211/psl211_alldecks.v:874-874`

current:
```
(** ad_read p — the code the reading names at the position p. *)
```
replacement:
```
(** ad_read p — the code the view names at the position p. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V106** &nbsp; `instances/psl211/psl211_alldecks.v:878-878`

current:
```
(** ad_A — the positions the reading names with a heart code. *)
```
replacement:
```
(** ad_A — the positions the view names with a heart code. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V107** &nbsp; `instances/psl211/psl211_alldecks.v:882-883`

current:
```
(** ad_offok — the reading is ord0 off the coalition, which is what the view
    of a coalition is by construction. *)
```
replacement:
```
(** ad_offok — the view is ord0 off the coalition, which is what the view of
    a coalition is by construction. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V108** &nbsp; `instances/psl211/psl211_alldecks.v:887-889`

current:
```
(** ad_readinj — the reading names distinct codes at distinct positions.  A
    reading that fails this is produced by no deal of either class, because
    every deal lays twelve distinct cards. *)
```
replacement:
```
(** ad_readinj — the view names distinct codes at distinct positions.  A view
    that fails this is produced by no deal of either class, because every deal
    lays twelve distinct cards. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V109** &nbsp; `instances/psl211/psl211_alldecks.v:893-897`

current:
```
(** ad_ok — the reading is one a deal can produce at all: it vanishes off the
    coalition and it names distinct codes at distinct read positions.  Both
    conditions are properties of the reading and the cut alone, so a reading
    that fails either has no deal of either chirality behind it and the two
    counts are zero together. *)
```
replacement:
```
(** ad_ok — the view is one a deal can produce at all: it vanishes off the
    coalition and it names distinct codes at distinct read positions.  Both
    conditions are properties of the view and the cut alone, so a view that
    fails either has no deal of either chirality behind it and the two counts
    are zero together. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V110** &nbsp; `instances/psl211/psl211_alldecks.v:900-901`

current:
```
(** ad_A_sub — the heart positions of the reading are positions the coalition
    reads. *)
```
replacement:
```
(** ad_A_sub — the heart positions of the view are positions the coalition
    reads. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V111** &nbsp; `instances/psl211/psl211_alldecks.v:909-910`

current:
```
(** ad_inA — the reading names a heart at a position it reads exactly when
    that position is one of the heart positions. *)
```
replacement:
```
(** ad_inA — the view names a heart at a position it reads exactly when that
    position is one of the heart positions. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V112** &nbsp; `instances/psl211/psl211_alldecks.v:915-916`

current:
```
(** ad_readP — a position the coalition reads is the image of a seat and the
    reading there is that seat's. *)
```
replacement:
```
(** ad_readP — a position the coalition reads is the image of a seat and the
    view there is that seat's. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V113** &nbsp; `instances/psl211/psl211_alldecks.v:921-923`

current:
```
(** ad_memE — a deal produces the reading exactly when the reading vanishes
    off the coalition and the laid deck carries the named code at every
    position the coalition reads. *)
```
replacement:
```
(** ad_memE — a deal produces the view exactly when the view vanishes off the
    coalition and the laid deck carries the named code at every position the
    coalition reads. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V114** &nbsp; `instances/psl211/psl211_alldecks.v:946-946`

current:
```
(** ad_hpin H — the heart ranks the reading pins inside the block H. *)
```
replacement:
```
(** ad_hpin H — the heart ranks the view pins inside the block H. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V115** &nbsp; `instances/psl211/psl211_alldecks.v:950-950`

current:
```
(** ad_cpin H — the club ranks the reading pins inside the complement. *)
```
replacement:
```
(** ad_cpin H — the club ranks the view pins inside the complement. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V116** &nbsp; `instances/psl211/psl211_alldecks.v:954-954`

current:
```
(** ad_th H — the heart code the reading forces at a rank of the block. *)
```
replacement:
```
(** ad_th H — the heart code the view forces at a rank of the block. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V117** &nbsp; `instances/psl211/psl211_alldecks.v:958-959`

current:
```
(** ad_tc H — the club code the reading forces at a rank of the complement,
    decoded back into the six club codes. *)
```
replacement:
```
(** ad_tc H — the club code the view forces at a rank of the complement,
    decoded back into the six club codes. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V118** &nbsp; `instances/psl211/psl211_alldecks.v:963-964`

current:
```
(** ad_thE — at a heart position the block prescription names the code the
    reading names there. *)
```
replacement:
```
(** ad_thE — at a heart position the block prescription names the code the
    view names there. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V119** &nbsp; `instances/psl211/psl211_alldecks.v:973-974`

current:
```
(** ad_tcE — at a club position the complement prescription names the
    reading's code decoded past the six heart codes. *)
```
replacement:
```
(** ad_tcE — at a club position the complement prescription names the view's
    code decoded past the six heart codes. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V120** &nbsp; `instances/psl211/psl211_alldecks.v:987-988`

current:
```
(** ad_patE — the pattern equation read at one position: a read position lies
    on the block line exactly when the reading names a heart there. *)
```
replacement:
```
(** ad_patE — the pattern equation read at one position: a read position lies
    on the block line exactly when the view names a heart there. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V121** &nbsp; `instances/psl211/psl211_alldecks.v:994-995`

current:
```
(** ad_A_inrow — a heart position of the reading lies on the block line, once
    the block line meets the read positions in the reading's heart pattern. *)
```
replacement:
```
(** ad_A_inrow — a heart position of the view lies on the block line, once
    the block line meets the read positions in the view's heart pattern. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V122** &nbsp; `instances/psl211/psl211_alldecks.v:1001-1001`

current:
```
(** ad_D_incorow — a club position of the reading lies off the block line. *)
```
replacement:
```
(** ad_D_incorow — a club position of the view lies off the block line. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V123** &nbsp; `instances/psl211/psl211_alldecks.v:1012-1015`

current:
```
(** ad_patternE — a deal producing the reading has its block line meeting the
    read positions exactly in the reading's heart pattern.  This is the
    passage from the reading seat by seat to the set-level pattern the block
    count is taken at. *)
```
replacement:
```
(** ad_patternE — a deal producing the view has its block line meeting the
    read positions exactly in the view's heart pattern.  This is the passage
    from the view seat by seat to the set-level pattern the block count is
    taken at. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V124** &nbsp; `instances/psl211/psl211_alldecks.v:1033-1037`

current:
```
(** ad_factorE — at a block line meeting the read positions in the reading's
    heart pattern, producing the reading is exactly prescribing the heart
    labelling on the heart ranks and the club labelling on the club ranks.
    The two prescriptions are independent, which is what makes the fiber a
    product of two extension counts. *)
```
replacement:
```
(** ad_factorE — at a block line meeting the read positions in the view's
    heart pattern, producing the view is exactly prescribing the heart
    labelling on the heart ranks and the club labelling on the club ranks. The
    two prescriptions are independent, which is what makes the fiber a product
    of two extension counts. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V125** &nbsp; `instances/psl211/psl211_alldecks.v:1090-1093`

current:
```
(** ad_hpin_card — the heart ranks the reading pins are as many as the heart
    positions it names, because rank and position are mutually inverse on the
    block line.  This is what turns the extension count's (6 - |K|)! into a
    factor the class comparison can cancel. *)
```
replacement:
```
(** ad_hpin_card — the heart ranks the view pins are as many as the heart
    positions it names, because rank and position are mutually inverse on the
    block line.  This is what turns the extension count's (6 - |K|)! into a
    factor the class comparison can cancel. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V126** &nbsp; `instances/psl211/psl211_alldecks.v:1106-1107`

current:
```
(** ad_cpin_card — the club ranks the reading pins are as many as the club
    positions it names. *)
```
replacement:
```
(** ad_cpin_card — the club ranks the view pins are as many as the club
    positions it names. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V127** &nbsp; `instances/psl211/psl211_alldecks.v:1120-1122`

current:
```
(** ad_th_inj — the heart prescription is injective on the ranks it pins, so
    the extension count is the positive one.  Injectivity of the reading on
    the read positions is what decides this, and it mentions no class. *)
```
replacement:
```
(** ad_th_inj — the heart prescription is injective on the ranks it pins, so
    the extension count is the positive one.  Injectivity of the view on the
    read positions is what decides this, and it mentions no class. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V128** &nbsp; `instances/psl211/psl211_alldecks.v:1172-1181`

current:
```
(* The ad_ok premise is a departure from the audit counter-probe, which
   assumed this equation unconditionally as a section hypothesis
   (notes/probes/2026-09-15-psl211-planb/audit-plan/audit_t4_percut.v).  The
   unconditional form is false.  A reading that is nonzero off the coalition,
   or that names one code at two read positions, is produced by no deal, so
   its left side is 0 at every block line, while the right side is
   (6 - #|ad_A|)! * (6 - #|ad_P :\: ad_A|)! at every block line meeting the
   read positions in the pattern.  The premise constrains the reading and the
   cut alone and never the class, so ad_fiber_empty answers its negation with
   0 on both sides. *)
```
replacement:
```
(* The ad_ok premise is a departure from the audit counter-probe, which assumed
   this equation unconditionally as a section hypothesis
   (notes/probes/2026-09-15-psl211-planb/audit-plan/audit_t4_percut.v).  The
   unconditional form is false.  A view that is nonzero off the coalition, or
   that names one code at two read positions, is produced by no deal, so its
   left side is 0 at every block line, while the right side is (6 - #|ad_A|)! *
   (6 - #|ad_P :\: ad_A|)! at every block line meeting the read positions in
   the pattern.  The premise constrains the view and the cut alone and never
   the class, so ad_fiber_empty answers its negation with 0 on both sides. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V129** &nbsp; `instances/psl211/psl211_alldecks.v:1182-1186`

current:
```
(** ad_fiber_at_row — the deals on one block line producing the reading are
    the pairs of labellings prescribed by that reading: the product of the two
    extension counts when the block line meets the read positions in the
    reading's heart pattern, and none otherwise.  Both factors are functions
    of the pattern alone, so neither mentions the class. *)
```
replacement:
```
(** ad_fiber_at_row — the deals on one block line producing the view are the
    pairs of labellings prescribed by that view: the product of the two
    extension counts when the block line meets the read positions in the view's
    heart pattern, and none otherwise.  Both factors are functions of the
    pattern alone, so neither mentions the class. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V130** &nbsp; `instances/psl211/psl211_alldecks.v:1214-1216`

current:
```
(** ad_fiber_empty — a reading that does not vanish off the coalition, or
    that names one code at two read positions, is produced by no deal of
    either class: every laid deck carries twelve distinct cards. *)
```
replacement:
```
(** ad_fiber_empty — a view that does not vanish off the coalition, or that
    names one code at two read positions, is produced by no deal of either
    class: every laid deck carries twelve distinct cards. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V131** &nbsp; `instances/psl211/psl211_alldecks.v:1235-1237`

current:
```
(** ad_split_over_row — the deals producing the reading split over the block
    line they name.  The block line is the coordinate the chirality enters
    through, so it is the coordinate the count is taken along. *)
```
replacement:
```
(** ad_split_over_row — the deals producing the view split over the block
    line they name.  The block line is the coordinate the chirality enters
    through, so it is the coordinate the count is taken along. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V132** &nbsp; `instances/psl211/psl211_alldecks.v:1254-1257`

current:
```
(** ad_deal_count — the deals of one class producing the reading are the
    block lines of that class's Steiner system meeting the read positions in
    the reading's heart pattern, each carrying the same pair of labelling
    factors.  Only the first factor mentions the class. *)
```
replacement:
```
(** ad_deal_count — the deals of one class producing the view are the block
    lines of that class's Steiner system meeting the read positions in the
    view's heart pattern, each carrying the same pair of labelling factors.
    Only the first factor mentions the class. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V133** &nbsp; `instances/psl211/psl211_alldecks.v:1285-1291`

current:
```
(** ad_pattern_classE — the two Steiner systems have equally many block lines
    meeting the read positions in the reading's heart pattern.  Both are
    S(5,6,12) designs and the pattern has at most five points, so no block
    count a coalition of that size can take separates them.  At an empty
    coalition both counts are the whole table, which is where
    psl211_pattern_transfer's positivity premise is avoided rather than
    met. *)
```
replacement:
```
(** ad_pattern_classE — the two Steiner systems have equally many block lines
    meeting the read positions in the view's heart pattern.  Both are S(5,6,12)
    designs and the pattern has at most five points, so no block count a
    coalition of that size can take separates them.  At an empty coalition both
    counts are the whole table, which is where psl211_pattern_transfer's
    positivity premise is avoided rather than met. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V134** &nbsp; `instances/psl211/psl211_alldecks.v:1322-1332`

current:
```
(** psl211_alldecks_per_cut_count — at one cut, one coalition of at most five
    seats and one reading, the two chiralities have equally many deals
    producing that reading.  The deals of class b producing a reading are
    indexed by the blocks of the class's Steiner system meeting the cut image
    of the coalition in the reading's heart pattern, times one extension count
    for the heart labelling and one for the club labelling; the block counts
    agree between the two systems because both are S(5,6,12) designs and the
    pattern has at most five points, and the two extension counts do not
    depend on the class at all.  This is the per-cut form;
    psl211_alldecks_fiber_transfer is its sum over the group and is the form
    the bridge consumes. *)
```
replacement:
```
(** psl211_alldecks_per_cut_count — at one cut, one coalition of at most five
    seats and one view, the two chiralities have equally many deals producing
    that view.  The deals of class b producing a view are indexed by the blocks
    of the class's Steiner system meeting the cut image of the coalition in the
    view's heart pattern, times one extension count for the heart labelling and
    one for the club labelling; the block counts agree between the two systems
    because both are S(5,6,12) designs and the pattern has at most five points,
    and the two extension counts do not depend on the class at all.  This is
    the per-cut form; psl211_alldecks_fiber_transfer is its sum over the group
    and is the form the bridge consumes. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V135** &nbsp; `instances/psl211/psl211_alldecks.v:1365-1366`

current:
```
(** ad_partition_cut — the deck descriptions and cuts producing a reading
    split over the cut they name. *)
```
replacement:
```
(** ad_partition_cut — the deck descriptions and cuts producing a view split
    over the cut they name. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

**V136** &nbsp; `instances/psl211/psl211_alldecks.v:1388-1393`

current:
```
(** psl211_alldecks_fiber_transfer — the same counts summed over the cuts of
    the group: for every reading of a coalition of at most five seats, the
    deck descriptions and cuts producing it are as many under one chirality as
    under the other.  This is the counting premise the uniform-pair bridge
    consumes: no other instance-specific fact enters the independence
    statement. *)
```
replacement:
```
(** psl211_alldecks_fiber_transfer — the same counts summed over the cuts of
    the group: for every view of a coalition of at most five seats, the deck
    descriptions and cuts producing it are as many under one chirality as under
    the other.  This is the counting premise the uniform-pair bridge consumes:
    no other instance-specific fact enters the independence statement. *)
```
reason: reading names a value of psl211_alldecks_view; the file's own word for that value is view

### instances/psl211/psl211_analysis.v

**V137** &nbsp; `instances/psl211/psl211_analysis.v:111-114`

current:
```
(* Three carriers, kept distinct: a card of the twelve-card deck for one      *)
(* seat's endpoint, a finfun of cards indexed by seats for a coalition's      *)
(* endpoints, for its reading of the laid deck and for the content reading of *)
(* its executed rows, and bool for the chirality.                             *)
```
replacement:
```
(* Three carriers, kept distinct: a card of the twelve-card deck for one      *)
(* seat's endpoint, a finfun of cards indexed by seats for a coalition's      *)
(* endpoints, for its view of the laid deck and for the content trace of its  *)
(* executed rows, and bool for the chirality.                                 *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V138** &nbsp; `instances/psl211/psl211_analysis.v:130-134`

current:
```
(** static_view — the coalition's reading of the laid deck: a seat of the
    coalition reads the card the layout puts at the cut image of that seat.
    The instance's counting argument is stated about this function, and the
    framework's static_coalition_obs is the same reading in the framework's
    own spelling. *)
```
replacement:
```
(** static_view — the coalition's view of the laid deck: a seat of the
    coalition reads the card the layout puts at the cut image of that seat. The
    instance's counting argument is stated about this function, and the
    framework's static_coalition_obs is the same function in the framework's
    own spelling. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V139** &nbsp; `instances/psl211/psl211_analysis.v:189-191`

current:
```
(** exact_coalition_distE — the model's executed coalition distribution is the
    pushforward of its own law along the coalition's reading of the laid
    deck. *)
```
replacement:
```
(** exact_coalition_distE — the model's executed coalition distribution is
    the pushforward of its own law along the coalition's view of the laid deck.
    *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V140** &nbsp; `instances/psl211/psl211_analysis.v:226-227`

current:
```
(** static_indep — the same independence at the framework's static reading,
    which is the form the exact-independence witness's field takes. *)
```
replacement:
```
(** static_indep — the same independence at the framework's static endpoints,
    which is the form the exact-independence witness's field takes. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V141** &nbsp; `instances/psl211/psl211_analysis.v:252-255`

current:
```
(** exact_transfer_status — the all-decks path's transfer status.
    StaticExecutedOnly, the path carrying its results from the deck-level
    reading to the executed one and comparing no idealized model, the cut it
    draws being the uniform law on the group already. *)
```
replacement:
```
(** exact_transfer_status — the all-decks path's transfer status.
    StaticExecutedOnly, the path carrying its results from the deck-level view
    to the executed one and comparing no idealized model, the cut it draws
    being the uniform law on the group already. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

### instances/psl211/psl211_models.v

**V142** &nbsp; `instances/psl211/psl211_models.v:8-17`

current:
```
(* The all-decks run of psl211_alldecks.v carries no probability model. This  *)
(* file supplies one: a deck description drawn uniformly from the 136857600   *)
(* of them and a cut drawn uniformly from the 660 elements of the group, the  *)
(* two independent. Under that law the run is packaged as an observed         *)
(* execution, its three run facts collected, and the reading of a coalition   *)
(* of at most five of the twelve seats is proved independent of the           *)
(* chirality. The independence is exact and is an average over decks and      *)
(* cuts; it neither implies nor is implied by the fixed-dealer colour result  *)
(* of psl211_secrecy.v, which is about a different dealer and a different     *)
(* observer.                                                                  *)
```
replacement:
```
(* The all-decks run of psl211_alldecks.v carries no probability model. This  *)
(* file supplies one: a deck description drawn uniformly from the 136857600   *)
(* of them and a cut drawn uniformly from the 660 elements of the group, the  *)
(* two independent. Under that law the run is packaged as an observed         *)
(* execution, its three run facts collected, and the view of a coalition of   *)
(* at most five of the twelve seats is proved independent of the chirality.   *)
(* The independence is exact and is an average over decks and cuts; it        *)
(* neither implies nor is implied by the fixed-dealer colour result of        *)
(* psl211_secrecy.v, which is about a different dealer and a different        *)
(* observer.                                                                  *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V143** &nbsp; `instances/psl211/psl211_models.v:19-27`

current:
```
(* Two readings of a coalition are identified here. The framework's           *)
(* static_coalition_obs reads seat i at tnth (pi_starts _) i through the      *)
(* layout's share cast; the instance's psl211_alldecks_view reads it at i.    *)
(* The share cast disappears by conversion, the scheme's share count and the  *)
(* algebra's card count both being twelve, and the starting tuple is          *)
(* ord_tuple 12, so the two agree. What the interpreter's messages give of a  *)
(* coalition's endpoints is carried to the static computation by the endpoint *)
(* equation of psl211_endpoints.v, which enters here only through             *)
(* supplied_endpointsE and is never unfolded.                                 *)
```
replacement:
```
(* Two computations of a coalition's endpoints are identified here. The       *)
(* framework's static_coalition_obs reads seat i at tnth (pi_starts _) i      *)
(* through the layout's share cast; the instance's psl211_alldecks_view reads *)
(* it at i. The share cast disappears by conversion, the scheme's share count *)
(* and the algebra's card count both being twelve, and the starting tuple is  *)
(* ord_tuple 12, so the two agree. What the interpreter's messages give of a  *)
(* coalition's endpoints is carried to the static computation by the endpoint *)
(* equation of psl211_endpoints.v, which enters here only through             *)
(* supplied_endpointsE and is never unfolded.                                 *)
```
reason: Two readings of a coalition names two computations of the endpoints, not two CoalitionReadings

**V144** &nbsp; `instances/psl211/psl211_models.v:45-53`

current:
```
(* The dealer route. The all-decks independence is obtained a second way,     *)
(* from the dealer model of reconstruct/dealer_privacy.v, by placing the      *)
(* chirality, the deal and the cut in its sample space. The                   *)
(* route goes through the mixed-law condition, whose premise the per-cut      *)
(* count of psl211_alldecks.v discharges, and it restates                     *)
(* psl211_alldecks_view_indep without replacing its proof. Two refutations    *)
(* bound it: the per-deck condition has no solution under this dealer, and    *)
(* under a dealer laying one fixed deal the reading of three                  *)
(* seats is not independent of the chirality.                                 *)
```
replacement:
```
(* The dealer route. The all-decks independence is obtained a second way,     *)
(* from the dealer model of reconstruct/dealer_privacy.v, by placing the      *)
(* chirality, the deal and the cut in its sample space. The route goes        *)
(* through the mixed-law condition, whose premise the per-cut count of        *)
(* psl211_alldecks.v discharges, and it restates psl211_alldecks_view_indep   *)
(* without replacing its proof. Two refutations bound it: the per-deck        *)
(* condition has no solution under this dealer, and under a dealer laying one *)
(* fixed deal the view of three seats is not independent of the chirality.    *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V145** &nbsp; `instances/psl211/psl211_models.v:79-80`

current:
```
(*   psl211_perdeck_view     == the reading that fixes the counterexample     *)
(*   psl211_perdeck_fiber    == the cuts producing that reading               *)
```
replacement:
```
(*   psl211_perdeck_view     == the view that fixes the counterexample        *)
(*   psl211_perdeck_fiber    == the cuts producing that view                  *)
```
reason: index block; reading names the random variable a coalition computes from the run, whose name in this file is view

**V146** &nbsp; `instances/psl211/psl211_models.v:89-91`

current:
```
(*   psl211_alldecks_static_obsE == the framework's reading at a seat is the  *)
(*                              card the laid deck puts at its cut image,     *)
(*                              and ord0 outside the coalition                *)
```
replacement:
```
(*   psl211_alldecks_static_obsE == the framework's endpoint at a seat is     *)
(*                              the card the laid deck puts at its cut        *)
(*                              image, and ord0 outside the coalition         *)
```
reason: index block; the framework's reading at a seat names the value

**V147** &nbsp; `instances/psl211/psl211_models.v:112-113`

current:
```
(*   psl211_dealer_sectionE  == at one cut the two chiralities send the       *)
(*                              uniform law on deals to the same reading law  *)
```
replacement:
```
(*   psl211_dealer_sectionE  == at one cut the two chiralities send the       *)
(*                              uniform law on deals to the same view law     *)
```
reason: index block; the same reading law names the pushforward law

**V148** &nbsp; `instances/psl211/psl211_models.v:119-121`

current:
```
(*   psl211_perdeck_raw_countE == at one deal the two                         *)
(*                              chiralities have 0 and 1 cuts producing one   *)
(*                              reading                                       *)
```
replacement:
```
(*   psl211_perdeck_raw_countE == at one deal the two                         *)
(*                              chiralities have 0 and 1 cuts producing one   *)
(*                              view                                          *)
```
reason: index block; reading names the random variable a coalition computes from the run, whose name in this file is view

**V149** &nbsp; `instances/psl211/psl211_models.v:128-130`

current:
```
(*   psl211_fixed_deal_view_dep == under a dealer laying one fixed deck       *)
(*                              description the reading of three seats is     *)
(*                              not independent of the chirality              *)
```
replacement:
```
(*   psl211_fixed_deal_view_dep == under a dealer laying one fixed deck       *)
(*                              description the view of three seats is        *)
(*                              not independent of the chirality              *)
```
reason: index block; reading names the random variable a coalition computes from the run, whose name in this file is view

**V150** &nbsp; `instances/psl211/psl211_models.v:131-132`

current:
```
(*   psl211_dealer_viewE == the model's reading along the reassociation is    *)
(*                              the instance's reading                        *)
```
replacement:
```
(*   psl211_dealer_viewE == the model's view along the reassociation is       *)
(*                              the instance's view                           *)
```
reason: index block; reading names the random variable a coalition computes from the run, whose name in this file is view

**V151** &nbsp; `instances/psl211/psl211_models.v:269-274`

current:
```
(** psl211_alldecks_static_obsE — seat i's entry of the framework's static
    coalition reading is the card the laid deck puts at the cut image of
    seat i, and ord0 at every seat outside C. Every security statement of this
    instance is made about the left-hand side and every counting argument
    about the right, so this equation is the whole of what carries one to the
    other. *)
```
replacement:
```
(** psl211_alldecks_static_obsE — seat i's entry of the framework's static
    coalition endpoints is the card the laid deck puts at the cut image of seat
    i, and ord0 at every seat outside C. Every security statement of this
    instance is made about the left-hand side and every counting argument about
    the right, so this equation is the whole of what carries one to the other.
    *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V152** &nbsp; `instances/psl211/psl211_models.v:289-291`

current:
```
(** psl211_alldecks_static_obs_viewE — the whole reading, as one finite
    function: the framework's static coalition observation at a description
    and a cut is the instance's view of the laid deck. *)
```
replacement:
```
(** psl211_alldecks_static_obs_viewE — the whole view, as one finite
    function: the framework's static coalition observation at a description and
    a cut is the instance's view of the laid deck. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V153** &nbsp; `instances/psl211/psl211_models.v:476-479`

current:
```
(** psl211_alldecks_exec_viewE — the executed coalition reader of the
    all-decks model is the static coalition reading. This is the step that
    turns a claim about the interpreter's messages into a claim about the
    group action, and it is what the endpoint equation gives. *)
```
replacement:
```
(** psl211_alldecks_exec_viewE — the executed coalition reader of the
    all-decks model is the static coalition view. This is the step that turns a
    claim about the interpreter's messages into a claim about the group action,
    and it is what the endpoint equation gives. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V154** &nbsp; `instances/psl211/psl211_models.v:504-509`

current:
```
(** psl211_alldecks_view_indep — under the all-decks dealer the raw code
    reading of any coalition of at most five of the twelve seats is
    independent of the chirality. Exact, at every real field, and an average
    over decks and cuts rather than a statement about one deck: the whole
    instance-specific content is the equality of the two chiralities' deal
    counts, which the uniform-pair bridge turns into independence. *)
```
replacement:
```
(** psl211_alldecks_view_indep — under the all-decks dealer the raw code view
    of any coalition of at most five of the twelve seats is independent of the
    chirality. Exact, at every real field, and an average over decks and cuts
    rather than a statement about one deck: the whole instance-specific content
    is the equality of the two chiralities' deal counts, which the uniform-pair
    bridge turns into independence. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V155** &nbsp; `instances/psl211/psl211_models.v:541-546`

current:
```
(** psl211_alldecks_coalition_distE — the executed coalition distribution of
    the all-decks model is the pushforward of the model's own law along the
    instance-side reading. This is the equation that makes a counting result
    proved about the laid deck a result about what the interpreter's messages
    carry, so every independence statement here is attached to the executed
    observer and not only to the static one. *)
```
replacement:
```
(** psl211_alldecks_coalition_distE — the executed coalition distribution of
    the all-decks model is the pushforward of the model's own law along the
    instance-side view. This is the equation that makes a counting result
    proved about the laid deck a result about what the interpreter's messages
    carry, so every independence statement here is attached to the executed
    observer and not only to the static one. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V156** &nbsp; `instances/psl211/psl211_models.v:560-566`

current:
```
(** psl211_alldecks_exec_exact_view_indep — at five seats the executed
    coalition observation of the all-decks model and the chirality have a
    product joint distribution, for a coalition of at most five of the twelve
    seats. This is psl211_alldecks_view_indep transported to the executed
    sample layer, so the independence is a statement about what the
    interpreter's messages contain and not only about the instance-side
    reading. *)
```
replacement:
```
(** psl211_alldecks_exec_exact_view_indep — at five seats the executed
    coalition observation of the all-decks model and the chirality have a
    product joint distribution, for a coalition of at most five of the twelve
    seats. This is psl211_alldecks_view_indep transported to the executed
    sample layer, so the independence is a statement about what the
    interpreter's messages contain and not only about the instance-side view.
    *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V157** &nbsp; `instances/psl211/psl211_models.v:595-600`

current:
```
(* psl211_alldecks_view expands to the laid deck and through it to the two
   132-row block tables of psl211_alldecks.v.  Sealing it keeps a failed
   unification from descending into those tables: a rule differing from the
   other side of the goal only in the chirality bit makes the matcher compare
   the two table literals, and it does not come back.  No step below needs the
   body of the reading; each names it and closes by exact. *)
```
replacement:
```
(* psl211_alldecks_view expands to the laid deck and through it to the two
   132-row block tables of psl211_alldecks.v.  Sealing it keeps a failed
   unification from descending into those tables: a rule differing from the
   other side of the goal only in the chirality bit makes the matcher compare
   the two table literals, and it does not come back.  No step below needs the
   body of the view; each names it and closes by exact. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V158** &nbsp; `instances/psl211/psl211_models.v:661-664`

current:
```
(** psl211_dealer_view C — the reading of a coalition C of seats, as a
    function of the dealer model's three coordinates.  It reads the chirality
    only through the deck the deal lays, which is why a symmetry between the two
    chiralities is enough to hide the chirality from C. *)
```
replacement:
```
(** psl211_dealer_view C — the view of a coalition C of seats, as a function
    of the dealer model's three coordinates.  It reads the chirality only
    through the deck the deal lays, which is why a symmetry between the two
    chiralities is enough to hide the chirality from C. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V159** &nbsp; `instances/psl211/psl211_models.v:669-670`

current:
```
(** psl211_dealer_viewE — the dealer model's reading, composed with the
    reassociation, is the instance's reading. *)
```
replacement:
```
(** psl211_dealer_viewE — the dealer model's view, composed with the
    reassociation, is the instance's view. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V160** &nbsp; `instances/psl211/psl211_models.v:727-729`

current:
```
(** psl211_dealer_mixed_lawE — the two chiralities have the same averaged
    reading law.  The per-cut equality is lifted to the pair of deal and cut,
    which is the dealer model's privacy premise at this instance. *)
```
replacement:
```
(** psl211_dealer_mixed_lawE — the two chiralities have the same averaged
    view law.  The per-cut equality is lifted to the pair of deal and cut,
    which is the dealer model's privacy premise at this instance. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V161** &nbsp; `instances/psl211/psl211_models.v:743-746`

current:
```
(** psl211_dealer_view_indep — in the dealer model's sample space, the reading
    of a coalition of at most five seats is independent of the chirality.  This
    is dealer_shuffle_view_indep at the common averaged law, and it is exact: no
    approximation and no computational premise. *)
```
replacement:
```
(** psl211_dealer_view_indep — in the dealer model's sample space, the view
    of a coalition of at most five seats is independent of the chirality.  This
    is dealer_shuffle_view_indep at the common averaged law, and it is exact:
    no approximation and no computational premise. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V162** &nbsp; `instances/psl211/psl211_models.v:779-781`

current:
```
(* the two commuting equations are rewritten into the goal, not into Hgen: the
   goal names the reading only through psl211_alldecks_view, which is sealed,
   so the matcher never reaches the block tables underneath it *)
```
replacement:
```
(* the two commuting equations are rewritten into the goal, not into Hgen: the
   goal names the view only through psl211_alldecks_view, which is sealed, so
   the matcher never reaches the block tables underneath it *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V163** &nbsp; `instances/psl211/psl211_models.v:788-790`

current:
```
(* The counting below is on raw data and needs the body of the reading, so the
   seal is released here and taken again once the raw count is carried back to
   the real objects. *)
```
replacement:
```
(* The counting below is on raw data and needs the body of the view, so the
   seal is released here and taken again once the raw count is carried back to
   the real objects. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V164** &nbsp; `instances/psl211/psl211_models.v:797-805`

current:
```
(* Only raw nat data reduces here.  `inord` is `insubd ord0`, whose `insub`
   branches on the Qed-opaque `idP`, so `inord k` never becomes an `Ordinal`
   under vm_compute; measured 2026-09-18, `Eval vm_compute in val (inord 0)`
   returns a stuck `match idP with ...`.  Since `psl211_alldecks_seq` and every
   finfun or finset over the card type go through `inord` or `ord_enum`, the
   counted term below names none of them: it is a `count` over the raw
   permutation tables, and the three lemmas psl211_perdeck_seqE,
   psl211_perdeck_raw_viewE and psl211_perdeck_testE carry it back to the deck,
   the reading and the shuffle group symbolically. *)
```
replacement:
```
(* Only raw nat data reduces here. `inord` is `insubd ord0`, whose `insub`
   branches on the Qed-opaque `idP`, so `inord k` never becomes an `Ordinal`
   under vm_compute; measured 2026-09-18, `Eval vm_compute in val (inord 0)`
   returns a stuck `match idP with ...`.  Since `psl211_alldecks_seq` and every
   finfun or finset over the card type go through `inord` or `ord_enum`, the
   counted term below names none of them: it is a `count` over the raw
   permutation tables, and the three lemmas psl211_perdeck_seqE,
   psl211_perdeck_raw_viewE and psl211_perdeck_testE carry it back to the deck,
   the view and the shuffle group symbolically. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V165** &nbsp; `instances/psl211/psl211_models.v:816-817`

current:
```
(** psl211_perdeck_view — the reading that gives cards 0, 1 and 5 to seats 0,
    1 and 2, and card 0 to every seat outside the coalition. *)
```
replacement:
```
(** psl211_perdeck_view — the view that gives cards 0, 1 and 5 to seats 0, 1
    and 2, and card 0 to every seat outside the coalition. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V166** &nbsp; `instances/psl211/psl211_models.v:866-867`

current:
```
(** psl211_perdeck_raw_view sq t — the reading the coalition gets from the
    deck sq under the cut whose table is t, written on raw data. *)
```
replacement:
```
(** psl211_perdeck_raw_view sq t — the view the coalition gets from the deck
    sq under the cut whose table is t, written on raw data. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V167** &nbsp; `instances/psl211/psl211_models.v:873-874`

current:
```
(** psl211_perdeck_test sq t — the same reading matches psl211_perdeck_view,
    tested on raw codes. *)
```
replacement:
```
(** psl211_perdeck_test sq t — the same view matches psl211_perdeck_view,
    tested on raw codes. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V168** &nbsp; `instances/psl211/psl211_models.v:880-881`

current:
```
(** psl211_perdeck_testE — the raw test decides the reading, so the fiber over
    psl211_perdeck_view is counted by a boolean on nat lists. *)
```
replacement:
```
(** psl211_perdeck_testE — the raw test decides the view, so the fiber over
    psl211_perdeck_view is counted by a boolean on nat lists. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V169** &nbsp; `instances/psl211/psl211_models.v:906-909`

current:
```
(** psl211_perdeck_raw_countE — that count is zero at one chirality and one
    at the other, which is the per-deck failure of the chirality symmetry: at
    a fixed deal the two chiralities do not have equally many cuts producing
    a given reading, even though summing over the deals they do. *)
```
replacement:
```
(** psl211_perdeck_raw_countE — that count is zero at one chirality and one
    at the other, which is the per-deck failure of the chirality symmetry: at a
    fixed deal the two chiralities do not have equally many cuts producing a
    given view, even though summing over the deals they do. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V170** &nbsp; `instances/psl211/psl211_models.v:940-940`

current:
```
(** psl211_perdeck_raw_viewE — the raw reading is the instance's reading. *)
```
replacement:
```
(** psl211_perdeck_raw_viewE — the raw view is the instance's view. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V171** &nbsp; `instances/psl211/psl211_models.v:1014-1019`

current:
```
(** psl211_perdeck_fiber_card_neq — at one deal the two chiralities have
    different numbers of cuts producing one reading.  The symmetry the
    all-decks counting argument uses holds only in its per-cut form, which
    fixes a cut and counts deals.  The statement with the roles exchanged,
    fixing a deal and counting cuts, is false, and psl211_perdeck_deal
    witnesses it. *)
```
replacement:
```
(** psl211_perdeck_fiber_card_neq — at one deal the two chiralities have
    different numbers of cuts producing one view.  The symmetry the all-decks
    counting argument uses holds only in its per-cut form, which fixes a cut
    and counts deals.  The statement with the roles exchanged, fixing a deal
    and counting cuts, is false, and psl211_perdeck_deal witnesses it. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V172** &nbsp; `instances/psl211/psl211_models.v:1130-1135`

current:
```
(** psl211_dealer_view_indep_of_deck_unsat — at PSL(2,11) under its own dealer
    law the two premises of dealer_shuffle_view_indep_of_deck have no common
    solution, for every validity predicate and every candidate reading law.
    So of the model's two conditions only the mixed-law condition of
    dealer_shuffle_view_indep is available to this instance, and the uniform
    law on deals meets it. *)
```
replacement:
```
(** psl211_dealer_view_indep_of_deck_unsat — at PSL(2,11) under its own
    dealer law the two premises of dealer_shuffle_view_indep_of_deck have no
    common solution, for every validity predicate and every candidate view law.
    So of the model's two conditions only the mixed-law condition of
    dealer_shuffle_view_indep is available to this instance, and the uniform
    law on deals meets it. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V173** &nbsp; `instances/psl211/psl211_models.v:1168-1177`

current:
```
(** psl211_fixed_deal_view_dep — under that dealer law the reading of three
    seats is NOT independent of the chirality.  This is what entitles the paper
    to say that privacy depends on the dealer law and not on the protocol alone:
    the shuffle group, the design and the coalition are the ones PSL(2,11) uses,
    only the dealer changed, and the conclusion fails. Read together with
    psl211_alldecks_view_indep_via_dealer it says that for PSL(2,11) privacy
    depends on which deal law the dealer uses: the uniform one delivers it, and
    the point mass at psl211_perdeck_deal does not.  What is NOT shown here is
    that a hidden uniform deal leaks: the deal is public in this refutation,
    being a point mass. *)
```
replacement:
```
(** psl211_fixed_deal_view_dep — under that dealer law the view of three
    seats is NOT independent of the chirality.  This is what entitles the paper
    to say that privacy depends on the dealer law and not on the protocol
    alone: the shuffle group, the design and the coalition are the ones
    PSL(2,11) uses, only the dealer changed, and the conclusion fails.  Read
    together with psl211_alldecks_view_indep_via_dealer it says that for
    PSL(2,11) privacy depends on which deal law the dealer uses: the uniform
    one delivers it, and the point mass at psl211_perdeck_deal does not.  What
    is NOT shown here is that a hidden uniform deal leaks: the deal is public
    in this refutation, being a point mass. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V174** &nbsp; `instances/psl211/psl211_models.v:1217-1220`

current:
```
(* no /= and no case on a boolean numeral anywhere below: the sample carries
   psl211_perdeck_deal, whose permutations a simplification would try to
   compute, and the reading is only ever moved by conversion at an ascription
   or by a named rewrite *)
```
replacement:
```
(* no /= and no case on a boolean numeral anywhere below: the sample carries
   psl211_perdeck_deal, whose permutations a simplification would try to
   compute, and the view is only ever moved by conversion at an ascription or
   by a named rewrite *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V175** &nbsp; `instances/psl211/psl211_models.v:1240-1242`

current:
```
(* Nothing after this point reasons about the reading or the counts, so the
   seals are released; Opaque is not section-scoped and would otherwise leak
   into every file that requires this one. *)
```
replacement:
```
(* Nothing after this point reasons about the view or the counts, so the seals
   are released; Opaque is not section-scoped and would otherwise leak into
   every file that requires this one. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

### instances/psl211/psl211_alldecks_input_distinguishability.v

**V176** &nbsp; `instances/psl211/psl211_alldecks_input_distinguishability.v:28-31`

current:
```
(*   psl211_perdeck_static_mass_true                                          *)
(*                           == the group-uniform cut gives the reading       *)
(*                              psl211_perdeck_view mass zero at chirality    *)
(*                              true                                          *)
```
replacement:
```
(*   psl211_perdeck_static_mass_true                                          *)
(*                           == the group-uniform cut gives the view          *)
(*                              psl211_perdeck_view mass zero at chirality    *)
(*                              true                                          *)
```
reason: index block; reading names the random variable a coalition computes from the run, whose name in this file is view

**V177** &nbsp; `instances/psl211/psl211_alldecks_input_distinguishability.v:82-82`

current:
```
(** viewT — a reading, the card a coalition's seats see at each seat. *)
```
replacement:
```
(** viewT — a view, the card a coalition's seats see at each seat. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V178** &nbsp; `instances/psl211/psl211_alldecks_input_distinguishability.v:89-93`

current:
```
(** psl211_perdeck_static_mass_true — the mass the group-uniform cut gives the
    reading psl211_perdeck_view at chirality true, taken at the framework's own
    static reader: zero, the true fiber being empty. It is the first of the two
    masses psl211_alldecks_constancy_false_close computes inline, named here
    because the quantitative core below takes both as its inputs. *)
```
replacement:
```
(** psl211_perdeck_static_mass_true — the mass the group-uniform cut gives
    the view psl211_perdeck_view at chirality true, taken at the framework's
    own static reader: zero, the true fiber being empty. It is the first of the
    two masses psl211_alldecks_constancy_false_close computes inline, named
    here because the quantitative core below takes both as its inputs. *)
```
reason: reading names the random variable a coalition computes from the run, whose name in this file is view

**V179** &nbsp; `instances/psl211/psl211_alldecks_input_distinguishability.v:147-156`

current:
```
(** psl211_alldecks_perdeck_reading_ge — under the all-decks model's own cut
    law, the coalition psl211_perdeck_coalition of three of the twelve seats
    reads the two chiralities of the deal psl211_perdeck_deal at least the
    reciprocal 1/660 of the group order apart, in the sum of absolute
    differences. The two run arguments are named and not drawn, and no
    certificate occurs in the statement, so this is a fact about the model and
    a coalition's static reading alone. A distinguisher told to compare those
    two run arguments therefore has advantage at least 1/1320 at this model,
    the sum of absolute differences being twice the total variation distance
    of the literature. *)
```
replacement:
```
(** psl211_alldecks_perdeck_reading_ge — under the all-decks model's own cut
    law, the coalition psl211_perdeck_coalition of three of the twelve seats
    reads the two chiralities of the deal psl211_perdeck_deal at least the
    reciprocal 1/660 of the group order apart, in the sum of absolute
    differences. The two run arguments are named and not drawn, and no
    certificate occurs in the statement, so this is a fact about the model and
    a coalition's static endpoints alone. A distinguisher told to compare those
    two run arguments therefore has advantage at least 1/1320 at this model,
    the sum of absolute differences being twice the total variation distance of
    the literature. *)
```
reason: a coalition's static reading names the random variable

### instances/psl211/psl211_word_proximity.v

**V180** &nbsp; `instances/psl211/psl211_word_proximity.v:25-28`

current:
```
(*   psl211_word_proximity_close                                              *)
(*                              == the two models' joint laws of a            *)
(*                                 coalition's reading and the chirality are  *)
(*                                 within 2^-40                               *)
```
replacement:
```
(*   psl211_word_proximity_close                                              *)
(*                              == the two models' joint laws of a            *)
(*                                 coalition's endpoints and the chirality    *)
(*                                 are within 2^-40                           *)
```
reason: index block; a coalition's reading names the random variable

**V181** &nbsp; `instances/psl211/psl211_word_proximity.v:70-79`

current:
```
(** At every coalition of the twelve seats, the joint law of
    that coalition's reading with the chirality under the 584-letter word
    shuffle is within 2^-40 of the same joint law under the uniform shuffle.
    It is the closeness field of this instance's proximity certificate: the two
    models differ in the law of the cut alone, and the pair of a reading and the
    chirality is a deterministic function of the sample point, so the distance
    between the two cuts carries down to that pair unchanged. The claim is an
    average over the deck description and the cut. The bound holds at every
    coalition and not only below the threshold; the threshold enters the
    ideal-proximity proposition and not this distance. *)
```
replacement:
```
(** At every coalition of the twelve seats, the joint law of that coalition's
    endpoints with the chirality under the 584-letter word shuffle is within
    2^-40 of the same joint law under the uniform shuffle. It is the closeness
    field of this instance's proximity certificate: the two models differ in
    the law of the cut alone, and the pair of those endpoints and the chirality
    is a deterministic function of the sample point, so the distance between
    the two cuts carries down to that pair unchanged. The claim is an average
    over the deck description and the cut. The bound holds at every coalition
    and not only below the threshold; the threshold enters the ideal-proximity
    proposition and not this distance. *)
```
reason: that coalition's reading and a reading name the random variable

### instances/psl211/psl211_reading_constancy.v

**V182** &nbsp; `instances/psl211/psl211_reading_constancy.v:129-131`

current:
```
(*   psl211_blockline1_law_neq                                                *)
(*                           == two deck descriptions of one chirality send   *)
(*                              the group-uniform cut to two reading laws     *)
```
replacement:
```
(*   psl211_blockline1_law_neq                                                *)
(*                           == two deck descriptions of one chirality send   *)
(*                              the group-uniform cut to two different laws   *)
```
reason: index block; two reading laws names the two pushforward laws

**V183** &nbsp; `instances/psl211/psl211_reading_constancy.v:633-635`

current:
```
(* the true mass vanishes term by term: a cut producing the reading is either
   outside the group, where the law is zero, or inside it and in the empty
   true fiber *)
```
replacement:
```
(* the true mass vanishes term by term: a cut producing the view is either
   outside the group, where the law is zero, or inside it and in the empty true
   fiber *)
```
reason: the reading names a value of psl211_alldecks_view

**V184** &nbsp; `instances/psl211/psl211_reading_constancy.v:818-833`

current:
```
(** psl211_alldecks_indistinguishability_number_ge — every number at which an
    input-indistinguishability program over the all-decks model states its
    proposition is at least 1/660, whatever the program's certificate. That
    proposition bounds the distance between the readings of every two run
    arguments and the theorem above exhibits two whose distance reaches 1/660.
    This constrains the number a program publishes, where
    psl211_alldecks_no_small_eps_cert constrains the certificate's own marginal
    bound; the second follows from the general form of the tail lemma at the
    certificate's own number, and neither is edited by the other. A certificate
    whose ideal cut sits further than half of 1/660 from the group-uniform law
    is untouched by both, and a program over it still publishes at least
    1/660. Both the obstruction and the certificate are at the coalition's
    own endpoint reading: this is the framework's number bound at one
    reading, and a program whose certificate is at a coarser reading is
    bounded only through a factorisation, by
    indistinguishability_number_ge_across_readings. *)
```
replacement:
```
(** psl211_alldecks_indistinguishability_number_ge — every number at which
    an input-indistinguishability program over the all-decks model states
    its proposition is at least 1/660, whatever the program's certificate.
    That proposition bounds the distance between what the reading grants at
    every two run arguments and the theorem above exhibits two whose
    distance reaches 1/660. This constrains the number a program publishes,
    where psl211_alldecks_no_small_eps_cert constrains the certificate's own
    marginal bound; the second follows from the general form of the tail
    lemma at the certificate's own number, and neither is edited by the
    other. A certificate whose ideal cut sits further than half of 1/660
    from the group-uniform law is untouched by both, and a program over it
    still publishes at least 1/660. Both the obstruction and the certificate
    are at the coalition's own endpoint reading: this is the framework's
    number bound at one reading, and a program whose certificate is at a
    coarser reading is bounded only through a factorisation, by
    indistinguishability_number_ge_across_readings. *)
```
reason: the readings of every two run arguments names two laws; the other three uses in the paragraph are the record and stay

**V185** &nbsp; `instances/psl211/psl211_reading_constancy.v:983-986`

current:
```
(** psl211_dealt_static_obsE — seat i's entry of the framework's static
    coalition reading under the dealt parameters is the card the encoder deck
    of the run argument puts at the cut image of seat i. The dealt analogue of
    psl211_alldecks_static_obsE. *)
```
replacement:
```
(** psl211_dealt_static_obsE — seat i's entry of the framework's static
    coalition endpoints under the dealt parameters is the card the encoder deck
    of the run argument puts at the cut image of seat i. The dealt analogue of
    psl211_alldecks_static_obsE. *)
```
reason: static coalition reading names the computed value

**V186** &nbsp; `instances/psl211/psl211_reading_constancy.v:1057-1074`

current:
```
(** psl211_dealt_constancy_false — under the dealer-dealt run parameters the
    constancy field is false at the uniform law on the shuffle group, so no
    input-indistinguishability certificate over these parameters can take that
    law as its ideal cut, while a certificate at some other ideal stays open.
    The dealt run argument is the chirality and nothing else, so here the
    constancy field is exactly constancy in the secret, and it fails because the
    encoder decks of the two chiralities give one reading of three seats
    different masses. That is a fact about the group and the design: PSL(2,11)
    is 2-transitive and not 3-transitive, where PGL(2,7) proves the same field
    through pgl27_word_view_const. The statement rules out one named ideal and
    no certificate. An ideal can be pinned to these parameters through the
    dealer-dealt sample adapter psl211_dealt_sample of
    instances/psl211/psl211_colour_reading.v, and no certificate is built over
    it. The dealt parameters read their endpoints through profile_endpointsE, so
    instances/psl211/psl211_models.v carries an endpoints statement and an
    observed execution for them, and
    instances/psl211/tableau/psl211_tableau_dealt.v carries two programs and two
    paths over them. *)
```
replacement:
```
(** psl211_dealt_constancy_false — under the dealer-dealt run parameters the
    constancy field is false at the uniform law on the shuffle group, so no
    input-indistinguishability certificate over these parameters can take that
    law as its ideal cut, while a certificate at some other ideal stays open.
    The dealt run argument is the chirality and nothing else, so here the
    constancy field is exactly constancy in the secret, and it fails because
    the encoder decks of the two chiralities give one view of three seats
    different masses. That is a fact about the group and the design: PSL(2,11)
    is 2-transitive and not 3-transitive, where PGL(2,7) proves the same field
    through pgl27_word_view_const. The statement rules out one named ideal and
    no certificate. An ideal can be pinned to these parameters through the
    dealer-dealt sample adapter psl211_dealt_sample of
    instances/psl211/psl211_colour_reading.v, and no certificate is built over
    it. The dealt parameters read their endpoints through profile_endpointsE,
    so instances/psl211/psl211_models.v carries an endpoints statement and an
    observed execution for them, and
    instances/psl211/tableau/psl211_tableau_dealt.v carries two programs and
    two paths over them. *)
```
reason: one reading of three seats names one value the coalition sees

### instances/psl211/psl211_colour_reading.v

**V187** &nbsp; `instances/psl211/psl211_colour_reading.v:400-403`

current:
```
(** psl211_dealt_perdeck_readingE — the coalition's card-identity reading over
    this adapter is the card-identity reading of the sample point's two
    coordinates. One iota step of the reading record and two of the adapter
    record. *)
```
replacement:
```
(** psl211_dealt_perdeck_readingE — the coalition's card-identity endpoints
    over this adapter are the card-identity endpoints of the sample point's two
    coordinates. One iota step of the reading record and two of the adapter
    record. *)
```
reason: the coalition's card-identity reading names the random variable, while the reading record in the same sentence is the record

**V188** &nbsp; `instances/psl211/psl211_colour_reading.v:414-431`

current:
```
(** psl211_dealt_reading_indep_false — over the same model, the same adapter
    and at a coalition of three of the twelve positions, the coalition's
    card-identity reading is not independent of the dealt chirality, under
    every prior giving mass to both chiralities. Three is below the threshold
    of six, so this is a coalition psl211_colour_reading_indep covers: at one
    model and one coalition the proposition holds at the colour reading and
    fails at the card-identity one, so the colour reading's exact independence
    is not the image of the card-identity reading's, that one being false.
    What separates them is the card identity: the encoder decks of the two
    chiralities put one reading of three positions under exactly one cut and
    under none, which is psl211_dealt_raw_countE, while their colour patterns
    on five positions or fewer are equidistributed. It is the probabilistic
    form of psl211_dealt_constancy_false of
    instances/psl211/psl211_reading_constancy.v: the same coalition, the same
    fibers and the same two counts, a mass equality there and an independence
    here. It is stated of the model's law and the coalition's own endpoint
    reading, and it is why exact independence at the colour reading does not
    carry back to the endpoint reading. *)
```
replacement:
```
(** psl211_dealt_reading_indep_false — over the same model, the same adapter
    and at a coalition of three of the twelve positions, the coalition's
    card-identity reading is not independent of the dealt chirality, under
    every prior giving mass to both chiralities. Three is below the threshold
    of six, so this is a coalition psl211_colour_reading_indep covers: at one
    model and one coalition the proposition holds at the colour reading and
    fails at the card-identity one, so the colour reading's exact independence
    is not the image of the card-identity reading's, that one being false. What
    separates them is the card identity: the encoder decks of the two
    chiralities put one view of three positions under exactly one cut and under
    none, which is psl211_dealt_raw_countE, while their colour patterns on five
    positions or fewer are equidistributed. It is the probabilistic form of
    psl211_dealt_constancy_false of
    instances/psl211/psl211_reading_constancy.v: the same coalition, the same
    fibers and the same two counts, a mass equality there and an independence
    here. It is stated of the model's law and the coalition's own endpoint
    reading, and it is why exact independence at the colour reading does not
    carry back to the endpoint reading. *)
```
reason: one reading of three positions names one value; every other use in the paragraph is the record and stays

### instances/psl211/tableau/psl211_tableau_analysis_bridged.v

**V189** &nbsp; `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:225-228`

current:
```
(** The security property this program carries, at every real field and index,
    is exact independence: independence of the coalition's view from the
    chirality, and not a distance between two readings. The certify statement
    the program wrote settles which property that is. *)
```
replacement:
```
(** The security property this program carries, at every real field and index,
    is exact independence: independence of the coalition's view from the
    chirality, and not a distance between two laws. The certify statement the
    program wrote settles which property that is. *)
```
reason: a distance between two readings names two laws

**V190** &nbsp; `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:251-259`

current:
```
(** psl211_alldecks_view_secrecy — the program's view secrecy at this
    instance: at fewer than six colluding seats the executed coalition reading
    is independent of the chirality, carries zero mutual information with it,
    leaves the chirality's entropy unchanged under conditioning, and stays
    independent of it under every deterministic function of the seat-to-card
    map. The four conjuncts are the whole content of the exact-independence
    proposition here; the proof is the program's security projection applied, so
    a reader who wants the information-theoretic reading of the program needs no
    further derivation. *)
```
replacement:
```
(** psl211_alldecks_view_secrecy — the program's view secrecy at this
    instance: at fewer than six colluding seats the executed coalition view is
    independent of the chirality, carries zero mutual information with it,
    leaves the chirality's entropy unchanged under conditioning, and stays
    independent of it under every deterministic function of the seat-to-card
    map. The four conjuncts are the whole content of the exact-independence
    proposition here; the proof is the program's security projection applied,
    so a reader who wants the information-theoretic content of the program
    needs no further derivation. *)
```
reason: the executed coalition reading names the random variable and the information-theoretic reading names the content of the conclusion

**V191** &nbsp; `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:336-343`

current:
```
(** The carrier of that secret is the two-element type of the chirality bit.
    At a one-point carrier the ideal-proximity proposition compares two
    readings and mentions no secret at all, the second factor of the product
    being a point mass, so the number would bound nothing about what a
    coalition learns of the bit. The secret is also the one the protocol
    reconstructs: psl211_alldecks_secret_expectedE of
    instances/psl211/psl211_models.v reads it as the value the run recovers,
    at every sample point. *)
```
replacement:
```
(** The carrier of that secret is the two-element type of the chirality bit. At
    a one-point carrier the ideal-proximity proposition compares two laws and
    mentions no secret at all, the second factor of the product being a point
    mass, so the number would bound nothing about what a coalition learns of
    the bit. The secret is also the one the protocol reconstructs:
    psl211_alldecks_secret_expectedE of instances/psl211/psl211_models.v reads
    it as the value the run recovers, at every sample point. *)
```
reason: compares two readings names two laws

**V192** &nbsp; `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:379-397`

current:
```
(** The word model certified for ideal proximity and published at 2^-40, the
    number the certificate carries. What a static coalition of at most five of
    the twelve seats is shown is that the joint law of its reading with the
    chirality is within that number, in the sum of absolute differences, of the
    product of the two marginals the all-decks execution has, where the reading
    and the chirality are independent outright; a distinguisher's advantage is
    therefore at most 2^-41. The claim is an average over the deck description
    and the cut and is not a statement at a fixed deck description. That every
    coalition below the threshold reads an ideal cut by the same law at every
    run argument is false at each cut named here:
    psl211_alldecks_constancy_false refutes it at the group-uniform cut under
    the all-decks run, psl211_alldecks_constancy_false_word584 at every cut
    within eps of the 584-letter word law this program's model draws, once twice
    the sum of eps and 2^-40 stays below 1/660, and psl211_dealt_constancy_false
    at the group-uniform cut under the dealer-dealt run, a different execution.
    Each is witnessed at a coalition of three seats, and all three stay true
    beside this program. Its transfer status is IdealFinite: the cut is a
    shuffle of 584 letters where the model of psl211_alldecks_path draws it
    uniformly from the group. *)
```
replacement:
```
(** The word model certified for ideal proximity and published at 2^-40, the
    number the certificate carries. What a static coalition of at most five of
    the twelve seats is shown is that the joint law of its endpoints with the
    chirality is within that number, in the sum of absolute differences, of the
    product of the two marginals the all-decks execution has, where those
    endpoints and the chirality are independent outright; a distinguisher's
    advantage is therefore at most 2^-41. The claim is an average over the deck
    description and the cut and is not a statement at a fixed deck description.
    That every coalition below the threshold reads an ideal cut by the same law
    at every run argument is false at each cut named here:
    psl211_alldecks_constancy_false refutes it at the group-uniform cut under
    the all-decks run, psl211_alldecks_constancy_false_word584 at every cut
    within eps of the 584-letter word law this program's model draws, once
    twice the sum of eps and 2^-40 stays below 1/660, and
    psl211_dealt_constancy_false at the group-uniform cut under the
    dealer-dealt run, a different execution. Each is witnessed at a coalition
    of three seats, and all three stay true beside this program. Its transfer
    status is IdealFinite: the cut is a shuffle of 584 letters where the model
    of psl211_alldecks_path draws it uniformly from the group. *)
```
reason: its reading and the reading name the random variable

**V193** &nbsp; `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:404-406`

current:
```
(** The security property this program carries, at every real field and index,
    is ideal proximity: the distance to a private ideal model, and not the
    distance between two readings of one model. *)
```
replacement:
```
(** The security property this program carries, at every real field and index,
    is ideal proximity: the distance to a private ideal model, and not the
    distance between two laws of one model. *)
```
reason: two readings of one model names two laws

**V194** &nbsp; `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:443-449`

current:
```
(** The program's security statement at the twelve-card chirality instance: at a
    static coalition of at most five of the twelve seats, the joint law of the
    executed coalition reading and the chirality under the 584-letter word
    shuffle is within 2^-40, in the sum of absolute differences, of the product
    of the two marginals of the all-decks execution. The proof is the program's
    security projection applied, so the program and this statement are one
    theorem. *)
```
replacement:
```
(** The program's security statement at the twelve-card chirality instance: at
    a static coalition of at most five of the twelve seats, the joint law of
    the executed coalition view and the chirality under the 584-letter word
    shuffle is within 2^-40, in the sum of absolute differences, of the product
    of the two marginals of the all-decks execution. The proof is the program's
    security projection applied, so the program and this statement are one
    theorem. *)
```
reason: the executed coalition reading names the random variable

**V195** &nbsp; `instances/psl211/tableau/psl211_tableau_analysis_bridged.v:537-543`

current:
```
    Why it does not conflict with psl211_alldecks_published. The two are facts
    about one model under different quantifiers over the run argument. Exact
    independence is stated with the deck description drawn uniformly, and it
    says that a coalition of at most five of the twelve seats then learns
    nothing about the chirality, exactly. The obstruction fixes two run
    arguments and compares the readings at those two values. A second and
    separate fact is that the chirality reindexes the laid deck.
```
replacement:
```
    Why it does not conflict with psl211_alldecks_published. The two are facts
    about one model under different quantifiers over the run argument. Exact
    independence is stated with the deck description drawn uniformly, and it
    says that a coalition of at most five of the twelve seats then learns
    nothing about the chirality, exactly. The obstruction fixes two run
    arguments and compares what the coalition reads at those two values. A
    second and separate fact is that the chirality reindexes the laid deck.
```
reason: compares the readings at those two values names two laws

note: a paragraph inside a longer docstring: no opener and no closer

### instances/psl211/tableau/psl211_tableau_dealt.v

**V196** &nbsp; `instances/psl211/tableau/psl211_tableau_dealt.v:23-29`

current:
```
(* Because the run argument is the chirality here, the second program is a    *)
(* privacy statement at this model and not only a statement about two inputs: *)
(* the two run arguments it compares are the two values of the secret. That   *)
(* reading of it is particular to the dealer-dealt mode and does not          *)
(* generalise: at the all-decks mode of this instance, and at every instance  *)
(* whose run argument is a deck description, input distinguishability         *)
(* compares two inputs and says nothing about a secret.                       *)
```
replacement:
```
(* Because the run argument is the chirality here, the second program is a    *)
(* privacy statement at this model and not only a statement about two inputs: *)
(* the two run arguments it compares are the two values of the secret. That   *)
(* interpretation of it is particular to the dealer-dealt mode and does not   *)
(* generalise: at the all-decks mode of this instance, and at every instance  *)
(* whose run argument is a deck description, input distinguishability         *)
(* compares two inputs and says nothing about a secret.                       *)
```
reason: That reading of it names a way of taking the statement, not a CoalitionReading

### instances/psl211/tableau/psl211_tableau_executable.v

**V197** &nbsp; `instances/psl211/tableau/psl211_tableau_executable.v:71-79`

current:
```
(** The all-decks mode at the Executable level: the run argument is a deck
    description, the dealer lays that description as the twelve dealt cards,
    the value the run is meant to recover is the chirality bit of its
    argument, and the interpreter is given the instance's fuel of 220
    steps. No party commits an input, so the run carries no commit process,
    and the value it names is a reading of the run's own argument rather than
    an ideal function of anyone's input. Naming the parameters as a program
    is what lets the run facts of the level above be adjoined to a value
    rather than to a prefix spelled out again. *)
```
replacement:
```
(** The all-decks mode at the Executable level: the run argument is a deck
    description, the dealer lays that description as the twelve dealt cards,
    the value the run is meant to recover is the chirality bit of its argument,
    and the interpreter is given the instance's fuel of 220 steps. No party
    commits an input, so the run carries no commit process, and the value it
    names is read off the run's own argument rather than an ideal function of
    anyone's input. Naming the parameters as a program is what lets the run
    facts of the level above be adjoined to a value rather than to a prefix
    spelled out again. *)
```
reason: a reading of the run's own argument names the value recovered

### instances/s5/s5_models.v

**V198** &nbsp; `instances/s5/s5_models.v:186-190`

current:
```
(** s5_sample_coalition_viewE — the executed coalition endpoint reader
    sa_coalition_view s5_rand_sample 0 C equals the randomized sharing's
    coalition view rsh_view C. The identification lets
    s5_exec_coalition_secrecy below reuse the sharing-level secrecy
    result for the executed adapter's coalition reading. *)
```
replacement:
```
(** s5_sample_coalition_viewE — the executed coalition endpoint reader
    sa_coalition_view s5_rand_sample 0 C equals the randomized sharing's
    coalition view rsh_view C. The identification lets
    s5_exec_coalition_secrecy below reuse the sharing-level secrecy result for
    the executed adapter's coalition endpoints. *)
```
reason: the executed adapter's coalition reading names the random variable

**V199** &nbsp; `instances/s5/s5_models.v:203-208`

current:
```
(** s5_exec_coalition_secrecy — a coalition of fewer than five seats reads
    its executed endpoints with zero mutual information about the tape
    secret, and the same reading leaves the secret's conditional entropy
    equal to its entropy. This is the full-coalition strengthening of
    s5_exec_trace_secrecy: it holds for any proper subset of seats acting
    together, not only for a single seat. *)
```
replacement:
```
(** s5_exec_coalition_secrecy — a coalition of fewer than five seats reads
    its executed endpoints with zero mutual information about the tape secret,
    and the same endpoints leave the secret's conditional entropy equal to its
    entropy. This is the full-coalition strengthening of s5_exec_trace_secrecy:
    it holds for any proper subset of seats acting together, not only for a
    single seat. *)
```
reason: the same reading names the random variable just described

**V200** &nbsp; `instances/s5/s5_models.v:357-359`

current:
```
(* The executed seat reading is compared against the encoder-image ideal,    *)
(* not against uniform: the uniform-ideal statement is false for this        *)
(* plug's deterministic encoder.                                             *)
```
replacement:
```
(* The executed seat law is compared against the encoder-image ideal,         *)
(* not against uniform: the uniform-ideal statement is false for this         *)
(* plug's deterministic encoder.                                              *)
```
reason: The executed seat reading names the law sa_seat_dist compares

note: this box is padded to 76 and not to 80; only the first line changes

**V201** &nbsp; `instances/s5/s5_models.v:382-390`

current:
```
(** s5_exec_endpoint_bound — one seat's interpreter-executed reading,
    under the finite-word adapter, sits within sqrt 5 * alpha^L of the
    encoder-image ideal reading s5_ideal_reading, in variation distance
    under the repository's convention, the sum of absolute differences with
    no factor one half. This is s5_spectral_convergence_proved transported
    through the executed interpreter, so it rests on the in-kernel Rayleigh
    certificate s5_rayleigh_Q2_R. It bounds one seat's endpoint marginal
    only: the ideal reading is neither uniform nor secret-independent, and
    no coalition, privacy, secrecy, or leakage conclusion follows from it. *)
```
replacement:
```
(** s5_exec_endpoint_bound — one seat's interpreter-executed endpoint law,
    under the finite-word adapter, sits within sqrt 5 * alpha^L of the
    encoder-image ideal law s5_ideal_reading, in variation distance under the
    repository's convention, the sum of absolute differences with no factor one
    half. This is s5_spectral_convergence_proved transported through the
    executed interpreter, so it rests on the in-kernel Rayleigh certificate
    s5_rayleigh_Q2_R. It bounds one seat's endpoint marginal only: that ideal
    law is neither uniform nor secret-independent, and no coalition, privacy,
    secrecy, or leakage conclusion follows from it. *)
```
reason: interpreter-executed reading and ideal reading name two laws; the identifier s5_ideal_reading is kept as a token

### instances/s5/s5_analysis.v

**V202** &nbsp; `instances/s5/s5_analysis.v:197-199`

current:
```
(** ideal_reading — the encoder-image ideal reading: the content one seat
    reads when the dealt position is exactly uniform, mixed over the secret
    prior; neither uniform nor secret-independent. *)
```
replacement:
```
(** ideal_reading — the encoder-image ideal law: the content one seat reads
    when the dealt position is exactly uniform, mixed over the secret prior;
    neither uniform nor secret-independent. *)
```
reason: the encoder-image ideal reading names a law; the identifier is kept as a token

**V203** &nbsp; `instances/s5/s5_analysis.v:287-294`

current:
```
(** exec_endpoint_bound — executed endpoint marginal mixing, conditional on
    s5_rayleigh_Q2_R: the variation distance, in the repository's
    convention, the sum of absolute differences with no factor one half,
    between sa_seat_dist of the interpreter-executed finite-word adapter at
    one seat and the encoder-image ideal reading is at most sqrt 5 times
    alpha to the power L. One endpoint marginal; the ideal is neither
    uniform nor secret-independent; no coalition, privacy, secrecy or
    leakage conclusion is claimed. *)
```
replacement:
```
(** exec_endpoint_bound — executed endpoint marginal mixing, conditional
    on s5_rayleigh_Q2_R: the variation distance, in the repository's
    convention, the sum of absolute differences with no factor one half,
    between sa_seat_dist of the interpreter-executed finite-word adapter at
    one seat and the encoder-image ideal law is at most sqrt 5 times alpha
    to the power L. One endpoint marginal; the ideal is neither uniform nor
    secret-independent; no coalition, privacy, secrecy or leakage conclusion
    is claimed. *)
```
reason: the encoder-image ideal reading names a law

**V204** &nbsp; `instances/s5/s5_analysis.v:300-307`

current:
```
(* One status per analysis path. The deterministic path compares no model     *)
(* with an idealized one. The randomized path carries its executed observers  *)
(* back to the landed static results by the two reader equalities below, and  *)
(* compares no idealized model. The finite-word path carries an               *)
(* observer-level transfer theorem to the encoder-image ideal reading on the  *)
(* endpoint carrier 'I_5 (exec_endpoint_bound); its base-distribution         *)
(* premise on the cut carrier {perm 'I_5} remains absent, is named by         *)
(* word_missing_premise, and for the group-uniform ideal is unsatisfiable.    *)
```
replacement:
```
(* One status per analysis path. The deterministic path compares no model     *)
(* with an idealized one. The randomized path carries its executed observers  *)
(* back to the landed static results by the two reader equalities below, and  *)
(* compares no idealized model. The finite-word path carries an               *)
(* observer-level transfer theorem to the encoder-image ideal law on the      *)
(* endpoint carrier 'I_5 (exec_endpoint_bound); its base-distribution premise *)
(* on the cut carrier {perm 'I_5} remains absent, is named by                 *)
(* word_missing_premise, and for the group-uniform ideal is unsatisfiable.    *)
```
reason: the encoder-image ideal reading names a law

**V205** &nbsp; `instances/s5/s5_analysis.v:331-338`

current:
```
(** word_transfer_status — the finite-word path's transfer status,
    IdealFinite: this path carries the observer-level model-transfer theorem
    exec_endpoint_bound to the encoder-image ideal reading on the endpoint
    carrier 'I_5. That ideal is not the group-uniform ideal: the base
    premise word_missing_premise on the cut carrier {perm 'I_5} remains
    absent, and for the uniform distribution on the generated group is
    unsatisfiable at every delta below one by sign-coset confinement. No
    bound against group-uniform on any carrier is stated or implied. *)
```
replacement:
```
(** word_transfer_status — the finite-word path's transfer status,
    IdealFinite: this path carries the observer-level model-transfer theorem
    exec_endpoint_bound to the encoder-image ideal law on the endpoint
    carrier 'I_5. That ideal is not the group-uniform ideal: the base
    premise word_missing_premise on the cut carrier {perm 'I_5} remains
    absent, and for the uniform distribution on the generated group is
    unsatisfiable at every delta below one by sign-coset confinement. No
    bound against group-uniform on any carrier is stated or implied. *)
```
reason: the encoder-image ideal reading names a law

### instances/s5/s5_exec.v

**V206** &nbsp; `instances/s5/s5_exec.v:84-85`

current:
```
(*   s5_exec_coalition_endpointsE == a coalition's endpoint readings are the  *)
(*                          shares at the cut images of its seats             *)
```
replacement:
```
(*   s5_exec_coalition_endpointsE == a coalition's endpoints are the          *)
(*                          shares at the cut images of its seats             *)
```
reason: index block; endpoint readings names the values

**V207** &nbsp; `instances/s5/s5_exec.v:451-455`

current:
```
(** s5_exec_seat_endpointE — seat i's endpoint equals the direct computation
    at the cut image of seat i's start,
    s5_content_obs s (w0, tnth (pi_starts (mp_PI mpS)) i). This is the
    per-seat reading a single coalition member sees, before any coalition
    view is assembled. *)
```
replacement:
```
(** s5_exec_seat_endpointE — seat i's endpoint equals the direct computation
    at the cut image of seat i's start, s5_content_obs s (w0, tnth (pi_starts
    (mp_PI mpS)) i). This is the per-seat endpoint a single coalition member
    sees, before any coalition view is assembled. *)
```
reason: the per-seat reading names the value

**V208** &nbsp; `instances/s5/s5_exec.v:462-466`

current:
```
(** s5_exec_coalition_endpointsE — a coalition C's endpoint readings are the
    finfun sending each seat in C to the share of s at the cut image of that
    seat's start, and every seat outside C to ord0. This is the object a
    secrecy statement conditions on: what a coalition can read is exactly
    this finfun, nothing outside C. *)
```
replacement:
```
(** s5_exec_coalition_endpointsE — a coalition C's endpoints are the finfun
    sending each seat in C to the share of s at the cut image of that seat's
    start, and every seat outside C to ord0. This is the object a secrecy
    statement conditions on: what a coalition can read is exactly this finfun,
    nothing outside C. *)
```
reason: endpoint readings names the values

**V209** &nbsp; `instances/s5/s5_exec.v:899-904`

current:
```
(* Supplied is the framework's name for the mode this instance calls randomized:
   no party commits, the dealer lays the cards itself from the layout the run
   argument names, and the value the run recovers is a reading of that argument
   rather than a function of anyone's input. The three obligations below carry
   the mode word and the plug, the family and the program keep the instance's
   own word. *)
```
replacement:
```
(* Supplied is the framework's name for the mode this instance calls
   randomized: no party commits, the dealer lays the cards itself from the
   layout the run argument names, and the value the run recovers is read off
   that argument rather than computed from anyone's input. The three
   obligations below carry the mode word and the plug, the family and the
   program keep the instance's own word. *)
```
reason: a reading of that argument names the value recovered

### instances/s5/tableau/s5_tableau_sampled.v

**V210** &nbsp; `instances/s5/tableau/s5_tableau_sampled.v:6-12`

current:
```
(* The Sampled level adjoins a probability model to a run, and what it adds   *)
(* to run correctness is the identification of the two readings of a          *)
(* coalition: at every real field and every index of the family, the reader   *)
(* built from the interpreter's own endpoints is the one computed directly    *)
(* from the run argument and the cut. That identification is what turns a     *)
(* claim about the messages a run exchanges into a claim about a group        *)
(* action, and it is the last thing proved before the certify statement.      *)
```
replacement:
```
(* The Sampled level adjoins a probability model to a run, and what it adds   *)
(* to run correctness is the identification of the two computations of a      *)
(* coalition's endpoints: at every real field and every index of the family,  *)
(* the reader built from the interpreter's own endpoints is the one computed  *)
(* directly from the run argument and the cut. That identification is what    *)
(* turns a claim about the messages a run exchanges into a claim about a      *)
(* group action, and it is the last thing proved before the certify           *)
(* statement.                                                                 *)
```
reason: the two readings of a coalition names two computations of the endpoints

**V211** &nbsp; `instances/s5/tableau/s5_tableau_sampled.v:19-39`

current:
```
(* The instance's other model, the finite word over the four adjacent         *)
(* transpositions, is not named at this level. It is a model of the           *)
(* dealer-dealt run, and the manifest's path over it, s5_word_path, is        *)
(* justified by a mixing theorem and by no program: two of the five parts of  *)
(* an input-indistinguishability certificate over that model are out of       *)
(* reach. Missing is the distance from the walk to an ideal cut, a variation  *)
(* distance on the shuffle group that s5_word_base_premise names as a premise *)
(* nothing in the tree proves, the instance's spectral theorem bounding one   *)
(* seat's endpoint marginal on 'I_5 instead. Missing too, and for a reason no *)
(* proof can remove, is the constancy of a coalition's reading of the ideal   *)
(* cut in the secret, which the certificate's constancy field asks for at     *)
(* every coalition below the threshold and so at every singleton: under every *)
(* cut exactly one seat holds the card carrying the whole secret, so that     *)
(* seat's reading law moves with the secret, and no choice of ideal avoids    *)
(* it, the seat in question varying with the cut while the ideal is fixed     *)
(* before any coalition is named. What the manifest names for that path is an *)
(* endpoint marginal bound against the encoder-image ideal, with no claim     *)
(* about a coalition. That bound is stated here as s5_word_seat_marginal, a   *)
(* one-seat marginal bound of manifest/pgg_tableau_marginal_bounds.v: it      *)
(* mentions no coalition, no second run argument and no secret, and it is not *)
(* security evidence.                                                         *)
```
replacement:
```
(* The instance's other model, the finite word over the four adjacent         *)
(* transpositions, is not named at this level. It is a model of the           *)
(* dealer-dealt run, and the manifest's path over it, s5_word_path, is        *)
(* justified by a mixing theorem and by no program: two of the five parts of  *)
(* an input-indistinguishability certificate over that model are out of       *)
(* reach. Missing is the distance from the walk to an ideal cut, a variation  *)
(* distance on the shuffle group that s5_word_base_premise names as a premise *)
(* nothing in the tree proves, the instance's spectral theorem bounding one   *)
(* seat's endpoint marginal on 'I_5 instead. Missing too, and for a reason no *)
(* proof can remove, is the constancy in the secret of the law of what a      *)
(* coalition reads of the ideal cut, which the certificate's constancy field  *)
(* asks for at every coalition below the threshold and so at every singleton: *)
(* under every cut exactly one seat holds the card carrying the whole secret, *)
(* so that seat's law moves with the secret, and no choice of ideal avoids    *)
(* it, the seat in question varying with the cut while the ideal is fixed     *)
(* before any coalition is named. What the manifest names for that path is an *)
(* endpoint marginal bound against the encoder-image ideal, with no claim     *)
(* about a coalition. That bound is stated here as s5_word_seat_marginal, a   *)
(* one-seat marginal bound of manifest/pgg_tableau_marginal_bounds.v: it      *)
(* mentions no coalition, no second run argument and no secret, and it is not *)
(* security evidence.                                                         *)
```
reason: a coalition's reading of the ideal cut names the random variable and that seat's reading law names its law

### instances/s5/tableau/s5_tableau_analysis_bridged.v

**V212** &nbsp; `instances/s5/tableau/s5_tableau_analysis_bridged.v:6-12`

current:
```
(* The AnalysisBridged level adjoins one security payload per real field and  *)
(* per index of the model, and the proposition it carries is the one that     *)
(* payload proves, on top of everything the levels below proved. This is the  *)
(* level at which a program says something about a coalition, and which       *)
(* security property the evidence proves is what it says: the                 *)
(* exact-independence proposition asserts independence, and not a distance    *)
(* between two readings.                                                      *)
```
replacement:
```
(* The AnalysisBridged level adjoins one security payload per real field and  *)
(* per index of the model, and the proposition it carries is the one that     *)
(* payload proves, on top of everything the levels below proved. This is the  *)
(* level at which a program says something about a coalition, and which       *)
(* security property the evidence proves is what it says: the                 *)
(* exact-independence proposition asserts independence, and not a distance    *)
(* between two laws.                                                          *)
```
reason: a distance between two readings names two laws

**V213** &nbsp; `instances/s5/tableau/s5_tableau_analysis_bridged.v:97-97`

current:
```
(*     The instance-side reading of a coalition                               *)
```
replacement:
```
(*     The instance-side computation of a coalition's endpoints               *)
```
reason: banner; the instance-side reading names the computation

**V214** &nbsp; `instances/s5/tableau/s5_tableau_analysis_bridged.v:192-195`

current:
```
(** The security property this program carries, at every real field and index,
    is exact independence: independence of the coalition's view from the tape
    secret, and not a distance between two readings. The certify statement the
    program wrote settles which property that is. *)
```
replacement:
```
(** The security property this program carries, at every real field and index,
    is exact independence: independence of the coalition's view from the tape
    secret, and not a distance between two laws. The certify statement the
    program wrote settles which property that is. *)
```
reason: a distance between two readings names two laws

**V215** &nbsp; `instances/s5/tableau/s5_tableau_analysis_bridged.v:216-224`

current:
```
(** The randomized program's view secrecy at this instance: at fewer than five
    colluding seats the executed coalition view is independent of the tape
    secret, carries zero mutual information with it, leaves its entropy
    unchanged under conditioning, and stays independent of it under every
    deterministic function of the seat-to-card map. The four conjuncts are the
    whole content of the exact-independence proposition at this instance; the
    proof is the program's security projection applied, so a reader who wants
    the information-theoretic reading of the program needs no further
    derivation. *)
```
replacement:
```
(** The randomized program's view secrecy at this instance: at fewer than five
    colluding seats the executed coalition view is independent of the tape
    secret, carries zero mutual information with it, leaves its entropy
    unchanged under conditioning, and stays independent of it under every
    deterministic function of the seat-to-card map. The four conjuncts are the
    whole content of the exact-independence proposition at this instance; the
    proof is the program's security projection applied, so a reader who wants
    the information-theoretic content of the program needs no further
    derivation. *)
```
reason: the information-theoretic reading names the content of the conclusion

### instances/s5/tableau/s5_tableau_observed.v

**V216** &nbsp; `instances/s5/tableau/s5_tableau_observed.v:167-173`

current:
```
(** The supplied run of the five-seat instance: the algebra, the
    additive layout of a sampler tape at fuel 150, the value the run recovers
    written beside it, and the three run facts. The layout is supplied with
    the run argument and no party commits, so the value recovered is a
    reading of that argument rather than an ideal function of anyone's input;
    what has been proved at this point is run correctness and nothing about a
    coalition. *)
```
replacement:
```
(** The supplied run of the five-seat instance: the algebra, the additive
    layout of a sampler tape at fuel 150, the value the run recovers written
    beside it, and the three run facts. The layout is supplied with the run
    argument and no party commits, so the value recovered is read off that
    argument rather than an ideal function of anyone's input; what has been
    proved at this point is run correctness and nothing about a coalition. *)
```
reason: a reading of that argument names the value recovered

**V217** &nbsp; `instances/s5/tableau/s5_tableau_observed.v:235-241`

current:
```
(** The specification the supplied run realises: the tape's secret coordinate
    carried through the codec, tolerating coalitions of up to four seats. The
    record is written out rather than taken from a functionality statement,
    because a sharing family names no ideal function: the value recovered is
    a reading of the run's own argument and not a function of any committer's
    input, so there is nothing here a run could fail to meet. Only the
    tolerated size is read off the algebra. *)
```
replacement:
```
(** The specification the supplied run realises: the tape's secret coordinate
    carried through the codec, tolerating coalitions of up to four seats. The
    record is written out rather than taken from a functionality statement,
    because a sharing family names no ideal function: the value recovered is
    read off the run's own argument and not a function of any committer's
    input, so there is nothing here a run could fail to meet. Only the
    tolerated size is read off the algebra. *)
```
reason: a reading of the run's own argument names the value recovered

### manifest/pgg_analysis_manifest.v

**V218** &nbsp; `manifest/pgg_analysis_manifest.v:312-314`

current:
```
(*                          : {ffun 'I_5 -> 'I_5}, a coalition's reading of   *)
(*                            the endpoint card positions at one committed    *)
(*                            pair and one shuffle, with no execution |       *)
```
replacement:
```
(*                          : {ffun 'I_5 -> 'I_5}, a coalition's endpoint     *)
(*                            card positions at one committed pair and one    *)
(*                            shuffle, with no execution |                    *)
```
reason: a coalition's reading of the endpoint card positions names the value

note: table cell, edited line by line

**V219** &nbsp; `manifest/pgg_analysis_manifest.v:358-376`

current:
```
(* Level justification. single_biased_sample is the sample adapter with the   *)
(* same carrier and the same argument and cut maps as uniform_sample and with *)
(* Kim's biased distribution, and single_cut_distE identifies its cut         *)
(* distribution with the biased rotation, giving Sampled.                     *)
(* colour_view_leak_bound bounds a conditional mutual information of a joint  *)
(* distribution whose middle component is the executed reader colour_view     *)
(* itself, over that same biased distribution, giving AnalysisBridged.        *)
(* biased_cut_mixing bounds the distance of that cut distribution from the    *)
(* uniform rotation law on the cut carrier itself, and static_obs_const is    *)
(* the equality of two readings of that law, so both hypotheses of            *)
(* var_dist_fdistmap_transfer are discharged and the transfer status is       *)
(* IdealFinite rather than StaticExecutedOnly. The conclusion of that         *)
(* transfer is biased_static_obs_indistinguishability, a bound on the         *)
(* variation distance between the static readings of a coalition of at most   *)
(* one seat at two committed pairs. Its distribution is this path's cut law   *)
(* at bias one hundredth, by biased_sample_cut_witnessE, and its observer is  *)
(* static_obs, the second observer this path declares, so it reaches          *)
(* AnalysisBridged beside colour_view_leak_bound, which reaches it at the     *)
(* executed reader colour_view.                                               *)
```
replacement:
```
(* Level justification. single_biased_sample is the sample adapter with the   *)
(* same carrier and the same argument and cut maps as uniform_sample and with *)
(* Kim's biased distribution, and single_cut_distE identifies its cut         *)
(* distribution with the biased rotation, giving Sampled.                     *)
(* colour_view_leak_bound bounds a conditional mutual information of a joint  *)
(* distribution whose middle component is the executed reader colour_view     *)
(* itself, over that same biased distribution, giving AnalysisBridged.        *)
(* biased_cut_mixing bounds the distance of that cut distribution from the    *)
(* uniform rotation law on the cut carrier itself, and static_obs_const is    *)
(* the equality of the two laws that law gives at the two committed pairs, so *)
(* both hypotheses of var_dist_fdistmap_transfer are discharged and the       *)
(* transfer status is IdealFinite rather than StaticExecutedOnly. The         *)
(* conclusion of that transfer is biased_static_obs_indistinguishability, a   *)
(* bound on the variation distance between the laws of the static endpoints   *)
(* of a coalition of at most one seat at two committed pairs. Its             *)
(* distribution is this path's cut law at bias one hundredth, by              *)
(* biased_sample_cut_witnessE, and its observer is static_obs, the second     *)
(* observer this path declares, so it reaches AnalysisBridged beside          *)
(* colour_view_leak_bound, which reaches it at the executed reader            *)
(* colour_view.                                                               *)
```
reason: two readings of that law and the static readings name laws

**V220** &nbsp; `manifest/pgg_analysis_manifest.v:394-396`

current:
```
(*                          : {ffun 'I_5 -> 'I_5}, a coalition's reading of   *)
(*                            the endpoint card positions at one committed    *)
(*                            pair and one shuffle, with no execution;        *)
```
replacement:
```
(*                          : {ffun 'I_5 -> 'I_5}, a coalition's endpoint     *)
(*                            card positions at one committed pair and one    *)
(*                            shuffle, with no execution;                     *)
```
reason: a coalition's reading of the endpoint card positions names the value

note: table cell, edited line by line

**V221** &nbsp; `manifest/pgg_analysis_manifest.v:439-453`

current:
```
(* Level justification. Both models are sample adapters over the plug and     *)
(* both cut distributions are named, giving Sampled. centi_cut_mixing bounds  *)
(* the distance of the seven-cut distribution from the uniform rotation law   *)
(* on the cut carrier itself, and with static_obs_const it discharges both    *)
(* hypotheses of var_dist_fdistmap_transfer, giving IdealFinite. The          *)
(* conclusion of that transfer, centi_static_obs_indistinguishability, is a   *)
(* bound on the variation distance between the static readings of a coalition *)
(* of at most one seat at two committed pairs. Its distribution is this       *)
(* path's cut law, by centi_cut_distE, and its observer is static_obs, which  *)
(* the path declares, and that is what gives AnalysisBridged. endpoint_bound  *)
(* and deal_centi_lt stay named in the path for what they are: they bound the *)
(* distance from uniform of ONE seat's endpoint distribution, neither         *)
(* quantifies over a coalition and neither mentions a second secret. A        *)
(* ShuffleCertificateBundle exists for both models, and centi_cut_mixing is   *)
(* proved from the marginal bound that bundle carries.                        *)
```
replacement:
```
(* Level justification. Both models are sample adapters over the plug and     *)
(* both cut distributions are named, giving Sampled. centi_cut_mixing bounds  *)
(* the distance of the seven-cut distribution from the uniform rotation law   *)
(* on the cut carrier itself, and with static_obs_const it discharges both    *)
(* hypotheses of var_dist_fdistmap_transfer, giving IdealFinite. The          *)
(* conclusion of that transfer, centi_static_obs_indistinguishability, is a   *)
(* bound on the variation distance between the laws of the static endpoints   *)
(* of a coalition of at most one seat at two committed pairs. Its             *)
(* distribution is this path's cut law, by centi_cut_distE, and its observer  *)
(* is static_obs, which the path declares, and that is what gives             *)
(* AnalysisBridged. endpoint_bound and deal_centi_lt stay named in the path   *)
(* for what they are: they bound the distance from uniform of ONE seat's      *)
(* endpoint distribution, neither quantifies over a coalition and neither     *)
(* mentions a second secret. A ShuffleCertificateBundle exists for both       *)
(* models, and centi_cut_mixing is proved from the marginal bound that bundle *)
(* carries.                                                                   *)
```
reason: the static readings of a coalition names two laws

**V222** &nbsp; `manifest/pgg_analysis_manifest.v:582-582`

current:
```
(*                          'I_5), and one seat's executed reading            *)
```
replacement:
```
(*                          'I_5), and one seat's executed endpoint law       *)
```
reason: one seat's executed reading names a law

note: table cell, edited line by line

**V223** &nbsp; `manifest/pgg_analysis_manifest.v:598-598`

current:
```
(*                          transfers the executed reading to the             *)
```
replacement:
```
(*                          transfers the executed endpoint law to the        *)
```
reason: the executed reading names a law

note: table cell, edited line by line

**V224** &nbsp; `manifest/pgg_analysis_manifest.v:622-622`

current:
```
(*   | one seat's executed reading against the encoder-image ideal           *)
```
replacement:
```
(*   | one seat's executed endpoint law against the encoder-image ideal       *)
```
reason: one seat's executed reading names a law

note: table cell, edited line by line

**V225** &nbsp; `manifest/pgg_analysis_manifest.v:657-657`

current:
```
(*                          : {ffun 'I_12 -> 'I_12}, the reading of the laid  *)
```
replacement:
```
(*                          : {ffun 'I_12 -> 'I_12}, the view of the laid     *)
```
reason: the reading of the laid deck names the function static_view

note: table cell, edited line by line

**V226** &nbsp; `manifest/pgg_analysis_manifest.v:688-688`

current:
```
(*   | static_view, the coalition's reading of the laid deck                  *)
```
replacement:
```
(*   | static_view, the coalition's view of the laid deck                     *)
```
reason: the coalition's reading of the laid deck names static_view

note: table cell, edited line by line

**V227** &nbsp; `manifest/pgg_analysis_manifest.v:728-728`

current:
```
(*                        framework's reading of a coalition at this model    *)
```
replacement:
```
(*                        framework's endpoints of a coalition at this model  *)
```
reason: the framework's reading of a coalition names the computation

note: table cell, edited line by line

**V228** &nbsp; `manifest/pgg_analysis_manifest.v:757-772`

current:
```
(* Level justification. profile gives Algebraic; exec_plug is indexed by      *)
(* profile, giving Executable; observed is the ObservedExecution over that    *)
(* profile and plug, giving Observed; prior_sample is a SampleAdapter over    *)
(* that plug and pgl27_prior_viewE identifies the framework's reading of a    *)
(* coalition at its sample points with static_view, so the pushforward of     *)
(* this model's law along the framework's reader is the pushforward along     *)
(* static_view, giving Sampled; pgl27_view_indep_gen is a security theorem    *)
(* stated at this model's own law and at static_view, giving AnalysisBridged. *)
(* The privacy line quantifies over coalitions of at most three of the eight  *)
(* seats, the profile's own privacy threshold being four, and it holds at     *)
(* every law of the dealt secret, three-transitivity of the group saying      *)
(* nothing about how that secret is drawn. Path 1 records the same instance   *)
(* and the same cut at the uniform secret alone, its family being indexed by  *)
(* the unit type. The two paths agree in their other four coordinates and     *)
(* differ in the model family, and the member of this path's family at the    *)
(* uniform prior is the member of Path 1's at tt.                             *)
```
replacement:
```
(* Level justification. profile gives Algebraic; exec_plug is indexed by      *)
(* profile, giving Executable; observed is the ObservedExecution over that    *)
(* profile and plug, giving Observed; prior_sample is a SampleAdapter over    *)
(* that plug and pgl27_prior_viewE identifies the framework's endpoints of a  *)
(* coalition at its sample points with static_view, so the pushforward of     *)
(* this model's law along the framework's reader is the pushforward along     *)
(* static_view, giving Sampled; pgl27_view_indep_gen is a security theorem    *)
(* stated at this model's own law and at static_view, giving AnalysisBridged. *)
(* The privacy line quantifies over coalitions of at most three of the eight  *)
(* seats, the profile's own privacy threshold being four, and it holds at     *)
(* every law of the dealt secret, three-transitivity of the group saying      *)
(* nothing about how that secret is drawn. Path 1 records the same instance   *)
(* and the same cut at the uniform secret alone, its family being indexed by  *)
(* the unit type. The two paths agree in their other four coordinates and     *)
(* differ in the model family, and the member of this path's family at the    *)
(* uniform prior is the member of Path 1's at tt.                             *)
```
reason: the framework's reading of a coalition names the computation

**V229** &nbsp; `manifest/pgg_analysis_manifest.v:793-794`

current:
```
(*                          : {ffun 'I_12 -> 'I_12}, the reading the          *)
(*                            certificate's distance field is stated at;      *)
```
replacement:
```
(*                          : {ffun 'I_12 -> 'I_12}, the endpoints the        *)
(*                            certificate's distance field is stated at;      *)
```
reason: the reading the certificate's distance field is stated at names the values

note: table cell, edited line by line

**V230** &nbsp; `manifest/pgg_analysis_manifest.v:797-804`

current:
```
(* | distribution-to-observer bridges | psl211_word_sampleP_E and             *)
(*                        psl211_word_cut_distE of                            *)
(*                        instances/psl211/psl211_word_model.v, which name    *)
(*                        the adapter's own law and its cut law; the path's   *)
(*                        reading is the framework's own sa_coalition_view at *)
(*                        word_sample, which the adapter's projections make   *)
(*                        the all-decks reading, so no facade-level reading   *)
(*                        bridge is named |                                   *)
```
replacement:
```
(* | distribution-to-observer bridges | psl211_word_sampleP_E and             *)
(*                        psl211_word_cut_distE of                            *)
(*                        instances/psl211/psl211_word_model.v, which name    *)
(*                        the adapter's own law and its cut law; the path's   *)
(*                        observer is the framework's own sa_coalition_view   *)
(*                        at word_sample, which the adapter's projections     *)
(*                        make the all-decks view, so no facade-level bridge  *)
(*                        is named |                                          *)
```
reason: the path's reading, the all-decks reading and facade-level reading bridge name the random variable

note: table cell, edited line by line

**V231** &nbsp; `manifest/pgg_analysis_manifest.v:820-820`

current:
```
(*                          to the joint law of a coalition's reading with    *)
```
replacement:
```
(*                          to the joint law of a coalition's endpoints       *)
```
reason: a coalition's reading names the random variable

note: table cell, edited line by line

**V232** &nbsp; `manifest/pgg_analysis_manifest.v:884-884`

current:
```
(*                          : {ffun 'I_12 -> 'I_12}, the reading of the laid  *)
```
replacement:
```
(*                          : {ffun 'I_12 -> 'I_12}, the view of the laid     *)
```
reason: the reading of the laid deck names static_view

note: table cell, edited line by line

**V233** &nbsp; `manifest/pgg_analysis_manifest.v:925-943`

current:
```
(* Level justification. profile gives Algebraic; exec_plug is indexed by      *)
(* profile, giving Executable; observed is the ObservedExecution over that    *)
(* profile and plug, giving Observed; exact_sample is a SampleAdapter over    *)
(* that plug and cut_distE identifies its cut distribution with the uniform   *)
(* law on the shuffle group, giving Sampled; perdeck_reading_ge is a          *)
(* limitation theorem stated at that cut distribution and at the coalition's  *)
(* static reading of it, and AnalysisBridged admits a limitation theorem      *)
(* about the same distribution and the same observer, giving AnalysisBridged. *)
(* The transfer status is NegativeTransfer, which is defined as a theorem     *)
(* transporting an obstruction to the path's observer, and the theorem is     *)
(* that one. Path 9 records the same instance, the same execution and the     *)
(* same model, and this path differs from it in the transfer status alone.    *)
(* The two describe different theorems about one model: Path 9 the exact      *)
(* independence a coalition of at most five of the twelve seats has of the    *)
(* chirality when the deck description is drawn, and this path the distance   *)
(* between the readings of two named deck descriptions. The program that      *)
(* publishes this path is psl211_alldecks_obstruction_published of            *)
(* psl211_tableau_analysis_bridged.v in instances/psl211/tableau/, which      *)
(* certifies no security property.                                            *)
```
replacement:
```
(* Level justification. profile gives Algebraic; exec_plug is indexed by      *)
(* profile, giving Executable; observed is the ObservedExecution over that    *)
(* profile and plug, giving Observed; exact_sample is a SampleAdapter over    *)
(* that plug and cut_distE identifies its cut distribution with the uniform   *)
(* law on the shuffle group, giving Sampled; perdeck_reading_ge is a          *)
(* limitation theorem stated at that cut distribution and at the coalition's  *)
(* static endpoints under it, and AnalysisBridged admits a limitation theorem *)
(* about the same distribution and the same observer, giving AnalysisBridged. *)
(* The transfer status is NegativeTransfer, which is defined as a theorem     *)
(* transporting an obstruction to the path's observer, and the theorem is     *)
(* that one. Path 9 records the same instance, the same execution and the     *)
(* same model, and this path differs from it in the transfer status alone.    *)
(* The two describe different theorems about one model: Path 9 the exact      *)
(* independence a coalition of at most five of the twelve seats has of the    *)
(* chirality when the deck description is drawn, and this path the distance   *)
(* between the laws at two named deck descriptions. The program that          *)
(* publishes this path is psl211_alldecks_obstruction_published of            *)
(* psl211_tableau_analysis_bridged.v in instances/psl211/tableau/, which      *)
(* certifies no security property.                                            *)
```
reason: the coalition's static reading of it names the random variable and the readings of two named deck descriptions names two laws

**V234** &nbsp; `manifest/pgg_analysis_manifest.v:982-988`

current:
```
(* Five-card development. Section 7 of its facade carries the distance of     *)
(* each of Kim's two cut laws from the uniform rotation law on the cut        *)
(* carrier and the constancy of the reading of that law at every coalition of *)
(* at most one of the five seats, so paths 4 and 5 claim a cut-carrier        *)
(* transfer and name no absent premise. Path 3's own cut law is the uniform   *)
(* rotation, so that path has no finite model to compare with an ideal one    *)
(* and claims no transfer.                                                    *)
```
replacement:
```
(* Five-card development. Section 7 of its facade carries the distance of     *)
(* each of Kim's two cut laws from the uniform rotation law on the cut        *)
(* carrier and the constancy of the law of a coalition's endpoints under that *)
(* cut law, at every coalition of at most one of the five seats, so paths 4   *)
(* and 5 claim a cut-carrier transfer and name no absent premise. Path 3's    *)
(* own cut law is the uniform rotation, so that path has no finite model to   *)
(* compare with an ideal one and claims no transfer.                          *)
```
reason: the constancy of the reading of that law names the law of the endpoints

**V235** &nbsp; `manifest/pgg_analysis_manifest.v:990-1006`

current:
```
(* S_5 finite-word path (path 8). The absent premise is                       *)
(* S5Analysis.word_missing_premise, that is var_dist (sa_cut_dist             *)
(* (S5Analysis.word_sample secretP L)) Q <= delta on the cut carrier {perm    *)
(* 'I_5}, against a named reference distribution Q.                           *)
(* S5Analysis.word_endpoint_bound bounds a pushforward on the carrier 'I_5    *)
(* instead, and the executed transfer S5Analysis.exec_endpoint_bound compares *)
(* the executed reading with the encoder-image ideal, the content one seat    *)
(* reads when the dealt position is exactly uniform mixed over the secret     *)
(* prior, on the carrier 'I_5; neither discharges it. That ideal is not the   *)
(* group-uniform ideal. For Q the uniform distribution on the generated group *)
(* the premise is moreover UNSATISFIABLE at every delta below one: every      *)
(* generator of this instance is a transposition, so a word of length L       *)
(* evaluates into the coset of the alternating subgroup determined by the     *)
(* parity of L, and the sum of the absolute differences between the cut       *)
(* distribution and group uniform is at least one. That sign-coset            *)
(* confinement is not formalized at S_5, and no theorem of this repository    *)
(* asserts it there.                                                          *)
```
replacement:
```
(* S_5 finite-word path (path 8). The absent premise is                       *)
(* S5Analysis.word_missing_premise, that is var_dist (sa_cut_dist             *)
(* (S5Analysis.word_sample secretP L)) Q <= delta on the cut carrier {perm    *)
(* 'I_5}, against a named reference distribution Q.                           *)
(* S5Analysis.word_endpoint_bound bounds a pushforward on the carrier 'I_5    *)
(* instead, and the executed transfer S5Analysis.exec_endpoint_bound compares *)
(* the executed endpoint law with the encoder-image ideal, the content one    *)
(* seat reads when the dealt position is exactly uniform mixed over the       *)
(* secret prior, on the carrier 'I_5; neither discharges it. That ideal is    *)
(* not the group-uniform ideal. For Q the uniform distribution on the         *)
(* generated group the premise is moreover UNSATISFIABLE at every delta below *)
(* one: every generator of this instance is a transposition, so a word of     *)
(* length L evaluates into the coset of the alternating subgroup determined   *)
(* by the parity of L, and the sum of the absolute differences between the    *)
(* cut distribution and group uniform is at least one. That sign-coset        *)
(* confinement is not formalized at S_5, and no theorem of this repository    *)
(* asserts it there.                                                          *)
```
reason: the executed reading names a law

**V236** &nbsp; `manifest/pgg_analysis_manifest.v:1078-1092`

current:
```
(** The AnalysisPath for the same development under one biased cut at
    Kim's input distribution: FiveCardAnalysis.observed paired with the
    single-biased model family at bias one hundredth, AnalysisBridged,
    IdealFinite, BaselineClassicalOnly. colour_view_leak_bound bounds
    a conditional mutual information over that same biased distribution at
    the path's own executed reader colour_view, reaching AnalysisBridged. The
    ideal the transfer names is the uniform rotation law on the cut group,
    and its base premise is FiveCardAnalysis.biased_cut_mixing, the distance
    of this path's cut law from that ideal on the cut carrier itself, with
    FiveCardAnalysis.static_obs_const for the reading equality; those two
    give IdealFinite. Their transfer concludes
    FiveCardAnalysis.biased_static_obs_indistinguishability, the bound a
    coalition of at most one seat has on telling two committed pairs apart by
    what it reads, which is a second theorem reaching AnalysisBridged at this
    path. *)
```
replacement:
```
(** The AnalysisPath for the same development under one biased cut at Kim's
    input distribution: FiveCardAnalysis.observed paired with the
    single-biased model family at bias one hundredth, AnalysisBridged,
    IdealFinite, BaselineClassicalOnly. colour_view_leak_bound bounds a
    conditional mutual information over that same biased distribution at the
    path's own executed reader colour_view, reaching AnalysisBridged. The
    ideal the transfer names is the uniform rotation law on the cut group,
    and its base premise is FiveCardAnalysis.biased_cut_mixing, the distance
    of this path's cut law from that ideal on the cut carrier itself, with
    FiveCardAnalysis.static_obs_const for the equality of the two laws;
    those two give IdealFinite. Their transfer concludes
    FiveCardAnalysis.biased_static_obs_indistinguishability, the bound a
    coalition of at most one seat has on telling two committed pairs apart
    by what it reads, which is a second theorem reaching AnalysisBridged at
    this path. *)
```
reason: the reading equality names an equality of two laws

**V237** &nbsp; `manifest/pgg_analysis_manifest.v:1097-1111`

current:
```
(** The AnalysisPath for the same development under repeated biased
    cuts: FiveCardAnalysis.observed paired with the seven-cut model family
    at bias one hundredth, AnalysisBridged, IdealFinite,
    BaselineClassicalOnly. The ideal the transfer names is the uniform
    rotation law on the cut group, and its base premise is
    FiveCardAnalysis.centi_cut_mixing, the distance of this path's seven-cut
    law from that ideal on the cut carrier itself, with
    FiveCardAnalysis.static_obs_const for the reading equality; those two
    give IdealFinite. Their transfer concludes
    FiveCardAnalysis.centi_static_obs_indistinguishability, the bound a
    coalition of at most one seat has on telling two committed pairs apart by
    what it reads, and that conclusion is what reaches AnalysisBridged.
    endpoint_bound and deal_centi_lt are listed for this path as endpoint
    marginal bounds: each bounds one seat's endpoint distribution and neither
    quantifies over a coalition. *)
```
replacement:
```
(** The AnalysisPath for the same development under repeated biased cuts:
    FiveCardAnalysis.observed paired with the seven-cut model family at bias
    one hundredth, AnalysisBridged, IdealFinite, BaselineClassicalOnly. The
    ideal the transfer names is the uniform rotation law on the cut group,
    and its base premise is FiveCardAnalysis.centi_cut_mixing, the distance
    of this path's seven-cut law from that ideal on the cut carrier itself,
    with FiveCardAnalysis.static_obs_const for the equality of the two laws;
    those two give IdealFinite. Their transfer concludes
    FiveCardAnalysis.centi_static_obs_indistinguishability, the bound a
    coalition of at most one seat has on telling two committed pairs apart
    by what it reads, and that conclusion is what reaches AnalysisBridged.
    endpoint_bound and deal_centi_lt are listed for this path as endpoint
    marginal bounds: each bounds one seat's endpoint distribution and
    neither quantifies over a coalition. *)
```
reason: the reading equality names an equality of two laws

**V238** &nbsp; `manifest/pgg_analysis_manifest.v:1192-1202`

current:
```
(** The AnalysisPath for the twelve-card chirality instance under its
    all-decks dealer, recording the limitation that model carries rather than
    its exact independence: PSL211Analysis.observed paired with the
    unit-indexed exact-uniform family, AnalysisBridged, NegativeTransfer,
    BaselineClassicalOnly.  perdeck_reading_ge bounds from below the distance
    between the readings of two named deck descriptions under this path's own
    cut distribution and at this path's own observer, which is a limitation
    theorem there and so reaches AnalysisBridged; NegativeTransfer is defined
    as a theorem transporting an obstruction to the path's observer, and that
    theorem is this one. It differs from psl211_alldecks_path in the transfer
    status alone, the two being different theorems about one model. *)
```
replacement:
```
(** The AnalysisPath for the twelve-card chirality instance under its
    all-decks dealer, recording the limitation that model carries rather
    than its exact independence: PSL211Analysis.observed paired with the
    unit-indexed exact-uniform family, AnalysisBridged, NegativeTransfer,
    BaselineClassicalOnly. perdeck_reading_ge bounds from below the distance
    between the laws at two named deck descriptions under this path's own
    cut distribution and at this path's own observer, which is a limitation
    theorem there and so reaches AnalysisBridged; NegativeTransfer is
    defined as a theorem transporting an obstruction to the path's observer,
    and that theorem is this one.  It differs from psl211_alldecks_path in
    the transfer status alone, the two being different theorems about one
    model. *)
```
reason: the readings of two named deck descriptions names two laws

**V239** &nbsp; `manifest/pgg_analysis_manifest.v:2372-2374`

current:
```
(* The S_5 word path names an executed theorem alias, pinned here at its full *)
(* spelled type, the observer being sa_seat_dist of the interpreter-executed  *)
(* finite-word adapter and the ideal the encoder-image reading.               *)
```
replacement:
```
(* The S_5 word path names an executed theorem alias, pinned here at its full *)
(* spelled type, the observer being sa_seat_dist of the interpreter-executed  *)
(* finite-word adapter and the ideal the encoder-image law.                   *)
```
reason: the encoder-image reading names a law

### manifest/pgg_tableau_security_property_relations.v

**V240** &nbsp; `manifest/pgg_tableau_security_property_relations.v:26-29`

current:
```
(* What the two propositions share is a carrier. idealproximity_reading_le    *)
(* reads the proximity number as a bound between the two models' reading      *)
(* marginals, which is the carrier the input-indistinguishability proposition *)
(* states its own bound on.                                                   *)
```
replacement:
```
(* What the two propositions share is a carrier. idealproximity_reading_le    *)
(* reads the proximity number as a bound between the marginals of what the    *)
(* reading grants in the two models, which is the carrier the                 *)
(* input-indistinguishability proposition states its own bound on.            *)
```
reason: the two models' reading marginals names the marginals of what the reading grants

**V241** &nbsp; `manifest/pgg_tableau_security_property_relations.v:54-66`

current:
```
(* At a model that draws its run argument independently of its cut, an        *)
(* input-indistinguishability certificate does build ideal-proximity          *)
(* evidence over that same model, and the ideal-proximity proposition holds   *)
(* there at the certificate's marginal-bound epsilon once, where the          *)
(* input-indistinguishability proposition holds at that epsilon twice. The    *)
(* independence is a hypothesis on the model and not a theorem about it, and  *)
(* the comparison is an average over the prior on the run argument, at one    *)
(* run. The construction reads the run argument through a finite coordinate   *)
(* of the sample point, and the strength of the conclusion is the fineness    *)
(* of that coordinate. Two further hypotheses are carried, not proved: the    *)
(* run argument factors through that coordinate, and the model's executed     *)
(* coalition reading is its static one, which every program at Sampled        *)
(* holds. At a one-point carrier the statement is true and says nothing.      *)
```
replacement:
```
(* At a model that draws its run argument independently of its cut, an        *)
(* input-indistinguishability certificate does build ideal-proximity evidence *)
(* over that same model, and the ideal-proximity proposition holds there at   *)
(* the certificate's marginal-bound epsilon once, where the                   *)
(* input-indistinguishability proposition holds at that epsilon twice. The    *)
(* independence is a hypothesis on the model and not a theorem about it, and  *)
(* the comparison is an average over the prior on the run argument, at one    *)
(* run. The construction reads the run argument through a finite coordinate   *)
(* of the sample point, and the strength of the conclusion is the fineness of *)
(* that coordinate. Two further hypotheses are carried, not proved: the run   *)
(* argument factors through that coordinate, and the model's executed         *)
(* coalition view is its static one, which every program at Sampled holds. At *)
(* a one-point carrier the statement is true and says nothing.                *)
```
reason: the model's executed coalition reading names the random variable

**V242** &nbsp; `manifest/pgg_tableau_security_property_relations.v:109-110`

current:
```
(*   idealproximity_reading_le  == the proximity number bounds the distance   *)
(*                                 between the two models' reading marginals  *)
```
replacement:
```
(*   idealproximity_reading_le  == the proximity number bounds the distance   *)
(*                                 between the marginals of what the reading  *)
(*                                 grants in the two models                   *)
```
reason: index block; the two models' reading marginals names the marginals

note: the replacement is three lines where the current block is two

**V243** &nbsp; `manifest/pgg_tableau_security_property_relations.v:134-137`

current:
```
(*   var_dist_joint_reading_arg_le                                            *)
(*                              == the two models' joint laws of the reading  *)
(*                                 and the finite coordinate are no further   *)
(*                                 apart than the two cut laws                *)
```
replacement:
```
(*   var_dist_joint_reading_arg_le                                            *)
(*                              == the two models' joint laws of what the     *)
(*                                 reading grants and the finite coordinate   *)
(*                                 are no further apart than the two cut      *)
(*                                 laws                                       *)
```
reason: index block; joint laws of the reading names the joint laws of what it grants

note: the replacement is five lines where the current block is four

**V244** &nbsp; `manifest/pgg_tableau_security_property_relations.v:231-237`

current:
```
(** The proximity number bounds the distance between the two models' reading
    marginals, at every coalition below the threshold. The secret leaves the
    statement by data processing along the first projection, and the ideal's
    joint law is a product, so its first marginal is the ideal reading outright.
    This is the proximity number read on the carrier the
    input-indistinguishability proposition states its own bound on, and it needs
    no model of one proposition to be a model of the other. *)
```
replacement:
```
(** The proximity number bounds the distance between the marginals of what the
    reading grants in the two models, at every coalition below the threshold.
    The secret leaves the statement by data processing along the first
    projection, and the ideal's joint law is a product, so its first marginal
    is what the reading grants the ideal model outright. This is the proximity
    number read on the carrier the input-indistinguishability proposition
    states its own bound on, and it needs no model of one proposition to be a
    model of the other. *)
```
reason: reading marginals and the ideal reading name laws

**V245** &nbsp; `manifest/pgg_tableau_security_property_relations.v:501-502`

current:
```
(** The same fact in the form an exact witness asks for: below the threshold
    the ideal model's coalition reading is independent of its run argument. *)
```
replacement:
```
(** The same fact in the form an exact witness asks for: below the threshold
    the ideal model's static coalition endpoints are independent of its run
    argument. *)
```
reason: the ideal model's coalition reading names the random variable

**V246** &nbsp; `manifest/pgg_tableau_security_property_relations.v:544-549`

current:
```
(** The ideal model's secret is distributed as the finite coordinate arg_read
    takes off the actual model's sample point. The two sides of the
    ideal-proximity proposition therefore speak of one secret and not only of
    one carrier, and idealproximity_close_of_indistinguishability then bounds
    the distance between the two joint laws of that secret with a coalition's
    reading. *)
```
replacement:
```
(** The ideal model's secret is distributed as the finite coordinate arg_read
    takes off the actual model's sample point. The two sides of the
    ideal-proximity proposition therefore speak of one secret and not only of
    one carrier, and idealproximity_close_of_indistinguishability then bounds
    the distance between the two joint laws of that secret with a coalition's
    endpoints. *)
```
reason: a coalition's reading names the random variable

**V247** &nbsp; `manifest/pgg_tableau_security_property_relations.v:556-560`

current:
```
(** At every coalition the two models' joint laws of the reading and the
    finite coordinate are no further apart than the two cut laws. Both models
    draw that coordinate from one law and read one function of the pair, so
    the only quantity the two sides can differ in is the cut law. The
    threshold plays no part here. *)
```
replacement:
```
(** At every coalition the two models' joint laws of what the reading grants
    and the finite coordinate are no further apart than the two cut laws. Both
    models draw that coordinate from one law and read one function of the pair,
    so the only quantity the two sides can differ in is the cut law. The
    threshold plays no part here. *)
```
reason: joint laws of the reading names the joint laws of what it grants

**V248** &nbsp; `manifest/pgg_tableau_security_property_relations.v:622-630`

current:
```
(** The ideal-proximity proposition at that evidence, at the marginal-bound
    epsilon once. The premise instance_endpoints_stmt E identifies each
    model's executed coalition reading with the static one; every program at
    Sampled holds it, so a user inside a program has it and a user outside
    supplies it. The strength of the statement is the fineness of arg_read:
    at a one-point argT that coordinate is constant, the statement is true
    and it says nothing. var_dist is the sum of absolute differences,
    twice the literature's total variation distance, so a distinguisher's
    advantage is at most half the number. *)
```
replacement:
```
(** The ideal-proximity proposition at that evidence, at the marginal-bound
    epsilon once. The premise instance_endpoints_stmt E identifies each
    model's executed coalition view with the static one; every program at
    Sampled holds it, so a user inside a program has it and a user outside
    supplies it. The strength of the statement is the fineness of arg_read:
    at a one-point argT that coordinate is constant, the statement is true
    and it says nothing. var_dist is the sum of absolute differences, twice
    the literature's total variation distance, so a distinguisher's
    advantage is at most half the number. *)
```
reason: each model's executed coalition reading names the random variable

### protocol/pgg_functionality.v

**V249** &nbsp; `protocol/pgg_functionality.v:14-21`

current:
```
(* Correctness is available in two forms. realises is pointwise: at every     *)
(* run argument and every shuffle in the group, decoding the static endpoint  *)
(* reading returns the ideal function's value. realises_expected identifies   *)
(* the record's recovered value with the ideal function as terms, which       *)
(* conversion decides, so an instance whose expected value is written as the  *)
(* ideal function discharges it by reflexivity. The second implies the first  *)
(* and also transfers to the executed endpoints, so an instance proves the    *)
(* term identification alone.                                                 *)
```
replacement:
```
(* Correctness is available in two forms. realises is pointwise: at every run *)
(* argument and every shuffle in the group, decoding the static endpoints     *)
(* returns the ideal function's value. realises_expected identifies the       *)
(* record's recovered value with the ideal function as terms, which           *)
(* conversion decides, so an instance whose expected value is written as the  *)
(* ideal function discharges it by reflexivity. The second implies the first  *)
(* and also transfers to the executed endpoints, so an instance proves the    *)
(* term identification alone.                                                 *)
```
reason: the static endpoint reading names the values decoded

**V250** &nbsp; `protocol/pgg_functionality.v:117-121`

current:
```
(* The execution computes the functionality: at every run argument and every
   shuffle in the group, decoding the static endpoint reading returns fn_f F
   at that argument. The correctness half of a security claim, stated at the
   static group-action reading, which is where a coalition's view is also
   stated, so correctness and privacy speak about the same object. *)
```
replacement:
```
(* The execution computes the functionality: at every run argument and every
   shuffle in the group, decoding the static endpoints returns fn_f F at that
   argument. The correctness half of a security claim, stated at the static
   group-action observation, which is where a coalition's view is also stated,
   so correctness and privacy speak about the same object. *)
```
reason: the static endpoint reading and the static group-action reading name the values and the observation

### reconstruct/design_privacy.v

**V251** &nbsp; `reconstruct/design_privacy.v:84-88`

current:
```
(** uniform_fdistmap_fiberTE — two maps out of a finite type whose fibers over
    every value are equinumerous push the uniform law on the whole type to the
    same law.  It is uniform_fdistmap_fiberE at the full set, with the fibers
    written as comprehensions over the type, which is the shape a count of the
    deals producing one reading takes. *)
```
replacement:
```
(** uniform_fdistmap_fiberTE — two maps out of a finite type whose fibers
    over every value are equinumerous push the uniform law on the whole type to
    the same law.  It is uniform_fdistmap_fiberE at the full set, with the
    fibers written as comprehensions over the type, which is the shape a count
    of the deals producing one value takes. *)
```
reason: the deals producing one reading names a value of the map f

**V252** &nbsp; `reconstruct/design_privacy.v:284-284`

current:
```
(* the marginal count of the reading *)
```
replacement:
```
(* the marginal count of the value read *)
```
reason: the marginal count of the reading names the value of f

### reconstruct/gap_dimension.v

**V253** &nbsp; `reconstruct/gap_dimension.v:10-17`

current:
```
(* Framework reading (reconstruct/ag_massey_bridge.v): for the AG-Massey       *)
(* scheme on a length-n code of dimension D = k and genus g, ts_T = n-1 and    *)
(* ts_k = k-g. The section constraints g < k and k+g < n together with the     *)
(* gap bound n <= k+g+1 pin n = k+g+1, so a strict gap ts_k < ts_T equals 2g.  *)
(* This file isolates the resulting dimension window as reusable nat           *)
(* arithmetic; the invariant-submodule profiler's condition feasible          *)
(* intersects this band with the available invariant dimensions to reject     *)
(* mathematically impossible instances before any code is constructed.        *)
```
replacement:
```
(* Framework restatement (reconstruct/ag_massey_bridge.v): for the AG-Massey  *)
(* scheme on a length-n code of dimension D = k and genus g, ts_T = n-1 and   *)
(* ts_k = k-g. The section constraints g < k and k+g < n together with the    *)
(* gap bound n <= k+g+1 pin n = k+g+1, so a strict gap ts_k < ts_T equals 2g. *)
(* This file isolates the resulting dimension window as reusable nat          *)
(* arithmetic; the invariant-submodule profiler's condition feasible          *)
(* intersects this band with the available invariant dimensions to reject     *)
(* mathematically impossible instances before any code is constructed.        *)
```
reason: Framework reading labels a restatement in the framework's terms

note: only the first line changes; the rest is copied

### instances/kim2025/tableau/five_card_tableau_analysis_bridged.v

**V254** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:7-17`

current:
```
(* The AnalysisBridged level adjoins security evidence to a Sampled value at  *)
(* every real field and index, and the proposition it carries is the one that *)
(* evidence proves, on top of run correctness and of the identification of    *)
(* the two readings of a coalition. A publish terminal then turns the value   *)
(* into a Published. Every payload this instance gives a certify statement is *)
(* here, every program it publishes is here, and every statement whose        *)
(* subject is a payload or a program is here. Of the statements this          *)
(* directory makes, the one whose subject is neither a payload nor a program  *)
(* is Kim's input-privacy bound, which is in five_card_tableau_sampled.v; the *)
(* distance kim_biased_proximity_close is in                                  *)
(* instances/kim2025/five_card_proximity.v and is at no level.                *)
```
replacement:
```
(* The AnalysisBridged level adjoins security evidence to a Sampled value at  *)
(* every real field and index, and the proposition it carries is the one that *)
(* evidence proves, on top of run correctness and of the identification of    *)
(* the two computations of a coalition's endpoints. A publish terminal then   *)
(* turns the value into a Published. Every payload this instance gives a      *)
(* certify statement is here, every program it publishes is here, and every   *)
(* statement whose subject is a payload or a program is here. Of the          *)
(* statements this directory makes, the one whose subject is neither a        *)
(* payload nor a program is Kim's input-privacy bound, which is in            *)
(* five_card_tableau_sampled.v; the distance kim_biased_proximity_close is in *)
(* instances/kim2025/five_card_proximity.v and is at no level.                *)
```
reason: the two readings of a coalition names two computations of the endpoints

**V255** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:19-30`

current:
```
(* All three security properties are certified over the one committed run.    *)
(* Certifying exact independence takes an ExactWitness, whose one field is    *)
(* independence of a coalition's endpoints from the conjunction of the two    *)
(* committed bits; under the uniform rotation this is leak_view_set, the      *)
(* exact mutual information of a reveal pattern, at a pattern of at most one  *)
(* card, where that information is zero, and the witness carries no number.   *)
(* Certifying input indistinguishability takes a certificate comparing the    *)
(* readings of two committed pairs under one model, with the uniform rotation *)
(* law as the ideal cut. Certifying ideal proximity takes a certificate       *)
(* comparing one model with an ideal one at the same index, and the ideal it  *)
(* names here is the uniform model itself, whose own privacy is               *)
(* five_card_exact_view_secrecy.                                              *)
```
replacement:
```
(* All three security properties are certified over the one committed run.    *)
(* Certifying exact independence takes an ExactWitness, whose one field is    *)
(* independence of a coalition's endpoints from the conjunction of the two    *)
(* committed bits; under the uniform rotation this is leak_view_set, the      *)
(* exact mutual information of a reveal pattern, at a pattern of at most one  *)
(* card, where that information is zero, and the witness carries no number.   *)
(* Certifying input indistinguishability takes a certificate comparing the    *)
(* laws at two committed pairs under one model, with the uniform rotation law *)
(* as the ideal cut. Certifying ideal proximity takes a certificate comparing *)
(* one model with an ideal one at the same index, and the ideal it names here *)
(* is the uniform model itself, whose own privacy is                          *)
(* five_card_exact_view_secrecy.                                              *)
```
reason: the readings of two committed pairs names two laws

**V256** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:65-90`

current:
```
(* Seven programs are published, and the three the manifest carries for this  *)
(* instance are among them: five_card_uniform_published_pathE,                *)
(* five_card_repeated_indistinguishability_published_pathE and                *)
(* five_card_biased_indistinguishability_published_pathE discharge            *)
(* five_card_uniform_path, five_card_repeated_path and five_card_biased_path  *)
(* of pgg_analysis_manifest.v by conversion, and those three are all the      *)
(* AnalysisPaths the manifest carries over the five-card instance. Of the     *)
(* three, the repeated path is the one whose route the programs here share:   *)
(* the manifest reaches AnalysisBridged for it by the transfer whose base     *)
(* premise is kim_centi_cut_mixing, with five_card_static_obs_const for the   *)
(* reading equality, and kim_centi_cert carries those same two as fields. For *)
(* the one-cut path the manifest names two theorems reaching that level: the  *)
(* corresponding transfer, whose premises kim_biased_cert carries, and        *)
(* five_card_colour_view_leak_bound, a conditional mutual information no      *)
(* statement of certify takes and which is carried at Sampled. For the        *)
(* uniform path the manifest names five_card_exec_trace_secrecy at that       *)
(* path's own content trace, where the program's statement is                 *)
(* five_card_exact_view_secrecy, read off the published program by            *)
(* view_secrecy_of. Of the other four, three write a claim the manifest       *)
(* already carries a second way: the repeated program and the one-cut program *)
(* concluded at the constants a text quotes, and the one-cut program          *)
(* continued from its named Sampled value. The fourth is the proximity        *)
(* program, which publishes that same AnalysisPath for a different security   *)
(* property. A published program carries its own theorem, and an AnalysisPath *)
(* holds descriptive metadata and no Prop, so two programs publishing one     *)
(* AnalysisPath say nothing about each other's claim.                         *)
```
replacement:
```
(* Seven programs are published, and the three the manifest carries for this  *)
(* instance are among them: five_card_uniform_published_pathE,                *)
(* five_card_repeated_indistinguishability_published_pathE and                *)
(* five_card_biased_indistinguishability_published_pathE discharge            *)
(* five_card_uniform_path, five_card_repeated_path and five_card_biased_path  *)
(* of pgg_analysis_manifest.v by conversion, and those three are all the      *)
(* AnalysisPaths the manifest carries over the five-card instance. Of the     *)
(* three, the repeated path is the one whose route the programs here share:   *)
(* the manifest reaches AnalysisBridged for it by the transfer whose base     *)
(* premise is kim_centi_cut_mixing, with five_card_static_obs_const for the   *)
(* equality of the two laws, and kim_centi_cert carries those same two as     *)
(* fields. For the one-cut path the manifest names two theorems reaching that *)
(* level: the corresponding transfer, whose premises kim_biased_cert carries, *)
(* and five_card_colour_view_leak_bound, a conditional mutual information no  *)
(* statement of certify takes and which is carried at Sampled. For the        *)
(* uniform path the manifest names five_card_exec_trace_secrecy at that       *)
(* path's own content trace, where the program's statement is                 *)
(* five_card_exact_view_secrecy, read off the published program by            *)
(* view_secrecy_of. Of the other four, three write a claim the manifest       *)
(* already carries a second way: the repeated program and the one-cut program *)
(* concluded at the constants a text quotes, and the one-cut program          *)
(* continued from its named Sampled value. The fourth is the proximity        *)
(* program, which publishes that same AnalysisPath for a different security   *)
(* property. A published program carries its own theorem, and an AnalysisPath *)
(* holds descriptive metadata and no Prop, so two programs publishing one     *)
(* AnalysisPath say nothing about each other's claim.                         *)
```
reason: the reading equality names an equality of two laws

**V257** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:93-98`

current:
```
(* five_card_uniform_published, under The uniform program:                    *)
(*     five_card_uniform_published_sampledE,                                  *)
(*     five_card_uniform_published_pathE,                                     *)
(*     five_card_uniform_published_propertyE, and, under                      *)
(*     The exact-independence proposition's four conjuncts at this instance,  *)
(*     the reading five_card_exact_view_secrecy.                              *)
```
replacement:
```
(* five_card_uniform_published, under The uniform program:                    *)
(*     five_card_uniform_published_sampledE,                                  *)
(*     five_card_uniform_published_pathE,                                     *)
(*     five_card_uniform_published_propertyE, and, under                      *)
(*     The exact-independence proposition's four conjuncts at this instance,  *)
(*     the read-off statement five_card_exact_view_secrecy.                   *)
```
reason: the reading X names the theorem read off the published program

note: hanging-indent list, edited line by line

**V258** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:99-102`

current:
```
(* five_card_repeated_indistinguishability_published, under Kim's two         *)
(*     programs, certified against the uniform rotation law:                  *)
(*     five_card_repeated_indistinguishability_published_sampledE, _pathE,    *)
(*     _propertyE and _publishedE, and no reading of its own.                 *)
```
replacement:
```
(* five_card_repeated_indistinguishability_published, under Kim's two         *)
(*     programs, certified against the uniform rotation law:                  *)
(*     five_card_repeated_indistinguishability_published_sampledE, _pathE,    *)
(*     _propertyE and _publishedE, and no read-off statement of its own.      *)
```
reason: no reading of its own names the absence of such a theorem

**V259** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:103-105`

current:
```
(* five_card_biased_indistinguishability_published, under the same banner:    *)
(*     five_card_biased_indistinguishability_published_sampledE, _pathE,      *)
(*     _propertyE and _publishedE, and no reading of its own.                 *)
```
replacement:
```
(* five_card_biased_indistinguishability_published, under the same banner:    *)
(*     five_card_biased_indistinguishability_published_sampledE, _pathE,      *)
(*     _propertyE and _publishedE, and no read-off statement of its own.      *)
```
reason: no reading of its own names the absence of such a theorem

**V260** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:106-110`

current:
```
(* five_card_repeated_published39, under The same two programs at the         *)
(*     constants they publish: five_card_repeated_published39_sampledE,       *)
(*     five_card_repeated_published39_atE,                                    *)
(*     five_card_repeated_published39_propertyE, no _pathE of its own, and no *)
(*     reading of its own.                                                    *)
```
replacement:
```
(* five_card_repeated_published39, under The same two programs at the         *)
(*     constants they publish: five_card_repeated_published39_sampledE,       *)
(*     five_card_repeated_published39_atE,                                    *)
(*     five_card_repeated_published39_propertyE, no _pathE of its own, and    *)
(*     no read-off statement of its own.                                      *)
```
reason: no reading of its own names the absence of such a theorem

**V261** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:111-115`

current:
```
(* five_card_biased_published_inv25, under the same banner:                   *)
(*     five_card_biased_published_inv25_sampledE,                             *)
(*     five_card_biased_published_inv25_propertyE,                            *)
(*     five_card_biased_forms_pathE in place of a _pathE of its own, and no   *)
(*     reading of its own.                                                    *)
```
replacement:
```
(* five_card_biased_published_inv25, under the same banner:                   *)
(*     five_card_biased_published_inv25_sampledE,                             *)
(*     five_card_biased_published_inv25_propertyE,                            *)
(*     five_card_biased_forms_pathE in place of a _pathE of its own, and no   *)
(*     read-off statement of its own.                                         *)
```
reason: no reading of its own names the absence of such a theorem

**V262** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:116-119`

current:
```
(* five_card_biased_branch_indistinguishability_published, under One model,   *)
(*     two claims, two programs: written from five_card_biased_sampled, so no *)
(*     _sampledE, then _atE, _pathE and _propertyE, and no reading of its     *)
(*     own.                                                                   *)
```
replacement:
```
(* five_card_biased_branch_indistinguishability_published, under One model,   *)
(*     two claims, two programs: written from five_card_biased_sampled, so    *)
(*     no _sampledE, then _atE, _pathE and _propertyE, and no read-off        *)
(*     statement of its own.                                                  *)
```
reason: no reading of its own names the absence of such a theorem

**V263** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:120-125`

current:
```
(* five_card_biased_proximity_published, under the same banner: written from  *)
(*     five_card_biased_sampled, so no _sampledE,                             *)
(*     five_card_biased_proximity_published_pathE, _publishedE and            *)
(*     _propertyE, and, under What the proximity program states at this       *)
(*     instance, the readings five_card_biased_view_proximity and             *)
(*     five_card_biased_view_own_marginals.                                   *)
```
replacement:
```
(* five_card_biased_proximity_published, under the same banner: written       *)
(*     from five_card_biased_sampled, so no _sampledE,                        *)
(*     five_card_biased_proximity_published_pathE, _publishedE and            *)
(*     _propertyE, and, under What the proximity program states at this       *)
(*     instance, the read-off statements five_card_biased_view_proximity      *)
(*     and five_card_biased_view_own_marginals.                               *)
```
reason: the readings X and Y names the theorems read off the published program

**V264** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:191-193`

current:
```
(*   five_card_static_obsE   == the framework's direct computation of a       *)
(*                              coalition's endpoints is the instance's       *)
(*                              colour reading encoded                        *)
```
replacement:
```
(*   five_card_static_obsE   == the framework's direct computation of a       *)
(*                              coalition's endpoints is the instance's       *)
(*                              colour view encoded                           *)
```
reason: index block; the instance's colour reading names the random variable colour_view

**V265** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:374-374`

current:
```
(*     The instance-side reading of a coalition                               *)
```
replacement:
```
(*     The instance-side computation of a coalition's endpoints               *)
```
reason: banner; the instance-side reading names the computation

**V266** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:460-465`

current:
```
(** The same identification as five_card_static_obsE, with the committed pair
    and the cut left inside the sample point. The exact-independence proposition
    compares a coalition's endpoints with the secret on one probability space,
    so neither can be fixed first: the direct computation is a random variable
    of the sample point, and that random variable is the coalition's colour
    reading encoded. *)
```
replacement:
```
(** The same identification as five_card_static_obsE, with the committed pair
    and the cut left inside the sample point. The exact-independence
    proposition compares a coalition's endpoints with the secret on one
    probability space, so neither can be fixed first: the direct computation is
    a random variable of the sample point, and that random variable is the
    coalition's colour view encoded. *)
```
reason: the coalition's colour reading names the random variable colour_view

**V267** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:549-552`

current:
```
(** The security property this program carries, at every real field and index,
    is exact independence: independence of the coalition's view from the
    conjunction of the committed bits, and not a distance between two readings.
    The certify statement the program wrote settles which property that is. *)
```
replacement:
```
(** The security property this program carries, at every real field and index,
    is exact independence: independence of the coalition's view from the
    conjunction of the committed bits, and not a distance between two laws. The
    certify statement the program wrote settles which property that is. *)
```
reason: a distance between two readings names two laws

**V268** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:564-572`

current:
```
(** The program's view secrecy at this instance: at fewer than two colluding
    seats the executed coalition view is independent of the conjunction of the
    committed bits, carries zero mutual information with it, leaves its
    entropy unchanged under conditioning, and stays independent of it under
    every deterministic function of the seat-to-card map. The four conjuncts are
    the whole content of the exact-independence proposition at this instance;
    the proof is the program's security projection applied, so a reader who
    wants the information-theoretic reading of the program needs no further
    derivation. *)
```
replacement:
```
(** The program's view secrecy at this instance: at fewer than two colluding
    seats the executed coalition view is independent of the conjunction of the
    committed bits, carries zero mutual information with it, leaves its entropy
    unchanged under conditioning, and stays independent of it under every
    deterministic function of the seat-to-card map. The four conjuncts are the
    whole content of the exact-independence proposition at this instance; the
    proof is the program's security projection applied, so a reader who wants
    the information-theoretic content of the program needs no further
    derivation. *)
```
reason: the information-theoretic reading names the content of the conclusion

**V269** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:723-727`

current:
```
(** The security property this program carries, at every real field and index,
    is input indistinguishability: a variation distance between the readings of
    the cut at two committed pairs, and not independence of the view from the
    conjunction of the committed bits. The certify statement the program wrote
    settles which property that is. *)
```
replacement:
```
(** The security property this program carries, at every real field and index,
    is input indistinguishability: a variation distance between the laws the
    cut gives at two committed pairs, and not independence of the view from the
    conjunction of the committed bits. The certify statement the program wrote
    settles which property that is. *)
```
reason: the readings of the cut at two committed pairs names two laws

**V270** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:878-881`

current:
```
(** The repeated program concluded at 2^-39 and the program at the bundle's
    own number accumulate one stack, so the constant a text cites and the
    expression the certificate proved are two readings of one security claim
    and not two claims a reader must reconcile. *)
```
replacement:
```
(** The repeated program concluded at 2^-39 and the program at the bundle's own
    number accumulate one stack, so the constant a text cites and the
    expression the certificate proved are two forms of one security claim and
    not two claims a reader must reconcile. *)
```
reason: two readings of one security claim names two forms of it

**V271** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:1093-1102`

current:
```
(** Kim's one-cut model certified for ideal proximity and published at its
    certificate's own number, one fiftieth. What a coalition of fewer than two
    seats is shown is that the joint law of its reading with the conjunction of
    the committed bits is within that number of the product of the two marginals
    the den Boer uniform execution has, where the reading and the conjunction
    are independent outright. The proximity certificate's closeness field is one
    hop to the ideal, so that number is lost once, where the
    input-indistinguishability tail makes two hops. Its transfer status is
    IdealFinite, the same the input-indistinguishability program carries, and
    the two certificates compare against the same ideal cut. *)
```
replacement:
```
(** Kim's one-cut model certified for ideal proximity and published at its
    certificate's own number, one fiftieth. What a coalition of fewer than two
    seats is shown is that the joint law of its endpoints with the conjunction
    of the committed bits is within that number of the product of the two
    marginals the den Boer uniform execution has, where those endpoints and the
    conjunction are independent outright. The proximity certificate's closeness
    field is one hop to the ideal, so that number is lost once, where the
    input-indistinguishability tail makes two hops. Its transfer status is
    IdealFinite, the same the input-indistinguishability program carries, and
    the two certificates compare against the same ideal cut. *)
```
reason: its reading and the reading name the random variable

**V272** &nbsp; `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:1140-1142`

current:
```
(** The security property this program carries, at every real field and index,
    is ideal proximity: the distance to a private ideal model, and not the
    distance between two readings of one model. *)
```
replacement:
```
(** The security property this program carries, at every real field and index,
    is ideal proximity: the distance to a private ideal model, and not the
    distance between two laws of one model. *)
```
reason: two readings of one model names two laws

### manifest/pgg_tableau_syntax.v

**V273** &nbsp; `manifest/pgg_tableau_syntax.v:421-426`

current:
```
   expecting is the value the run recovers, a reading of the run argument
   rather than an ideal function of committed inputs, which is why the
   statement begins at an algebra and not at a Targeted. The sharing claim is
   not written here, so such a program discharges its reconstruction
   obligation through supplied_static_recon at its own algebra and validity
   lemma, or through the interpreter. *)
```
replacement:
```
   expecting is the value the run recovers, read off the run argument rather
   than an ideal function of committed inputs, which is why the statement
   begins at an algebra and not at a Targeted. The sharing claim is not
   written here, so such a program discharges its reconstruction obligation
   through supplied_static_recon at its own algebra and validity lemma, or
   through the interpreter. *)
```
reason: a reading of the run argument names the value recovered; the same sentence pattern is in four instance files

---

# Part 2. LEFT ALONE

Counts are of whole-word occurrences in comments. "changed" counts the
occurrences a Part 1 replacement removes; "left" is the rest, in the same file
and including the occurrences that a touched paragraph keeps.

| file | total | changed | left | the sense the remaining ones carry |
|---|---:|---:|---:|---|
| `groups/pgg_raag_clique.v` | 1 | 0 | 1 | one interpretation of a counting result; see unsure U5 |
| `groups/pgg_raag_path.v` | 3 | 0 | 3 | the ordinary gerund: reading a tuple at an index, reading a count as a count |
| `instances/denboer1989/five_card_leakage.v` | 2 | 0 | 2 | the ordinary gerund: reading a row at a set of positions |
| `instances/denboer1989/five_card_program.v` | 3 | 0 | 3 | the face value a card position shows; see unsure U6 |
| `instances/kim2025/five_card_analysis.v` | 7 | 6 | 1 | the ordinary gerund: a coalition reading the static endpoint colours |
| `instances/kim2025/five_card_exec.v` | 7 | 5 | 2 | the ordinary gerund: reading ord0 off a seat, reading a process identifier |
| `instances/kim2025/five_card_mixing.v` | 10 | 7 | 3 | the ordinary gerund: a coalition reading the static endpoints, reading one position |
| `instances/kim2025/five_card_models.v` | 1 | 0 | 1 | the ordinary gerund: reading a marginal off a distribution |
| `instances/kim2025/kim_input_privacy.v` | 1 | 0 | 1 | one interpretation of a cardinality; see unsure U1 |
| `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v` | 29 | 20 | 9 | the record: the reading a witness is indexed by, what that reading grants, the coalition's own endpoint reading; and one gerund |
| `instances/pgl27/pgl27_mixing.v` | 1 | 0 | 1 | the ordinary gerund: reading a key list at an index |
| `instances/pgl27/pgl27_profile_privacy.v` | 1 | 0 | 1 | the ordinary gerund: reading the secret off a card |
| `instances/pgl27/pgl27_proximity.v` | 21 | 20 | 1 | the ordinary gerund: the framework reading seat i at a start |
| `instances/pgl27/pgl27_run.v` | 1 | 0 | 1 | the ordinary gerund: a content readout reading the shares |
| `instances/pgl27/pgl27_secrecy.v` | 1 | 0 | 1 | one restatement of a dealer's marginal; see unsure U2 |
| `instances/pgl27/pgl27_spectral.v` | 1 | 0 | 1 | the ordinary gerund: using a shuffle without reading the tables |
| `instances/pgl27/pgl27_view_census.v` | 1 | 0 | 1 | the ordinary gerund: reading listed coordinates of a view |
| `instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v` | 40 | 25 | 15 | the record: at a reading, the coalition's own endpoint reading, a coarser reading, what that reading grants; and two gerunds |
| `instances/psl211/psl211_alldecks.v` | 58 | 57 | 1 | the ordinary gerund, in the heading "Reading one position of the layout" |
| `instances/psl211/psl211_alldecks_input_distinguishability.v` | 5 | 4 | 1 | the ordinary gerund: a coalition reading its own endpoints at two run arguments |
| `instances/psl211/psl211_colour_reading.v` | 62 | 3 | 59 | the record and two named readings, which this file introduces: `psl211_colour_reading`, the colour reading, the card-identity reading, the coalition's own endpoint reading |
| `instances/psl211/psl211_models.v` | 38 | 38 | 0 | — |
| `instances/psl211/psl211_reading_constancy.v` | 46 | 4 | 42 | the record: at that reading, a coarser reading, the coalition's own endpoint reading, the colour reading |
| `instances/psl211/psl211_secrecy.v` | 4 | 0 | 4 | three ordinary gerunds and one notation-scope sense; see unsure U3 |
| `instances/psl211/psl211_word_proximity.v` | 4 | 3 | 1 | the ordinary gerund: two adapters reading a sample point by the same projections |
| `instances/psl211/tableau/psl211_tableau_analysis_bridged.v` | 19 | 9 | 10 | the record: the reading a witness is indexed by, the coalition's own endpoint reading, a coarser reading |
| `instances/psl211/tableau/psl211_tableau_dealt.v` | 29 | 1 | 28 | the record and two named readings: the colour reading, the coalition's own endpoint reading, a reading as a coordinate of the security claim; one is unsure, U4 |
| `instances/psl211/tableau/psl211_tableau_executable.v` | 1 | 1 | 0 | — |
| `instances/psl211/tableau/psl211_tableau_sampled.v` | 1 | 0 | 1 | the record |
| `instances/s5/s5_analysis.v` | 4 | 4 | 0 | — |
| `instances/s5/s5_exec.v` | 4 | 4 | 0 | — |
| `instances/s5/s5_models.v` | 6 | 6 | 0 | — |
| `instances/s5/s5_run.v` | 2 | 0 | 2 | the ordinary gerund: a content readout reading the shares, reading a deck back |
| `instances/s5/s5_trace.v` | 1 | 0 | 1 | the ordinary gerund: reading an executed trace back |
| `instances/s5/tableau/s5_tableau_analysis_bridged.v` | 5 | 4 | 1 | the record: the reading the witness is indexed by |
| `instances/s5/tableau/s5_tableau_observed.v` | 3 | 2 | 1 | one sense of conversion; see unsure U7 |
| `instances/s5/tableau/s5_tableau_sampled.v` | 3 | 3 | 0 | — |
| `lib/fdist_prod_cst_cond.v` | 16 | 16 | 0 | — |
| `lib/mutual_info_recoding.v` | 1 | 0 | 1 | the ordinary gerund: reading a view at relabelled positions |
| `lib/proba_entropy_ext.v` | 2 | 0 | 2 | the ordinary gerund: reading a variable under a conditioned law |
| `lib/var_dist_supp.v` | 7 | 7 | 0 | — |
| `manifest/pgg_analysis_manifest.v` | 26 | 26 | 0 | — |
| `manifest/pgg_tableau.v` | 116 | 0 | 116 | the record throughout: `CoalitionReading`, `coalition_endpoint_reading`, `reading_of`, at a reading, what the reading grants, a coarser reading. The landing and its audit rewrote this file and the main session checked it again; nothing here names a value, a law or an act |
| `manifest/pgg_tableau_marginal_bounds.v` | 2 | 0 | 2 | the record once, and one gerund in the same sentence: a marginal bound is not a statement at a reading, the seat form reading one seat |
| `manifest/pgg_tableau_reading.v` | 43 | 0 | 43 | the record throughout: factorisation between two readings, a finer and a coarser one, `ReadingExactIndependence` |
| `manifest/pgg_tableau_security_property_relations.v` | 24 | 4 | 20 | the record: at a reading, what the reading grants a coalition, the coarsest reading, the coalition's own endpoint reading |
| `manifest/pgg_tableau_syntax.v` | 26 | 1 | 25 | the record and the surface: the term after `of` is the reading, the three certify rules that name a reading, an obstruction at a coarser reading |
| `protocol/pgg_functionality.v` | 3 | 3 | 0 | — |
| `reconstruct/design_privacy.v` | 2 | 2 | 0 | — |
| `reconstruct/gap_dimension.v` | 1 | 1 | 0 | — |
| `security/pgg_sample_adapter.v` | 5 | 4 | 1 | the ordinary gerund: the two maps reading a sample point as one run |
| `security/var_dist_joint_law.v` | 9 | 8 | 1 | the code's own binder, named in a proof comment: `var_dist_fdistmap at (reading, secret)`; see Part 3 item 1 |

Frozen files, not examined here and left out of the table: 51 occurrences across
`groups/pgg_raag.v`, `instances/psl211/psl211_blocks.v`, `psl211_closure.v`,
`psl211_endpoints.v`, `protocol/pgg_execution_plug.v`, `pgg_instance.v`,
`pgg_interface.v`, `pgg_observed_execution.v` and
`reconstruct/algebraic_rigidity.v`.

## Unsure

Seven occurrences I could not settle. Each reads naturally where it stands and
none of them can be taken for the record by a reader who knows what the sentence
is about, so I left them out of Part 1; each is a third sense of the word and an
owner may want them changed.

**U1** &nbsp; `instances/kim2025/kim_input_privacy.v:324-326` — "This combinatorial
reading is what kim_qctr_eq transports den_boer_view_count_eq's fibre-count
equality across." The word names one way of reading a cardinality. Nothing here
is a coalition or a function of endpoints.

**U2** &nbsp; `instances/pgl27/pgl27_secrecy.v:270` — "The uniform-over-valid-decks
reading of the dealer." The word names a restatement of a marginal. A dealer has
no reading in the record's sense, so it cannot be mistaken for one, but it is a
third sense.

**U3** &nbsp; `instances/psl211/psl211_secrecy.v:74` — "ring_scope is opened after it
so that the real-valued statements of the leak lemma keep their usual reading."
The word names how a notation resolves. Plainly not a coalition's reading.

**U4** &nbsp; `instances/psl211/tableau/psl211_tableau_dealt.v:135-139` — "It is what
carries a claim about a reading of the endpoints to a claim about an execution."
This could be the record, since the link lemma is stated at whatever reading the
program names, or it could be the static computation. I could not decide which
the author meant, and the two give different sentences.

**U5** &nbsp; `groups/pgg_raag_clique.v:1114` — "For the search-space reading this
means the choice between two graphs with the same clique polynomial leaves the
deck designer's trace counts equal." The word names an interpretation of a
counting result.

**U6** &nbsp; `instances/denboer1989/five_card_program.v:167, 172, 183` — "the
physical face reading of a card position", "fixes the identity card's face
reading once and for all", "the boolean reading fc_content discards". The word
names the face value a card shows. This is a physical-card sense, local to den
Boer's program file and consistent within it.

**U7** &nbsp; `instances/s5/tableau/s5_tableau_observed.v:254-256` — "is that
specification's function, as terms, on the same reading of conversion as the
dealer-dealt case." The word names a sense of conversion.

---

# Part 3. OTHER VOCABULARY RESIDUE

Report only. No rows proposed, and nothing below was checked against a compile.

**1. Identifiers that use `reading` for something that is not a
`CoalitionReading`.** A comment that names one of these is naming an identifier
and is not a site, so the Part 1 replacements keep the tokens; but the
identifiers themselves carry the collision, and several of the replacements read
oddly beside them.

- `security/var_dist_joint_law.v:75` — the binder `(reading : U -> V)` of
  `var_dist_fdistmap_pair`, an arbitrary map out of the sample space. The proof
  comment at `:80` names it. If the binder is renamed, that comment follows.
- `instances/kim2025/five_card_proximity.v:104` — `five_card_reading_secretE`,
  about the pair of `static_coalition_obs` and the secret.
- `instances/psl211/psl211_alldecks_input_distinguishability.v:157` —
  `psl211_alldecks_perdeck_reading_ge`, a lower bound on a distance between two
  laws; aliased in the manifest as `PSL211Analysis.perdeck_reading_ge` and named
  in the manifest's path prose.
- `instances/psl211/psl211_colour_reading.v:395` —
  `psl211_dealt_perdeck_reading`, whose type is `{RV ... -> {ffun seats ->
  cards}}`: a random variable, not a reading. `psl211_dealt_perdeck_readingE` and
  `psl211_dealt_reading_indep_false` inherit the fragment.
- `instances/s5/s5_analysis.v:200` — `ideal_reading`, and
  `instances/s5/s5_models.v` — `s5_ideal_reading`. Both are distributions. Five
  comment sites name them; V201, V202, V203, V205, V222, V223, V224 and V239
  leave the tokens and change only the common noun around them, so the sheet
  reads "the encoder-image ideal law `s5_ideal_reading`", which is honest but
  not comfortable.
- `manifest/pgg_tableau_security_property_relations.v` —
  `idealproximity_reading_le`, `ideal_prod_reading_arg_prodE`,
  `ideal_prod_reading_indep_arg`, `var_dist_joint_reading_arg_le`. These are
  about what the reading grants rather than about the reading, so the fragment
  is elliptical rather than wrong.

**2. A `var_dist` called a total-variation distance.** `var_dist` is the sum of
absolute differences, twice the literature's total variation distance, and the
tree says so in six places. `security/pgg_mixing.v` nonetheless calls its
`var_dist` bound a total-variation bound throughout: `:6`, `:37`, `:302`, `:423`,
`:442`, `:555`, `:619`, `:648`, `:650`, `:726`, and the identifier
`symm_ds_TV_bound`. `instances/pgl27/pgl27_mixing.v:13` does the same
("certifies its total-variation bound"), and `security/pgg_schreier.v:321` cites
Saloff-Coste's "sum-of-squares to TV conversion". A reader who takes those at
face value is off by a factor of two, in the conservative direction for a bound
and in the wrong one for a lower bound. `instances/kim2025/kim_input_privacy.v`
at `:236`, `:256`, `:378` and `:527` uses "total-variation" for a quantity that
is a plain sum of absolute deviations, which is the same mismatch.

**3. Economic words earlier passes missed.** The ban covers cost, spend, pay,
price, budget, buy, owe and currency.

- `manifest/pgg_tableau.v:1501` — "a path carrying either of them owes the
  manifest the premise it lacks", and `:1582` — "the manifest then owes that path
  the premise the payload stands for".
- `instances/psl211/psl211_colour_reading.v:246` — "where the instance's seat
  reconciliation is spent".
- `instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:884`,
  `instances/pgl27/tableau/pgl27_tableau_checks.v:131`, `:134`, `:135`,
  `instances/psl211/psl211_alldecks_input_distinguishability.v:175` and
  `instances/s5/s5_mixing.v:211` all use "costs" for elaboration time. These are
  measurements of seconds rather than metaphors, so whether the ban reaches them
  is the owner's call; "takes 147 s" says the same thing.

**4. "view" or "observation" used where a reading is meant.** None found. The
files that name a reading name it as a reading, and the files that name a view
name a random variable or an instance's own function. The manifest's "observer"
column stays the column word and is used for nothing else.

**5. `apex`, `gate`, `posit`, `arm`, `port`, and the letter-and-digit norm
abbreviation.** None found in any comment of any non-frozen file.
