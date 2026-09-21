# The fix pass over the audit of landing commit 2

Per finding: the file, the final line range and the final text, copied from the file after the pass.

## R1 and R29

`manifest/pgg_tableau_syntax.v:567-582`

```coq
(* The kind, the reading, the number, the proof and then the assumption
   status. The obstruction occupies the column the transfer status occupies
   in the other two publish rules, that coordinate being fixed at
   NegativeTransfer by the terminal, so a program's last statement reads in
   the order the manifest column headings run.

   The kind's name follows the literal Obstruction, the reading follows of
   and the number follows at, so the line says which kind is published, at
   which reading and at which number with no payload named elsewhere, and
   the proof is what the kind's proposition asks for at that number. When the
   reading named is the coalition's own endpoints, the finest, what the
   program publishes refutes certificates at that reading and leaves
   certificates at every coarser reading open; an obstruction at a coarser
   reading refutes certificates there and at every reading it factors
   through, the endpoint reading among them, which is
   input_distinguishability_prop_coalition_endpoint_reading. *)
```

## R29 (the rule that stays)

`manifest/pgg_tableau_syntax.v:583-588`

```coq
Notation "s |> 'publish' 'Obstruction' 'InputDistinguishability' 'of' r 'at' c 'by' pf 'assuming' a" :=
  (s ;;; publish_obstruction a
     of (mk_obstruction (tableau_at s)
           (input_distinguishability_obstruction (tableau_at s) r c) pf))
  (at level 90, left associativity, r at level 0, c at level 0,
   pf at level 0, a at level 0).
```

## R29 (the of paragraph of the header)

`manifest/pgg_tableau_syntax.v:108-114`

```coq
(* of introduces what is read. It follows the literal naming the security     *)
(* property in the three certify rules that name a reading, and the literal   *)
(* InputDistinguishability in the obstruction terminal; the term after it is  *)
(* the reading. It is also the word of the bind of pgg_tableau.v, following   *)
(* that rule's slot f, and it reserves nothing, being a keyword of Rocq       *)
(* independently of this file, measured on 2026-09-21 in the same way, so the *)
(* count stays twenty.                                                        *)
```

## R29 (the all-decks program)

`instances/psl211/tableau/psl211_tableau_analysis_bridged.v:557-562`

```coq
Definition psl211_alldecks_obstruction_published : PublishedObstruction :=
  psl211_exact_sampled
    |> publish Obstruction InputDistinguishability
       of (coalition_endpoint_reading psl211_algebra)
       at psl211_alldecks_number
       by psl211_alldecks_obstruction_pf assuming BaselineClassicalOnly.
```

## R2

`instances/psl211/psl211_reading_constancy.v:794-806`

```coq
(** psl211_alldecks_input_distinguishability — the all-decks model is input
    distinguishable at 1/660: the coalition and the pair of run arguments of
    psl211_alldecks_perdeck_reading_ge witness the existential the framework's
    proposition asks for. It is the quantitative negation of input
    indistinguishability at this model and it certifies no security property.
    What a coalition of at most five of the twelve seats learns about the
    chirality when the deck description is drawn is
    psl211_alldecks_static_indep, exactly nothing; the two facts stand under
    different quantifiers over the run argument, one drawing it and one fixing
    two of its values. The reading is the coalition's own endpoints, the finest,
    so this is the weakest of the distinguishability statements about the model:
    an obstruction at any coarser reading implies it, and the converse does not
    hold in general. *)
```

## R3

`manifest/pgg_tableau_security_property_relations.v:341-343`

```coq
(** The reading whose value type is unit at every coalition: a coalition is
    granted one value and reads it whatever the deal. It is the coarsest reading
    of all, factoring through every reading of this algebra. *)
```

## R4

`manifest/pgg_tableau_security_property_relations.v:347-356`

```coq
(** The exact witness at that reading, over an arbitrary model and at an
    arbitrary secret. Its independence field is inde_RV_cst read on the reading
    rather than on the secret, so it uses no property of the model and no
    property of the secret either. Holding exact-independence evidence is
    therefore by itself no statement about what a model hides: what a program
    says depends on the reading it certifies at as much as on the property it
    certifies, and this is the reading at which it says nothing. A program built
    on this witness publishes the same manifest path and carries the same
    security property as one built at the coalition's own endpoints, and
    reading_of is the only coordinate that separates the two. *)
```

## R5 (the header)

`instances/psl211/psl211_reading_constancy.v:72-79`

```coq
(* seats. The dealt statement rules out one named ideal and no certificate.   *)
(* An ideal can be pinned to these parameters through the dealer-dealt sample *)
(* adapter psl211_dealt_sample of instances/psl211/psl211_colour_reading.v,   *)
(* and no certificate is built over it. The dealt parameters read their       *)
(* endpoints through profile_endpointsE, so instances/psl211/psl211_models.v  *)
(* carries an endpoints statement and an observed execution for them, and     *)
(* instances/psl211/tableau/psl211_tableau_dealt.v carries two programs and   *)
(* two paths over them.                                                       *)
```

## R5 (the docstring)

`instances/psl211/psl211_reading_constancy.v:1057-1074`

```coq
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

## R6

`instances/psl211/psl211_colour_reading.v:187-187`

```coq
(*     The colour view as a reading of a coalition's endpoints                *)
```

## R7

`instances/psl211/psl211_colour_reading.v:190-196`

```coq
(** psl211_colour_of_reading — the colour map on a coalition's endpoints:
    send each position of the coalition to the colour, heart or club, of the
    card that position holds, and every position outside the coalition to
    false. It is the read function of psl211_colour_reading below, and it is
    a function of the coalition as well as of the endpoint map, because a
    coalition's endpoints give card zero outside the coalition and card zero
    is a heart. *)
```

## R8, R17 and R32 (the Definitions index)

`instances/psl211/psl211_colour_reading.v:39-42`

```coq
(*   psl211_colour_of_reading  == the colour map on a coalition's endpoints   *)
(*   psl211_colour_reading     == the colour of the card at each position of  *)
(*                                a coalition, as a reading of its endpoints  *)
(*   psl211_dealt_perdeck_reading                                             *)
```

## R32 and R17 (the Key results index)

`instances/psl211/psl211_colour_reading.v:54-60`

```coq
(*   psl211_colour_of_reading_obsE                                            *)
(*                             == a coalition's endpoints read through the    *)
(*                                colour map give its colour pattern          *)
(*   psl211_colour_readingE    == the model's colour view is the reading's    *)
(*                                value at that sample point                  *)
(*   psl211_colour_reading_funE                                               *)
(*                             == the same with the sample point left free    *)
```

## R9

`instances/psl211/psl211_colour_reading.v:279-289`

```coq
(** psl211_colour_indistinguishability_of_coalition_reading — the framework's
    post-processing law discharged at this pair of readings: an
    input-indistinguishability proposition at the coalition's card-identity
    reading gives the same number at the colour reading. The factorisation it
    consumes holds by conversion, psl211_colour_of_reading being the read
    function of the colour reading itself. That map is not injective, so this is
    the data processing inequality applied at a genuine coarsening and not at a
    renaming. It transports a bound and produces none. At zero the card-identity
    reading has no such proposition over this adapter, by
    psl211_dealt_constancy_false of instances/psl211/psl211_reading_constancy.v;
    at a positive number none is proved and none is refuted. *)
```

## R10 and R33

`instances/psl211/tableau/psl211_tableau_dealt.v:57-67`

```coq
(* Key results:                                                               *)
(*   psl211_dealt_sampled_viewE                                               *)
(*                          == the link lemma of the Sampled level, for both  *)
(*                             programs                                       *)
(*   psl211_colour_exact_published_readingE                                   *)
(*                          == the colour program's reading is the colour     *)
(*                             reading                                        *)
(*   psl211_colour_exact_published_propertyE                                  *)
(*                          == its security property is exact independence    *)
(*   psl211_colour_exact_published_pathE                                      *)
(*                          == the path it publishes                          *)
```

## R11 and R38

`instances/psl211/tableau/psl211_tableau_dealt.v:206-226`

```coq
(** psl211_dealt_input_distinguishable — the fixed-dealer model is input
    distinguishable at the coalition's own endpoint reading, at the reciprocal
    of the order of the shuffle group. The coalition is the three positions
    psl211_perdeck_coalition, below the threshold of six, and the two run
    arguments are the two chiralities, the dealer laying the cards from each:
    the encoder deck of one puts the three cards of psl211_dealt_view under
    exactly one cut and the other under none, so the two pushforwards of the
    uniform cut law differ at that reading by one cut's mass and the sum of
    absolute differences is at least that. Over these parameters the run
    argument is the chirality, so this is a privacy statement at this model, and
    that does not generalise to a mode whose run argument is a deck
    description. *)
Lemma psl211_dealt_input_distinguishable (R : realType)
    (secretP : R.-fdist bool) :
  InputDistinguishabilityPropAt (psl211_dealt_sample secretP)
    (coalition_endpoint_reading psl211_algebra)
    ((#|pgg_G psl211_M|%:R)^-1 : R).
Proof.
(* each mass is pinned in a statement naming one chirality, and the two are
   brought together afterwards: a rewrite with a mass lemma in a goal
   holding both chiralities searches a goal holding both deck tables *)
```

## R12

`instances/psl211/tableau/psl211_tableau_analysis_bridged.v:479-482`

```coq
(** psl211_alldecks_obstruction — the obstruction, at every real field and at
    the one index of the all-decks family: at the coalition's own endpoint
    reading the model is input distinguishable at 1/660, the reciprocal of
    the order of the shuffle group. *)
```

## R13

`instances/psl211/tableau/psl211_tableau_analysis_bridged.v:521-535`

```coq
    What it refutes, at the coalition's own endpoint reading. Every number at
    which an input-indistinguishability program over this model and that
    reading states its proposition is at least 1/660, whatever the
    certificate, by psl211_alldecks_indistinguishability_number_ge. Through
    the general form of the tail lemma,
    indistinguishability_prop_of_ideal_close, it also rules out every
    certificate at that reading whose ideal cut sits within eps of this
    model's own cut law once eps added to itself stays below 1/660, which is
    no_indistinguishability_cert_ideal_close_of_input_distinguishability at
    this model. A certificate at a coarser reading is bounded only through a
    factorisation, by indistinguishability_number_ge_across_readings. The
    tree's psl211_alldecks_no_small_eps_cert is the companion exclusion on
    the other coordinate: it constrains a certificate's own marginal bound
    rather than where its ideal sits, and it follows by the same route at
    the certificate's own number.
```

## R14

`instances/psl211/tableau/psl211_tableau_analysis_bridged.v:573-578`

```coq
(** psl211_alldecks_published_input_distinguishability — the program's reader
    gives the obstruction back, at every real field, and this is its second
    conjunct: at the coalition's own endpoint reading the all-decks model is
    input distinguishable at 1/660. The first conjunct is that 1/660 is above
    zero, which is what makes the second a comparison. The published value
    and this statement are one theorem. *)
```

## R15

`instances/psl211/psl211_reading_constancy.v:731-747`

```coq
(** psl211_alldecks_no_small_eps_cert — no input-indistinguishability
    certificate over the all-decks run of the twelve-card chirality instance has
    its shuffle bound epsilon added to itself strictly below the reciprocal
    1/660 of the group order, so every such certificate has an epsilon of at
    least 1/1320, the value 1/1320 itself not excluded. A program publishes
    odflt (cert_eps cert) (c R) at its own coordinate c, and cert_eps cert is
    the shuffle bound epsilon twice, so a program over this model that publishes
    its certificate's own number publishes at least 1/660. The obligation of
    conclude bounds the published number below by cert_eps cert, so no program
    over this model whose certificate is at that reading publishes less. This
    fixes from below what an input-indistinguishability program can publish at
    this model. It says neither that input indistinguishability is unavailable
    here nor anything about what a coalition of at most five seats reads. The
    certificate is at the coalition's own endpoint reading, the finest; what a
    certificate at a coarser reading may hold as its epsilon stays open, and the
    colour reading of instances/psl211/psl211_colour_reading.v is such a
    reading. *)
```

## R16 (the header prose)

`instances/psl211/psl211_reading_constancy.v:33-33`

```coq
(* The quantitative form fixes what an input-indistinguishability program     *)
```

## R16 (the second prose paragraph)

`instances/psl211/psl211_reading_constancy.v:49-49`

```coq
(* The same quantity read off the model rather than off a certificate. Under  *)
```

## R16 (the index)

`instances/psl211/psl211_reading_constancy.v:141-158`

```coq
(*   psl211_alldecks_no_small_eps_cert                                        *)
(*                           == no certificate over the all-decks model at    *)
(*                              the coalition's own endpoint reading carries  *)
(*                              a shuffle bound epsilon under 1/1320          *)
(*   psl211_alldecks_no_zero_eps_cert                                         *)
(*                           == in particular none carries an epsilon of      *)
(*                              zero, the epsilon of this instance's          *)
(*                              single-card marginal bound                    *)
(*   psl211_alldecks_input_distinguishability                                 *)
(*                           == the all-decks model is input distinguishable  *)
(*   psl211_alldecks_input_distinguishability                                 *)
(*                           == at the coalition's own endpoint reading the   *)
(*                              all-decks model is input distinguishable at   *)
(*                              1/660                                         *)
(*   psl211_alldecks_indistinguishability_number_ge                           *)
(*                           == every number an input-indistinguishability    *)
(*                              program over that model at that reading       *)
(*                              states is at least 1/660                      *)
```

## R17 and R31 and R40 (the Definitions index)

`manifest/pgg_tableau.v:129-151`

```coq
(* Definitions:                                                               *)
(*   CoalitionReading       == what a coalition is granted to read off its    *)
(*                             own endpoints                                  *)
(*   coalition_endpoint_reading                                               *)
(*                          == the identity at every coalition                *)
(*   ExactWitness           == the security witness for exact independence    *)
(*   IndistinguishabilityCert                                                 *)
(*                          == the security certificate for input             *)
(*                             indistinguishability                           *)
(*   IdealProximityCert     == the security certificate for ideal proximity   *)
(*   SecurityEvidence       == the evidence an instance certifies with        *)
(*   evidence_reading       == the reading the evidence is stated at          *)
(*   SecurityProperty       == which security property, with no witness or    *)
(*                             certificate                                    *)
(*   evidence_property      == the security property the evidence proves      *)
(*   StackAt                == the data a program holds at one completion     *)
(*                             level                                          *)
(*   ab_reading             == the reading the data at AnalysisBridged        *)
(*                             carries                                        *)
(*   ReadingIndistinguishabilityPropAt                                        *)
(*                          == the input-indistinguishability proposition of  *)
(*                             a reading, with no certificate in it           *)
(*   StackProp              == the proposition a program holds at one level   *)
```

## R18

`manifest/pgg_tableau_syntax.v:125-142`

```coq
(* The surface has two kinds of word. A preposition carries one meaning       *)
(* throughout: at a number, a size or a real field with its index, by a proof *)
(* or a piece of evidence, assuming an assumption status, and of what is      *)
(* read. The bind of manifest/pgg_tableau.v writes of ahead of a payload and  *)
(* is not one of these rules. A slot name names a thing, and the term that is *)
(* that thing follows it, at once or after a preposition: dealt, encoded and  *)
(* supplied name the mode a run is driven in, inputs the input carrier,       *)
(* layout the sharing the dealer deals, decoded_by the reader of the          *)
(* committed payload list, committed_by the commit processes, expecting the   *)
(* value a run recovers, fuel the number of steps the interpreter is allowed, *)
(* execute the run statement, terminates, endpoints and recon its three       *)
(* obligations, sample the model family, certify the security property, leaks *)
(* the coalition size of a tightness annotation, tied the equation between    *)
(* the bound's law and the model's cut law, ideal the ideal cut, mixing the   *)
(* distance from it, invariant the constancy of a coalition's view,           *)
(* functionality the ideal function, conclude the number a program publishes, *)
(* and publish what a program hands over, a transfer status in one rule, a    *)
(* completion level in two and the published object in the fourth.            *)
```

## R20

`manifest/pgg_tableau_reading.v:12-21`

```coq
(* One reading factors through another when a coalitionwise map sends what    *)
(* the finer grants to what the coarser grants. Along such a map the two      *)
(* distance properties travel in opposite directions, and saying which is     *)
(* most of what the file holds. An input-indistinguishability bound travels   *)
(* from the finer reading to the coarser one, which is the data processing    *)
(* inequality: granting a coalition less cannot separate two run arguments    *)
(* further. Input DISTINGUISHABILITY travels the other way, from the coarser  *)
(* to the finer: a coalition granted more still tells the two arguments       *)
(* apart. The coalition's own endpoints are the finest reading of all, every  *)
(* reading factoring through them, so every obstruction is an obstruction     *)
```

## R21 (the index)

`manifest/pgg_tableau_reading.v:55-58`

```coq
(*   indistinguishability_number_ge_across_readings                           *)
(*                              == an obstruction at a reading bounds from    *)
(*                                 below the number of a certificate at a     *)
(*                                 finer one                                  *)
```

## R21 (the docstring)

`manifest/pgg_tableau_reading.v:202-205`

```coq
(* An obstruction at one reading bounds from below the number of a
   certificate at a reading the first factors through. The number bound of
   the framework is this one at a single reading. A bound across two
   readings needs the factorisation and is this lemma, not that one. *)
```

## R22

`manifest/pgg_tableau.v:1455-1459`

```coq
(* The reading a published program's claim is made at, at one real field and
   one index of its family. It is the observer coordinate of the manifest's
   description of a capability, which the path itself does not carry: two
   programs over one model and one pair of statuses are one manifest path, and
   the security property and the reading are where they differ. *)
```

## R23 (IdealProximityCert)

`manifest/pgg_tableau.v:409-423`

```coq
(* The proximity certificate at a reading: a second sample adapter over the
   program's own execution, standing for the ideal run; an exact witness for
   that ideal at the same reading, which is what makes the ideal a model whose
   own privacy is proved and not a bare law; the actual model's secret, typed
   at the carrier the ideal's witness names, so that the two models speak of
   one secret; a number; and, at every coalition below the privacy threshold,
   that number as a bound on the variation distance between the two models'
   joint laws of what the reading grants the coalition and the secret. One
   reading serves both models, so the number measures the distance between two
   models and not between two readings. The comparison is an average over the
   run argument of each model and not a statement at a fixed run argument, and
   the number is an upper bound the instance chooses on what the actual model
   loses against an execution that leaks nothing, not a quantity the record
   determines: any number at which ipc_close is provable is a legal field, so
   a certificate says as much as its number is small and no more. *)
```

## R23, R24 and R25 (ObstructionKind)

`manifest/pgg_tableau.v:1721-1738`

```coq
(* The obstructions a program may publish at one model, one constructor each.
   A constructor of SecurityEvidence names a security property a program
   certifies; a constructor here names a fact about the model from which no
   security property follows, so the two enumerations are disjoint in kind and
   this one leaves SecurityEvidence with its three members. It is a closed
   enumeration and not a free proposition: a free proposition is what restate
   hands over, and a reader of a free payload cannot tell what kind of fact
   was published. The one member carries the reading the model is
   distinguishable at and the number it is distinguishable at, the reading
   standing to an obstruction as it stands to security evidence, so
   security_property_of and reading_of answer the same question of a negative
   result and of a positive one. The proposition that member stands for
   requires the number positive. At a number at or below zero the inequality
   is free, var_dist being non-negative, and the empty coalition is below
   every threshold, so the distinguishability proposition alone would hold at
   every model whose run-argument type is inhabited. Positivity is what makes
   a published member a comparison of what the reading grants at two run
   arguments. *)
```

## R26

`manifest/pgg_tableau.v:1967-1972`

```coq
Lemma certify_exact_readingE (x : StackAt Sampled) (q : StackProp Sampled x)
    (p : ExactPayload x) (R : realType)
    (idx : amf_index (ab_f (tableau_at (@certify_exact x q p))) R) :
  ab_reading (tableau_at (@certify_exact x q p)) R idx
  = coalition_endpoint_reading (projT1 x).
Proof. exact: erefl. Qed.
```

## R27

`instances/psl211/psl211_models.v:357-362`

```coq
(** psl211_dealt_endpoints — the interpreter's messages of the dealer-dealt
    run compute the direct computation of the laid deck. It is the twin of
    psl211_alldecks_endpoints over the other mode a run of this instance is
    driven in: the profile's abstract-readout equation quantifies over the
    content readout, so one equation serves both modes and neither needs a
    reduction of its own. *)
```

## R28

`instances/psl211/tableau/psl211_tableau_dealt.v:31-31`

```coq
(* The two programs share every line up to the Sampled level, and they must:  *)
```

## R30 (s5, the witness)

`instances/s5/tableau/s5_tableau_analysis_bridged.v:147-156`

```coq
(** The exact-independence witness: the tape secret as a random variable on the
    tape space, and, at every coalition of fewer than five seats, the
    independence from it of the whole of that coalition's endpoints, which is
    the reading this witness is indexed by. The independence is exact, four
    additive shares of a uniform tape carrying no information about the secret
    at all rather than a small amount, and it is exact for a reason no shuffle
    takes part in. The framework derives the zero mutual information, the
    unchanged conditional entropy and the closure under post-processing from
    this one field, so the witness is all that certifying exact independence
    requires of this instance. *)
```

## R30 (s5, the header prose)

`instances/s5/tableau/s5_tableau_analysis_bridged.v:24-29`

```coq
(* The mathematics reaches the program through one payload and two facts. The *)
(* payload is the exact witness. The first fact identifies the framework's    *)
(* direct computation of a coalition's endpoints with the additive sharing's  *)
(* own, which holds because this model draws the identity cut. The second is  *)
(* s5_exec_coalition_secrecy, the sharing's privacy at a uniform tape, read   *)
(* from zero mutual information back to independence. No other security       *)
```

## R30 (s5, the index)

`instances/s5/tableau/s5_tableau_analysis_bridged.v:52-54`

```coq
(*   s5_rand_static_obsE  == the framework's direct computation of a          *)
(*                           coalition's endpoints is the one the additive    *)
(*                           sharing makes                                    *)
```

## R30 (kim, the witness)

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:492-501`

```coq
(** The exact-independence witness: the conjunction of the two committed bits as
    a random variable on the uniform sample space, and, at every coalition of
    fewer than two seats, the independence from it of the whole of that
    coalition's endpoints, which is the reading this witness is indexed by. The
    independence is exact, the uniform rotation making what that reading grants
    carry no information about the conjunction at all rather than a small
    amount. The framework derives the zero mutual information, the unchanged
    conditional entropy and the closure under post-processing from this one
    field, so the witness is all that certifying exact independence requires of
    this instance. *)
```

## R30 (kim, kim_centi_cert)

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:622-630`

```coq
(** The input-indistinguishability certificate of the repeated certified
    program, at the coalition's own endpoint reading. Its five fields are the
    seven-cut bundle's marginal bound; the identification of that bound's law
    with the law the repeated adapter draws its cut from; the uniform rotation
    law as the ideal cut; the distance of the seven-cut law from that ideal; and
    the constancy, at every coalition of at most one seat, of what that reading
    grants of the ideal cut in the committed pair. The only inexact quantity in
    the program is the bundle's spectral number; the ideal cut and the constancy
    field are exact. *)
```

## R30 (kim, kim_biased_cert)

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:643-648`

```coq
(** The input-indistinguishability certificate of the one-cut certified program,
    at the coalition's own endpoint reading, with the same five fields at word
    length one. The ideal cut and the constancy, at every coalition of at most
    one seat, of what that reading grants of it are the same two terms as in the
    repeated certified program's certificate, so the two programs differ only in
    the shuffle and its number. *)
```

## R30 (kim, kim_biased_cert_exact)

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:902-903`

```coq
(** The one-cut program's certificate at the coalition's own endpoint reading
    and at the exact number one fiftieth. *)
```

## R30 (kim, kim_biased_proximity_cert)

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:985-996`

```coq
(** The proximity certificate of Kim's one-cut program, at the coalition's own
    endpoint reading. Its five fields are the den Boer uniform model as the
    ideal; that model's exact witness, which is what makes the ideal an
    execution whose coalitions learn nothing at all; the conjunction of the
    committed bits as the one-cut model's own secret; one fiftieth; and the
    distance above. The ideal and the witness are the terms the published
    uniform program carries, which kim_biased_proximity_cert_idealE states, and
    the secret is the same conjunction that program's witness is stated at. The
    number is the bound kim_biased_cut_mixing_exact proves on the cut group's
    own distance, and the last field is kim_biased_proximity_close of
    five_card_proximity.v, which says the distance between the two joint laws is
    at most that number. *)
```

## R30 (kim, the identification)

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:460-465`

```coq
(** The same identification as five_card_static_obsE, with the committed pair
    and the cut left inside the sample point. The exact-independence proposition
    compares a coalition's endpoints with the secret on one probability space,
    so neither can be fixed first: the direct computation is a random variable
    of the sample point, and that random variable is the coalition's colour
    reading encoded. *)
```

## R30 (kim, the proximity statement)

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:1155-1160`

```coq
(** The proximity program's security statement at the five-card instance: at
    fewer than two colluding seats, the joint law of what the coalition is
    granted of the executed run and the conjunction of the committed bits under
    Kim's one biased cut is within one fiftieth of the product of the two
    marginals of the den Boer uniform execution. The proof is the program's
    security projection applied, so the program and this statement are one
```

## R30 (kim, the own-marginals statement)

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:1178-1185`

```coq
(** The one-cut program's bound restated against the executed law's own two
    marginals: at fewer than two colluding seats, the joint law of a coalition's
    endpoints with the conjunction of the committed bits is within three
    fiftieths of the product of that same law's two marginals. The den Boer
    uniform model has left the statement. What remains is a bound on how far the
    one-cut run is from making a coalition's endpoints and the secret
    independent, and the advantage a distinguisher gets from it is at most three
    hundredths. *)
```

## R30 (kim, the singleton)

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:1244-1247`

```coq
    field, one coalition of one named seat, and the threshold condition proved
    rather than assumed. The coalition is not empty, so what the bound is stated
    on is the seat's own content observation at that seat, where the empty
    coalition is granted ord0 at every seat. *)
```

## R30 (kim, the header prose)

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:19-24`

```coq
(* All three security properties are certified over the one committed run.    *)
(* Certifying exact independence takes an ExactWitness, whose one field is    *)
(* independence of a coalition's endpoints from the conjunction of the two    *)
(* committed bits; under the uniform rotation this is leak_view_set, the      *)
(* exact mutual information of a reveal pattern, at a pattern of at most one  *)
(* card, where that information is zero, and the witness carries no number.   *)
```

## R30 (kim, the factorisation prose)

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:138-138`

```coq
(* This file requires instances/kim2025/five_card_proximity.v, which holds    *)
```

## R30 (kim, the index)

`instances/kim2025/tableau/five_card_tableau_analysis_bridged.v:191-193`

```coq
(*   five_card_static_obsE   == the framework's direct computation of a       *)
(*                              coalition's endpoints is the instance's       *)
(*                              colour reading encoded                        *)
```

## R30 (pgl27, the witness)

`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:285-295`

```coq
(** The exact-independence witness: the dealt secret as a random variable on the
    exact sample space, and, at every coalition of fewer than four seats, the
    independence from it of the whole of that coalition's endpoints, which is
    the reading this witness is indexed by. The independence is
    pgl27_view_indep, which is three-transitivity of PGL(2,7) on the eight
    points read as a privacy statement, and it is exact: the uniform cut makes
    what that reading grants carry no information about the secret at all, not a
    small amount. The framework derives the zero mutual information, the
    unchanged conditional entropy and the closure under post-processing from
    this one field, so the witness is all that certifying exact independence
    requires of this instance. *)
```

## R30 (pgl27, the prior witness)

`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:779-787`

```coq
(** The exact-independence witness at every prior: the dealt secret as a random
    variable on this sample space, and, at every coalition of fewer than four
    seats, the independence from it of the whole of that coalition's endpoints,
    which is the reading this witness is indexed by. The independence is
    pgl27_view_indep_gen, three-transitivity of PGL(2,7) read as a privacy
    statement, which holds whatever the law of the secret is. What that reading
    grants carries no information about the secret at all and not a small
    amount, so this model is an execution a proximity certificate may call
    ideal. *)
```

## R30 (pgl27, pgl27_word_cert)

`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:351-362`

```coq
(** The input-indistinguishability certificate at each secret prior, at the
    coalition's own endpoint reading. Its five fields are the two-hundred-letter
    walk's marginal bound; the identification of that bound's law with the law
    the word adapter draws its cut from, which is pgl27_word_cut_distE read
    backwards; the uniform distribution on the group as the ideal cut; the
    distance pgl27_word_mixing of the walk from that ideal, an unconditional
    theorem about the walk whose bound is 2^-40; and the constancy of what that
    reading grants a coalition of the ideal cut in the dealt secret, which is
    pgl27_word_view_const and is exact. Perfect and statistical security are
    both visible in the fields: everything about the ideal cut is exact and
    three-transitive, and the only statistical quantity anywhere in this program
    is the walk's 2^-40. *)
```

## R30 (pgl27, the proximity certificate)

`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:851-859`

```coq
(** The proximity certificate of the PGL(2,7) word program at every prior, at
    the coalition's own endpoint reading. Its five fields are the prior-indexed
    exact shuffle as the ideal; that model's exact witness, which is what makes
    the ideal an execution whose coalitions below four seats learn nothing at
    all; the dealt secret of the word model; the walk's marginal number 2^-40;
    and the distance pgl27_word_proximity_close of pgl27_proximity.v. The only
    inexact quantity is that number: the ideal and its witness are the terms the
    ideal program already publishes, and the secret is the word model's own
    first projection, typed at the carrier that witness names. *)
```

## R30 (pgl27, the identification)

`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:272-276`

```coq
(** The same identification once more, with the secret left inside the sample
    point. The exact-independence proposition compares a coalition's endpoints
    with the secret on one probability space, so the secret cannot be fixed
    first: the reader is a random variable of the pair, and that random variable
    is pgl27_view R C. *)
```

## R30 (pgl27, the closeness field)

`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:946-952`

```coq
    and the one the published reading statement pgl27_word_view_proximity
    carries. The certificate's own number is 2^-40, half of that. Below four
    seats its distance field, pgl27_word_proximity_close, puts the joint law of
    a coalition's endpoints with the dealt secret within that number of the same
    joint law under the prior-indexed exact execution, where those endpoints and
    the secret are independent outright, so the ideal side is the product of its
    two marginals. The proximity certificate's closeness field is one hop to the
```

## R30 (pgl27, the header prose)

`instances/pgl27/tableau/pgl27_tableau_analysis_bridged.v:15-19`

```coq
(* All three security properties are certified over the one dealer-dealt run. *)
(* Certifying exact independence takes an ExactWitness, whose one field is    *)
(* independence of a coalition's endpoints from the dealt secret; at the      *)
(* uniform cut this is three-transitivity of PGL(2,7) on the eight points     *)
(* read as a privacy statement, and it is exact, with no number in it.        *)
```

## R30 (psl211, the witness)

`instances/psl211/tableau/psl211_tableau_analysis_bridged.v:173-184`

```coq
(** psl211_exact_witness — the exact-independence witness: the chirality as a
    random variable on the all-decks sample space, and, at every coalition of
    fewer than six of the twelve seats, the independence from it of the whole of
    that coalition's endpoints, which is the reading this witness is indexed by.
    The independence is psl211_alldecks_view_indep, which is the equality of the
    two chiralities' deal counts read as a privacy statement, and it is exact: a
    uniform deck description and a uniform cut leave what that reading grants
    carrying no information about the chirality at all, not a small amount. The
    framework derives the zero mutual information, the unchanged conditional
    entropy and the closure under post-processing from this one field, so the
    witness is all that certifying exact independence requires of this
    instance. *)
```

## R30 (psl211, the proximity certificate)

`instances/psl211/tableau/psl211_tableau_analysis_bridged.v:287-296`

```coq
(** The proximity certificate of the PSL(2,11) word program, at the coalition's
    own endpoint reading. Its five fields are the all-decks model as the ideal;
    that model's exact witness, which is what makes the ideal an execution whose
    coalitions of at most five seats learn nothing at all; the chirality, which
    is the secret of the two models as one term; the word walk's number 2^-40;
    and psl211_word_proximity_close as the distance field, which bounds by that
    number the distance between the two models' joint laws of a coalition's
    endpoints with the chirality. The ideal, its witness and the secret are
    terms the all-decks program publishes, and the number is this certificate's
    own. *)
```

## R30 (psl211, the two secrets)

`instances/psl211/tableau/psl211_tableau_analysis_bridged.v:325-329`

```coq
(** The secret the certificate names and the secret its witness carries are one
    term, psl211_alldecks_secret. Where a certificate's two secrets differ, the
    ideal-proximity proposition compares a coalition's endpoints against a
    product taken in a different bit, so what a coalition is shown says nothing
    about the bit the ideal-proximity proposition names. *)
```

## R30 (relations, the index)

`manifest/pgg_tableau_security_property_relations.v:125-129`

```coq
(*   ideal_prod_reading_arg_prodE                                             *)
(*                              == below the threshold the ideal model's      *)
(*                                 joint law of what the reading grants a     *)
(*                                 coalition and the run argument is the      *)
(*                                 product of its two marginals               *)
```

## R30 (relations, exact_witness_cst_true)

`manifest/pgg_tableau_security_property_relations.v:328-331`

```coq
(** The exact witness at the coalition's own endpoint reading, over an arbitrary
    model whose secret is the constant true. Its independence field is
    inde_RV_cst, which uses no property of the model, so holding an exact
    witness is by itself no statement about what a model hides. *)
```

## R30 (relations, ideal_prod_reading_arg_prodE)

`manifest/pgg_tableau_security_property_relations.v:477-481`

```coq
(** Below the threshold the ideal model's joint law of what the reading grants a
    coalition and the run argument is the product of its two marginals. It is
    the input-indistinguishability certificate's constancy field read on that
    model, and it is what makes the ideal a model whose own privacy is proved
    rather than stipulated. *)
```

## R30 (psl211_models, the header prose)

`instances/psl211/psl211_models.v:20-27`

```coq
(* static_coalition_obs reads seat i at tnth (pi_starts _) i through the      *)
(* layout's share cast; the instance's psl211_alldecks_view reads it at i.    *)
(* The share cast disappears by conversion, the scheme's share count and the  *)
(* algebra's card count both being twelve, and the starting tuple is          *)
(* ord_tuple 12, so the two agree. What the interpreter's messages give of a  *)
(* coalition's endpoints is carried to the static computation by the endpoint *)
(* equation of psl211_endpoints.v, which enters here only through             *)
(* supplied_endpointsE and is never unfolded.                                 *)
```

## R30 (psl211_models, the index)

`instances/psl211/psl211_models.v:73-76`

```coq
(*   psl211_dealer_view      == a coalition's endpoints as a function of the  *)
(*                              dealer model's three coordinates              *)
(*   psl211_dealer_mixed_law == the law of those endpoints at one chirality,  *)
(*                              averaged over the deal and the cut            *)
```

## R30 (psl211_models, the banner)

`instances/psl211/psl211_models.v:266-266`

```coq
(*     The identification of a coalition's endpoints                          *)
```

## R30 (psl211_models, the exact identification)

`instances/psl211/psl211_models.v:312-315`

```coq
(** psl211_alldecks_exact_viewE — the same identification once more, with the
    deck description inside the sample point. The exact-independence proposition
    compares a coalition's endpoints with the secret on one probability space,
    so the run argument cannot be fixed first. *)
```

## R30 (psl211_models, psl211_dealer_mixed_law)

`instances/psl211/psl211_models.v:702-704`

```coq
(** psl211_dealer_mixed_law C b — the law of the coalition's endpoints at
    chirality b, averaged over the deal and the cut. It is the quantity the
    dealer model's privacy premise asks to be the same for both chiralities. *)
```

## R30 (psl211_models, psl211_perdeck_no_common_law)

`instances/psl211/psl211_models.v:1090-1094`

```coq
(** psl211_perdeck_no_common_law — no law on what a coalition is granted is
    the law of its endpoints at psl211_perdeck_deal under both chiralities. This
    is the second premise of dealer_shuffle_view_indep_of_deck written at
    PSL(2,11), for an arbitrary validity predicate that accepts that deal, and
    it has no solution, so the per-deck condition of
```

## R30 (reading_constancy, psl211_blockline1_test)

`instances/psl211/psl211_reading_constancy.v:348-350`

```coq
(** psl211_blockline1_test sq t — what the coalition is granted of the deck sq
    under the cut whose table is t matches psl211_blockline1_view, tested on raw
    codes. *)
```

## R30 (reading_constancy, psl211_dealt_test)

`instances/psl211/psl211_reading_constancy.v:941-943`

```coq
(** psl211_dealt_test sq t — what the coalition is granted of the deck sq
    under the cut whose table is t matches psl211_dealt_view, tested on raw
    codes. *)
```

## R34 (the header prose)

`manifest/pgg_tableau.v:49-54`

```coq
(* ic_close holds ic_ideal within the marginal bound's epsilon of that        *)
(* bound's own law, ic_Hd identifies that law with the model's own cut law,   *)
(* and ic_const asks a coalition below the threshold to read ic_ideal the     *)
(* same at every two run arguments. At some models these three fields leave   *)
(* no certificate at one reading whose marginal bound's epsilon, taken twice, *)
(* is below a positive number.                                                *)
```

## R34 (the index)

`manifest/pgg_tableau.v:274-282`

```coq
(*   indistinguishability_number_ge_of_input_distinguishability               *)
(*                          == a model distinguishable at a reading bounds    *)
(*                             from below the number an                       *)
(*                             input-indistinguishability program at that     *)
(*                             reading publishes                              *)
(*   no_indistinguishability_cert_ideal_close_of_input_distinguishability     *)
(*                          == and leaves no certificate at that reading      *)
(*                             whose ideal cut is that close to its own cut   *)
(*                             law                                            *)
```

## R35

`instances/psl211/psl211_colour_reading.v:305-310`

```coq
(** psl211_colour_of_reading_collides — two finite maps that give a position
    of the coalition two different hearts have the same colour value, so the
    colour map is not injective and the factorisation of
    psl211_colour_indistinguishability_of_coalition_reading runs in one
    direction only. That the two readings themselves differ is not this lemma's
    content; it is psl211_dealt_reading_indep_false. *)
```

## R36

`instances/psl211/tableau/psl211_tableau_dealt.v:298-307`

```coq
(** psl211_dealt_obstruction_published — the obstruction program. It certifies
    no security property, its data carrying no SecurityEvidence, and two
    exclusions follow from its one member: every number at which an
    input-indistinguishability program over this model at this reading states
    its proposition is at least 1/660, and no certificate at this reading has
    its ideal cut within eps of the model's own cut law once eps added to itself
    stays below 1/660. It leaves the colour reading untouched, where
    psl211_colour_exact_published certifies exact independence over the same
    model; the two are the pair a reading of a coalition's endpoints exists to
    separate. *)
```

## R39 (pgg_tableau.v)

`manifest/pgg_tableau.v:752-768`

```coq
(* The ideal-proximity proposition of a certificate, at the reading the
   certificate is indexed by: below the threshold, the joint law of what that
   reading grants the coalition of the executed run, with the secret, under
   the actual model, is within variation distance c of the product of the two
   marginals the ideal model has, what the reading grants it and its own
   secret. The right side is a product because the ideal's witness makes those
   two independent there, so c bounds the sum of the absolute differences
   between what a coalition below the threshold sees jointly with the secret
   and two quantities drawn apart, and a distinguisher's advantage is at most
   half of c, the sum of the absolute differences being twice the total
   variation distance of the literature. The attack model is a static
   coalition of fewer than k seats, and the reading is what that coalition is
   granted to see of its own endpoints; the claim is an average over the run
   argument and not a statement at a fixed run argument. The bound is a
   parameter, as it is for the input-indistinguishability proposition, so
   conclude can state a finished program at any number at or above the
   certificate's ipc_eps, the one a paper cites among them. *)
```

## R39 (pgg_tableau_reading.v)

`manifest/pgg_tableau_reading.v:223-228`

```coq
(* Exact independence at a reading r: below the privacy threshold, what r
   grants the coalition of the model's own run argument and cut is
   independent of the secret. It is an independence and not a numeric bound.
   The framework's entropy forms sit inside ExactProp, derived there from
   independence of the executed coalition view, which this proposition
   reaches along the link lemma of the Sampled level; none of those forms is
```

## R40 (the docstring)

`manifest/pgg_tableau.v:705-716`

```coq
(* The input-indistinguishability proposition at a reading: below the
   threshold, two run arguments give, of the model's own cut law, readings
   within variation distance c. It is stated of a reading, with no certificate
   in it, because the certificate's ideal cut and constancy field are used
   inside indistinguishability_tail and have left the claim; that is what lets
   a bound proved at one reading travel to another along a factorisation, with
   no certificate at the far end. The bound is a parameter rather than the
   certificate's own sum, so conclude can state a finished program at any
   number at or above that sum, the constant a paper cites among them, without
   reproving the proposition. The number bounds a sum of absolute differences,
   twice the total variation distance of the literature, so a distinguisher's
   advantage is at most half of it. *)
```
