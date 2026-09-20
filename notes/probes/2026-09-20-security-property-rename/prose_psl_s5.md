# prose_psl_s5 — comments-only pass, group psl_s5

Parent commit 77a2c84, branch feat/tableau-extensions-probe. Comments only: a
comment-stripped comparison of all eleven files against 77a2c84 reports the code
byte-identical in every one. `[N1]` stands for the first barred noun and `[N2]`
for the second in every quoted OLD line; nothing else in a quoted line is
altered.

## Counts per file, per case

| File | c1 | c2 | c3 | c4 | c5 | c7 | [N2] c1 | total |
|---|---|---|---|---|---|---|---|---|
| instances/psl211/tableau/psl211_tableau_analysis_bridged.v | 5 | 3 | 3 | 6 | 1 | 4 | 4 | 22 / 4 |
| instances/psl211/tableau/psl211_tableau_checks.v | 0 | 2 | 0 | 0 | 0 | 0 | 0 | 2 / 0 |
| instances/psl211/tableau/psl211_tableau_sampled.v | 0 | 1 | 0 | 0 | 2 | 0 | 0 | 3 / 0 |
| instances/psl211/psl211_reading_constancy.v | 3 | 2 | 0 | 0 | 4 | 0 | 1 | 9 / 1 |
| instances/psl211/psl211_models.v | 0 | 3 | 3 | 0 | 0 | 0 | 0 | 6 / 0 |
| instances/psl211/psl211_word_proximity.v | 0 | 1 | 0 | 3 | 0 | 0 | 0 | 4 / 0 |
| instances/psl211/psl211_analysis.v | 0 | 1 | 1 | 0 | 0 | 0 | 0 | 2 / 0 |
| instances/psl211/psl211_word_model.v | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 1 / 0 |
| instances/s5/tableau/s5_tableau_analysis_bridged.v | 2 | 2 | 2 | 4 | 0 | 2 | 0 | 12 / 0 |
| instances/s5/tableau/s5_tableau_sampled.v | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 / 0 |
| **edited total** | 10 | 16 | 9 | 13 | 8 | 6 | 5 | **62 / 5** |
| instances/psl211/psl211_exec.v (FROZEN, not edited) | 1 | | | | | | | 1 / 0 |

Group vocabulary, one word per concept across all ten files: "security
property", "the exact-independence witness", "a proximity certificate", "an
input-indistinguishability certificate", "the exact-independence proposition",
"the ideal-proximity proposition", "the certify statement", "the evidence".

---

## instances/psl211/tableau/psl211_tableau_analysis_bridged.v

**Header, lines 7-12 (cases 4, 1, 2, 2).** Decided against `EvidenceProp`
("the proposition the evidence proves"), `SecurityProperty` ("which of three
security properties the evidence proves") and `ExactProp`.

OLD
```
(* per index of the model, and the proposition it carries is that payload's   *)
(* [N1] on top of everything the levels below proved. This is the level at     *)
(* which a program says something about a coalition, and the [N1] decides what *)
(* it says: the exact [N1] asserts independence, and the proximity [N1] a       *)
(* distance to a model whose own privacy is a theorem.                        *)
```
NEW
```
(* per index of the model, and the proposition it carries is the proposition  *)
(* that payload proves, on top of everything the levels below proved. This is *)
(* the level at which a program says something about a coalition, and the     *)
(* security property decides what it says: the exact-independence proposition *)
(* asserts independence, and the ideal-proximity proposition a distance to a  *)
(* model whose own privacy is a theorem.                                      *)
```

**Header, lines 23-32 (cases 1, 1).** Decided against `SecurityEvidence`: an
instance supplies the witness or the certificate; a property receives nothing.

OLD
```
(* outright, at every real field and with no number in the claim; that is the *)
(* exact [N1], and the instance gives it one witness. Over the 584-letter word *)
(* cut, what a coalition is shown is within 2^-40, in the sum of absolute     *)
(* differences, of what the uniform-cut execution shows it, so a              *)
(* distinguisher's advantage is at most 2^-41; that is the proximity [N1], and *)
(* the instance gives it a certificate whose ideal is the first program's own *)
```
NEW
```
(* outright, at every real field and with no number in the claim; that is     *)
(* exact independence, and the instance supplies one witness for it. Over the *)
(* 584-letter word cut, what a coalition is shown is within 2^-40, in the sum *)
(* of absolute differences, of what the uniform-cut execution shows it, so a  *)
(* distinguisher's advantage is at most 2^-41; that is ideal proximity, and   *)
(* the instance supplies a certificate whose ideal is the first program's own *)
```

**Header, lines 34-37 (case 1).** Decided against `IndistinguishabilityCert`,
whose fifth field `ic_const` is the constancy field named here.

OLD
```
(* No input-indistinguishability program is published over either model. A    *)
(* certificate of that [N1] carries a constancy field, and                     *)
```
NEW
```
(* No input-indistinguishability program is published over either model. An   *)
(* input-indistinguishability certificate carries a constancy field, and      *)
```

**Index entry, psl211_exact_witness (case 3).**

OLD `(*   psl211_exact_witness    == the exact [N1]'s witness at every field and    *)` / `(*                              index                                         *)`
NEW
```
(*   psl211_exact_witness    == the exact-independence witness at every field *)
(*                              and index                                     *)
```

**Index entry, psl211_alldecks_published_propertyE (case 7).**

OLD `(*                           == the program carries the exact [N1]             *)`
NEW
```
(*                           == the program's security property is exact      *)
(*                              independence                                  *)
```

**Index entry, psl211_alldecks_view_secrecy (case 4).**

OLD `(*                           == the exact [N1]'s four conjuncts at this        *)` / `(*                              instance                                      *)`
NEW
```
(*                           == the exact-independence proposition's four     *)
(*                              conjuncts at this instance                    *)
```

**Index entry, psl211_word_proximity_cert_idealE ([N2] case 1, two sites).**
The two things compared are `ExactIndependence (ipc_witness ...)` and
`ab_evidence ...`, both of type `SecurityEvidence`.

OLD `(*                              program's model, and the [N2] built from its  *)` / `(*                              witness is that program's [N2]                *)`
NEW
```
(*                              program's model, and the evidence built from  *)
(*                              its witness is that program's evidence        *)
```

**Index entry, psl211_word_proximity_published_propertyE (case 7).**

OLD `(*                           == the program carries the proximity [N1]         *)`
NEW
```
(*                           == the program's security property is ideal      *)
(*                              proximity                                     *)
```

**Banner, line 140 (case 3).**

OLD `(*     The exact [N1]'s witness                                                *)`
NEW `(*     The exact-independence witness                                         *)`

**psl211_exact_witness docstring (cases 3 and 2).** Decided against
`ExactWitness` and `certify_exact`: a property requires nothing of an instance,
certifying one does.

OLD
```
(** psl211_exact_witness — the exact [N1]'s witness: the chirality as a random
    variable on the all-decks sample space, and, at every coalition of fewer
    than six of the twelve seats, the independence of that coalition's reading
    from it. The independence is psl211_alldecks_view_indep, which is the
    equality of the two chiralities' deal counts read as a privacy statement,
    and it is exact: a uniform deck description and a uniform cut leave the
    reading carrying no information about the chirality at all, not a small
    amount. The framework derives the zero mutual information, the unchanged
    conditional entropy and the closure under post-processing from this one
    field, so the witness is all the exact [N1] requires of this instance. *)
```
NEW
```
(** psl211_exact_witness — the exact-independence witness: the chirality as a
    random variable on the all-decks sample space, and, at every coalition of
    fewer than six of the twelve seats, the independence of that coalition's
    reading from it. The independence is psl211_alldecks_view_indep, which is
    the equality of the two chiralities' deal counts read as a privacy
    statement, and it is exact: a uniform deck description and a uniform cut
    leave the reading carrying no information about the chirality at all, not a
    small amount. The framework derives the zero mutual information, the
    unchanged conditional entropy and the closure under post-processing from
    this one field, so the witness is all that certifying exact independence
    requires of this instance. *)
```

**psl211_alldecks_published_propertyE docstring (case 7 twin, then case 1).**
The lemma's statement is `security_property_of ... = ExactIndependenceProperty`.

OLD
```
(** The [N1] this program carries, at every real field and index: independence of
    the coalition's view from the chirality, and not a distance between two
    readings. The certify statement the program wrote settles which [N1]
    that is. *)
```
NEW
```
(** The program's security property, at every real field and index, is exact
    independence: independence of the coalition's view from the chirality, and
    not a distance between two readings. The certify statement the program wrote
    settles which property that is. *)
```

**Banner, line 213 (case 4).**

OLD `(*     The exact [N1]'s four conjuncts at this instance                        *)`
NEW `(*     The exact-independence proposition's four conjuncts at this instance   *)`

**psl211_alldecks_view_secrecy docstring (case 4).** The four conjuncts are
`ExactProp`'s.

OLD
```
    map. The four conjuncts are the whole content of the exact [N1] here; the
    proof is the program's security projection applied, so a reader who wants
    the information-theoretic reading of the program needs no further
    derivation. *)
```
NEW
```
    map. The four conjuncts are the whole content of the exact-independence
    proposition here; the proof is the program's security projection applied, so
    a reader who wants the information-theoretic reading of the program needs no
    further derivation. *)
```

**psl211_word_proximity_cert_idealE docstring ([N2] case 1, two sites).**

OLD
```
    program carries, and the [N2] built from the witness the certificate carries
    is that program's [N2]. Conversion decides both, so the ideal a word program
    is measured against is the model the all-decks program publishes and not a
    second description of it. *)
```
NEW
```
    program carries, and the evidence built from the witness the certificate
    carries is that program's evidence. Conversion decides both, so the ideal a
    word program is measured against is the model the all-decks program
    publishes and not a second description of it. *)
```

**psl211_word_proximity_cert_secretE docstring (case 4).** The bit named is the
one `IdealProximityPropAt` pairs with a coalition's reading.

OLD `    the [N1]'s proposition names. *)`
NEW `    the ideal-proximity proposition names. *)`

**psl211_word_proximity_cert_secretTE docstring (case 4).**

OLD
```
    At a one-point carrier the [N1]'s proposition compares two readings and
    mentions no secret at all, the second factor of the product being a point
    mass, so the number would bound nothing about what a coalition learns of
    the bit. The secret is also the one the protocol reconstructs:
    psl211_alldecks_secret_expectedE of instances/psl211/psl211_models.v
    reads it as the value the run recovers, at every sample point. *)
```
NEW
```
    At a one-point carrier the ideal-proximity proposition compares two
    readings and mentions no secret at all, the second factor of the product
    being a point mass, so the number would bound nothing about what a
    coalition learns of the bit. The secret is also the one the protocol
    reconstructs: psl211_alldecks_secret_expectedE of
    instances/psl211/psl211_models.v reads it as the value the run recovers,
    at every sample point. *)
```

**psl211_word_proximity_published docstring (case 5).**

OLD `(** The word model certified by the proximity [N1] and published at 2^-40, the`
NEW `(** The word model certified for ideal proximity and published at 2^-40, the`

**psl211_word_proximity_published_propertyE docstring (case 7 twin).**

OLD
```
(** The [N1] the program carries, at every real field and index: the distance to
    a private ideal model, and not the distance between two readings of one
    model. *)
```
NEW
```
(** The program's security property, at every real field and index, is ideal
    proximity: the distance to a private ideal model, and not the distance
    between two readings of one model. *)
```

---

## instances/psl211/tableau/psl211_tableau_checks.v

Both sites name the holder of the ideal field, which is `IdealProximityCert`'s
`ipc_ideal`; the sentence two clauses later already says "A certificate's ideal
is a sample adapter over the program's own execution".

**Header, lines 20-26 (case 2).**

OLD `(* which ideal the proximity [N1] admits. A certificate's ideal is a sample    *)` (with lines 21-26 following)
NEW
```
(* which ideal a proximity certificate admits. A certificate's ideal is a     *)
(* sample adapter over the program's own execution, so the eight-card orbit   *)
(* instance's model is refused at its type and no distance is reached. Beside *)
(* it, the ideal of the certificate this instance builds is refused as the    *)
(* word model the certificate is about; a certificate whose ideal were its    *)
(* own model would hold its distance field at zero, the two sides of that     *)
(* field being one term.                                                      *)
```

**Banner, line 90 (case 2).**

OLD `(*     Which ideal the [N1] refuses                                            *)`
NEW `(*     Which ideal a proximity certificate refuses                            *)`

---

## instances/psl211/tableau/psl211_tableau_sampled.v

**Header line 12 (case 5).** The next line of a program is a `certify_*`
statement.

OLD `(* action, and it is the last thing proved before an [N1] is named.            *)`
NEW `(* action, and it is the last thing proved before the certify statement.      *)`

**Header lines 20-22 (case 2).** What compares two laws is
`IdealProximityPropAt`.

OLD
```
(* proximity [N1] compares, and it is the reason the two programs of the       *)
(* instance part here and not lower. The deck description is drawn            *)
(* uniformly in both.                                                         *)
```
NEW
```
(* ideal-proximity proposition compares, and it is the reason the two         *)
(* programs of the instance part here and not lower. The deck description is  *)
(* drawn uniformly in both.                                                   *)
```

**psl211_exact_sampled docstring (case 5).**

OLD
```
    uniform over the shuffle group. This is the model the exact [N1] is certified
    over, and the one a word program is measured against: an execution whose own
    privacy below the six-seat threshold is a theorem rather than a number. The
    value is what psl211_alldecks_published_sampledE continues, so the program
    and the model are named apart. *)
```
NEW
```
    uniform over the shuffle group. This is the model over which exact
    independence is certified, and the one a word program is measured against:
    an execution whose own privacy below the six-seat threshold is a theorem
    rather than a number. The value is what psl211_alldecks_published_sampledE
    continues, so the program and the model are named apart. *)
```

---

## instances/psl211/psl211_reading_constancy.v

This file restates `ic_const`, the fifth field of `IndistinguishabilityCert`, and
refutes it in both run modes, so its sites name which certificate holds that
field (`IndistinguishabilityCert`) and which does not (`IdealProximityCert`,
already spelled "a proximity certificate" in the tree at line 44).

**Header lines 14-17 (cases 5, 5, 2).**

OLD
```
(* publishes its all-decks program through the exact [N1] and its word program *)
(* through the proximity [N1], in                                              *)
(* instances/psl211/tableau/psl211_tableau_analysis_bridged.v, and this file  *)
(* is what the input-indistinguishability [N1] would require of it.            *)
```
NEW
```
(* publishes its all-decks program with exact-independence evidence and its   *)
(* word program with ideal-proximity evidence, in                             *)
(* instances/psl211/tableau/psl211_tableau_analysis_bridged.v, and this file  *)
(* is what certifying input indistinguishability would require of it.         *)
```

**Header lines 43-47 (cases 1, 5).**

OLD
```
(* marginal bound. The exclusion covers the input-indistinguishability [N1]    *)
(* alone: a proximity certificate carries no shuffle bound and no constancy   *)
(* field, and the program of                                                  *)
(* instances/psl211/tableau/psl211_tableau_analysis_bridged.v publishes 2^-40 *)
(* over the word model through the proximity [N1].                             *)
```
NEW
```
(* marginal bound. The exclusion covers input indistinguishability alone: a   *)
(* proximity certificate carries no shuffle bound and no constancy field, and *)
(* the program of instances/psl211/tableau/psl211_tableau_analysis_bridged.v  *)
(* publishes 2^-40 over the word model with ideal-proximity evidence.         *)
```

**Header lines 61-64 (case 1).** Re-flow re-synchronizes with the untouched text
at old line 65.

OLD
```
(* Not claimed. The input-indistinguishability [N1] is not shown unavailable   *)
(* at this instance. What is excluded is a range of epsilon, and the range of *)
(* larger epsilon is occupied: the uniform law on the whole of {perm 'I_12}   *)
(* reads the same at every deck description, its variation distance from `U   *)
```
NEW
```
(* Not claimed. Input indistinguishability is not shown unavailable at this   *)
(* instance. What is excluded is a range of epsilon, and the range of larger  *)
(* epsilon is occupied: the uniform law on the whole of {perm 'I_12} reads    *)
(* the same at every deck description, its variation distance from `U         *)
```

**psl211_perdeck_coalition_below_k docstring (case 2).** The premise
`#|C| < profile_k` is stated by `ExactProp`, `IndistinguishabilityPropAt` and
`IdealProximityPropAt` alike.

OLD
```
    premise every security [N1] states, the derived profile declaring six. A
    refutation of a field quantified over coalitions below the threshold has
    to discharge this premise, and it is the counterexample's only nontrivial
    premise. *)
```
NEW
```
    premise every security proposition states, the derived profile declaring
    six. A refutation of a field quantified over coalitions below the
    threshold has to discharge this premise, and it is the counterexample's
    only nontrivial premise. *)
```

**psl211_alldecks_no_small_eps_cert docstring (cases 5, 1) and the comment above
its statement ([N2] case 1).** The `[N2]` site is a value of `SecurityEvidence`
built by `InputIndistinguishability`, and `conclude`'s obligation is read at that
value; "an input-indistinguishability program" matches the file's own line 33.

OLD
```
    over this model publishes less. This fixes from below what the
    input-indistinguishability [N1] can publish at this model. It says neither
    that the [N1] is unavailable here nor anything about what a coalition of at
    most five seats reads. *)
(* The obligation of conclude at an input-indistinguishability [N2] is cert_eps
```
NEW
```
    over this model publishes less. This fixes from below what an
    input-indistinguishability program can publish at this model. It says
    neither that input indistinguishability is unavailable here nor anything
    about what a coalition of at most five seats reads. *)
(* The obligation of conclude at input-indistinguishability evidence is cert_eps
```

---

## instances/psl211/psl211_models.v

Six docstrings of model families, each read against the certificate whose field
it feeds. All five sites about `ExactWitness` say "the exact-independence
witness"; the one about `ExactProp` says "the exact-independence proposition".

**Header line 39 (case 3).**

OLD `(* The exact [N1]'s witness over psl211_exact_family is built in               *)`
NEW `(* The exact-independence witness over psl211_exact_family is built in        *)`

**psl211_alldecks_cut_distE docstring (case 2).** The uniform cut is what
`ew_indep` of the instance's `ExactWitness` holds at.

OLD `    the shuffle group. This is the cut the exact [N1] needs. *)`
NEW `    the shuffle group. This is the cut the exact-independence witness needs. *)`

**psl211_alldecks_exact_viewE docstring (case 2).** `ExactProp` states
independence of a coalition's reading and the secret on one space.

OLD
```
    deck description inside the sample point. The exact [N1] compares a
    coalition's reading with the secret on one probability space, so the run
    argument cannot be fixed first. *)
```
NEW
```
    deck description inside the sample point. The exact-independence proposition
    compares a coalition's reading with the secret on one probability space, so
    the run argument cannot be fixed first. *)
```

**psl211_alldecks_secret_expectedE docstring (cases 2, 3).** `ew_secret` is the
field that holds the secret; a program, not a property, certifies.

OLD
```
(** psl211_alldecks_secret_expectedE — the secret the exact [N1] certifies is
    the value the run recovers, read off the same sample point. The exact
    [N1]'s witness has no field relating its secret to the run's expected
    value, so without this equation that secret could be independent of a bit
    the protocol never reconstructs and the published independence would be
    true and empty. *)
```
NEW
```
(** psl211_alldecks_secret_expectedE — the secret the exact-independence
    witness carries is the value the run recovers, read off the same sample
    point. The exact-independence witness has no field relating its secret to
    the run's expected value, so without this equation that secret could be
    independent of a bit the protocol never reconstructs and the published
    independence would be true and empty. *)
```

**psl211_alldecks_static_indep docstring (case 3).**

OLD `    side, which is the form the exact [N1]'s witness demands of it. *)`
NEW `    side, which is the form the exact-independence witness demands of it. *)`

---

## instances/psl211/psl211_word_proximity.v

**Header lines 10-12 (case 2).** The distance field is `ipc_close` of
`IdealProximityCert`.

OLD `(* it carries the bound the proximity [N1] of this instance takes as its       *)`
NEW `(* it carries the bound this instance's proximity certificate takes as its    *)`

**Header line 22 (case 4).**

OLD `(* threshold entering the [N1]'s proposition and not the bound.                *)`
NEW `(* threshold entering the ideal-proximity proposition and not the bound.      *)`

**psl211_word_proximity_close docstring (case 4).**

OLD `    the [N1]'s proposition and not this distance. *)`
NEW `    the ideal-proximity proposition and not this distance. *)`

**psl211_word_law_le2 docstring (case 4).** `IdealProximityPropAt cert c` is
indexed by the number, so reading the proposition is reading the number.

OLD
```
(** The two models' laws are within two of each other by the bound every pair of
    laws on one finite sample space meets, with no fact about the twelve-card
    instance and no fact about the 584-letter walk. A proximity certificate
    carrying two would be a certificate about nothing, which is why the number a
    program publishes is what a reader of the [N1] must read. *)
```
NEW
```
(** The two models' laws are within two of each other by the bound every pair
    of laws on one finite sample space meets, with no fact about the
    twelve-card instance and no fact about the 584-letter walk. A proximity
    certificate carrying two would be a certificate about nothing, which is
    why the number a program publishes is what a reader of the ideal-proximity
    proposition must read. *)
```

---

## instances/psl211/psl211_analysis.v

**Section 5 header (case 2).** The second alias is `secret_expectedE`; the
secret it names is `ew_secret`, the wording matching psl211_models.v.

OLD
```
(* names the secret the exact [N1] is about as the value that recovery         *)
(* returns.                                                                   *)
```
NEW
```
(* names the secret the exact-independence witness carries as the value that  *)
(* recovery returns.                                                          *)
```

**static_indep docstring (case 3).** The field is `ew_indep`.

OLD `    which is the form the exact [N1]'s witness field takes. *)`
NEW `    which is the form the exact-independence witness's field takes. *)`

---

## instances/psl211/psl211_word_model.v

**psl211_word_cut_distE docstring (case 2).**

OLD
```
    psl211_word_mixing bounds against uniform, so the distance the proximity
    [N1] bounds is a distance between the two cuts of one execution and not a
    distance between two executions. *)
```
NEW
```
    psl211_word_mixing bounds against uniform, so the distance the
    ideal-proximity proposition bounds is a distance between the two cuts of
    one execution and not a distance between two executions. *)
```

---

## instances/s5/tableau/s5_tableau_analysis_bridged.v

Sibling of the psl211 and five-card AnalysisBridged files; the three twin
sentences carry the sheet's wording verbatim.

**Header lines 6-11 (cases 4, 1, 2).**

OLD
```
(* per index of the model, and the proposition it carries is that payload's   *)
(* [N1] on top of everything the levels below proved. This is the level at     *)
(* which a program says something about a coalition, and the [N1] decides what *)
(* it says: the exact [N1] asserts independence, and not a distance between    *)
(* two readings.                                                              *)
```
NEW
```
(* per index of the model, and the proposition it carries is the proposition  *)
(* that payload proves, on top of everything the levels below proved. This is *)
(* the level at which a program says something about a coalition, and the     *)
(* security property decides what it says: the exact-independence proposition *)
(* asserts independence, and not a distance between two readings.             *)
```

**Index entry, s5_rand_exact_witness (case 3).**

OLD `(*                        == the exact [N1]'s witness at every field and index *)`
NEW
```
(*                        == the exact-independence witness at every field    *)
(*                           and index                                        *)
```

**Index entry, s5_rand_published_propertyE (case 7).**

OLD `(*                        == the program carries the exact [N1]                *)`
NEW
```
(*                        == the program's security property is exact         *)
(*                           independence                                     *)
```

**Index entry, s5_rand_view_secrecy (case 4).**

OLD `(*   s5_rand_view_secrecy == the exact [N1]'s four conjuncts at this instance  *)`
NEW
```
(*   s5_rand_view_secrecy == the exact-independence proposition's four        *)
(*                           conjuncts at this instance                       *)
```

**s5_rand_exact_witness docstring (cases 3, 2).**

OLD
```
(** The exact [N1]'s witness: the tape secret as a random variable on the tape
    space, and, at every coalition of fewer than five seats, the independence
    of that coalition's reading from it. The independence is exact, four
    additive shares of a uniform tape carrying no information about the
    secret at all rather than a small amount, and it is exact for a reason no
    shuffle takes part in. The framework derives the zero mutual information,
    the unchanged conditional entropy and the closure under post-processing
    from this one field, so the witness is all the exact [N1] requires of this
    instance. *)
```
NEW
```
(** The exact-independence witness: the tape secret as a random variable on the
    tape space, and, at every coalition of fewer than five seats, the
    independence of that coalition's reading from it. The independence is exact,
    four additive shares of a uniform tape carrying no information about the
    secret at all rather than a small amount, and it is exact for a reason no
    shuffle takes part in. The framework derives the zero mutual information,
    the unchanged conditional entropy and the closure under post-processing from
    this one field, so the witness is all that certifying exact independence
    requires of this instance. *)
```

**s5_rand_published_propertyE docstring (case 7 twin, then case 1).**

OLD
```
(** The [N1] this program carries, at every real field and index: independence of
    the coalition's view from the tape secret, and not a distance between two
    readings. The certify statement the program wrote settles which [N1]
    that is. *)
```
NEW
```
(** The program's security property, at every real field and index, is exact
    independence: independence of the coalition's view from the tape secret, and
    not a distance between two readings. The certify statement the program wrote
    settles which property that is. *)
```

**Banner, line 206 (case 4).**

OLD `(*     The exact [N1]'s four conjuncts at this instance                        *)`
NEW `(*     The exact-independence proposition's four conjuncts at this instance   *)`

**s5_rand_view_secrecy docstring (case 4).**

OLD
```
    deterministic function of the seat-to-card map. The four conjuncts are the
    whole content of the exact [N1] at this instance; the proof is the program's
    security projection applied, so a reader who wants the information-theoretic
    reading of the program needs no further derivation. *)
```
NEW
```
    deterministic function of the seat-to-card map. The four conjuncts are the
    whole content of the exact-independence proposition at this instance; the
    proof is the program's security projection applied, so a reader who wants
    the information-theoretic reading of the program needs no further
    derivation. *)
```

---

## instances/s5/tableau/s5_tableau_sampled.v

**Header line 12 (case 5), twin of psl211_tableau_sampled.v line 12.**

OLD `(* action, and it is the last thing proved before an [N1] is named.            *)`
NEW `(* action, and it is the last thing proved before the certify statement.      *)`

---

## FROZEN, for the owner: instances/psl211/psl211_exec.v

Not edited. One site, in the `profile_k_psl211_algebra` docstring, at line 127
of the file as of 77a2c84 (case 1, but the verb needs the proposition, since a
property quantifies over nothing):

OLD
```
(** profile_k_psl211_algebra — the privacy threshold the derived profile
    declares is six, so every [N1] of a row over this algebra quantifies over
    coalitions of at most five of the twelve seats.  It is profile_k_psl211
    read at the derived profile.  The rows' witness converts the framework's
    threshold hypothesis to the numeric bound directly, and this lemma records
    the number that conversion relies on. *)
```
PROPOSED (two lines re-flowed, the two-space sentence spacing of the file kept,
every line at most 80 bytes)
```
(** profile_k_psl211_algebra — the privacy threshold the derived profile
    declares is six, so the security proposition of every row over this algebra
    quantifies over coalitions of at most five of the twelve seats.  It is
    profile_k_psl211 read at the derived profile.  The rows' witness converts
    the framework's threshold hypothesis to the numeric bound directly, and this
    lemma records the number that conversion relies on. *)
```

---

## Sentences the verb rule showed were already untrue, and how they were made true

1. "the proposition it carries is that payload's [N1]" (analysis_bridged 9, s5 8).
   A proposition is not a property. Now "is the proposition that payload proves".
2. "the exact [N1] asserts independence" (analysis_bridged 11, s5 10). A property
   asserts nothing. Now "the exact-independence proposition asserts independence".
3. "the instance gives it one witness" / "gives it a certificate"
   (analysis_bridged 26, 29). A property receives nothing. Now "the instance
   supplies one witness for it" / "the instance supplies a certificate".
4. "the witness is all the exact [N1] requires of this instance"
   (analysis_bridged 152, s5 150). A property requires nothing. Now "all that
   certifying exact independence requires of this instance".
5. "which ideal the proximity [N1] admits" and "Which ideal the [N1] refuses"
   (checks 20, 90). The ideal is a certificate field. Now "a proximity
   certificate admits" / "a proximity certificate refuses".
6. "the shape the proximity [N1] compares" (sampled 20), "the distance the
   proximity [N1] bounds" (word_model 103). A property compares and bounds
   nothing. Now "the ideal-proximity proposition compares" / "bounds".
7. "the model the exact [N1] is certified over" (sampled 58). A property is not
   certified over a model; a program certifies a property over one. Now "the
   model over which exact independence is certified".
8. "this file is what the input-indistinguishability [N1] would require of it"
   (reading_constancy 17). Now "what certifying input indistinguishability would
   require of it".
9. "the threshold premise every security [N1] states" (reading_constancy 247).
   A property states nothing. Now "every security proposition states".
10. "what the input-indistinguishability [N1] can publish at this model"
    (reading_constancy 705). A property publishes nothing; a program does. Now
    "what an input-indistinguishability program can publish at this model".
11. "the cut the exact [N1] needs" (models 248). Now "the cut the
    exact-independence witness needs".
12. "the secret the exact [N1] certifies" (models 442) and "the secret the exact
    [N1] is about" (analysis 196). A property certifies nothing. Now "the secret
    the exact-independence witness carries", the same phrase in both files.
13. "the bound the proximity [N1] of this instance takes as its distance field"
    (word_proximity 10). Now "the bound this instance's proximity certificate
    takes as its distance field".
14. "publishes its all-decks program through the exact [N1]" and "through the
    proximity [N1]" (reading_constancy 14, 15, 47). Sheet case 5: now "with
    exact-independence evidence" and "with ideal-proximity evidence".

## Sentences that could not be made true

None. Two observations for the main session, both outside a barred-noun site and
therefore left alone under rule 1:

- `psl211_tableau_analysis_bridged.v`, psl211_word_proximity_cert_secretE
  docstring: "A proximity certificate whose two secrets differ compares a
  coalition's reading against a product taken in a different bit". A certificate
  holds fields; the proposition compares. The sentence following it, which was a
  barred-noun site, now reads "the ideal-proximity proposition names".
- `psl211_reading_constancy.v` header line 34: "A certificate over the all-decks
  model states its distance against the group-uniform law". Same shape.

## Final scan

Word-boundary search for either noun in any inflection and any case across all
ten edited files: **0 occurrences**. No token of a capital L followed by a digit
was introduced. Every added line is at most 80 bytes; every added boxed line is
exactly 80 bytes and ends with a space before the closing delimiter; `==` and
continuation columns are unchanged; docstring continuations stay at 4 spaces;
each banner stays one content line. A comment-stripped comparison against
77a2c84 reports the code of all eleven files, the frozen one included,
byte-identical.
