# The spectral arm at Kim's rows and at PSL(2,11): what two probes found

Date: 2026-09-19. Branch `feat/kim-spectral-probe`. No permanent file was
edited by either probe. Every `.v` edit was made by an Opus `rocq-prover`
subagent, every result was recompiled from source and scanned by the main
session before it was committed, and every audit was run by an independent
Opus agent.

Specs and records: [[20260919-kim-spectral-arm-probe-design]],
`notes/probes/2026-09-19-kim-spectral-arm/STATUS.md`,
`notes/probes/2026-09-19-psl211-sc-const/STATUS.md`. Next:
[[20260919-tableau-three-extensions-probe-design]] with its design audit
[[20260919-tableau-extensions-design-audit]].

## The question

The paper tells one story about every instance: an ideal model with a uniform
cut, which is private, and an actual model with a biased cut, which is close to
the ideal one. The Tableau has an arm for that story, `SpectralDecay`. On
2026-09-19 both of Kim's five-card programs stopped one level below it, and
PSL(2,11) had no row for its word model at all. The question was whether the
existing arm can carry them. It can carry Kim's rows. It cannot carry
PSL(2,11), and the reason says what the Tableau is missing.

## Kim's rows: yes, through the existing arm

A `SpectralCert` has five fields. Three were already compiled. The two that
were missing are now proved at their exact field types.

- The fourth field, the distance on the cut group. The rotations of five cards
  act so that a rotation is fixed by the image of one card position, and every
  cut law in play is supported on the rotations. Reading one card position is
  then injective on the support, so the distance on the group equals the
  distance of the one-position marginal, which the tree already bounds
  (`kim_centi_cut_mixing`, `kim_biased_cut_mixing`).
- The fifth field, the constancy of a coalition's reading of the ideal cut. The
  threshold is 2, so a coalition is at most one seat, and a seat reads a
  colour. den Boer's layout has three hearts and two clubs at each of the four
  inputs, so under the uniform rotation the law of one seat's colour does not
  depend on the input (`five_card_static_obs_const`).

Numbers, each below the ceiling 2 of infotheo's `var_dist`, which is the sum of
absolute differences (`var_dist_le2`).

| Row | The certificate's own number | Written as a constant |
|---|---|---|
| seven cuts | `2 * sqrt 5 * (1/80)^7`, about `2.13e-13` | `2^-39`, about eight and a half times weaker |
| one cut | `sqrt 5 / 40`, about `0.056` | `1/25`, exact, and the stronger of the two |

What the certified rows state: for every coalition of at most one seat and
every two committed pairs, the variation distance between the two static
endpoint readings under the row's own cut law is at most the published number.
It is not independence from the secret, it is not about two seats, and it is
not about the full reveal. The landed leakage bound covers the full reveal and
stays beside the programs.

A landing changes both manifest rows. The repeated row moves to
`AnalysisBridged` and `IdealFinite`. The biased row moves from
`StaticExecutedOnly` to `IdealFinite`, because a row certified by comparison
with an ideal cut is `IdealFinite` by the manifest's own definitions. A landing
also meets seven `erefl` pins, two shared facade aliases and several header
passages. The record holds a seed list and the method for rebuilding it.

## PSL(2,11): no, and not for want of a lemma

The fifth field is false at PSL(2,11), at the field type, in both run modes.

- All-decks mode. The run argument is the public deck description. The reading
  of seats 0, 1 and 2 under the uniform cut has different laws at the two
  chiralities of one deck description (`psl211_alldecks_sc_const_false`) and
  also at two block lines of one chirality (`psl211_samechir_law_neq`). So the
  failure does not need the secret to move. It is no proof of leakage: under
  the all-decks law three seats read nothing about the chirality, which is the
  exact arm's theorem and is an average over deck descriptions.
- Dealt mode. The run argument is the secret alone, the field is constancy in
  the secret, and it fails because PSL(2,11) is 2-transitive and not
  3-transitive (`psl211_dealt_sc_const_false`). PGL(2,7) proves the same field
  from 3-transitivity.

No `SpectralCert` over the all-decks model has an epsilon below `1/1320`, so a
row there would publish at least `1/660`
(`psl211_alldecks_no_spectral_cert`). The same holds for any cut law within
`2^-40` of uniform, which covers the word model
(`psl211_alldecks_sc_const_false_word584`, from `psl211_word_mixing`). A
certificate does exist at an epsilon near the ceiling, with the uniform law on
all of `{perm 'I_12}` as its ideal, so the arm is not unavailable. It is
useless at any number worth publishing. By a computed diagnostic, not a
theorem, the floor is about `10/11`.

## What this says about the Tableau

The fifth field asks that the ideal's reading be the same at every two run
arguments. A privacy argument over a mixed law needs less: constancy in the
secret, on average over what is public. The field can be proved where the run
argument is the secret or determines it, and it fails where the run argument is
public data. `pgl27_view_mixing` already states the weaker and right
proposition at PGL(2,7), is aliased in the facade and pinned in the manifest,
and is carried by no row.

Two further facts came from the design audit of the next batch. The ideal in a
`SpectralCert` is a bare law on the cut group that never passed through the
phases. And `spectral_tail` does not consume the link lemma of `Sampled`, so
the claim a spectral row publishes never reaches the executed reader, where the
exact arm's claim does.

The user's two directions for what follows: the Tableau presents what we have,
so a finding it cannot hold is a reason to extend it, by the meaning of its
phases and not wherever a constructor fits; and a row is one security claim
with its whole chain, so two models are two rows and two claims about one
model are two rows.

## How the batch was run, and what it taught

| | Kim probe | PSL(2,11) probe |
|---|---|---|
| Soundness audits | 5, mathematics confirmed in each | 3, every statement true in each |
| Naming audits | 5 | none, by scope |
| Fix passes | 5 | 3 |
| Last step verified by | the main session | the main session, by the user's decision |

Every NO-GO after the first round was about English, and most of the blocking
sentences were written during a fix pass. Three times the defective sentence
was the auditor's own replacement text applied verbatim, so a replacement is
checked against the lemma like any other text. A document that cites its own
lines by number goes wrong as soon as a pass inserts a line above them. The
list of what a landing breaks was incomplete three rounds running, because it
was built by searching for names while the tree states the same facts in
sentences that carry no name; it is now a seed list with a method. One
acceptance criterion was narrowed for that reason and the narrowing was told
to the user when it was made.

Two presentation rules from the user: never write the two-character name of
the sum-of-absolute-differences norm, since `L` is a word length here; and
write every Tableau program in one surface syntax, which needs a keyword
notation for `conclude`.

## Left open

1. Landing Kim's rows: the user's decision, with two choices inside it, the
   form of each row and the home of the mixing and constancy theorems.
2. A local hypothesis name in `psl211_sc_const_probe.v` spells the barred
   term and is code, to be renamed at a landing.
3. `kim_centi_small` still sits in `five_card_rows.v`.
4. The main checkout still has files out of date by modification time since
   commit 1654fde. Nothing was compiled against the `.vo` files that commit
   will produce. The rule in force is to compile only related files.
