# What does the shuffle buy? den Boer, Kim, S5, S5xS5, Dic_3

Date: 2026-07-01

Answer to: "Yes for Shamir's secret sharing since that position's value is never
distributed to the share holders. If Dic_3 follows the same pattern, the PGG flow need
to make sure there is a place such variant flow can be compatible. Also, this makes
consider the value of shuffle again. What does den Boer's and Kim's security gain from
shuffling, and do we gain the same thing by shuffling for S5, S5xS5 and Dic_3?"

Companions: [[20260701-nonabelian-ag-genus1-CONTENTS]],
[[20260701-nonabelian-ag-recoverable-genus1-worked-example]],
[[20260701-nonabelian-ag-genus1-ROCQ-formalization-spec]].

---

Two things here: your framework point, then the shuffle question. The second is the more
interesting one and it reframes what the whole security axis is for.

## Your framework point is right, and it names the exact compatibility requirement

Yes. Dic_3 follows the Shamir pattern: coordinate 0 holds the secret value, is publicly
known, is never dealt to a share-holder, and is fixed by every shuffle element. The Massey
scheme already puts the secret at coordinate 0 and the shares at 1..n-1, so the *data* is
latent. What is missing is the *flow-level* guarantee: the PGG monodromy has to fix that
coordinate and the dealing has to skip it. That is precisely an intransitive action with a
distinguished fixed point plus a transitive share-orbit. S5's flow is transitive, so it has
no such slot, which is the structural reason S5 cannot recover. So "make a place for the
non-dealt secret slot in the PGG flow" is the same requirement as the recovery migration
(fixed-coordinate monodromy + a reconstruction-threshold field). Good framing to carry into
P4.

## What a shuffle buys, in one sentence

A uniform draw from a group makes the observable depend on the hidden data *only through
the orbit-invariant of that group*. Everything inside the orbit is averaged away; only the
invariant survives to be read. That single mechanism is what all of these protocols run on.
What differs is *which invariant survives* and *what you wanted it to be*.

## den Boer and Kim: the shuffle IS the security of a computation

den Boer's five-card trick computes `a AND b`. The inputs are encoded as a card
arrangement, then one party does a random cut (a uniform draw from the cyclic group Z_5).
Opening reveals only the cyclic-adjacency pattern, which is exactly `a AND b`, and nothing
about `a` or `b` individually. The gain from the shuffle is **input privacy**: conditioned
on the output, the opened cards are uniform over the cuts, so an observer's posterior on the
inputs collapses to the posterior given only the AND. Remove the shuffle and opening leaks
the inputs. The shuffle is not a helper here, it is the entire security argument.

Kim and Cetinkaya do the same on Z_5 but with a **biased** cut. A biased draw does not fully
average over the orbit, so a residual bias survives: input privacy with a floor. Their
contribution is to quantify that floor. This matters for you because Kim's biased-shuffle
floor is the *same mathematical object* as your `sa_eps_inf`. A shuffle that fails to reach
uniform, whether from bias (Kim) or from an intransitive group (Dic_3, S5xS5), leaves a
residual distinguishing advantage. Kim is the imperfect-mixing story on a cyclic group;
Dic_3 is the imperfect-mixing story from a fixed point.

## The three groups: same mechanism, different goal, different quality

Do S5, S5xS5, Dic_3 gain the *same thing* as den Boer and Kim? The mechanism is identical.
The goal is not.

In den Boer and Kim the surviving invariant IS the answer you want to reveal (the AND), and
the shuffle protects the inputs. In the AG secret-sharing setting the actual secret-privacy
comes from the **code** (dual distance), not the shuffle. So the shuffle is not carrying the
secret-privacy at all. What the shuffle buys there is **unlinkability of shares**: hiding
which position holds which share. The surviving invariant is a *structural* feature, and it
shows up as the anonymity floor.

By quality:

- **S5**: transitive, mixes to full uniform. Full anonymity, no surviving invariant. But
  nothing to recover either, precisely because no invariant survives to pin a secret slot.
  This is why S5 needs the mixing-rate machinery (Schreier, spectral gap): reaching uniform
  takes many rounds and you have to bound the rate.
- **S5xS5**: uniform within each factor, pile identity survives. Within-pile anonymity,
  floor = which pile. The surviving pile-invariant is what the product recovery uses.
- **Dic_3**: uniform draw, transitive on the 12 shares, fixes the secret. Within-share
  anonymity, floor = the secret position. Because it is transitive on the shares, **one**
  uniform draw already gives uniform-on-orbit. The walk is one step. None of S5's mixing-rate
  machinery is needed. The only non-trivial security content is the floor itself.

## The takeaway that ties it together

In den Boer and Kim the shuffle's surviving invariant is the *output*, and there is no
recovery side. In the AG cases the shuffle earns *share anonymity*, the secret's value is
protected elsewhere by the code, and the surviving invariant (pile, or fixed secret slot) is
exactly the structural handle that recovery needs. So the floor is not the shuffle failing at
its job. The floor is the recovery structure made visible. That is why S5 shuffles perfectly
and cannot recover, while Dic_3 shuffles with a floor and can: the very invariant that floors
the anonymity is the coordinate that recovery reads. den Boer and Kim never face this trade
because they compute a function, they do not reconstruct a hidden slot.

---

# Second pass (concrete): the shuffle does two different jobs

Follow-up after "I still cannot get it." Drops the abstraction. I think the phrase
"orbit-invariant" is what is not landing. Two concrete micro-examples that show the shuffle
doing two *different* jobs.

## Job A: den Boer. The shuffle makes a full face-up reveal safe.

Five cards in a circle: 3 hearts, 2 clubs. The inputs `a`, `b` decide the starting
arrangement. The encoding is rigged so that:

- `a AND b = 1` puts the three hearts *consecutive*.
- `a AND b = 0` puts the three hearts *not all consecutive*.

Now the random cut: rotate the circle by 0,1,2,3,4 steps, each equally likely. Then flip
*everything* face up.

- If the AND was 1, you see one of the 5 rotations of "three hearts in a row," each equally
  likely.
- If the AND was 0, you see one of the 5 rotations of a "hearts split" pattern, each equally
  likely.

You can read off consecutive-or-not, so you learn the AND. But you cannot tell which starting
`(a,b)` you had, because the cut threw away the starting offset. The inputs `(0,0)`, `(0,1)`,
`(1,0)` all collapse into the same "not consecutive" picture. **That collapse is the entire
gain.** Without the cut you would flip the cards up and read `a` and `b` directly. The shuffle
is the whole security, and it works precisely because you *do* open everything at the end.

## Job B: the AG scheme. Turn the shuffle OFF and the secret is still hidden.

Take the worked example. Secret `s = c_0`, shares `c_1..c_12` dealt to parties. Now imagine
**no shuffle at all**: share `c_3` just sits in position 3, dealt to party 3, forever.

Does party 3 learn anything about `s`? Check whether the secret column `(1,0,0)` is in the
span of party 3's column `G_3`. It is not. Party 3 learns **nothing** about the secret. That
required zero shuffling. The *code* did it.

So in the AG scheme the secret-value privacy is already complete with the shuffle switched
off. The shuffle therefore cannot be the thing that hides the secret value, because the value
is already fully hidden without it.

Then what is the shuffle for here? Only this: with no shuffle, everyone knows "position 3 is
the share belonging to curve point `T_3`, held by party 3." The shuffle randomizes *which
share sits in which position*, so an observer cannot attach that label. The shuffle hides the
**labeling**, never the **value**. And unlike den Boer, you **never** flip the secret card
face up. There is no reveal moment for the shuffle to protect. It is a pure anonymity add-on.

## The two jobs, side by side

| | den Boer / Kim | S5 / S5xS5 / Dic_3 |
|---|---|---|
| Do you open the secret at the end? | Yes, open everything | No, never |
| What hides the secret value? | The shuffle | The code (dual distance) |
| What does the shuffle do? | Makes the open safe (learn only the AND) | Anonymize which position is which |
| Turn shuffle off: | Inputs leak on open | Secret still fully hidden, only labels leak |

Same physical act both times, apply a random group element to the positions. Completely
different payoff, because one protocol opens the cards and the other never does.

## The floor, in these terms

Dic_3 can shuffle the 12 share positions among themselves fully (it is transitive there), but
it *cannot* move position 0. So one label stays pinned: everyone always knows position 0 is
the secret slot. That pinned label is the floor. Notice what it costs you: not the secret
value (the code still hides that with the shuffle off), only the *anonymity of one position's
role*, and that role was public anyway. den Boer never has a floor of this kind because he has
no held-back slot. He opens all five cards.
