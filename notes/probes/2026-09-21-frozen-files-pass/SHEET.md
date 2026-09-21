# Sheet: the barred-word pass over the frozen files, and the norm-abbreviation renames

Written 2026-09-21 against HEAD 124f950, branch `feat/tableau-extensions-probe`.
Nothing was edited, nothing was compiled, no Rocq process was started.

The frozen set is the 35 files `common.py:FROZEN_MODULES` names, resolved here
against `git ls-files '*.v'`. All 35 were scanned; every hit is listed, in
Part A (a change), in the register of Part A0 (no change, with the reason) or
in Part B (an identifier).

Scan performed, whole word and case-insensitive, over the COMMENTS of all 35
frozen files: spend/spends/spent/spending, price/prices/priced/pricing,
pay/pays/paid/paying, budget/budgets, buy/buys/bought/buying,
owe/owes/owed/owing, cost/costs/costing, currency, and a second sweep for
cheap/cheaper/expensive/afford/charge/bill/debt/invest/cash/worth/tax/toll/
fee/rent/wage/profit/revenue/credit/loan/borrow/lend/trade/sell/purchase/
bargain/economy/coin/ledger/dividend/overhead/premium/subsidy/tariff/levy.
Also, over comments AND code of the 35: "row"/"rows", "arm"/"arms",
"port"/"ports", "gate"/"gates"/"gated"/"gating",
"posit"/"posits"/"posited"/"positing", "apex", "indist", the norm
abbreviation as a capital letter with the digit one or two (plain and caret
spellings), and their lower-case forms.

Results of the barred-noun sweep: `apex` 0, `gate` and forms 0, `posit` and
forms 0, `port`/`ports` 0, `indist` 0, `arm` 1 (row A10). "row"/"rows" 72 in
the frozen files, of which 2 mean a Tableau program (row A10) and 70 mean a
table row or a trace row (register A0-R).

Counts: Part A, 38 change rows (A1 to A38) over 12 files — `pgg_raag.v` 1,
`psl211_endpoints.v` 1, `psl211_exec.v` 8, `psl211_profile.v` 3,
`pgg_algebra_syntax.v` 3, `pgg_execution_plug.v` 1, `pgg_instance.v` 11,
`pgg_session_types.v` 1, `algebraic_rigidity.v` 4, `covering_scheme.v` 1,
`pgg_collusion_bound.v` 3, `pgg_security_solver.v` 1. Part A0 register, left
alone: 70 occurrences of "row", 1 measured-time "cost", 1 "worth", 12 lines of
GL(2,q) names. Part B, 8 rename groups over 9 files, one of them (B3)
recommended for deferral. Part C, 9 risks.

Vocabulary reused from the owner's own pass `cca5e24` ("docs(comments): the
economic words for a relation replaced by the field's terms"), which fixed
these substitutions in the non-frozen twins of most sentences below:

| current | the owner's replacement, and where |
|---|---|
| the interpreter budget is X | the interpreter fuel is X (`pgl27_exec.v`) |
| within / inside the budget | within / inside the fuel (`five_card_run.v`, `psl211_alldecks.v`) |
| leaves the instance owing termination alone among the three run facts | leaves termination as the instance's only obligation among the three run facts (`pgl27_exec.v`) |
| owes no proof at all for the third | needs no proof at all for the third (`pgl27_exec.v`) |
| the whole of what this instance owes the exact X | all the exact X requires of this instance (`pgl27_tableau_*.v`) |
| the whole of what this instance owes reconstruction is Y | all reconstruction requires of this instance is Y (`psl211_alldecks.v`) |
| costs no further proof | needs no further proof (`pgl27_exec.v`) |
| pays no reduction of its own | uses no reduction of its own (`pgl27_exec.v`, `s5_*.v`) |
| pays two reductions | needs two reductions (`five_card_*.v`) |
| spends the reduction once at the profile | uses one reduction, at the profile (`five_card_*.v`) |
| both spend the instance's own vm_compute | both use the instance's own vm_compute (`pgl27_exec.v`) |
| is spent (a field of a mixin) | is used |
| spends no mixing bound | appeals to no mixing bound (`pgl27_*`, `five_card_*`) |
| costs nothing | leaves it unchanged / adds nothing / loses nothing |
| at no cost | unchanged (`psl211_alldecks.v`) |
| costs no more to terminate than | needs no more reduction to terminate than (`psl211_alldecks.v`) |
| the most expensive mistake | the mistake hardest to diagnose (`psl211_alldecks.v`) |
| the expensive one (of two proof shapes) | the slow one (`pgl27_tableau_*.v`) |
| Three costs are each why | Three timings are each why (`pgl27_tableau_*.v`) |
| the price of that idealisation is paid by Z | the loss of that idealisation is bounded by Z (`pgl27_profile.v`) |
| at a cost of 2^-40 | losing at most 2^-40 (`pgl27_mixing.v`, `psl211_mixing.v`) |
| the whole price of replacing the exact shuffle by a finite word | 2^-40 bounds the whole loss of replacing the exact shuffle by a finite word |
| buys (a consequence) | gives (`den_boer_*.v`, `psl211_alldecks_*.v`) |
| one letter of the word buys a factor 1 - gap | one letter of the word contributes a factor 1 - gap (`pgl27_*.v`, `s5_*.v`) |
| would cost it | would require of it (`psl211_reading_constancy.v`) |
| **a measured time keeps its verb** | "costs 147 s here", "costs 78.7 s in the statement alone" were KEPT (`pgl27_tableau_*.v`, `five_card_*.v`) |

That last line is the owner's own precedent and it is why rows A2 and A18 keep
one "cost" each and change the others: a verb with a measured number beside it
stays, a noun naming the expense in the abstract goes.

The replacement column gives the WORDS, run together as one paragraph.
Line breaks in it are not the layout. The applier lays the paragraph out with
`scripts/comment_pass/reflow.py`, which keeps each file's own shape: a boxed
line is exactly 80 bytes with a space before the closing delimiter, a docstring
continuation stays at four spaces, an index entry keeps its `==` column.
The one exception is A30: that block sits on a 77/78-byte grid of its own and
must not be pulled onto the 80-byte grid (see Part C, C8).

---

## Part A: comment rows

### A1 — `groups/pgg_raag.v:1042`

Declaration: `Lemma word_eval_adj_swap L (w1 w2 : pgg_word M L) : adj_swap w1 w2 -> word_eval w1 = word_eval w2.`

Current (lines 1040-1044):

```
(* Exchanging two adjacent letters that commute leaves the deck permutation
   the word evaluates to unchanged.
   This is where the raag_sigmas_comm field of the mixin is spent, and it is why
   trace classes are coarser than words while still finer than deck
   permutations. *)
```

Replacement words:

```
Exchanging two adjacent letters that commute leaves the deck permutation the
word evaluates to unchanged. This is where the raag_sigmas_comm field of the
mixin is used, and it is why trace classes are coarser than words while still
finer than deck permutations.
```

Reason: "spent" for a mixin field that a proof appeals to; the owner's word is
"used", and the sentence is unchanged otherwise.

### A2 — `instances/psl211/psl211_endpoints.v:6-15`

File header of the 900 s declaration. Three of the five hits change; "cost
568 s" stays by the measured-time precedent.

Current (lines 6-15, each line exactly 80 bytes):

```
(* One declaration, alone in its own file.  Compiling it on 2026-09-15 cost   *)
(* 568 s of vm_compute, 324 s of Qed and 898 s wall, with a resident set      *)
(* reported at 10.45 GB through make.  The same reduction run directly under  *)
(* /usr/bin/time -l as probe P1b2, in a file that also carried the            *)
(* termination lemma, reported 17.15 GB.  Budget 17 GB on a 32 GB machine.    *)
(* The cost is the twelve-card, fourteen-process interpreter trace and not    *)
(* the budget: the same reduction at fuel 380 measured 562 s and 343 s, a     *)
(* difference inside the noise.  The reduction is symbolic in the cut; were   *)
(* it enumerating the 479001600 permutations of twelve points it would not    *)
(* finish at any per-element cost.                                            *)
```

Replacement words:

```
One declaration, alone in its own file.  Compiling it on 2026-09-15 cost 568 s
of vm_compute, 324 s of Qed and 898 s wall, with a resident set reported at
10.45 GB through make.  The same reduction run directly under /usr/bin/time -l
as probe P1b2, in a file that also carried the termination lemma, reported
17.15 GB.  Allow 17 GB on a 32 GB machine.  The twelve-card, fourteen-process
interpreter trace is what takes the time, not the fuel: the same reduction at
fuel 380 measured 562 s and 343 s, a difference inside the noise.  The
reduction is symbolic in the cut; were it enumerating the 479001600
permutations of twelve points, no per-element time would make it finish.
```

Reason: the memory figure is an allowance, the second sentence names the fuel
value, and the last clause quantifies over per-element times; the measured
"cost 568 s" keeps its verb by the owner's precedent.

### A3 — `instances/psl211/psl211_exec.v:7-20`

File header, first paragraph.

Current (lines 7-20, each exactly 80 bytes):

```
(* The twelve-card chirality instance is written as a PGGAlgebraic in the     *)
(* block surface of pgg_algebra_syntax.v: two generating permutations of      *)
(* twelve card positions, the inverse-closed three-letter walk alphabet, the  *)
(* Boolean chirality secret the orbit scheme deals, and the explicit seat     *)
(* list the interpreter reads because enum 'I_12 does not reduce.  From that  *)
(* one value the framework of pgg_instance.v derives the seat interface, the  *)
(* monodromy profile and the execution plug.  The run written here is the     *)
(* dealer-dealt one: the dealer draws the chirality bit, no party commits an  *)
(* input, and the interpreter budget is psl211_fuel.  Of the three run facts  *)
(* it owes termination alone, decided by reduction at fuel 220 in 0.49 s of   *)
(* vm_compute and 0.47 s of Qed (measured 2026-09-15 with Time in place, then *)
(* removed); reconstruction follows from the coordinate law and spends no     *)
(* reduction, and the endpoint equation is stated once at the profile in      *)
(* psl211_endpoints.v.                                                        *)
```

Replacement words:

```
The twelve-card chirality instance is written as a PGGAlgebraic in the block
surface of pgg_algebra_syntax.v: two generating permutations of twelve card
positions, the inverse-closed three-letter walk alphabet, the Boolean
chirality secret the orbit scheme deals, and the explicit seat list the
interpreter reads because enum 'I_12 does not reduce.  From that one value the
framework of pgg_instance.v derives the seat interface, the monodromy profile
and the execution plug.  The run written here is the dealer-dealt one: the
dealer draws the chirality bit, no party commits an input, and the interpreter
fuel is psl211_fuel.  Of the three run facts termination is the only one it
must prove, decided by reduction at fuel 220 in 0.49 s of vm_compute and 0.47 s
of Qed (measured 2026-09-15 with Time in place, then removed); reconstruction
follows from the coordinate law and uses no reduction, and the endpoint
equation is stated once at the profile in psl211_endpoints.v.
```

Reason: three sites, each taking the owner's word for its shape: fuel for the
interpreter allowance, "the only one it must prove" for the obligation, "uses
no reduction" for the reduction.

### A4 — `instances/psl211/psl211_exec.v:34-36` (index entry)

Current:

```
(*                          instance                                          *)
(*   psl211_fuel         == the interpreter budget of the fourteen-process    *)
(*                          run                                               *)
```

Replacement words for the `psl211_fuel` entry:

```
psl211_fuel == the interpreter fuel of the fourteen-process run
```

Reason: same word as the definition's own docstring (A6) and as the owner's
`psl211_alldecks.v` index entry.

### A5 — `instances/psl211/psl211_exec.v:42-45` (index entry)

Current:

```
(*   psl211_profileE         == the derived profile is psl211_profile         *)
(*   psl211_dealt_terminates == every process of the dealt run reaches Finish *)
(*                              inside the budget                             *)
(*   profile_k_psl211_algebra == the derived privacy threshold is six         *)
```

Replacement words for the `psl211_dealt_terminates` entry:

```
psl211_dealt_terminates == every process of the dealt run reaches Finish inside the fuel
```

Reason: exactly the owner's `psl211_alldecks_terminates == every process
finishes inside the fuel`.

### A6 — `instances/psl211/psl211_exec.v:99-104`

Declaration: `Definition psl211_fuel : nat := 220.`

Current:

```
(** psl211_fuel — the interpreter budget of the fourteen-process run: the
    dealer, the verifier and the twelve seats.  220 steps, the budget the
    eight-card instance uses.  The value has only to exceed the number of
    communication rounds: the interpreter halts once no process advances, so
    a budget past that number is never spent, and that 220 exceeds it is
    decided by reduction, not by counting rounds. *)
```

Replacement words:

```
psl211_fuel — the interpreter fuel of the fourteen-process run: the dealer, the
verifier and the twelve seats.  220 steps, the fuel the eight-card instance
uses.  The value has only to exceed the number of communication rounds: the
interpreter halts once no process advances, so fuel past that number is never
used, and that 220 exceeds it is decided by reduction, not by counting rounds.
```

Reason: three occurrences of the same word for the same thing; the claim about
the eight-card instance is unchanged and is true (`pgl27_run.v:50`,
`pgl27_fuel := 220`).

### A7 — `instances/psl211/psl211_exec.v:107-111`

Declaration: `Definition psl211_dealt_params : ExecutionParams psl211_algebra := dealt_secret_params psl211_algebra psl211_fuel.`

Current:

```
(** psl211_dealt_params — the run-level data of a run that deals the
    chirality bit and recovers it: the run argument is the secret itself, no
    party commits an input, and the interpreter budget is psl211_fuel.  The
    dealer-dealt mode is what leaves the instance owing termination alone
    among the three run facts. *)
```

Replacement words (the owner's `pgl27_dealt_params` docstring, at this
instance's names):

```
psl211_dealt_params — the run-level data of a run that deals the chirality bit
and recovers it: the run argument is the secret itself, no party commits an
input, and the interpreter fuel is psl211_fuel.  The dealer-dealt mode is what
leaves termination as the instance's only obligation among the three run facts.
```

Reason: the twin docstring in `instances/pgl27/pgl27_exec.v` was rewritten in
`cca5e24` to exactly these words.

### A8 — `instances/psl211/psl211_exec.v:115-116`

Declaration: `Definition psl211_dealt_recon : instance_recon_stmt psl211_dealt_params := dealt_static_recon psl211_algebra psl211_fuel.`

Current:

```
(** psl211_dealt_recon — the reconstruction obligation, derived by the
    framework from the coordinate law alone.  No reduction is spent. *)
```

Replacement words:

```
psl211_dealt_recon — the reconstruction obligation, derived by the framework
from the coordinate law alone.  No reduction is used.
```

Reason: the owner's verb for a reduction a declaration does or does not run.

### A9 — `instances/psl211/psl211_exec.v:120-122`

Declaration: `Lemma psl211_dealt_terminates : instance_terminates_stmt psl211_dealt_params.`

Current:

```
(** psl211_dealt_terminates — every process of the dealer-dealt run reaches
    Finish inside that budget.  The reduction is symbolic in the cut, so it
    does not enumerate the group. *)
```

Replacement words:

```
psl211_dealt_terminates — every process of the dealer-dealt run reaches Finish
inside that fuel.  The reduction is symbolic in the cut, so it does not
enumerate the group.
```

Reason: one word, matching A6 and the owner's "finishes inside the fuel".

### A10 — `instances/psl211/psl211_exec.v:126-131`

Declaration: `Lemma profile_k_psl211_algebra : profile_k (instance_profile psl211_algebra) = 6.`

This one paragraph carries three separate barred items: the noun for a
constructor of the security-evidence type ("arm", line 127), and "row"/"rows"
in the published-program sense (lines 127 and 129). The replacement merges the
six-line proposal of
`notes/probes/2026-09-20-security-property-rename/prose_psl_s5.md`, last
section, with the word chosen in
`notes/probes/2026-09-20-published-rename/frozen_prose_occurrences.md`.

Current:

```
(** profile_k_psl211_algebra — the privacy threshold the derived profile
    declares is six, so every arm of a row over this algebra quantifies over
    coalitions of at most five of the twelve seats.  It is profile_k_psl211
    read at the derived profile.  The rows' witness converts the framework's
    threshold hypothesis to the numeric bound directly, and this lemma records
    the number that conversion relies on. *)
```

Replacement words:

```
profile_k_psl211_algebra — the privacy threshold the derived profile declares
is six, so the security proposition of every program over this algebra
quantifies over coalitions of at most five of the twelve seats.  It is
profile_k_psl211 read at the derived profile.  The programs' witness converts
the framework's threshold hypothesis to the numeric bound directly, and this
lemma records the number that conversion relies on.
```

Reason: a Tableau value is a program, a program certifies a security property,
and what quantifies over a coalition is the proposition; the witness meant is
`psl211_exact_witness`, which the published programs of
`psl211_tableau_analysis_bridged.v` carry and no manifest path holds.

### A11 — `instances/psl211/psl211_profile.v:75-80`

Declaration: `Lemma psl211_se_exact (s : 'I_12) : var_dist (fdistmap (fun sigma : {perm 'I_12} => sigma s) psl211_rho_dist) (fdist_uniform (card_ord 12)) = 0%R.`

Current:

```
(** psl211_se_exact — the single-card pushforward of the uniform shuffle is
    at variation distance zero from uniform, not merely close to it.  This is
    the exact certificate the bundle below carries: at one card position the
    idealised shuffle has no error to price, so every epsilon in this
    instance's marginal layer is zero and the only price paid anywhere is the
    2^-40 of psl211_word_mixing for the realistic word shuffle. *)
```

Replacement words:

```
psl211_se_exact — the single-card pushforward of the uniform shuffle is at
variation distance zero from uniform, not merely close to it.  This is the
exact certificate the bundle below carries: at one card position the idealised
shuffle has no error at all, so every epsilon in this instance's marginal layer
is zero and the only loss anywhere is the one psl211_word_mixing bounds by
2^-40 for the realistic word shuffle.
```

Reason: `psl211_word_mixing` (`psl211_mixing.v:545`) states `var_dist ... <=
2^-40`, a bound on a loss and not the loss itself, so the sentence names the
loss and says the number bounds it.

Note for the auditor: the reminder note calls this sentence a word-for-word
twin of one already rewritten in `pgl27_profile.v`. It is not. `pgl27_profile.v`
has no counterpart of it at all; its `pgl27_se_exact` docstring is two lines
("the single-card pushforward is at variational distance zero from uniform").
Only A12 has a real twin. See "What could not be settled", item 1.

### A12 — `instances/psl211/psl211_profile.v:98-103`

Declaration: `Definition psl211_marginal_bound : ShuffleMarginalBound R psl211_M := @MkShuffleMarginalBound R psl211_M 0 0%R psl211_rho_dist psl211_sw_bound.`

Current:

```
(** psl211_marginal_bound — the marginal bound at epsilon = 0: single-card
    perfect uniformity of the PSL(2,11) shuffle, carrying word length 0,
    the uniform shuffle distribution and its per-position bound. Word
    length 0 records that this model does no word shuffling at all: the
    cut is drawn from the group itself, and the price of that idealisation
    is paid by psl211_word_mixing, not here. *)
```

Replacement words:

```
psl211_marginal_bound — the marginal bound at epsilon = 0: single-card perfect
uniformity of the PSL(2,11) shuffle, carrying word length 0, the uniform
shuffle distribution and its per-position bound. Word length 0 records that
this model does no word shuffling at all: the cut is drawn from the group
itself, and the loss of that idealisation is bounded by psl211_word_mixing,
not here.
```

Reason: the twin sentence in `instances/pgl27/pgl27_profile.v:99` was rewritten
in `cca5e24` to exactly these words, at that instance's name.

### A13 — `instances/psl211/psl211_profile.v:126-133`

Declaration: `Lemma profile_k_psl211 : profile_k psl211_profile = 6.`

Current:

```
(** profile_k_psl211 — the PSL(2,11) plug's privacy threshold is six:
    coalitions of at most five card positions are private. The threshold
    is the scheme's and not the group's. PSL(2,11) is only 2-transitive
    on the twelve positions, so it fixes no arbitrary five-set; the bound
    comes from the two Steiner systems meeting every five-set in the same
    block patterns with the same multiplicities (psl211_count_okT).
    Two-transitivity buys the single-card marginal above and nothing
    about this threshold. *)
```

Replacement words:

```
profile_k_psl211 — the PSL(2,11) plug's privacy threshold is six: coalitions of
at most five card positions are private. The threshold is the scheme's and not
the group's. PSL(2,11) is only 2-transitive on the twelve positions, so it
fixes no arbitrary five-set; the bound comes from the two Steiner systems
meeting every five-set in the same block patterns with the same multiplicities
(psl211_count_okT). Two-transitivity gives the single-card marginal above and
nothing about this threshold.
```

Reason: "buys" to "gives" is the owner's substitution for this shape, and the
claim is unchanged: `psl211_point_uniform` is proved from
`psl211_2transitive`, the threshold from the Steiner count.

Note for the auditor: this sentence too has no twin in `pgl27_profile.v`; the
`profile_k_pgl27` docstring there is two lines and says nothing about
transitivity. See "What could not be settled", item 1.

### A14 — `protocol/pgg_algebra_syntax.v:41-48`

File header paragraph about the block surface's keywords.

Current (each line exactly 80 bytes):

```
(* The block spends four identifiers as global keywords in every file that    *)
(* requires this one: encode, read, private and shuffled_by. Each of them     *)
(* follows a slot in some rule, which is what makes a token a keyword; the    *)
(* tokens mount, walk, along, seat, players, secret, deal, cache, seats and   *)
(* pgg_rho follow a literal and stay identifiers. The leading token algebra   *)
(* stays an identifier too: measured on 2026-09-14 it can be declared and     *)
(* then used bare in a term, in an application, as a binder and as a record   *)
(* field, because the literal that follows it in every rule is not a slot.    *)
```

Replacement words (only the first four words change):

```
The block reserves four identifiers as global keywords in every file that
requires this one: encode, read, private and shuffled_by. Each of them follows
a slot in some rule, which is what makes a token a keyword; the tokens mount,
walk, along, seat, players, secret, deal, cache, seats and pgg_rho follow a
literal and stay identifiers. The leading token algebra stays an identifier
too: measured on 2026-09-14 it can be declared and then used bare in a term, in
an application, as a binder and as a record field, because the literal that
follows it in every rule is not a slot.
```

Reason: what a keyword does to a token is reserve it; "reserves" states the
relation and keeps the sentence's meaning exactly.

### A15 — `protocol/pgg_algebra_syntax.v:80-84`

Declaration: `Definition ord_monodromy (m n : nat) (gens : m.+1.-tuple {perm 'I_n.+2}) (T : nat) (Hc : T = n.+2) : {perm 'I_n.+2} -> {perm 'I_T} := ...`

Current:

```
(* The shuffle action on share indices of an instance whose shares are the
   deck positions: the deck action, transported along the share-count equation.
   It is the map a block writes into pga_monodromy, and the reason an instance
   in this surface owes no relation between share indices and cards beyond the
   share count itself. *)
```

Replacement words:

```
The shuffle action on share indices of an instance whose shares are the deck
positions: the deck action, transported along the share-count equation. It is
the map a block writes into pga_monodromy, and the reason an instance in this
surface needs no relation between share indices and cards beyond the share
count itself.
```

Reason: the owner's substitution "owes no proof at all" to "needs no proof at
all", at this sentence's object.

### A16 — `protocol/pgg_algebra_syntax.v:146-151`

Declaration: `Definition pinned_scheme (secretT shareT : Type) (S : ThresholdScheme secretT shareT) ...`

Current:

```
(* The scheme itself, with its encoding, its reconstruction and its privacy
   obligation checked by conversion against the three terms written in the
   block.
   The three equations are the whole content: the result is the scheme
   unchanged, and what the combinator buys is that a block naming a different
   encoding from the scheme's own is rejected where it is written. *)
```

Replacement words (the blank-less two-part shape of the current comment is
kept; only "buys" changes):

```
The scheme itself, with its encoding, its reconstruction and its privacy
obligation checked by conversion against the three terms written in the block.
The three equations are the whole content: the result is the scheme unchanged,
and what the combinator gives is that a block naming a different encoding from
the scheme's own is rejected where it is written.
```

Reason: "buys" to "gives", the owner's substitution for a consequence.

### A17 — `protocol/pgg_execution_plug.v:85-87`

Field of the `ExecutionPlug` record: `ep_fuel : nat ;`

Current:

```
    (* ep_fuel selects the interpreter evaluation budget used by exec_run.
       Replacing a sufficient fuel value by another sufficient one does not
       define a different algebraic profile. *)
```

Replacement words:

```
ep_fuel selects the interpreter evaluation fuel used by exec_run. Replacing a
sufficient fuel value by another sufficient one does not define a different
algebraic profile.
```

Reason: one word, and the field's own name already is the concept; the second
sentence of the same comment already says "fuel value".

### A18 — `protocol/pgg_instance.v:18-34`

File header paragraph about the three run obligations. Four hits; three
change, and the measured "8.8 s" sentence carries no barred word.

Current (each line exactly 80 bytes):

```
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
```

Replacement words:

```
One of the three run obligations is discharged here for every instance, and a
second is replaced by an equivalent that reduces faster. generic_static_recon
proves that decoding the static endpoint reading returns the dealt value, from
the reconstruction invariance of the plug's scheme and a single coordinate
hypothesis; dealt_static_recon supplies that hypothesis from pga_coordE, so a
dealer-dealt instance needs no reconstruction proof at all. profile_endpointsE
leaves the endpoint obligation with the instance and only makes it faster: it
carries the endpoint equation from a statement whose content readout is a
variable to the statement about the dealt readout. The equation is decided by
reduction, and it is reduction of a concrete dealt card that makes that slow,
or impossible where an encoding passes through an opaque insub and never
reduces at all. Keeping the readout a variable removes the dealt card from the
reduction, so one reduction per profile replaces one reduction per plug:
measured on 2026-09-14, the PGL(2,7) form closes by vm_compute in 8.8 s with a
3.8 s Qed, and its dealt instance follows by instantiation with no reduction of
its own.
```

Reason: the paragraph is about reduction time throughout, so each of the three
sites takes the plain comparative; "the slow one" is the owner's own
replacement for "the expensive one" in the same sense.

### A19 — `protocol/pgg_instance.v:54-57`

File header, the paragraph naming what the framework leaves to an instance.

Current (each line exactly 80 bytes):

```
(* What an instance owes is termination, instance_terminates_stmt, which has  *)
(* no route through the algebra, and one reduction proof at its own profile:  *)
(* profile_endpoints_stmt in the sharing family, and                          *)
(* profile_commit_endpoints_stmt in the input family.                         *)
```

Replacement words:

```
What an instance must supply is termination, instance_terminates_stmt, which
has no route through the algebra, and one reduction proof at its own profile:
profile_endpoints_stmt in the sharing family, and
profile_commit_endpoints_stmt in the input family.
```

Reason: "must supply" carries both conjuncts (a proof of termination and a
reduction proof), which "must prove" would not.

### A20 — `protocol/pgg_instance.v:303-304`

Field of the `ExecutionParams` record: `ex_fuel : nat ;`

Current:

```
  (* ex_fuel is the interpreter budget. Replacing a sufficient budget by
     another sufficient one leaves every statement below unchanged. *)
```

Replacement words:

```
ex_fuel is the interpreter fuel. Replacing a sufficient fuel value by another
sufficient one leaves every statement below unchanged.
```

Reason: the same two words as A17's field comment on `ep_fuel`, which this
field feeds.

### A21 — `protocol/pgg_instance.v:312-319`

Declaration: `Definition instance_exec (A : PGGAlgebraic) (E : ExecutionParams A) ...`

Current:

```
(* The plug a parameter record builds: params_exec at the record's own mode,
   readout and fuel. Four of the six fields reach the plug, ex_inputT as its
   run argument type and ex_content, ex_commits and ex_fuel as its readout,
   process list and budget. ex_content_obs and ex_expected do not, because they
   are not execution data, and they enter at instance_observed. Routing the
   plug through the record rather than letting an instance call params_exec is
   what stops a run whose interpreter readout disagrees with the static
   observation its security statements are made about. *)
```

Replacement words:

```
The plug a parameter record builds: params_exec at the record's own mode,
readout and fuel. Four of the six fields reach the plug, ex_inputT as its run
argument type and ex_content, ex_commits and ex_fuel as its readout, process
list and fuel. ex_content_obs and ex_expected do not, because they are not
execution data, and they enter at instance_observed. Routing the plug through
the record rather than letting an instance call params_exec is what stops a run
whose interpreter readout disagrees with the static observation its security
statements are made about.
```

Reason: the three-item list names what each field becomes in the plug, and the
plug field is `ep_fuel`; the same paragraph already says "readout and fuel" in
its first sentence.

### A22 — `protocol/pgg_instance.v:362-365`

Declaration: `Definition instance_observed (A : PGGAlgebraic) (E : ExecutionParams A) (Ht : ...) (He : ...) (Hr : ...) : OE.ObservedExecution := ...`

Current:

```
(* The observed execution of a parameter record, packed with its three run
   facts. This is the value every downstream analysis consumes, so supplying
   an algebra, a parameter record and the three proofs is the whole of what
   an instance owes the framework. *)
```

Replacement words:

```
The observed execution of a parameter record, packed with its three run facts.
This is the value every downstream analysis consumes, so supplying an algebra,
a parameter record and the three proofs is all the framework requires of an
instance.
```

Reason: the owner's rewriting of "the whole of what this instance owes X" to
"all X requires of this instance".

### A23 — `protocol/pgg_instance.v:452-458`

Declaration: `Definition supplied_input_params (A : PGGAlgebraic) (inputT : Type) (layout : ...) (expected : ...) (fuel : nat) : ExecutionParams A := ...`

Current:

```
(* The sharing family's parameters at a supplied layout: no party commits, the
   dealer lays the cards itself from the layout the run argument names, and
   the value the run recovers is the one written beside it. That value is a
   reading of the run argument and not a function of any committer's input,
   which is what keeps this mode in the sharing family. The sharing claim is
   not an argument here, which is what leaves such a run owing a
   reconstruction obligation of its own. *)
```

Replacement words:

```
The sharing family's parameters at a supplied layout: no party commits, the
dealer lays the cards itself from the layout the run argument names, and the
value the run recovers is the one written beside it. That value is a reading of
the run argument and not a function of any committer's input, which is what
keeps this mode in the sharing family. The sharing claim is not an argument
here, which is what leaves such a run with a reconstruction obligation of its
own.
```

Reason: "owing a" to "with a" removes the word and changes nothing else.

### A24 — `protocol/pgg_instance.v:689-692`

Declaration: `Lemma encoded_static_recon (A : PGGAlgebraic) (inputT : Type) ... : instance_recon_stmt (encoded_input_params ...).`

Current:

```
(* The reconstruction obligation of an input-family run, discharged from the
   sharing claim written in its own parameter statement. Every argument occurs
   in the conclusion, so such a run owes no reconstruction proof beyond the
   encoding it already named. *)
```

Replacement words:

```
The reconstruction obligation of an input-family run, discharged from the
sharing claim written in its own parameter statement. Every argument occurs in
the conclusion, so such a run needs no reconstruction proof beyond the encoding
it already named.
```

Reason: the owner's "owes no proof" to "needs no proof".

### A25 — `protocol/pgg_instance.v:707-709`

Declaration: `Arguments encoded_static_recon {A inputT f layout Hv dec procs fuel} x w0.`

Current:

```
(* The eight arguments of encoded_input_params occur in the statement the
   obligation is made about, so the lemma is written unapplied where the
   obligation is owed. *)
```

Replacement words:

```
The eight arguments of encoded_input_params occur in the statement the
obligation is made about, so the lemma is written unapplied where the
obligation is discharged.
```

Reason: what the `Arguments` line achieves is that the name alone closes the
goal at the site where the obligation is discharged, which is what the
sentence means.

### A26 — `protocol/pgg_instance.v:753-756`

Declaration: `Lemma profile_endpointsE (A : PGGAlgebraic) (fuel : nat) : profile_endpoints_stmt A fuel -> instance_endpoints_stmt (dealt_secret_params A fuel).`

Current:

```
(* The endpoint obligation of a dealer-dealt run, read off the profile's own
   abstract-readout equation. Instantiating the variable readout at
   dealt_content gives the dealt direct computation by conversion, so the
   instance-level statement costs no reduction of its own. *)
```

Replacement words:

```
The endpoint obligation of a dealer-dealt run, read off the profile's own
abstract-readout equation. Instantiating the variable readout at dealt_content
gives the dealt direct computation by conversion, so the instance-level
statement uses no reduction of its own.
```

Reason: the owner's "pays no reduction of its own" to "uses no reduction of its
own", in the twin sentences of `pgl27_exec.v` and the S_5 files.

### A27 — `protocol/pgg_instance.v:762-766`

Declaration: `Lemma supplied_endpointsE (A : PGGAlgebraic) (inputT : Type) (layout : ...) (expected : ...) (fuel : nat) : profile_endpoints_stmt A fuel -> instance_endpoints_stmt (supplied_input_params ...).`

Current:

```
(* The endpoint obligation of a sharing-family run at a supplied layout, read
   off the same abstract-readout equation. The profile statement already
   quantifies over the content readout, so instantiating it at the supplied
   layout costs the run no reduction of its own, and the two modes of the
   sharing family share the profile's one decision. *)
```

Replacement words:

```
The endpoint obligation of a sharing-family run at a supplied layout, read off
the same abstract-readout equation. The profile statement already quantifies
over the content readout, so instantiating it at the supplied layout needs no
reduction of the run's own, and the two modes of the sharing family share the
profile's one decision.
```

Reason: same substitution as A26, with the possessive moved so the clause keeps
its subject.

### A28 — `protocol/pgg_instance.v:797-802`

Declaration: `Lemma encoded_endpointsE (A : PGGAlgebraic) (inputT : Type) ...`

Current:

```
(* The endpoint obligation of an input-family run, from the profile's
   commit-mode equation and the single fact that decoding the payload list
   returns the input the committers hold. That decoding fact is the whole of
   what an instance adds: the reduction is spent once at the profile, and this
   lemma is what turns the layout the dealer assembled from the payloads into
   the layout the direct computation reads. *)
```

Replacement words:

```
The endpoint obligation of an input-family run, from the profile's commit-mode
equation and the single fact that decoding the payload list returns the input
the committers hold. That decoding fact is the whole of what an instance adds:
the reduction runs once, at the profile, and this lemma is what turns the
layout the dealer assembled from the payloads into the layout the direct
computation reads.
```

Reason: the owner rewrote the twin sentence in `five_card_run.v` to "uses one
reduction, at the profile"; here the subject is the reduction, so it runs once,
at the profile.

### A29 — `protocol/pgg_session_types.v:110-112`

Declaration: `Definition PGGRet {party : nat} (x : data) : @sproc pgg_dtype data party 2 senv_end := SRet x.`

Current:

```
(* Types a process's final return of data x under the empty session
   environment: every send this process owed has already been matched, so
   nothing remains to type-check downstream of it. *)
```

Replacement words:

```
Types a process's final return of data x under the empty session environment:
every send this process had to make has already been matched, so nothing
remains to type-check downstream of it.
```

Reason: what the empty environment records is that no send of this process is
still unmatched; "had to make" says that without the debt metaphor.

### A30 — `reconstruct/algebraic_rigidity.v:119-125`

Comment block above the `SecurityAsymptotic` record. The norm abbreviation in
its caret spelling, line 125.

Current (a run of one-line comments on a 77/78-byte grid, NOT the 80-byte grid
of the rest of the tree; see C8):

```
(* sa_eps_inf is the constant variation-distance floor: the bound is        *)
(*   var_dist (sigma s) uniform <= sa_eps_inf + sqrt(N) * (1 - gap)^L      *)
(* For irreducible Schreier walks (e.g. S_5) sa_eps_inf = 0 and the bound  *)
(* decays to 0. For reducible walks (e.g. S_5 x S_5 with pile-disjoint     *)
(* generators) the actual stationary distribution is uniform on the orbit, *)
(* and the gap to fdist_uniform is the constant sa_eps_inf (1 in infotheo's *)
(* un-halved L^1 var_dist convention; 1/2 in standard TV).                  *)
```

Replacement words, for the last sentence only (lines 124-125); the five lines
above it do not change:

```
and the gap to fdist_uniform is the constant sa_eps_inf (1 in infotheo's
var_dist, the un-halved sum of absolute differences; 1/2 in the standard total
variation of the literature).
```

Reason: `var_dist` is the sum of absolute differences, twice the total
variation of the literature; spelling that out removes the abbreviation and
makes the factor of two explicit where the sentence is about exactly that.

### A31 — `reconstruct/algebraic_rigidity.v:155-156`

Field of the `ShuffleMarginalBound` record: `sw_bound_eps : R;`

Current:

```
  (* sw_bound_eps is the stated full-L1 upper bound on one endpoint marginal.
     It is a per-position quantity, not a coalition-view distance. *)
```

Replacement words (the sentence suggested in
`notes/probes/2026-09-20-barred-words-pass/frozen_and_code_residue.md`, with
the second sentence kept):

```
sw_bound_eps is the stated upper bound on one endpoint marginal, in the sum of
absolute differences with no factor one half. It is a per-position quantity,
not a coalition-view distance.
```

Reason: the field is the right-hand side of `var_dist ... <= sw_bound_eps`, so
naming the measure by what it computes removes the abbreviation and states the
convention the record uses.

### A32 — `reconstruct/algebraic_rigidity.v:192-195`

Comment above the discussion of `cs_gap` (not attached to a declaration; it
heads the block that ends at the `Operationalising` sentence). The paragraph
continues past line 195; only line 194 changes.

Current (lines 192-195):

```
(* The cs_gap field of [tw_covering] (ts_T <= ts_k + 2 * cd_genus,
   from cover_tradeoff.v:gap_bound) is a privacy-vs-reveal gap, not
   a dropout-tolerance budget. Reconstruction in every concrete
   threshold scheme used here consumes the FULL share tuple:
```

Replacement words for the first sentence (the rest of the comment, from
"Reconstruction in every concrete" to its closing delimiter, is untouched):

```
The cs_gap field of [tw_covering] (ts_T <= ts_k + 2 * cd_genus, from
cover_tradeoff.v:gap_bound) is a privacy-vs-reveal gap, not a
dropout-tolerance allowance.
```

Reason: one word; the coqdoc bracket `[tw_covering]` and the reference
`cover_tradeoff.v:gap_bound` must survive verbatim (see C6).

### A33 — `reconstruct/algebraic_rigidity.v:388-392`

Declaration: `Lemma ar_gap_bound : let cs := tw_covering (ar_threshold ar) in ts_T (cs_scheme cs) - ts_k (cs_scheme cs) <= 2 * cd_genus (cs_data cs).`

Current:

```
(** The reconstruction/privacy gap ts_T - ts_k is at most twice the genus,
    unconditionally, whichever regime ar_genus_gap_dichotomy places the
    scheme in. This is the numeric form of the threshold leg of algebraic
    rigidity: genus is not just a classification but a literal price cap on
    the gap. *)
```

Replacement words:

```
The reconstruction/privacy gap ts_T - ts_k is at most twice the genus,
unconditionally, whichever regime ar_genus_gap_dichotomy places the scheme in.
This is the numeric form of the threshold leg of algebraic rigidity: genus is
not just a classification, and twice it is a literal upper bound on the gap.
```

Reason: the statement bounds the gap by twice the genus, not by the genus, so
the replacement is type-honest where the current sentence is loose.

### A34 — `reconstruct/covering_scheme.v:187-191`

Declaration: `Lemma gap_bound (cs : CoveringScheme M) : ts_T (cs_scheme cs) - ts_k (cs_scheme cs) <= 2 * cd_genus (cs_data cs).`

Current:

```
(* The reconstruction/privacy gap ts_T - ts_k never exceeds twice the
   genus, restated in subtraction form directly from cs_gap. This is the
   CoveringScheme-level statement of the same price cap that
   algebraic_rigidity.v's ar_gap_bound exposes at the AlgebraicRigidity
   level. *)
```

Replacement words:

```
The reconstruction/privacy gap ts_T - ts_k never exceeds twice the genus,
restated in subtraction form directly from cs_gap. This is the
CoveringScheme-level statement of the same upper bound that
algebraic_rigidity.v's ar_gap_bound exposes at the AlgebraicRigidity level.
```

Reason: the same two declarations, so the same word as A33; one word changes.

### A35 — `security/pgg_collusion_bound.v:159-164`

Declaration: `Lemma var_dist_uniform_supp : var_dist (@fdist_uniform_supp R A C card_C_gt0) (fdist_uniform card_A) = 2%:R * k%:R / #|A|%:R.`

Current:

```
(** var_dist_uniform_supp — the TV distance from uniform-on-a-support-C to
    the fully uniform distribution on A is 2k / |A|, where k = |A| - |C| is
    the size of the excluded complement. This is the generic price, in TV
    distance, of shrinking a uniform distribution's support by k elements;
    the file's coalition bounds cash it in wherever a coalition narrows an
    ideal posterior's support. *)
```

Replacement words:

```
var_dist_uniform_supp — the variation distance from uniform-on-a-support-C to
the fully uniform distribution on A is 2k / |A|, where k = |A| - |C| is the
size of the excluded complement. This is the generic loss, in variation
distance, of shrinking a uniform distribution's support by k elements; the
file's coalition bounds use it wherever a coalition narrows an ideal
posterior's support.
```

Reason: "price" and "cash it in" both go; and since the word for the measure
had to be written twice anyway, both say "variation distance", because
`var_dist` is twice the total variation of the literature and the equality
proved here is `2k/|A|` in `var_dist`. Flag for the auditor: renaming "TV
distance" is a correction beyond the barred word, made because the sentence had
to be rewritten at that exact spot; if the auditor prefers the minimal edit,
keep "TV" in both places and change only "price" to "loss" and "cash it in" to
"use it". "cash it in" is also a judgement call: it is not on the owner's word
list, but it is the same metaphor.

### A36 — `security/pgg_collusion_bound.v:464-470`

Declaration: `Theorem collusion_bound_conditional : var_dist adversary_posterior full_uniform <= epsilon + 2%:R * T'%:R / N%:R.`

Current:

```
(** collusion_bound_conditional — the coalition's conditional posterior over
    the unobserved card position's value is within epsilon + 2T'/N of
    fully uniform, where epsilon is the DPI-derived distance to the ideal
    posterior conditional on dpi_bound, and
    2T'/N is the unconditional TV price of that ideal posterior itself
    being uniform only over the N - T' card positions the coalition has
    not observed. *)
```

Replacement words:

```
collusion_bound_conditional — the coalition's conditional posterior over the
unobserved card position's value is within epsilon + 2T'/N of fully uniform,
where epsilon is the DPI-derived distance to the ideal posterior conditional on
dpi_bound, and 2T'/N is the unconditional variation distance from that ideal
posterior, uniform only over the N - T' card positions the coalition has not
observed, to the fully uniform law.
```

Reason: the proof reads `2T'/N` off `var_dist_uniform_supp` as an equality, so
it is that variation distance exactly; and the two summands are now
each labelled, the first assumption-conditional (on `dpi_bound`), the second
unconditional, as the current sentence already says.

### A37 — `security/pgg_security_solver.v:71-75`

Declaration: `Definition solve_L (Tg N eps_n eps_d : nat) : option nat := solve_L_aux Tg N eps_n eps_d 100 1.`

Current:

```
(* Wraps solve_L_aux with a fixed fuel budget of 100: the smallest L such
   that epsilon_endpoint_rat Tg N L <= eps_n/eps_d, or None if no such L
   is found within 100 steps.  The search that solve's FixEps branch
   performs to turn a dealer's target epsilon into a concrete word length,
   starting at L = 1. *)
```

Replacement words:

```
Wraps solve_L_aux with a fixed fuel of 100: the smallest L such that
epsilon_endpoint_rat Tg N L <= eps_n/eps_d, or None if no such L is found
within 100 steps.  The search that solve's FixEps branch performs to turn a
dealer's target epsilon into a concrete word length, starting at L = 1.
```

Reason: one word deleted; `solve_L_aux`'s own argument is called `fuel`.

### A38 — `security/pgg_collusion_bound.v:388-392` (OPTIONAL)

Declaration: `Theorem collusion_bound_unconditional : var_dist adversary_marginal target_uniform <= epsilon.`

Current:

```
(* The unconditional bound: pushing Assumption 1's group-level gap epsilon
   through the endpoint-evaluation map (the data processing inequality
   above) gives the same epsilon for the coalition's marginal at a single
   card position, with no overhead from the coalition's other
   observations. *)
```

Replacement words:

```
The unconditional bound: pushing Assumption 1's group-level gap epsilon through
the endpoint-evaluation map (the data processing inequality above) gives the
same epsilon for the coalition's marginal at a single card position, with no
extra term from the coalition's other observations.
```

Reason: "overhead" is not on the owner's list; it is offered because the
sentence's meaning is exactly that the bound has no second summand, and the
plain word says so. Auditor's call.

---

## Part A0: the register of hits left alone, with the reason

### A0-R — "row"/"rows" in the frozen files, 70 occurrences, NO EDIT

Every one is a table row, a matrix-like trace row, or the row of a
permutation table, never a Tableau program and never a manifest path. The two
that are not are row A10.

| file | count | lines | what the word means |
|---|---|---|---|
| `instances/psl211/psl211_blocks.v` | 16 | 9, 338, 339, 345, 407, 421, 425 (x2), 449 (x4), 459, 462, 502, 505 | a row of a Steiner block table: one ascending six-list of the 132 |
| `instances/psl211/psl211_closure.v` | 8 | 13, 46, 104, 109, 166, 339, 393, 402 | a row of the alphabet permutation table, and the 660-state enumeration |
| `instances/psl211/psl211_orbit.v` | 29 | 28, 45, 64, 100, 132, 142, 151, 162, 172, 173, 190, 305 (x2), 393, 404, 405 (x2), 407, 412, 427, 856, 915, 994, 1139, 1161, 1165 (x2), 1214, 1232 | a block-table row, chiefly "the representative row" of a Steiner system |
| `protocol/pgg_execution_plug.v` | 9 | 183, 189, 196, 205, 213 (x2), 221 (x2), 231 | an interpreter-trace row, the message log a process identifier indexes |
| `protocol/pgg_observed_execution.v` | 8 | 18, 20 (x2), 234, 238 (x2), 262, 279 | the same trace rows, at the extractors specialised to the package |

This reproduces the survey in
`notes/probes/2026-09-20-published-rename/frozen_prose_occurrences.md` and
agrees with it exactly, 72 = 70 + 2.

### A0-M — the measured-time verb, 1 occurrence, NO EDIT

`instances/psl211/psl211_endpoints.v:6`, "Compiling it on 2026-09-15 cost
568 s of vm_compute". Kept inside row A2 by the owner's own precedent in
`cca5e24`, where "costs 147 s here against reflexivity's 0.07 s" and "costs
78.7 s in the statement alone" were left standing while every abstract use of
the word was replaced. If the auditor overrules the precedent, the replacement
is "Compiling it on 2026-09-15 took 568 s of vm_compute, 324 s of Qed and 898 s
wall".

### A0-W — "worth", 1 occurrence, NO EDIT

`security/pgg_collusion_bound.v:12`: "What this law is worth as an Assumption-1
input depends on word-eval injectivity". Not on the owner's list, and the sense
is the ordinary one of how much a hypothesis yields, not a transaction.
Replacement if wanted: "What this law gives as an Assumption-1 input depends on
word-eval injectivity".

### A0-N — the norm abbreviation in the group names, 13 lines, NO EDIT

`reconstruct/pgl_bound.v` lines 12, 13, 14, 17, 18, 19, 20, 78, 96, 155, 207,
211 carry `gl2`, `pgl2`, `scalar_gl2`, `card_gl2`, `card_scalar_gl2`,
`card_pgl2`, `scalar_gl2_normal`. The "l2" there is the 2 of GL(2,F_q) and
PGL(2,F_q), a matrix size, not a norm. A scan that reads the substring will
flag them; they are innocent.

### A0-S — the barred nouns, 0 occurrences outside A10

`apex`, `gate`/`gates`/`gated`/`gating`, `posit`/`posits`/`posited`/`positing`,
`port`/`ports`, `indist`: zero hits in the comments or the code of all 35
frozen files. `arm`: one hit, `instances/psl211/psl211_exec.v:127`, which is
row A10.

### A0-E — economic words already absent

`currency`, `buy`, `bought`, `buying`, `owe`, `spending`, `pricing`, `priced`,
`budgets`, `paying`: zero hits in the frozen files. The forms that do occur are
exactly the 49 + 4 of
`notes/probes/2026-09-20-economic-words-pass/frozen_occurrences.md` and its
addendum; my independent scan found the same set and no more, plus "cash"
(A35), "worth" (A0-W) and "overhead" (A38), which that record's word list did
not carry.

---

## Part B: identifier rows

The owner reads a variable named with the capital letter L and the digit one
or two as the barred norm abbreviation. Whole-tree inventory of every
identifier that spells it, tracked `.v`, outside `notes/` and `legacy/`:

| identifier | occurrences | files | judgement |
|---|---|---|---|
| `L1` / `L2` as binders | 66 | `pgg_schreier.v`, `pgg_schreier_weighted.v`, `pgl27_orbit.v`, `psl211_alldecks.v`, `psl211_orbit.v` | rename, rows B1, B4-B7 |
| `l1` / `l2` as binders | 6 + 10 | `transitivity_privacy.v`, `smc_interpreter.v` | rename B2; B3 recommended for deferral |
| `s5_nt_L1` / `L2` / `L3` | 3 + 3 + 3 | `pgg_raag_s5.v`, `rigidity_s5_instance.v` | rename, row B8 |
| `psl1` / `psl2`, `Hpsl1` / `Hpsl2` | 6 + 4 | `smc_interpreter.v` | follow B3 or not at all |
| `gl2`, `pgl2`, `scalar_gl2`, `card_gl2`, `card_scalar_gl2`, `card_pgl2` | 46 | `reconstruct/pgl_bound.v`, `instances/pgl27/*` | INNOCENT: the 2 of GL(2,q) and PGL(2,q) |
| `card_bool2`, `five_card_card_bool2` | 19 | `instances/denboer1989/*`, `instances/kim2025/*` | INNOCENT: the cardinality of `bool`, which is 2 |
| `pgl27_gen_val1`, `pgl27_gen_val2` | 5 | `instances/pgl27/pgl27_group.v` | INNOCENT: the first and second generator, no L |
| `mul1r` and the rest of the MathComp `*1*`/`*2*` names | many | everywhere | INNOCENT: library names |

No `.tex` file in `paper/`, `paper-wadt2026/` or
`paper-wadt2026-baseline-application/` mentions any of the names below; checked
with `git grep -n -E "s5_nt_L|security_monotone|schreier_epsilon_decreasing|list_to_set_inj|nclass_perm|rstep_disjoint" -- '*.tex'`, zero hits. Nothing in Part B
therefore reaches a paper.

Naming chosen throughout: **`L` and `L'`** where the two objects are the file's
own `L` (a code list in the orbit files, a word length in the Schreier files),
and **`i` and `j`** where they are ordinals indexing a tuple. Both are
MathComp's own conventions, both avoid the digit, and neither shadows a section
variable in the file it lands in.

### B1 — `instances/psl211/psl211_orbit.v` (FROZEN)

`L1 L2` to `L L'`. Bound variables of one `Local Lemma`, plus one `Arguments`
line and two intro patterns. `Local`, so no other file sees the name; the
lemma's own name does not change.

| line | current | new |
|---|---|---|
| 842 | `Local Lemma list_to_set_inj (L1 L2 : seq nat) :` | `Local Lemma list_to_set_inj (L L' : seq nat) :` |
| 843 | `  sorted ltn L1 -> all (fun n => (n < 12)%N) L1 ->` | `  sorted ltn L -> all (fun n => (n < 12)%N) L ->` |
| 844 | `  sorted ltn L2 -> all (fun n => (n < 12)%N) L2 ->` | `  sorted ltn L' -> all (fun n => (n < 12)%N) L' ->` |
| 845 | `  psl211_list_to_set L1 = psl211_list_to_set L2 -> L1 = L2.` | `  psl211_list_to_set L = psl211_list_to_set L' -> L = L'.` |
| 851 | `Arguments list_to_set_inj [L1 L2].` | `Arguments list_to_set_inj [L L'].` |
| 871 | `    move=> L1 L2; rewrite !mem_filter => /andP[_ H1] /andP[_ H2].` | `    move=> L L'; rewrite !mem_filter => /andP[_ H1] /andP[_ H2].` |
| 1028 | `    move=> L1 L2; rewrite !mem_filter => /andP[_ H1] /andP[_ H2].` | `    move=> L L'; rewrite !mem_filter => /andP[_ H1] /andP[_ H2].` |

Totals: 8 occurrences of `L1`, 8 of `L2`, all in code; no comment in this file
mirrors them. Scope check: the file declares no `Variable`, `Let` or
`Hypothesis` at all, so nothing is shadowed. `L` occurs as a binder of other
declarations (`Arguments perm_list_to_set [L].` at 829, `Arguments
mem_sets_of [tbl L].` at 913, `Arguments psl211_word_perm_imset w [L].` at
1201), each in its own declaration, so no capture. At 871 the proof context of
`class_count` holds `s p pn Hu Hasc Hcomp Hp key`; at 1028 the context of
`psl211_pattern_countE` holds `tbl C A ... Hasc Hrow`; neither holds `L` or
`L'`. Use sites of the lemma at 874, 910, 1025, 1031 are positional or
implicit and do not name the binders.

**The `Arguments` line at 851 must change in the same edit.** `Arguments f [x]`
is matched by NAME; leaving `[L1 L2]` there after the binders are renamed is a
hard error, and the three call sites that rely on the implicit arguments (874,
910, 1025, 1031) would break with it.

### B2 — `reconstruct/transitivity_privacy.v` (FROZEN)

`l1 l2` to `i j`. Intro names inside three proof scripts, each consumed on the
same line. Nothing outside the line sees them.

| line | current | new |
|---|---|---|
| 401 | `  by apply/tuple_uniqP => l1 l2; rewrite !tnth_mktuple => /perm_inj/stinj->.` | `  by apply/tuple_uniqP => i j; rewrite !tnth_mktuple => /perm_inj/stinj->.` |
| 605 | `    apply/tuple_uniqP => l1 l2; rewrite !tnth_mktuple => /b_inj/perm_inj.` | `    apply/tuple_uniqP => i j; rewrite !tnth_mktuple => /b_inj/perm_inj.` |
| 615 | `      apply/tuple_uniqP => l1 l2; rewrite !tnth_mktuple => /(can_inj ebK').` | `      apply/tuple_uniqP => i j; rewrite !tnth_mktuple => /(can_inj ebK').` |

Totals: 3 of `l1`, 3 of `l2`, all in code; no comment mirrors them. They are
the two ordinal indices `tuple_uniqP` introduces, so `i j` is the MathComp
name. Scope check: the section variables of the three enclosing sections are
`N' gT G rho t orbit_class deck_ok R secretP card_G_gt0 encode P secretT viewT
viewT' secret fullview proj` and the `Let`s `P`; none is `i` or `j`. At 401 the
context is `k st tt Hk Hst stinj`; at 605 it is `b_inj eb ebK ebK' g`; at 615
it is `r Hr`. No `i` or `j` in any of them. The surrounding scripts do use `l`
for a single index (lines 394, 406, 407, 412, 602, 621, 625) but never `i` or
`j`, so the rename introduces no ambiguity in the reader's eye either.

### B3 — `smc/smc_interpreter.v` (FROZEN) — RECOMMENDED: DO NOT RENAME

The file's first three lines are:

```
(* Vendored verbatim from the infotheo fork
   (~/Projects/coq/infotheo @ dumas2017dual, commit b5a899f7, smc/smc_interpreter.v):
   the piSMC language is fork-only work, absent from released coq-infotheo. *)
```

Renaming inside it makes that statement false and turns the next re-vendor from
a copy into a merge. `rstep_disjoint` has no use site anywhere in the tree
(`git grep -w rstep_disjoint -- '*.v'` returns the declaration alone), so the
names reach nothing. My recommendation is to leave the file and record the
exception, either in the vendoring comment or in the owner's reminder note.

If the owner overrules, the rename is `l1 l2` to `l l'` (infotheo names a lens
`l`), `psl1 psl2` to `psl psl'`, `Hpsl1 Hpsl2` to `Hpsl Hpsl'`:

| line | current | new |
|---|---|---|
| 187 | `Lemma rstep_disjoint n m p (ps : n.-tuple proc) (l1 : lens n m) (l2 : lens n p)` | `... (l : lens n m) (l' : lens n p)` |
| 188 | `  psl1 psl2 ps1 tr1 ps2 tr2 :` | `  psl psl' ps1 tr1 ps2 tr2 :` |
| 189 | `  psl1 = extract l1 ps -> psl2 = extract l2 ps ->` | `  psl = extract l ps -> psl' = extract l' ps ->` |
| 190 | `  rstep l1 psl1 ps1 tr1 -> rstep l2 psl2 ps2 tr2 ->` | `  rstep l psl ps1 tr1 -> rstep l' psl' ps2 tr2 ->` |
| 191 | `  l1 == l2 :> seq _ /\ ps1 = ps2 :> seq _ /\ tr1 = tr2 :> seq _` | `  l == l' :> seq _ /\ ...` |
| 192 | `  \/ {in l1 & l2, forall a b, a != b}.` | `  \/ {in l & l', forall a b, a != b}.` |
| 193 | `  (* [disjoint l1 & l2] *)` | `  (* [disjoint l & l'] *)` (the one comment that mirrors the code) |
| 195 | `move=> Hpsl1 Hpsl2 Hred1 Hred2.` | `move=> Hpsl Hpsl' Hred1 Hred2.` |
| 196 | `case: Hred1 Hpsl1 => [...]` | `case: Hred1 Hpsl => [...]` |
| 197 | `case: Hred2 Hpsl2 => [...]` | `case: Hred2 Hpsl' => [...]` |

Totals: `l1` 5 code + 1 comment, `l2` 5 code + 1 comment, `psl1` 3, `psl2` 3,
`Hpsl1` 2, `Hpsl2` 2. All are bound variables of one lemma, so no other file
sees them. Two cautions: the proof at 201, 203, 204, 205, 207 uses the
autogenerated hypothesis names `H` and `H0`, which this rename does not touch
but which make the script fragile to any other change; and `psl1 psl2` do not
themselves spell the abbreviation, they inherit it from `l1 l2` (a `psl` is the
process list `extract l ps`), so renaming one pair without the other leaves the
file half-converted. Rename both or neither.

### B4 — `security/pgg_schreier.v` (not frozen)

`L1 L2` to `L L'`, three declarations. All are bound variables; nothing outside
the file names them (`security_monotone`, `schreier_epsilon_decreasing` and
`envelope_decreasing` are applied positionally at 390, 406 and at
`pgg_schreier_weighted.v:198, 213`, never with a named argument).

Code, 9 occurrences of `L1` and 10 of `L2`:

| line | current | new |
|---|---|---|
| 255 | `Local Lemma envelope_decreasing (L1 L2 : nat) :` | `Local Lemma envelope_decreasing (L L' : nat) :` |
| 256 | `  (L1 <= L2)%N -> c * (1 - lam) ^+ L2 <= c * (1 - lam) ^+ L1.` | `  (L <= L')%N -> c * (1 - lam) ^+ L' <= c * (1 - lam) ^+ L.` |
| 387 | `Lemma schreier_epsilon_decreasing (sc : SchreierCertificate) (L1 L2 : nat) :` | `... (sc : SchreierCertificate) (L L' : nat) :` |
| 388 | `  (L1 <= L2)%N -> schreier_epsilon sc L2 <= schreier_epsilon sc L1.` | `  (L <= L')%N -> schreier_epsilon sc L' <= schreier_epsilon sc L.` |
| 396 | `    (L1 L2 : nat)` | `    (L L' : nat)` |
| 397 | `    (HL : (L1 <= L2)%N) :` | `    (HL : (L <= L')%N) :` |
| 400 | `                     (rho_from_words L2 sigmas))` | `                     (rho_from_words L' sigmas))` |
| 402 | `  <= schreier_epsilon sc L1.` | `  <= schreier_epsilon sc L.` |
| 405 | `apply: (Order.POrderTheory.le_trans (sc_convergence sc L2 s)).` | `apply: (Order.POrderTheory.le_trans (sc_convergence sc L' s)).` |

Comments that mirror the code, 8 + 7 occurrences on 4 lines:

| line | current | new |
|---|---|---|
| 59 | `(*   schreier_epsilon_decreasing == eps(L2) <= eps(L1) when L1 <= L2         *)` | `(*   schreier_epsilon_decreasing == eps(L') <= eps(L) when L <= L'          *)` (words: `schreier_epsilon_decreasing == eps(L') <= eps(L) when L <= L'`) |
| 60 | `(*   security_monotone == var_dist at L2 bounded by eps(L1) when L1 <= L2    *)` | words: `security_monotone == var_dist at L' bounded by eps(L) when L <= L'` |
| 376 | `   sqrt(N) * r^L2 <= sqrt(N) * r^L1 when 0 <= r < 1, L1 <= L2.` | `   sqrt(N) * r^L' <= sqrt(N) * r^L when 0 <= r < 1, L <= L'.` |
| 394 | `(* Monotone security: if secure at L1, at least as secure at L2 >= L1 *)` | `(* Monotone security: if secure at L, at least as secure at L' >= L *)` |

Scope check: the enclosing sections declare `Variable R`, `Variable m n'`,
`Let Tg`, `Let N`, `Variable sigmas`, and for `geometric_rate` `Variables (R
lam c)` with three hypotheses. Neither `L` nor `L'` is among them. `L` is a
binder of other declarations in the same section (252, 324, 371) and `L'` of
one more (360, 361), each in its own declaration, so no capture. `m n` was
rejected as a name here precisely because `m` IS a section variable.

**Also in this file, two prose sites that are NOT the norm the owner barred
and must NOT be renamed with the others** (the Euclidean norm of
Saloff-Coste's Theorem 2.6, a different object):

| line | current | replacement words |
|---|---|---|
| 94 | `(*     L2 to total variation conversion for reversible chains                *)` | `sum-of-squares to total variation conversion for reversible chains` |
| 321 | `       Saloff-Coste (1997), Theorem 2.6 (L2 to TV conversion)` | `Saloff-Coste (1997), Theorem 2.6 (sum-of-squares to TV conversion)` |

Read in context: line 94 sits in the `== Literature ==` block naming
Saloff-Coste's Theorem 2.6, and line 321 in the `Mathematical source:` note on
`sc_convergence`, beside Diaconis's upper bound lemma. Theorem 2.6 bounds total
variation by the chi-square quantity, a weighted sum of squares, so the phrase
names that conversion and not the sum of absolute differences. If the auditor
wants the sharper name, "chi-square to total variation conversion for
reversible chains" is the literature's own and equally free of the
abbreviation; I did not choose it because it introduces a term the file uses
nowhere else.

### B5 — `security/pgg_schreier_weighted.v` (not frozen)

`L1 L2` to `L L'`, two declarations, 6 + 7 code occurrences and 3 in one
comment. Bound variables only.

| line | current | new |
|---|---|---|
| 194 | `    (wsc : WeightedSchreierCertificate) (L1 L2 : nat) :` | `    (wsc : WeightedSchreierCertificate) (L L' : nat) :` |
| 195 | `  (L1 <= L2)%N ->` | `  (L <= L')%N ->` |
| 196 | `  weighted_schreier_epsilon wsc L2 <= weighted_schreier_epsilon wsc L1.` | `  weighted_schreier_epsilon wsc L' <= weighted_schreier_epsilon wsc L.` |
| 202 | `(* Monotone security: if secure at L1, at least as secure at L2 >= L1 *)` | `(* Monotone security: if secure at L, at least as secure at L' >= L *)` |
| 205 | `    (L1 L2 : nat) (HL : (L1 <= L2)%N) :` | `    (L L' : nat) (HL : (L <= L')%N) :` |
| 207 | `  var_dist (@endpoint_dist_weighted R n' m L2 sigmas W s)` | `  var_dist (@endpoint_dist_weighted R n' m L' sigmas W s)` |
| 209 | `  <= weighted_schreier_epsilon wsc L1.` | `  <= weighted_schreier_epsilon wsc L.` |
| 212 | `apply: (Order.POrderTheory.le_trans (wsc_convergence wsc L2 s)).` | `apply: (Order.POrderTheory.le_trans (wsc_convergence wsc L' s)).` |

Scope check: the section variables are `R m n' sigmas W` with `Let Tg`, `Let
N`. No `L`, no `L'` anywhere in the file (`git grep -w "L'"` is empty).
`weighted_schreier_epsilon_decreasing` is applied at 213 positionally, and
`weighted_security_monotone` has no use site.

### B6 — `instances/pgl27/pgl27_orbit.v` (not frozen)

`L1 L2` to `L L'`, two `Local Lemma`s, 9 + 9 code occurrences, no comment
mirrors them.

| line | current | new |
|---|---|---|
| 131 | `Local Lemma nclass_perm (L1 L2 : seq nat) :` | `Local Lemma nclass_perm (L L' : seq nat) :` |
| 132 | `  perm_eq L1 L2 -> nclass L1 = nclass L2.` | `  perm_eq L L' -> nclass L = nclass L'.` |
| 472 | `Local Lemma list_to_set_inj (L1 L2 : seq nat) :` | `Local Lemma list_to_set_inj (L L' : seq nat) :` |
| 473 | `  asc4 L1 -> asc4 L2 -> list_to_set L1 = list_to_set L2 -> L1 = L2.` | `  asc4 L -> asc4 L' -> list_to_set L = list_to_set L' -> L = L'.` |
| 478 | `- move=> n; rewrite -(perm_mem (@perm_list_to_set L1 A1)) Heq.` | `- move=> n; rewrite -(perm_mem (@perm_list_to_set L A1)) Heq.` |
| 479 | `  by rewrite (perm_mem (@perm_list_to_set L2 A2)).` | `  by rewrite (perm_mem (@perm_list_to_set L' A2)).` |
| 495 | `    move=> L1 L2; rewrite !mem_filter => /andP[_ H1] /andP[_ H2].` | `    move=> L L'; rewrite !mem_filter => /andP[_ H1] /andP[_ H2].` |

Scope check: the file declares no `Variable`, `Let`, `Hypothesis` or
`Arguments` at all. `L` is the file's own name for a code list
(`subset_class_list_to_set (L : seq nat)` at 464, and the `forall L, asc4 L ->
...` of `class_count` at 485), so `L L'` continues the file's convention. Use
sites of `nclass_perm` (229, 341, 467) and of `list_to_set_inj` (496) are
`apply:` with no named argument. At 495 the context is `p pn Hp key`; no `L`,
no `L'`.

### B7 — `instances/psl211/psl211_alldecks.v` (not frozen)

`L1 L2` to `L L'`, one `Local Lemma`, 6 + 6 code occurrences, no comment
mirrors them (the docstring at 787-789 names neither).

| line | current | new |
|---|---|---|
| 790 | `Local Lemma ad_list_to_set_inj (L1 L2 : seq nat) :` | `Local Lemma ad_list_to_set_inj (L L' : seq nat) :` |
| 791 | `  sorted ltn L1 -> all (fun n => (n < 12)%N) L1 ->` | `  sorted ltn L -> all (fun n => (n < 12)%N) L ->` |
| 792 | `  sorted ltn L2 -> all (fun n => (n < 12)%N) L2 ->` | `  sorted ltn L' -> all (fun n => (n < 12)%N) L' ->` |
| 793 | `  psl211_list_to_set L1 = psl211_list_to_set L2 -> L1 = L2.` | `  psl211_list_to_set L = psl211_list_to_set L' -> L = L'.` |
| 796 | `move=> n; rewrite -(perm_mem (ad_perm_list_to_set L1 S1 A1)) Heq.` | `move=> n; rewrite -(perm_mem (ad_perm_list_to_set L S1 A1)) Heq.` |
| 797 | `by rewrite (perm_mem (ad_perm_list_to_set L2 S2 A2)).` | `by rewrite (perm_mem (ad_perm_list_to_set L' S2 A2)).` |

Scope check: the `Variable`s of this file are `N` (587), and `C g v`
(867-869); no `L`, no `L'`. No `Arguments` line in the file. The single use
site, `apply: ad_list_to_set_inj.` at 821, names no argument.

### B8 — `instances/s5/pgg_raag_s5.v` and `instances/s5/rigidity_s5_instance.v` (not frozen) — GLOBAL name

`s5_nt_L1`, `s5_nt_L2`, `s5_nt_L3` to **`s5_n_traces_len1`, `s5_n_traces_len2`,
`s5_n_traces_len3`**.

All three go together: renaming only the first two would leave a family split
across two spellings, and the ban is on the pattern, not on the digit three.
`nt` is also a project-local abbreviation nobody can read without opening the
file; the new name spells the function the lemma evaluates (`n_traces`, defined
at `groups/pgg_raag.v:1033`, with `n_traces_natB` the decidable form) and the
word length it evaluates it at.

Every mention tree-wide:

| file | line | kind | current | new |
|---|---|---|---|---|
| `instances/s5/pgg_raag_s5.v` | 59 | docstring head | `(** s5_nt_L1 — [n_traces_natB] evaluated at the S_5 path-RAAG independence` | `(** s5_n_traces_len1 — [n_traces_natB] evaluated at the S_5 path-RAAG` |
| `instances/s5/pgg_raag_s5.v` | 63 | declaration | `Lemma s5_nt_L1 : n_traces_natB 4 1 path_comm_nat = 4.` | `Lemma s5_n_traces_len1 : n_traces_natB 4 1 path_comm_nat = 4.` |
| `instances/s5/pgg_raag_s5.v` | 66 | docstring head | `(** s5_nt_L2 — [n_traces_natB] evaluated at the S_5 path-RAAG independence` | `(** s5_n_traces_len2 — [n_traces_natB] evaluated at the S_5 path-RAAG` |
| `instances/s5/pgg_raag_s5.v` | 70 | declaration | `Lemma s5_nt_L2 : n_traces_natB 4 2 path_comm_nat = 13.` | `Lemma s5_n_traces_len2 : n_traces_natB 4 2 path_comm_nat = 13.` |
| `instances/s5/pgg_raag_s5.v` | 73 | docstring head | `(** s5_nt_L3 — the same count at length 3 is 40 distinct commutation` | `(** s5_n_traces_len3 — the same count at length 3 is 40 distinct commutation` |
| `instances/s5/pgg_raag_s5.v` | 75 | declaration | `Lemma s5_nt_L3 : n_traces_natB 4 3 path_comm_nat = 40.` | `Lemma s5_n_traces_len3 : n_traces_natB 4 3 path_comm_nat = 40.` |
| `instances/s5/rigidity_s5_instance.v` | 31 | header index | `(*   s5_nt_L1 : n_traces_natB 4 1 path_comm_nat = 4                          *)` | words: `s5_n_traces_len1 : n_traces_natB 4 1 path_comm_nat = 4` |
| `instances/s5/rigidity_s5_instance.v` | 32 | header index | `(*   s5_nt_L2 : n_traces_natB 4 2 path_comm_nat = 13                         *)` | words: `s5_n_traces_len2 : n_traces_natB 4 2 path_comm_nat = 13` |
| `instances/s5/rigidity_s5_instance.v` | 33 | header index | `(*   s5_nt_L3 : n_traces_natB 4 3 path_comm_nat = 40                         *)` | words: `s5_n_traces_len3 : n_traces_natB 4 3 path_comm_nat = 40` |

No `.v` file applies any of the three; they are `vm_compute` demonstrations.
Two generated inventory files mention them and are not compiled:
`audit-inventory/THEOREM_INDEX.md:395-397` and
`audit-inventory/theorem_index.tsv:303-305`. Regenerate them or leave them; say
which in the commit message. No `.tex` mentions any of the three.

Clash check: `git grep -w` for `s5_n_traces_len1`, `s5_n_traces_len2`,
`s5_n_traces_len3` and for `n_traces_len` over all tracked `.v` returns zero,
so the three names are free. The sibling in the same file is `s5_gens_agree`,
so a `s5_` prefix and a spelled-out body is the file's own style. Shorter
alternative, if the owner prefers it: `s5_n_traces1/2/3`, also free.

The three docstring heads must be re-laid-out: `s5_n_traces_len1` is six bytes
longer than `s5_nt_L1`, and the head lines at 59 and 66 are 76 and 76 bytes
before the change.

---

## Part C: risks to the single recompile

**C1. The `Arguments` line of B1.** `instances/psl211/psl211_orbit.v:851`,
`Arguments list_to_set_inj [L1 L2].` `Arguments` matches binders by name, so
renaming the binders at 842-845 without this line is an immediate error, and
renaming this line without the binders is the same error. It is the one place
in the whole sheet where two lines must change together or neither.
*Check without compiling:* after applying B1, grep the file for `L1` and `L2`
whole-word; the count must be zero. Then check that the multiset of tokens
inside `Arguments list_to_set_inj [...]` equals the multiset of the first two
binder names on line 842.

**C2. Renames inside a proof script that a later tactic names.** Audited: in
B1, B2, B4, B5, B6, B7 every renamed name is either a lemma binder or an intro
name consumed on the line that introduces it. The only script that refers to a
renamed name on a later line is B4 line 405 (`sc_convergence sc L2 s`, inside
the proof of `security_monotone`, where `L2` is the lemma's own binder) and B5
lines 207, 209, 212. All three are in the table. No `rewrite` in any of these
files names an autogenerated hypothesis derived from `L1`/`L2`.
*Check without compiling:* for each file, run
`python3 scripts/strip_comments.py` on the before and the after, and diff the
token streams; every difference must be exactly one of the pairs in the row's
table, and the two streams must have the same length.

**C3. Autogenerated hypothesis names near B3.** `smc/smc_interpreter.v` lines
201, 203, 204, 205, 207 use `H` and `H0`, which the `-[]` intro patterns
produce. The B3 rename does not touch them, but it changes the statement's
binder names, and any change to a statement can in principle shift which
hypothesis an `=> -[]` pattern generates. This is the second reason B3 is
recommended for deferral. If it is applied, it must be applied alone, in its
own commit, and verified by a real compile of that one file (see C9).

**C4. No comment edit may change a code token.** All 38 Part A rows are inside
comment delimiters. *Check without compiling:*
`python3 scripts/strip_comments.py FILE` before and after must be
byte-identical for every file touched only by Part A rows: `pgg_raag.v`,
`psl211_endpoints.v`, `psl211_exec.v`, `psl211_profile.v`,
`pgg_algebra_syntax.v`, `pgg_execution_plug.v`, `pgg_instance.v`,
`pgg_session_types.v`, `covering_scheme.v`, `pgg_collusion_bound.v`,
`pgg_security_solver.v`. `algebraic_rigidity.v` is also Part A only.
`scripts/comment_pass/check_pass.py` does this and more, but note that it
refuses a run in which a frozen file was written; the applier has to pass
whatever flag lifts that guard, or run `strip_comments.py` directly.

**C5. Unbalanced delimiters.** Two rows sit inside a nested-comment hazard.
A16 (`pgg_algebra_syntax.v:146-151`) and A32
(`algebraic_rigidity.v:192-195`) both rewrite a sentence in the MIDDLE of a
comment whose closing `*)` is several lines further down (A32's comment runs to
about line 207). Editing the middle of such a block risks losing the closer or
duplicating it. *Check without compiling:* `common.comment_spans` over the
edited file must return the same NUMBER of top-level comment spans as over the
original, and the code produced by `split()` must be unchanged (C4). A simple
count of `(*` and `*)` is not enough, because Rocq comments nest.

**C6. coqdoc brackets and code references inside comments.** A32 carries
`[tw_covering]`, which coqdoc renders as code, and
`cover_tradeoff.v:gap_bound`. A31 and A30 sit beside `var_dist`,
`sw_bound_eps`, `sa_eps_inf` and a displayed inequality. B8's three docstrings
carry `[n_traces_natB]`. None of the replacements changes a bracket or an
identifier. *Check without compiling:* for every Part A row, the set of tokens
matching `\[[A-Za-z_][A-Za-z0-9_']*\]` and the set matching
`[A-Za-z_][A-Za-z0-9_']*\.v` must be the same before and after.

**C7. The identifiers named inside the replaced prose.** A6 keeps
`psl211_fuel`, A11 keeps `psl211_word_mixing`, A12 keeps `psl211_word_mixing`,
A13 keeps `psl211_count_okT`, A18 keeps `generic_static_recon`,
`dealt_static_recon`, `pga_coordE`, `profile_endpointsE`, A19 keeps
`instance_terminates_stmt`, `profile_endpoints_stmt`,
`profile_commit_endpoints_stmt`, A21 keeps `params_exec`, `ex_inputT`,
`ex_content`, `ex_commits`, `ex_fuel`, `ex_content_obs`, `ex_expected`,
`instance_observed`, A28 keeps nothing new, A34 keeps `cs_gap` and
`ar_gap_bound`, A36 keeps `dpi_bound`. *Check without compiling:* the same
identifier-token comparison as C6, per row.

**C8. The 77/78-byte block of A30.** `reconstruct/algebraic_rigidity.v`
lines 112-125 are one-line comments on their own grid: 78, 77, 77, 77, 77, 78,
78 bytes, not the tree's 80. `reflow.py` lays a boxed line out at exactly 80
bytes with a space before the closer. Running it over this block would rewrite
five lines the sheet does not touch and would show up in the audit as an
unexplained change. The applier must lay A30's two lines out by hand at the
block's own width, or accept and declare the regularisation of the whole block.
A31's field comment and A32's block are ordinary indented comments and reflow
normally.

**C9. The compile order, and what can still be canaried.** Once ANY frozen file
is written, `make` will want to rebuild `psl211_endpoints.v`, and no short
compile of anything above it is possible. So:

1. Apply B4, B5, B6, B7, B8 first. These touch no frozen file.
2. Compile them single-file, shortest first:
   `instances/s5/pgg_raag_s5.v` (three `vm_compute` equations, seconds),
   `instances/s5/rigidity_s5_instance.v`, `security/pgg_schreier.v`,
   `security/pgg_schreier_weighted.v`, `instances/pgl27/pgl27_orbit.v`
   (carries a `vm_compute` census, minutes), `instances/psl211/psl211_alldecks.v`
   (the heaviest of the five; it sits ABOVE `psl211_endpoints.v`, so it must be
   compiled here, while `psl211_endpoints.vo` is still valid, or not at all).
   `scripts/comment_pass/compile_closure.py` does this through the lock, one
   process at a time; it refuses a frozen file, which is the behaviour wanted
   at this step.
3. Only then apply Part A and B1, B2 (and B3 if the owner overrules), and run
   the one full recompile with `make -j1`, per the instruction at
   `psl211_endpoints.v:17`, and not beside a second rocqworker.
4. Before step 3's compile, run the C2 and C4 token comparisons over every
   frozen file touched. They are the only evidence available before the 900 s.

A pre-compile of an edited frozen file without invalidating its `.vo` is
possible in principle: copy the edited source to a scratch directory and run
`rocq c` on the copy with the `_CoqProject` flags and `-o` pointing at a
scratch `.vo`, so the repository's `.vo` is never overwritten. It takes that
one file's own compile time. For B1 that is `psl211_orbit.v`, which carries the
BFS orbit certificates and is slow; for B2 it is `transitivity_privacy.v`. Do
this for B1 and B2 if the owner wants evidence before the 900 s; it is
unnecessary for the Part A rows, which the token comparison settles.

---

## What could not be settled

1. **The reminder note's "three word-for-word twins" is wrong; there is one.**
   `notes/2026-09-21-014953-reminder-to-the-owner-frozen-files-and-open-decisions.md`
   says lines 78, 102 and 132 of `instances/psl211/psl211_profile.v` are word
   for word sentences already rewritten in `instances/pgl27/pgl27_profile.v`.
   Only line 102 is: the `pgl27_marginal_bound` docstring, rewritten in
   `cca5e24` to "the loss of that idealisation is bounded by pgl27_word_mixing,
   not here", and A12 copies it. Lines 78 and 132 have no counterpart at all:
   `pgl27_se_exact`'s docstring in `pgl27_profile.v` is two lines with no such
   sentence, and `profile_k_pgl27`'s is two lines with no transitivity
   sentence. A11 and A13 are therefore written fresh, using only substitutions
   the owner made elsewhere in `cca5e24`. An auditor should read those two rows
   as new prose, not as a copy.

2. **"TV distance" in `pgg_collusion_bound.v`.** The file calls `var_dist` "the
   TV distance" at lines 159 and 161, while `var_dist` is twice the total
   variation of the literature and the value proved is `2k/|A|`. A35 corrects
   both occurrences because it had to rewrite that exact clause anyway;
   A36 does the same at line 468. Whether the correction should extend to the
   rest of the file (line 8's "idealized uniform permutation" paragraph and the
   `TV` of line 476's proof comment) is the auditor's call, and I did not make
   it.

3. **`smc/smc_interpreter.v`** is vendored verbatim from the infotheo fork. I
   recommend not renaming in it (B3). That is a policy question, not a
   technical one, and it is the owner's.

4. **The `audit-inventory/` files** carry the old `s5_nt_L*` names in two
   generated tables. Whether they are regenerated as part of this pass, or left
   until the next inventory run, I did not decide.

5. **A38 and A0-W** ("overhead", "worth") are words the owner never listed. I
   offer A38 as an optional change and leave A0-W alone; either could go the
   other way.
