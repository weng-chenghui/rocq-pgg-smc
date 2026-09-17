# Style and statement audit, group C

Date: 2026-09-18
Branch: `feat/pgl27-encoding-parameter`
Files: `instances/pgl27/pgl27_trace_encoding.v` (292 lines),
`instances/pgl27/pgl27_encoding_compare.v` (205 lines). Both new in full.
Context read: `pgl27_encoding.v`, `pgl27_trace.v`, `pgl27_run.v`,
`pgl27_recovery.v`, `pgl27_orbit.v`, `pgl27_leakage_r7.v`,
`pgl27_leakage_r5.v`, `pgl27_encoding_r5.v`, the plan and its Amendments,
and the A/B audits with `style-audit-rulings-AB.md`.
Read-only: no source edited, no build run, no tactic executed.

## Verdict

**PASS-WITH-FIXES.**

One must-fix, seven should-fix, five optional, three informational. Nothing is
mathematically wrong and no banned word appears. The executed-trace layer is
a faithful generalisation: the definitions really are the interpreter's output,
the recovery lemma is the honest twin of `pgl27_run_recovers_class`, premises
are minimal, and the termination lemma has the same fuel and the same shape as
`pgl27_run.v:105`. F1 is stated correctly in the comparison header, nothing
claims `r = 7` for both pairs, and `pgl27_seven_reveal_class` is cited as the
encoding-free all-decks claim exactly as F1 requires.

The defects are in the comment layer and in two proofs that take a longer
route than the kernel needs.

| # | File | Severity | One line |
|---|---|---|---|
| C1 | encoding_compare | must-fix | `pgl27_compare_classE` comment says a coalition with enough positions recovers the same bit on either pair; the file's own `pgl27_compare_recovery_thresholdE` says 7 against 5 |
| T1 | trace_encoding | should-fix | `pgl27_r7_player_traceE` and `pgl27_r7_coalition_traceE` are provable by conversion; the rewrite route drags functional extensionality into two otherwise axiom-light lemmas |
| T2 | trace_encoding | should-fix | header line 29-31 claims definitional identity with `pgl27_trace.v`; the proofs as written establish only propositional equality |
| T3 | trace_encoding | should-fix | `pgl27_enc_player_traceE`'s position sentence asserts what only `pgl27_enc_player_trace_full` proves, and duplicates that lemma's own sentence |
| T4 | trace_encoding | should-fix | `pgl27_enc_endpoints_size` and `pgl27_aprocs_abs_terminates` are public and absent from the header |
| T5 | trace_encoding | should-fix | header line 36 is 79 columns; the comment box is misaligned |
| C2 | encoding_compare | should-fix | `pgl27_compare_classE` is forced by the record field and holds for any two encodings; route it through `pgl27_compare_heart_setE` instead |
| C3 | encoding_compare | should-fix | header line 39-41 cites two trace theorems stated about two different objects and calls a boolean equality a "value" |
| C4 | encoding_compare | should-fix | the F1 paragraph says the two recovery claims differ but not why a fixed pair can need fewer than seven |
| T6 | trace_encoding | optional | `pgl27_aprocs_abs_terminates` is encoding-free and untagged, sitting in an encoding file with no note saying why |
| T7 | trace_encoding | optional | "the coalition's whole pre-reveal knowledge" is wider than the seat processes the definition reads |
| T8 | trace_encoding | optional | two eight-branch proofs, each branch identical up to one lemma name |
| C5 | encoding_compare | optional | `Order.POrderTheory` imported, no order lemma used |
| C6 | encoding_compare | optional | `Import` block carries six modules with no visible user |
| T9 | trace_encoding | info | `pgl27_enc_player_traceE` against the frozen twin `pgl27_player_trace_E`: keep the new spelling |
| T10 | trace_encoding | info | the new recovery twin does not inherit the record-free, axiom-free property the frozen one advertises |
| C7 | encoding_compare | info | no conjunction carries a premise that only one conjunct needs |

Checks that passed with nothing to report: banned words (`apex`, `gate*`,
`posit*`, `ramp`, `beats`, `escape`, `dodge`, `smash`, `cap`) absent from both
files under a word-boundary grep; 80 columns respected in every code line of
both files and in every header line but one; no trailing whitespace; no tabs;
`Set Implicit Arguments` leaves `R` and `e` explicit in every exported name, as
the call sites in `pgl27_leakage_r5.v` confirm; `move=>`, `apply:`, `apply/`
spacing uniform.

---

## A. `instances/pgl27/pgl27_trace_encoding.v`

### Semantic sanity (rule 4): the four questions

**Are the executed-trace definitions really the interpreter's output?** Yes.
`pgl27_trace_encoding.v:91-95` reads `content_of` of
`(run_interp pgl27_fuel (pgl27_procs_deck (enc_deck e u.1) u.2)).2` at process
index `2 + i`. That is the interpreter's own trace list at the seat process,
not a restatement of `pgl27_enc_view`. The view enters only at line 169, as the
conclusion of an equality, which is the right direction.

**Is the agreement with `pgl27_player_trace` an equality of the definitions or
only extensional?** It is stated as an equality of random variables
(`pgl27_trace_encoding.v:276-277`), and the two sides are in fact convertible,
so the strong reading is available. See T1 and T2: the proof does not take it.

**Is `pgl27_enc_run_recovers_class` the honest twin of
`pgl27_run_recovers_class`?** Yes. Same premise `w0 \in pgg_G pgl27_M`, same
`tcast`-of-`in_tuple`-of-`endpoints_of_trace` shape at trace index 1, same
`orbit_class ... = s` conclusion, same proof skeleton. The new one is stated
over `pgl27_procs_deck (enc_deck e s) w0` where the frozen one uses
`pgl27_aprocs_abs (tnth (orbit_encode s)) w0`, which is one step closer to the
run the protocol executes, so nothing is weakened. See T10 for the one property
that does not carry over.

**Are premises minimal?** Yes. `pgl27_enc_run_recovers_class` needs `w0` in the
group for `orbit_class_invariant` and nothing else; deck validity rides inside
the record rather than appearing as a hypothesis, which matches F4.
`pgl27_enc_coalition_trace_secrecy` takes `#|C| <= 3` alone.
`pgl27_enc_player_traceE`, `_trace_full` and `pgl27_enc_coalition_traceE` are
unconditional, as the header's "deck validity enters nowhere" paragraph
(lines 22-27) promises.

**Is the termination lemma stated at the same fuel and shape as the source?**
Yes. `pgl27_run.v:105-106` is
`(run_interp pgl27_fuel (pgl27_procs s w0)).1 = nseq 10 Finish`;
`pgl27_trace_encoding.v:262-263` is the same with `pgl27_procs_deck
(enc_deck e s) w0`. Same fuel constant, same `nseq 10 Finish`, same `.1`
projection. F7 is satisfied: `pgl27_aprocs_abs_terminates` (line 252) proves it
at abstract readout by `vm_compute`, and the per-encoding statement is a
one-line corollary.

### T1 (should-fix). Two lemmas prove by rewriting what holds by conversion

`instances/pgl27/pgl27_trace_encoding.v:276-291`

```coq
Lemma pgl27_r7_player_traceE (R : realType) (i : 'I_8) :
  pgl27_enc_player_trace R pgl27_encoding_r7 i = pgl27_player_trace R i.
Proof.
by rewrite pgl27_enc_player_traceE pgl27_player_trace_E.
Qed.
```

Three facts in the tree make both sides convertible:

- `pgl27_trace.v:252-255`: `pgl27_procs s w0 = pgl27_aprocs_abs (tnth
  (orbit_encode s)) w0`, `Proof. by []. Qed.`
- `pgl27_trace.v:448-450`: `pgl27_procs_deck sh w0 = pgl27_aprocs_abs (tnth sh)
  w0`, `Proof. by []. Qed.`
- `pgl27_leakage_r7.v:113-115`: `pgl27_enc_view R pgl27_encoding_r7 C =
  pgl27_view R C`, `Proof. by []. Qed.`, which can only hold if
  `enc_deck pgl27_encoding_r7` reduces to `orbit_encode`.

So `pgl27_procs_deck (enc_deck pgl27_encoding_r7 u.1) u.2` and
`pgl27_procs u.1 u.2` are the same term up to delta, and both definitions
wrap them in the same `content_of (nth [::] _ (2 + i))`. The same argument
carries to `pgl27_r7_coalition_traceE`, whose two sides are the identical
`[ffun i => if i \in C then _ else ord0]`.

The current route is not merely longer. `pgl27_enc_player_traceE` and
`pgl27_player_trace_E` are both proved with `boolp.funext`, so as written both
`pgl27_r7_*` lemmas carry functional extensionality in their assumption set,
where the conversion proof would carry nothing. Task S1 runs
`Print Assumptions`, and this is where the difference will show.

Fix, to be tried in that order and kept at the first that compiles:

```coq
Lemma pgl27_r7_player_traceE (R : realType) (i : 'I_8) :
  pgl27_enc_player_trace R pgl27_encoding_r7 i = pgl27_player_trace R i.
Proof. by []. Qed.

Lemma pgl27_r7_coalition_traceE (R : realType) (C : {set 'I_8}) :
  pgl27_enc_coalition_trace R pgl27_encoding_r7 C
  = pgl27_coalition_trace R C.
Proof. by []. Qed.
```

If `by []` does not close them, `Proof. exact: erefl. Qed.` and then
`Proof. by rewrite /pgl27_enc_player_trace /pgl27_player_trace. Qed.` are the
next two steps before falling back to the current proof. Should the conversion
genuinely fail, T2 below becomes must-fix rather than should-fix.

### T2 (should-fix). The header claims identity, the proofs give equality

`instances/pgl27/pgl27_trace_encoding.v:29-31`

```
(* At the deck pair of pgl27_encoding_r7.v the definitions below are the      *)
(* pgl27_trace.v ones, so the executed-trace results of the two files are     *)
(* results about one object.                                                  *)
```

"are the ... ones" asserts definitional identity. What the file exhibits is
two lemmas whose proofs go through functional extensionality, that is,
propositional equality of two functions. The sentence is true of the kernel
(T1), but the file does not show it.

Fix: land T1, and the sentence stands unchanged. If T1's conversion proofs do
not compile, replace the sentence with

```
(* At the deck pair of pgl27_encoding_r7.v the traces below are equal, as     *)
(* random variables, to those of pgl27_trace.v, so the executed-trace         *)
(* results of the two files are results about one object.                     *)
```

### T3 (should-fix). A position sentence that belongs to the next lemma

`instances/pgl27/pgl27_trace_encoding.v:97-100`

```coq
(** pgl27_enc_player_traceE — seat i's executed-trace content is the card the
    dealt deck holds at the cut-permuted position of seat i. The run puts no
    other card in reach of a seat, so one seat's whole knowledge before the
    reveal is that single value, at every deck pair. *)
```

against `pgl27_trace_encoding.v:126-129`

```coq
(** pgl27_enc_player_trace_full — the whole executed trace of seat i is the
    index marker and the one-card hand holding its dealt card. The seat's
    trace carries no residue of the shuffle beyond that card, which is why
    projecting it to its content loses nothing a coalition could use. *)
```

"The run puts no other card in reach of a seat" is precisely the content of
`pgl27_enc_player_trace_full`, which is proved twenty-five lines later.
`pgl27_enc_player_traceE` says only what `content_of` of the trace is; on its
own it cannot rule out a second card elsewhere in the trace. The two sentences
also say the same thing twice, in two vocabularies ("no other card in reach"
against "no residue of the shuffle beyond that card"), which is the synonym
drift the standard bans.

Fix: give `pgl27_enc_player_traceE` a position sentence about the cut, and let
`_trace_full` keep the exhaustiveness claim.

```coq
(** pgl27_enc_player_traceE — seat i's executed-trace content is the card the
    dealt deck holds at the cut-permuted position of seat i. The shuffle
    reaches a seat only through that position, so the deck pair and the cut
    together fix what the seat reads, at every deck pair. *)
```

### T4 (should-fix). Two public declarations the header does not carry

`instances/pgl27/pgl27_trace_encoding.v:202` declares
`pgl27_enc_endpoints_size` and line 252 declares `pgl27_aprocs_abs_terminates`.
Both are public; neither appears under Definitions or Key results
(lines 33-52), which list eight of the ten exported names. Rulings A2, C3 and
E2 of the A/B pass settled this convention: a public declaration is either
advertised in the header or made `Local`.

`pgl27_enc_endpoints_size` cannot be `Local`: it appears inside the type of
`pgl27_enc_run_recovers_class` (line 217) as the `tcast` proof, so it must be
exported with it. `pgl27_aprocs_abs_terminates` is the stronger of the two
termination facts and the one F7 names, so it earns an entry too.

Fix, after the `pgl27_enc_coalition_trace_secrecy` entry:

```
(*   pgl27_enc_endpoints_size == the run collects eight endpoints at the      *)
(*     verifier, the arity the decoder reads                                  *)
```

and after the `pgl27_enc_run_terminates` entry:

```
(*   pgl27_aprocs_abs_terminates == every process of the run over an          *)
(*     abstract card readout reaches Finish                                   *)
```

### T5 (should-fix). One header line is 79 columns

`instances/pgl27/pgl27_trace_encoding.v:36`

```
(*   pgl27_enc_coalition_trace R e C == the coalition joint executed trace   *)
```

Every other header line in both files, and every header line of
`pgl27_leakage_r5.v`, closes at column 80. This one closes at 79.

Fix: one more space before `*)`.

### T6 (optional). An encoding-free lemma in an encoding file, untagged

`pgl27_aprocs_abs_terminates` (line 252) quantifies over an arbitrary readout
`g : 'I_8 -> 'I_8` and mentions no encoding. By F8 such facts belong in a
shared, encoding-free file; the shared file here would be `pgl27_trace.v`,
which the plan freezes. Its name carries no `pgl27_enc_` tag, correctly, but a
reader of the file cannot tell whether that is deliberate.

Fix: a source comment, not a statement comment, above the section divider at
line 243:

```coq
(* pgl27_aprocs_abs_terminates is encoding-free and would sit in pgl27_trace.v
   if that file were open for edit; it is proved here because it is not. *)
```

### T7 (optional). A knowledge claim wider than the definition reads

`instances/pgl27/pgl27_trace_encoding.v:156-159`

```coq
    coalition's whole pre-reveal knowledge of one execution, and it refuses to
```

The definition reads the trace lists of the eight seat processes only. The
verifier's endpoint trace at index 1, which the same run writes and which
`pgl27_enc_endpoints_size` and `pgl27_enc_run_recovers_class` are about, is not
in it. "Whole pre-reveal knowledge of one execution" reads as covering the
run; what is meant is the seats' share of it.

Fix: "the coalition's whole pre-reveal knowledge at its seat processes".

### T8 (optional). Two eight-branch proofs

`pgl27_enc_player_traceE` (lines 104-124) and `pgl27_enc_player_trace_full`
(lines 135-154) each run eight bullets that differ only in the index of
`pgl27_abs_p*` or `pgl27_full_p*`. The shape mirrors the frozen twins in
`pgl27_trace.v:327-346` and `pgl27_trace.v:354-`, so consistency argues for
leaving it, and
this is optional for that reason. If a golf pass runs anyway, the candidate is

```coq
by case: i => -[|[|[|[|[|[|[|[|//]]]]]]]] Hi;
  rewrite ?(pgl27_abs_p0, pgl27_abs_p1, pgl27_abs_p2, pgl27_abs_p3,
            pgl27_abs_p4, pgl27_abs_p5, pgl27_abs_p6, pgl27_abs_p7)
          tnth_ord_tuple;
  congr (tnth (enc_deck e u.1) (@pgg_rho pgl27_M u.2 _)); apply: val_inj.
```

which must be compiled before it is believed. Do not let a golf pass change
which lemmas the proof names: `pgl27_abs_p*` and `pgl27_full_p*` are the
interface into the interpreter and the plan names them.

### T9 (info). Suffix spelling against the frozen twin

The new names are `pgl27_enc_player_traceE` and `pgl27_enc_coalition_traceE`;
the frozen twins are `pgl27_player_trace_E` and `pgl27_coalition_trace_E`.
MathComp writes `mulnE`, not `muln_E`, so the new spelling is the correct one
and the sibling encoding files (`pgl27_r7_viewE`, `pgl27_r5_view_mutual_infoE`)
already use it. No change. Recorded only so a later reader does not "fix" the
new names into the frozen file's shape.

### T10 (info). What the new recovery twin does not inherit

`pgl27_trace.v:279-285` advertises `pgl27_run_recovers_class` as holding "with
neither the threshold-scheme record nor its privacy axiom in scope".
`pgl27_trace_encoding.v:65-68` imports `covering_scheme`,
`pgg_sharing_framework`, `transitivity_privacy` and `pgl27_scheme`, so the new
twin is not in that position. Its comment (lines 210-214) correctly claims
nothing of the sort. No change; the point for S1 is that
`Print Assumptions pgl27_enc_run_recovers_class` should be read on its own and
not assumed to match the frozen twin's, and that a paper sentence about
record-free recovery must keep citing `pgl27_run_recovers_class`.

---

## B. `instances/pgl27/pgl27_encoding_compare.v`

### F1, the `r = 7` question, and the decoder question (rule 2, the three named checks)

**Does the header state F1 correctly?** Yes. Lines 28-37 say that at a fixed
pair the view determines the secret exactly when no shuffle produces that view
under both decks, that the census counts this as a collision count of zero,
that this is one full bit of mutual information, and that the recovery
threshold is therefore the smallest coalition size with one full bit: seven for
`_r7`, five for `_r5`. That is F1's chain in F1's order. `pgl27_seven_reveal_class`
is named as a different claim, quantified over every valid deck, encoding-free,
cited and not reproved, and not attributed to either pair. The lemma text at
`pgl27_recovery.v:68-71` confirms the description: two `deck_ok` decks agreeing
off one position have equal `orbit_class`. C4 below asks for one more clause,
not a correction.

**Does anything claim both pairs have `r = 7`?** No. The phrase does not occur,
and `pgl27_compare_recovery_thresholdE` (lines 195-199) states seven and five.
The plan's original C1 line ("possibilistic `r = 7` for both") is superseded by
F1 and the file follows F1.

**Does anything say the decoder cannot distinguish the pairs more strongly than
`pgl27_compare_classE` states?** Yes, once. See C1.

### C1 (must-fix). A comment that contradicts the file's own threshold lemma

`instances/pgl27/pgl27_encoding_compare.v:96-100`

```coq
(** pgl27_compare_classE — the two deck pairs decode to the same secret. A
    decoder that reads the heart positions returns the dealt secret on either
    pair, so a coalition holding enough positions recovers the same bit
    whichever pair the dealer uses, and the leakage values below compare like
    with like. *)
```

The clause "a coalition holding enough positions recovers the same bit
whichever pair the dealer uses" says the coalition story is pair-independent.
The file's last lemma says the opposite at the only place it matters:

```coq
Lemma pgl27_compare_recovery_thresholdE (C : {set 'I_8}) :
  (`I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r7 C) == 1)
    = (7 <= #|C|)%N
  /\ (`I(pgl27_secret R ; pgl27_enc_view R pgl27_encoding_r5 C) == 1)
    = (5 <= #|C|)%N.
```

"Enough positions" is seven at one pair and five at the other, and the two
sizes in between are exactly the content of `pgl27_compare_k5E` and
`pgl27_compare_k6E`. A domain reader taking the comment at face value would
conclude the pairs are interchangeable for a coalition, which is the one
conclusion the file exists to refute. `pgl27_compare_classE` itself is about
`orbit_class` applied to the whole deck, and says nothing about coalitions at
all.

Fix:

```coq
(** pgl27_compare_classE — the two deck pairs decode to the same secret. The
    decoder reads the whole dealt deck, so the dealer's choice between the
    pairs changes nothing a correct receiver sees, and the leakage values
    below compare like with like; what the choice does change is the
    coalition size at which the secret becomes recoverable. *)
```

### C2 (should-fix). The lemma is forced by the record, not by these decks

`instances/pgl27/pgl27_encoding_compare.v:101-104`

```coq
Lemma pgl27_compare_classE (s : bool) :
  orbit_class (enc_deck pgl27_encoding_r5 s)
  = orbit_class (enc_deck pgl27_encoding_r7 s).
Proof. by rewrite !enc_classK. Qed.
```

`enc_classK` is a field of `pgl27_encoding` (`pgl27_encoding.v:104`), so both
sides reduce to `s` for *any* two encodings whatever. As proved, the lemma
carries no information about these two decks; it is an instance of "any two
encodings decode to the same secret", which is a property of the record type.
Meanwhile the header (lines 15-19) attributes the equality to the shared heart
positions, and `pgl27_compare_heart_setE` — the lemma that does carry the deck
content — has no user anywhere in the tree.

`orbit_class` is `subset_class \o heart_set` (`pgl27_orbit.v:112-113`), so the
intended route exists:

```coq
Proof. by rewrite /orbit_class pgl27_compare_heart_setE. Qed.
```

That makes the file's dependency structure match its prose, gives
`pgl27_compare_heart_setE` the user it currently lacks, and leaves the
statement unchanged. Note that `pgl27_orbit.v` offers no exported equation to
unfold through: the name `orbit_classE` is taken, at `pgl27_orbit.v:337`, by a
`Local Lemma` about the ground form over heart codes, which is a different
statement and not in scope here. `rewrite /orbit_class` on the plain
`Definition` at `pgl27_orbit.v:112-113` is the route.

### C3 (should-fix). A citation sentence that crosses two different objects

`instances/pgl27/pgl27_encoding_compare.v:39-41`

```
(* Every value below is a value of the running protocol as well as of the     *)
(* coalition view, by pgl27_r7_trace_mutual_infoE and                         *)
(* pgl27_r5_trace_mutual_infoE.                                               *)
```

Two problems.

First, the two theorems are stated about different random variables.
`pgl27_leakage_r7.v:434` is about `pgl27_coalition_trace R C`, the frozen trace
of `pgl27_trace.v`; `pgl27_leakage_r5.v:324` is about
`pgl27_enc_coalition_trace R pgl27_encoding_r5 C`, the trace of
`pgl27_trace_encoding.v`. Every statement in this file is about
`pgl27_enc_view R e C`. The bridge from the r7 theorem's object to this file's
is `pgl27_r7_coalition_traceE` (`pgl27_trace_encoding.v:286-288`), which the
sentence does not name — and which, as noted under T1, has no other user.
Naming it is what makes the user's "one connected chain for both pairs" visible
in the file rather than left to the reader.

Second, `pgl27_compare_recovery_thresholdE` is a boolean equality, not a value,
so "every value below" does not reach the last Key result.

Fix:

```
(* Every leakage value below is a value of the running protocol as well as    *)
(* of the coalition view, by pgl27_r5_trace_mutual_infoE and, through         *)
(* pgl27_r7_coalition_traceE, by pgl27_r7_trace_mutual_infoE. The recovery    *)
(* thresholds transfer with them, being read off those same closed forms.     *)
```

### C4 (should-fix). Why a fixed pair can need fewer than seven is not said

`instances/pgl27/pgl27_encoding_compare.v:33-37` says
`pgl27_seven_reveal_class` "is a different claim: it quantifies over every
valid deck the dealer might use, holds independently of the deck pair, and is
cited here rather than reproved or attributed to either pair". True, and F1
asks for exactly that. What the paragraph leaves out is the reason the numbers
can differ at all, and a reader who meets seven, then five, will look for the
reason here. Ruling C1 of audit B accepted the same repair in
`pgl27_mutual_info.v`: state why a fixed-pair statement and an all-decks
statement are not comparable.

Fix, appended to that paragraph:

```
(* The two numbers differ because the quantifier differs: seven positions are *)
(* needed against an arbitrary valid deck, while a fixed pair puts only two   *)
(* decks in play, and five positions already separate them at the pair of     *)
(* pgl27_encoding_r5.v.                                                       *)
```

### C5 (optional). `Order.POrderTheory` with no order lemma in the file

`instances/pgl27/pgl27_encoding_compare.v:79`

```coq
Import GRing.Theory Num.Theory Order.POrderTheory.
```

No proof in the file uses `lra`, `le_anti`, `lt_eqF`, or any `ler`/`lter`
lemma; the six proofs are `exact:`, `rewrite` and `split` only. The `Order`
import looks carried over from `pgl27_leakage_r7.v`, where `lra` and `lt_eqF`
are genuinely used.

Fix: drop `Order.POrderTheory`, rebuild the single target
`make -f Makefile.rocq -j1 instances/pgl27/pgl27_encoding_compare.vo`, and
restore it if `%:R` or `== 1` needs it. `GRing.Theory` and `Num.Theory` should
be tested the same way but are likelier to be load-bearing for `%:R`.

### C6 (optional). Import block breadth

`instances/pgl27/pgl27_encoding_compare.v:60-74`. Candidates with no visible
user in the file, to be removed one at a time against the single target:
`morphism`, `action`, `bigop`, `div`, `prime`, `primitive_action`,
`pgg_monodromy_profile`, `covering_scheme`, `transitivity_privacy`. Load-bearing
and to be kept: `finset` and `fintype` for `{set 'I_8}` and `#|C|`,
`pgl27_orbit` for `heart_set`, `orbit_class` and `subset_class`, `pgl27_scheme`
and `pgl27_secrecy` for `pgl27_secret` and `pgl27_view`, `pgl27_encoding*` and
`pgl27_leakage_*` for everything cited, `entropy` for the `` `I( ; ) `` notation.
This is optional because the closure is unchanged either way; it matters only
for reading.

### C7 (info). The conjunction shape carries no hidden premise

Five of the eight lemmas state a conjunction of an `_r7` and an `_r5` fact
under a shared premise. In each one the premise is needed by both conjuncts:
`#|C| <= 3` at line 121, `#|C| = 4` with `subset_class C` at 136, `#|C| = 4`
with `subset_class C = false` at 156, `#|C| = 5` at 170, `#|C| = 6` at 182.
`pgl27_compare_recovery_thresholdE` is premise-free on both sides. So no
conjunct is silently conditionalized by a premise added for its neighbour, and
the side-by-side shape is the right one for the file's purpose. No change.

---

## C. Unused and redundant public declarations (rule 5)

Grep over `*.v` excluding `notes/` and `.claude/`, counting uses outside the
two audited files.

| declaration | external uses | ruling |
|---|---|---|
| `pgl27_enc_player_trace` | 0 | keep: the definition the chain starts from; used in-file by four lemmas |
| `pgl27_enc_player_traceE` | 0 | keep: plausible paper claim, "one seat reads one card"; used in-file |
| `pgl27_enc_player_trace_full` | 0 | keep: plausible paper claim, the exhaustiveness fact behind every secrecy statement; the frozen twin is a Key result of `pgl27_trace.v` |
| `pgl27_enc_coalition_trace` | 3 | used by `pgl27_leakage_r5.v` |
| `pgl27_enc_coalition_traceE` | 4 | used by `pgl27_leakage_r5.v` |
| `pgl27_enc_coalition_trace_secrecy` | 0 | keep: plausible paper claim, the executed-trace reading of the privacy threshold, generic in `e` |
| `pgl27_enc_endpoints_size` | 0 | keep, must stay public: it is in the type of `pgl27_enc_run_recovers_class`. Header entry owed, see T4 |
| `pgl27_enc_run_recovers_class` | 0 | keep: plausible paper claim, correctness of the run at an arbitrary pair |
| `pgl27_aprocs_abs_terminates` | 0 | keep: used in-file, and F7 names it. Header entry owed, see T4 |
| `pgl27_enc_run_terminates` | 0 | keep: plausible paper claim, the per-pair reading |
| `pgl27_r7_player_traceE` | 0 | keep: the identification the header's paragraph at lines 29-31 is about |
| `pgl27_r7_coalition_traceE` | 0 | keep, and give it the user C3 describes |
| `pgl27_compare_heart_setE` | 0 | keep **conditional on C2**; see below |
| `pgl27_compare_classE` | 0 | keep: plausible paper claim, the decoder agreement |
| `pgl27_compare_le3E` | 0 | keep: plausible paper claim |
| `pgl27_compare_equianharmonicE` | 0 | keep: plausible paper claim |
| `pgl27_compare_harmonicE` | 0 | keep: plausible paper claim, the separation |
| `pgl27_compare_k5E` | 0 | keep: plausible paper claim |
| `pgl27_compare_k6E` | 0 | keep: plausible paper claim |
| `pgl27_compare_recovery_thresholdE` | 0 | keep: plausible paper claim, the headline of the comparison |

Zero external uses is expected for `pgl27_encoding_compare.v`, which is the
terminal file of the chain, so the test there is the paper test rather than the
premise test. The six leakage-comparison lemmas and the threshold lemma are the
comparison the branch exists to produce.

One genuine wrapper. `pgl27_compare_heart_setE` (lines 91-94) is
`Proof. exact: pgl27_r5_hearts. Qed.`, and `exact:` succeeds only up to
conversion, so its statement is `pgl27_r5_hearts`
(`pgl27_encoding_r5.v:87-89`) with `deck_r5` and `orbit_encode` spelled through
the record. As things stand it restates a lemma and has no user. Under C2's fix
it becomes the proof of `pgl27_compare_classE` and earns its place. If C2 is
rejected, delete `pgl27_compare_heart_setE`, drop its header entry, and have
the header cite `pgl27_r5_hearts` directly.

Nothing else in either file is a candidate for `Local`.

---

## D. What was checked and found clean

- Banned vocabulary. Word-boundary grep for `apex`, `gate|gated|gating|gates`,
  `posit|posits|posited|positing`, `ramp`, `beats`, `escape|escapes`, `dodge`,
  `smash`, `cap`: no match in either file. The earlier `pgl27_leakage_ramp.v`
  name is gone from both.
- 80 columns. Every line of both files is 80 or fewer; the only defect is the
  79-column header line of T5.
- Naming grammar. `pgl27_enc_*` for the generic layer, `pgl27_r7_*` for the
  fixed-pair bridges, `pgl27_compare_*` for the comparison: consistent, and the
  `_r7`/`_r5` and `k5`/`k6` tags match `pgl27_r7_k6E` and `pgl27_r5_k4E` in the
  leakage files. The `E` suffix is used for equations throughout, `_full` for
  the exhaustive form, `_secrecy` and `_terminates` for the properties. No
  suffix is doing work it should not.
- Implicit arguments. `Set Implicit Arguments` with `Import Prenex Implicits`
  leaves `R` and `e` explicit in every exported name, since neither is
  inferable from a later argument's type; `pgl27_leakage_r5.v:353` calls
  `pgl27_enc_coalition_traceE` in the explicit form, which confirms it.
- One word per concept. "executed trace" is used throughout both files for the
  interpreter's output and "coalition view" for the statically defined object;
  "observes" and "reads" appear only in prose positions where no third object
  is implied. The one drift is T3.
- No status word, no plan id, no line number, no `Kind:`/`Why:`/`Used by:` slot
  and no restated signature appears in any statement comment in either file.
  The closest approach is `pgl27_compare_harmonicE`'s "This is the smallest
  coalition size at which the choice of decks is visible at all", which is a
  mathematical claim about the file's own values and is supported by
  `pgl27_compare_le3E` and `pgl27_compare_equianharmonicE`, not meta narration.
- F2 is respected. `pgl27_compare_harmonicE`'s sentence "the two pairs put the
  minimum of their leakage on opposite cross-ratio classes" checks out against
  the file's own values: `_r7` bottoms at `5/7` on the harmonic class, `_r5` at
  `11/14` on the equianharmonic class, and `11/14 < 6/7`.
- Proof idiom. `apply:`, `exact:`, `by rewrite`, `case: ifP => // _`,
  `move=> HC`, named `have` with an explicit statement: all ssreflect, no
  `pose proof`, no `f_equal`, no bare `auto`, no `assert`. `congr` is used
  where `f_equal` would be wrong. No tactic runs after the goal closes.
