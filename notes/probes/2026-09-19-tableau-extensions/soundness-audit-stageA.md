# Independent soundness and design audit of stage A

Date: 2026-09-19. Auditor: an independent session. No file of the probe, of
`manifest/` or of `instances/` was edited. Every compile below ran through the
machine-wide lock wrapper from a Python driver, so the return codes are real.
Scratch directory `scratchpad/extA_audit/`, logical path `tableau_ext_probe`,
holding copies of the nine stage-A files and of the five files of
`notes/probes/2026-09-19-kim-spectral-arm/`, with the Kim copies' imports of
`pgg_tableau`, `pgg_tableau_syntax` and `five_card_rows` pointed at the
extension copies.

## Verdict

**NO-GO**, on four false sentences and one incomplete blast radius. The Rocq
content of stage A is sound: the weakened obligation cannot publish a number
below the one a row proved, the exact arm is untouched, the claim reader is a
reader and not a new constructor, and the branch at `Sampled` needs no
framework change. Every blocking item below is a sentence, not a term, and
each is a one-clause fix. Once they are fixed, stage B may build on this copy
of the Tableau.

## What was compiled

| file | what it establishes | rc |
|---|---|---|
| `a1_c_soundness.v` | the routes into and out of the weakened obligation; the claim is constant in the field and the index | 0 |
| `a2_t0_pgl27.v` | T0's branch point at PGL(2,7), both families, both arms, two cross-model mutations | 0 |
| `a3_kim_reprice.v` | Kim's repeated row published at $2^{-39}$ from the certificate carrying the spectral number | 0 |
| `a4_exact_reprice.v` | an exact row published at an arbitrary `Reprice` | 0 |
| `a5_fail_msgs.v` | the messages of seven rejections, read with `rocq repl -q` | 0 |

Supporting recompiles from source, all rc=0: `pgg_tableau.v`,
`pgg_tableau_syntax.v`, `pgl27_rows.v`, `five_card_rows.v`, and the Kim probe's
five files.

Line numbers of a file named without a directory are the probe copy's;
lines given with `manifest/` or `instances/` are production.

## Findings

### F1. BLOCKING. The rewritten keyword sentence is false about `at`

`pgg_tableau_syntax.v:70-72` of the probe copy now reads "at and by follow a slot in some rule
but were keywords of Rocq and of ssreflect before this file". `at` occurs in
exactly two rules, `:374` (`'leaks' 'at' k`) and `:386`
(`'SpectralDecay' 'at' R idx`), and in both it follows a **literal**, never a
slot. The baseline sentence, "at follows a literal too and was a keyword of
Rocq before this file", was true; the rewrite made it false while adding the
true half about `by`.

Evidence: every `Notation` of the file listed; `'at'` appears twice, after
`'leaks'` and after `'SpectralDecay'`.

Change: keep `at` in the literal list and move only `by` out, for example
"`conclude`, and `at`, follow a literal and stay identifiers; `by` follows a
slot in the execute rule, the leaks rule and the conclude rule, and was a
keyword of ssreflect before this file, measured on 2026-09-19 by binding it in
a file that requires nothing but ssreflect."

### F2. BLOCKING. `SecurityClaim`'s comment states a falsehood the probe itself refutes

`pgg_tableau.v:163-168`: "two rows over one model publish the same manifest
row". `t0_sampled_branch.v:109-111` proves the opposite:
`t0_row_uniform_row_neq` shows two rows over one model publishing two
different manifest rows, because `publish` takes the transfer status. The
comment on `security_claim_of` (`:770-774`) carries the correct qualifier,
"two rows over one model **and one pair of statuses** are one manifest row",
so the two new comments contradict each other.

Change: add the same qualifier at `:166`.

### F3. BLOCKING. T0 did not demonstrate two claims

`STATUS.md` step 2 is headed "T0, two claims from one named `Tableau Sampled`
value", and `t0_sampled_branch.v:76-80` says "Two published rows over one
Sampled value are what one model carrying two claims looks like". Both
continuations write the identical clause
`certify ExactIndependence five_card_exact_witness`. The file's own
`t0_row_uniform_atE` proves the two continuations hold one `AnalysisBridged`
coordinate, so they carry one port, one witness and one claim; what differs is
the transfer status the terminal writes. Under K's own reader both rows return
`ExactViewIndependence`.

This matters for stage B, whose shape is one named `Sampled` value continued
by an exact witness on one side and an `IdealProximity` certificate on the
other. The payload type of a second, differently typed continuation is not
exercised anywhere in stage A at the same `Sampled` value.

Change: either write the second continuation through the other arm, or state
what was shown: one claim published twice, and a branch point whose payload
type reduces through the name. The audited evidence for the second option is
in F10.

### F4. BLOCKING. `stack_claim`'s comment gives a wrong reason

`pgg_tableau.v:276-280`: "a row whose two arguments give two different claims
is not expressible, because one port function answers for all of them". The
port is a function `forall R idx, SecurityPort (amf_sample f R idx)` and
`SecurityPort` is a `Variant`, so a function may return `ExactIndependence` at
one index and `SpectralDecay` at another; nothing in the type forbids it. What
forbids it is that `certify_exact` and `certify_spectral` are the only
statements that build a port, and each writes one constructor uniformly
(`pgg_tableau.v:622`, `:637`).

The counter-example was not compiled: no instance in the tree holds both an
`ExactWitness` and a `SpectralCert` over one sample adapter, so the branching
port cannot be written today. The reason in the comment is still the wrong
reason.

Change: give the statement reason, not the function-type reason.

### F5. SHOULD-FIX. C's blast radius omits the sibling probe, which it breaks

`STATUS.md` records "There is exactly one `conclude` in the whole tree outside
the framework". `notes/probes/2026-09-19-kim-spectral-arm/kim_spectral_rows_probe.v`
holds three more, and two of them are rows that stop compiling under the
weakened obligation:

```
kim_spectral_rows_probe.v:288  ;;; conclude five_card_reprice39 of (fun R _ => five_card_pow2_39_split R)
kim_spectral_rows_probe.v:365  ;;; conclude five_card_reprice_inv25 of (fun R _ => five_card_inv50_split R)
```

Compiled against the stage-A copy, `:288` fails with

```
The term "five_card_pow2_39_split R" has type "2 ^- 40 + 2 ^- 40 = 2 ^- 39"
while it is expected to have type
 "... | SpectralDecay cert =>
     is_true (cert_eps cert <= odflt (cert_eps cert) (five_card_reprice39 R))"
```

Wrapping both payloads in `ssr_ext.eqW` makes the file compile (rc=0), which is
the same one-token fix `pgl27_rows.v:382` took. The third occurrence, the
recorded `Fail` at `:299`, still fails.

The Kim batch is an open landing, so D2 owes these two lines. Change: add a
`kim_spectral_rows_probe.v` block to D2 naming `:288` and `:365` and the fix.

### F6. SHOULD-FIX. C degraded an isolating counter-probe

`pgl27_rows.v:425-428`, the comment on the `Fail` at `:429`, says the
rejection is what "keeps a row from publishing a bound that holds only at the
field a reader happened to pick". Under the weakened obligation a correctly
quantified payload of the old relation is rejected too, so the `Fail` no longer
isolates the quantification. Both measured in the repl:

| payload | quantified over `idx` | relation | rejected |
|---|---|---|---|
| `pow2_split` | no | `=` | yes |
| `(fun R _ => pow2_split R)` | yes | `=` | yes |
| `(fun R => ssr_ext.eqW (pow2_split R))` | no | `<=` | yes |

Change: keep the existing `Fail` and add the third row above as the isolating
one, or restate the comment to say that two things are wrong with a bare
`pow2_split` after C.

### F7. SHOULD-FIX. `conclude`'s payload is a second door for an instance's mathematics

`pgg_tableau.v:40-43` still says "The mathematics of a particular instance
never appears as a line: it enters only as the witness or the certificate a
certify statement takes", and `:629-630` says "The two certify statements are
the only lines through which an instance's own mathematics enters a row".
Under the equality obligation the `conclude` payload could only be a numeric
identity. Under `<=` it can be an arbitrary inequality about the instance's own
certificate: the Kim case compiled here supplies
`ltW (kim_centi_cert_eps_lt R idx)`, whose content is
$2\sqrt5\,(1/80)^7 < 2^{-39}$. Both sentences escape on the word "line", since
`conclude` is a terminal, but the paragraph at `:40-46` asserts that everything
outside the lines is framework post-processing, and that is no longer so.

Neither sentence is in the G3 list.

Change: say in the `:40-46` paragraph that `conclude` carries one instance
obligation, the comparison of the published number with the row's own.

### F8. SHOULD-FIX. `port_reprice` is sound only for a monotone arm, and nothing says so

`RepricePayload`'s spectral branch is sound because `SpectralPropAt cert c` is
`var_dist ... <= c`, monotone in `c`, and `port_reprice` closes by
`le_trans`. Stage B adds an arm whose certificate carries a distance; that arm
needs a third branch in `RepricePayload`, a third case in `port_reprice`, and
a proof that its proposition is monotone in its number. Nothing in the
framework enforces the monotonicity, and the comments do not name it as the
condition.

Change: one clause in the `RepricePayload` comment, that the obligation is an
upper bound because each numeric arm's proposition is monotone in its number,
and that an arm whose proposition is not owes a different obligation.

### F9. SHOULD-FIX. Three wording defects in the new and rewritten comments

- `conclude` (`:680`) reads "The terminal publishing a row's accumulated bound
  as an upper bound of it". It publishes an upper bound **of** the accumulated
  bound. The index line at `:65-66` already says it correctly, so the body
  contradicts the index.
- `RepricePayload` (`:646-651`) still says a spectral port is "republished
  at" a number, the word the change retires everywhere else. One word per
  concept.
- `SpectralViewDecay` names a claim that is not about a view. `ExactProp`
  bounds `sa_coalition_view`, the executed reader; `SpectralPropAt` bounds
  `fdistmap (static_coalition_obs C x) (sa_cut_dist sa)`, the static reading,
  and `spectral_tail` never consumes the link lemma of `Sampled` (the spec
  says so at its own lines 36-40). A paper table printing
  "claim = SpectralViewDecay" tells a reader the row bounds what a coalition
  sees when it runs the protocol, which the certificate does not prove. The
  pre-existing projection name `view_indist_of` has the same defect; K
  propagates it into the vocabulary the table prints.

Change: for the third, a name that says static reading, for instance
`SpectralReadingDistance` beside `ExactViewIndependence`, and then fix
`view_indist_of` in the same pass so the file keeps one word per concept.

### F10. NOTE. The claim is provably constant, so the six pins are a table column and not a theorem

Four lemmas, all closed by `erefl`, compiled in `a1_c_soundness.v`:

```coq
stack_claim (tableau_at (@certify_exact x q p)) R idx = ExactViewIndependence
stack_claim (tableau_at (@certify_spectral x q p)) R idx = SpectralViewDecay
stack_claim (tableau_at (conclude c q pf p)) R idx = stack_claim q R idx
security_claim_of (publish a q pf t) R idx = stack_claim q R idx
```

The first two are universally quantified over the data, the payload, the field
and the index, so every row built through the two `certify` statements has a
claim that does not depend on `R` or `idx`, and both terminals carry it
through unchanged. The six per-row pins say nothing a reader could not read
off the `certify` line. What they are for is the paper's table: each pin is the
manifest's own `Check (erefl : ...)` idiom, recording per row the value the
table column prints. That is a good reason to keep them, and it is not the
reason the comments give.

Change: add the four lemmas beside `security_claim_of`, and say in the pins'
comment that they record the table column, the general fact being the lemma.

### F11. NOTE. An exact row may be published at any number

`a4_exact_reprice.v` compiles

```coq
Definition a4_row_exact_at41 : PublishedRowAt pgl27_reprice41 :=
  pgl27_dealt sample pgl27_exact_family
    certify ExactIndependence pgl27_exact_witness
    |> conclude pgl27_reprice41 by (fun R _ => tt)
    |> publish StaticExecutedOnly BaselineClassicalOnly.
```

The exact branch of `RepricePayload` is `unit`, so the terminal asks for
nothing and the published **type** advertises $2^{-41}$ while no conjunct of
the row mentions a number; the manifest row it publishes is
`pgl27_row_exact`, unchanged. This is pre-existing, since the baseline branch
was `unit` too, and it is newly relevant because K gives a paper's table a
column for the number: the column must be read through
`security_claim_of`, since a `PublishedRowAt c` at an exact claim says nothing
about `c`.

### F12. NOTE. A number at or above the ceiling is publishable, and that is the instance's business

`a1_c_soundness.v` compiles a row publishing exactly $2$, the ceiling
`var_dist_le2` gives for a variation distance, hence a true and vacuous
statement. Nothing should guard it in the framework: a guard would attach a
second obligation about infotheo's variation distance to every reprice, would
have to be repeated in the `unit` branch and in every future numeric arm, and
would put an instance's numeric judgement inside a framework the Tableau keeps
free of instance mathematics. The discipline belongs where the Kim probe
already puts it, one lemma per published number comparing it with $2$
(`kim_biased_cert_eps_lt2`, `five_card_reprice_inv25_lt2`). Note for a landing
that `var_dist_le2` exists only in
`notes/probes/2026-09-19-kim-spectral-arm/var_dist_injective_probe.v:41` and
in no production file.

### F13. NOTE. Further D2 seed items, found by searching the tree

Each is a sentence the tree states without naming any of the searched
identifiers, which is why a name search misses it.

| file:line | text | why it moves |
|---|---|---|
| `manifest/pgg_tableau.v:39-41` | "The mathematics of a particular instance never appears as a line: it enters only as the witness or the certificate a certify statement takes" | F7 |
| `manifest/pgg_tableau.v:329-330` | "so a terminal can restate a finished row at the number a paper cites without reproving the arm" | after C, at any upper bound of its own; also uses "restate" for what `conclude` does, colliding with the `restate` terminal |
| `manifest/pgg_tableau.v:387` | "the family a terminal leaves when it republishes a row" | the retired word |
| `manifest/pgg_tableau.v:408` | "because a terminal that republishes the bound hands back a record" | the retired word |
| `manifest/pgg_tableau.v:590-591` | "The two certify statements are the only lines through which an instance's own mathematics enters a row" | F7 |
| `instances/pgl27/pgl27_rows.v:39-41` | "the reprice of the word row's bound from 2^-40 + 2^-40 to 2^-39, which moves a number and proves nothing new about a coalition" | header paragraph, not the index line D2 already lists |
| `security/pgg_mixing.v:304` | the English word "conclude" | D2 names only `legacy/reconstruct/ag_code.v:163` as the English-word hit; there are two |

Checked and confirmed unchanged: `manifest/pgg_analysis_manifest.v:22` and
`:702`, both "The record stores no theorem", which K's comments cite and which
K leaves true; the manifest's pins and header tables, which hold no reprice
name and no `pgl27_row_word39`.

### F14. NOTE. Two smaller things

- The `Definitions` index of `pgg_tableau.v` follows file order except for
  `stack_claim`, which is listed after `certify_spectral` and defined at
  `:281`, before `StackProp`.
- `assumptions_report.v` prints the lemmas and the readers but not the
  published rows the landing would cite, `pgl27_row_word39`, `t0_row_uniform`
  and `t0_row_uniform_transfer`; `STATUS.md` calls the list "Every new or
  reproved statement". `a3_kim_reprice.v` prints a published row through the
  weakened terminal and reports the same three boolp constants and nothing
  else, so the floor is what the report says it is.

## Question by question

### 1. C, soundness

`<=` is sound for every arm that carries a number. `SecurityPort` has two
constructors and only `SpectralDecay` carries one; `PortProp c (SpectralDecay
cert)` is `SpectralPropAt cert (odflt (cert_eps cert) (c R))`, whose body is
`var_dist ... <= c`, so it is monotone in `c`, and `port_reprice` closes the
step by `Order.POrderTheory.le_trans`. The soundness is conditional on that
monotonicity and nothing states the condition, which is F8.

The exact arm is untouched: the exact branch of `RepricePayload` is `unit` in
the baseline and after C, `PortProp c (ExactIndependence w)` is `ExactProp w`
with no occurrence of `c`, and `port_reprice`'s exact case closes by `//=`.

A program that does not reprice never builds a `RepricePayload`. `publish` takes
`pf : BridgedProp c q`; at `c := no_reprice` that type is exactly
`StackProp AnalysisBridged q`, which `certify_exact` and `certify_spectral`
return, so `... certify SpectralDecay cert |> publish t a` typechecks with no
obligation at all (`a1_row_word_plain`). When `conclude no_reprice` is written
explicitly the obligation is `cert_eps cert <= cert_eps cert`, which is a
proposition and not `unit`: `(fun R _ => Order.POrderTheory.lexx _)` is
accepted and `(fun R _ => tt)` is rejected, both compiled.

No row can publish a number below what it proved, for two independent reasons,
both compiled. First, the obligation type at a smaller number is empty:
`pgl27_word_reprice41_false` refutes
`cert_eps (@pgl27_word_cert R secretP) <= odflt ... (pgl27_reprice41 R)` at
every real field and every index, and `RepricePayload` demands it at every
field and index, so no term inhabits it. The recorded `Fail pgl27_row_word41`
is a unification failure of $2^{-39}$ with $2^{-41}$ in the expected type, so
by itself it only rejects that payload; the refutation lemma is what closes the
route, and the pair is adequate. Second, there is no ratchet: `conclude`'s
proof argument is `StackProp AnalysisBridged q`, the proposition at the row's
**own** bound, never at a number a previous `conclude` named, so a second
`conclude` on a concluded row is rejected with

```
(cannot unify "BridgedProp pgl27_reprice39 q" and "StackProp AnalysisBridged q")
```

`restate` is not a third route: `RestatedTableau` holds no `AnalysisPathRow`,
so nothing it produces can be published.

A number at or above the ceiling $2$ is publishable and the statement is true
and vacuous. See F12: this is the instance's business, not the framework's.

### 2. C, what it buys

The motivating program elaborates. Compiled in `a3_kim_reprice.v` against the
stage-A copy of the Tableau:

```coq
Definition a3_row_repeated39 : PublishedRowAt five_card_reprice39 :=
  five_card_committed
    sample kim_centi_family
    certify SpectralDecay kim_centi_cert
    |> conclude five_card_reprice39
         by (fun R idx => Order.POrderTheory.ltW (kim_centi_cert_eps_lt R idx))
    |> publish IdealFinite BaselineClassicalOnly.
```

`Print Assumptions` on it gives the three boolp constants and nothing else.

What this buys is exactly rule (2). Two further results compiled beside it:

```coq
Lemma a3_row_repeated39_atE :
  published_at a3_row_repeated39
  = published_at five_card_row_repeated_spectral_tableau.
Proof. by []. Qed.

Fail Definition a3_kim39_atE :
  published_at five_card_row_repeated39
  = published_at five_card_row_repeated_spectral_tableau := erefl.
```

Under the equality obligation the Kim probe could not publish $2^{-39}$ from
the certificate that proves $2\sqrt5\,(1/80)^7$. It had to build a second
certificate at the constant, `kim_centi_marginal_bound40`,
`kim_centi_cut_mixing40` and `kim_centi_cert40`, so the row at the paper's
number and the row at its own number were two rows holding two different
`AnalysisBridged` coordinates, which the `Fail` above records. Under `<=` they
are one row published twice. That is the ledger row C3's real content, and it
is stronger than "a row may publish a constant a paper cites": it is that one
security claim keeps one chain.

The cost is F5: two `conclude` payloads of the Kim probe stop compiling and
need `ssr_ext.eqW`.

The wiring cost of joining the two probe directories was five supporting
compiles and one patch of two lines in a scratch copy, within budget.

### 3. T0

The two continuations really do share one value: both are written from the
name `five_card_uniform_sampled`, one `Definition` of type `Tableau Sampled`,
so the algebra, the run, the three run facts and the model are one term in
both by construction and not by a conversion that happens to hold.

`t0_row_uniform_atE` is what it says. It is also weak, because the two
continuations are the same term: both write
`certify ExactIndependence five_card_exact_witness`. See F3.

T0's construction avoids the `pgl27_inline_reuse` and `psl211_row_vm_reuse`
rejections for the right reason, and the reason is stated. Those two Fails are
about two **prefixes** that reach the same run through different termination
proofs, so their observed executions are different terms and no typed evidence
crosses between them (`pgl27_rows.v:379-383`, `psl211_rows.v:295-301`). T0
has one prefix under one name, so there is nothing to diverge; the file says
so at `:56-60`, "all three are read off this single term".

The mutation fails for the right reason. Read in the repl, the cross-instance
mutation is rejected on the sample adapter,
`cannot unify "ExactWitness (amf_sample five_card_uniform_family R idx)" and
"ExactWitness (amf_sample (sp_f (tableau_at t0_s5_sampled)) R idx)"`, which is
the discrimination that matters.

Nothing in T0 relies on the five-card instance. `a2_t0_pgl27.v` reproduces the
whole shape at PGL(2,7), where the word family's index is `R.-fdist bool` and
the exact family's is `unit`: a named `Tableau Sampled` value for each family,
two published continuations from the exact one, and from the word one both a
plain `publish` and a `conclude ... by ... |> publish`, with

```coq
published_at a2_row_word = published_at pgl27_row_word_tableau
published_at a2_row_exact = published_at pgl27_row_exact_tableau
published_row a2_row_exact = pgl27_row_exact
```

all by `erefl`. So the spectral payload type also reduces through a name, which
T0 never tested, and the index type is irrelevant.

One gap for stage B. Both cross-model mutations compiled here are rejected on
the **index type**, `cannot unify "amf_index (sp_f (tableau_at (pgl27_dealt
sample pgl27_word_family))) R" and "unit"`, because the two PGL(2,7) families
happen to have different index types. Stage B's ideal and actual families over
one instance will share an index type, and no mutation in stage A exercises a
rejection between two adapters at one index type within one instance. T0's
cross-instance mutation is the closest, and it is across instances.

### 4. K, design

`SecurityClaim` is a faithful name for one of the two arms and not for the
other. `ExactViewIndependence` is right: `ExactProp` states independence of
`sa_coalition_view`, the executed reader, from the witness's secret, and the
header at `:22-28` says so. `SpectralViewDecay` is wrong twice.
`SpectralPropAt` bounds the distance between two `fdistmap
(static_coalition_obs C x) (sa_cut_dist sa)`, the **static** reading of the cut
law at two run arguments, and `spectral_tail` never consumes the link lemma of
`Sampled`, so the word "View" names the executed reader in one constructor and
the static reading in the other. And "Decay" names no decay: the bound is a
fixed number, not a quantity falling with a parameter. See F9.

The claim is provably constant in `R` and `idx` for every row built by
`certify_exact` or `certify_spectral`, and it should be a lemma. Four such
lemmas compiled, all by `erefl`; see F10. The six pins then say nothing new
mathematically, and their honest purpose is the paper's table column.

K respects rule (1). It adds no constructor to `SecurityPort` and no field to
`AnalysisPathRow`; it adds a reader at the level where a finished row is read,
which is where the design audit's h2 placed it, and the manifest stays below
the programs. The one design cost to record for stage B is that
`SecurityClaim` mirrors `SecurityPort`'s constructor set, so a new arm costs a
constructor in two places and a branch in `port_claim`; that is the price of a
claim name that `erefl` can decide, since a `SecurityPort` holds records and
`Prop`s and cannot be compared.

### 5. G2

The level is consistent. The rule is `at level 90, left associativity` like
every other statement rule, and `|>` already opens the `publish` rule at the
same level, so `prefix sample f certify A w |> conclude c by p |> publish t a`
associates left through both terminals. It parses the same way with and
without the `conclude` clause: `pgl27_row_word39` and `pgl27_row_word39E`
compile, and `a2_row_word` and `a2_row_word39` compile from one named `Sampled`
value, the first without the clause and the second with it.

The keyword measurement is real. `g2_keyword_measure.v:36` is
`Definition conclude_stays_bindable (conclude : nat) : nat := conclude.`, a
binder in a file that requires the extended surface, and it compiles. A `Check`
would indeed have passed either way; this does not. The negative half cannot be
recorded in the same file because a parse error is raised before `Fail` sees
the command, which the probe states. `by` follows a slot in three existing
rules already, so the surface spends no new identifier: the header's nineteen
stands. The header's sentence about `at` is F1.

Level-0 slots are the same as the existing clauses. `sample f`, `certify
ExactIndependence w`, `publish t a` and the three `by` clauses of `execute` all
put their slots at level 0; only the five-clause spectral rule uses level 10.
A lambda needs parentheses at level 10 as well, so nothing is gained by moving,
and level 0 keeps the precedent of the existing `by` clauses.

### 6. Headers and comments

Both headers read in full. What is true: `pgg_tableau.v:17`, "There are five
statements", since stage A adds no statement (`dealt_step`, `execute_step`,
`sample_step`, `certify_exact`, `certify_spectral`); `:28-30`, the clause on
`security_claim_of`; `:43-46`, that of the three terminals only `conclude`
returns a tableau, that it leaves the data and the arms untouched, and that the
real moves only upward; the whole `Definitions` and `Key results` index, apart
from the ordering in F14; `pgg_tableau_syntax.v:36`, "The separator of the two
terminal rules is |>", since `|>` now opens two rules; `:67-69`, that
`conclude` follows a literal and stays an identifier, which
`g2_keyword_measure.v` measures; `:74-80`, since the new rule binds nothing.

What is not: `pgg_tableau_syntax.v:70` about `at` (F1), and the first half of
the paragraph at `pgg_tableau.v:40-43` (F7).

The three rewritten comments are otherwise in the right form, fact then
position, with no status word, no effort estimate and no tactic. `port_reprice`
names the monotonicity of the spectral arm's proposition, which is the fact the
statement rests on and not a proof sketch. The defects are the wording of
`conclude`'s first sentence and the retired word in `RepricePayload` (F9).

Of the four new declarations, `port_claim` and `security_claim_of` are right.
`SecurityClaim` carries F2 and `stack_claim` carries F4.

### 7. D2

The list is right where it is a name search, and it misses seven sentences and
one code site. Seven are in F13, one in F5. The `Fail` accounting is right in
its count, twelve in the four rows files at the baseline, and wrong in its
reason for the twelfth (F6). The claim that the manifest, the client and the
facades are untouched is correct and was rechecked.

### 8. Rules (1) and (2)

Nothing in stage A violates rule (1). C changes a terminal's obligation, G2 a
surface rule, K adds a reader at the published row and no constructor to
`SecurityPort`, and T0 changes nothing.

C strengthens rule (2), measurably: `a3_row_repeated39_atE` shows the repriced
row and the row at its own number holding one `AnalysisBridged` coordinate,
where the equality obligation had forced two certificates. T0 as written does
not demonstrate rule (2), because its two rows carry one claim (F3). One shape
outside rule (2) is reachable and was already reachable at the baseline: an
exact row may be typed at any `Reprice` (F11), so a published type may name a
number no conjunct of the row mentions.
