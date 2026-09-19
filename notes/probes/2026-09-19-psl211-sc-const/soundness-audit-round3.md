# Soundness and statement-comment audit of the sc_const probe, round 3

**Verdict: NO-GO** for "the probe's statements are true and its English says no
more than they prove".

Independent adversarial audit, 2026-09-19, branch `feat/kim-spectral-probe`,
after the second fix pass. Audited: `psl211_sc_const_probe.v`,
`psl211_sc_const_bound_probe.v`, `psl211_dealt_sc_const_probe.v`,
`psl211_deck_diag.v` and `STATUS.md`, each against the sources it names, against
`audit-soundness/audit_diag.v` and its log, and against `history/`. No file of
the repository was edited except this one. No Rocq process was started: the
brief records that no code changed since round 2 and that the four files
recompiled at rc=0. Python and grep only. I wrote none of what I audit.

The four `.v` files are clean. Both of round 2's blocking findings are applied,
all twelve SHOULD-FIX items and all seven NOTEs are dispositioned correctly, and
every remaining sentence of every statement comment is true of the lemma it sits
on. The one blocking finding is in `STATUS.md`: a measured number is restated
there in a form that is false as written and carries no diagnostic label, and
three sections later the document certifies that no such occurrence exists. It
is a two-line fix.

## 1. Disposition of round 2, item by item

Checked against the current text and the sources, not against the fix pass's own
table.

| round 2 | state now | evidence |
|---|---|---|
| B1 wrong field ordinal | **applied** | `psl211_sc_const_probe.v:103-106` carries the audit's replacement verbatim. `MkSpectralCert` (`manifest/pgg_tableau.v:133-142`) is `sc_b:134`, `sc_Hd:135`, `sc_ideal:136`, `sc_close:137`, `sc_const:138-142`; the record comment at `:124-130` says "Five fields". `STATUS.md:84-85` names the position and the two line ranges, which also closes N1. No "fourth" survives anywhere. |
| B2 three sentences denying a proved failure | **applied, and swept** | Section 2 below. Eight sentences changed, no denial survives in any file. |
| SF1 support hypothesis weakened in the comment | **applied** | `psl211_sc_const_bound_probe.v:177-182`, the audit's text, both hypotheses carried. |
| SF2 "the whole of the per-deck asymmetry" | **applied in the file, regressed in STATUS** | `psl211_sc_const_bound_probe.v:164-168` carries the audit's replacement and names no number. `STATUS.md:633` restates the number and misstates it. See R3-1. |
| SF3 660 distinct readings stated as fact | **applied** | `psl211_sc_const_probe.v:239-242` is the audit's replacement; the count moved to the source comment at `:243-247`, labelled "Measured once and not proved", citing `audit_diag.v` line 62 and the log. |
| SF4 stale header paragraph | **applied** | `psl211_sc_const_probe.v:27-31`, the audit's text. |
| SF5 "the public deck description" | **applied at all four sites** | `psl211_sc_const_probe.v:16-18`, `:151-154`, `psl211_sc_const_bound_probe.v:129-131`, `STATUS.md:309-312`. Whole-file grep for the phrase returns only the change-log row at `STATUS.md:636`. |
| SF6 twelve versus thirteen `Print Assumptions` | **applied, recounted here** | I count 13 from the sources: 4 in `psl211_sc_const_probe.v`, 7 in `psl211_sc_const_bound_probe.v`, 2 in `psl211_dealt_sc_const_probe.v`, 0 in `psl211_deck_diag.v`. `STATUS.md:72-77` says exactly that, with `psl211_dealt_raw_countE` as the `Closed under the global context` one. |
| SF7 Q8 landing not a one-argument generalisation | **applied** | `STATUS.md:292-303` and the homes row at `:405` both say the reading and its raw test must be abstracted, and give the shape. |
| SF8 reprice coordinate | **applied, with one shorthand to repair** | `psl211_sc_const_bound_probe.v:300-308`, `STATUS.md:13-18`, `:657-665`. The argument is right and labelled everywhere; see section 4 and R3-3. |
| SF9 proof strategy in a rendered comment | **applied** | Moved to the source comment at `psl211_sc_const_bound_probe.v:133-135`. |
| SF10 reduction warning in a rendered comment | **applied at the named site, survives at a second** | `psl211_sc_const_probe.v:119-121` is now a source comment. The same sentence is still inside the rendered comment of `psl211_dealt_decktbl`. See R3-4. |
| SF11 occupancy asserted flatly | **applied** | "Argued and not compiled" at `STATUS.md:28-29`, `:156-158` with `:166`, `:488-489`, and `psl211_sc_const_bound_probe.v:315-321`. |
| SF12 "proved at the field type" | **applied as wording** | `STATUS.md:325-330`, `:479-481`, `:563-565` and the source comment at `psl211_sc_const_probe.v:161-162` all say the lemma refutes the field's own equation at one pair of run arguments. The corollary is listed as not applied at `:709-713`. |
| N1 | applied | `STATUS.md:85`. |
| N2 | applied | `psl211_sc_const_probe.v:233`, "block line one, both labellings the identity". |
| N3 | applied | `psl211_sc_const_bound_probe.v:96-99` says nothing here spends the lemma, and why. |
| N4 | recorded, unchanged, correct | `psl211_dealt_sc_const_probe.v:240-242`, per round 2's own ruling. |
| N5 | applied | `psl211_dealt_sc_const_probe.v:233-236` names the two levels, so the opening and the closing sentence no longer read against each other. |
| N6 | applied | The roadmap clause is gone from `psl211_sc_const_bound_probe.v:378-386`. It survives at `STATUS.md:232`, which is its proper home. |
| N7 | recorded | `STATUS.md:250-262` and `:667-673`, both call sites named. |

## 2. The B2 sweep, checked independently

I searched all four `.v` files and `STATUS.md` for any sentence that (a) denies
the cross-chirality failure, (b) implies the two chiralities give the same
reading law at a fixed deck description, or (c) reads the refutation as a proof
of leakage or of no leakage.

- **(a)** Every occurrence of "not constancy in the secret", "not of constancy
  in the chirality" and "not a statement about the secret" is inside the change
  log at `STATUS.md:598-599` and `:610-617`, as a quotation of replaced text.
  No assertion of any of them survives. `STATUS.md:482-486` now carries the
  opposite as a "May not say" bullet, citing `psl211_alldecks_sc_const_false`
  through `psl211_perdeck_law_neq` (`instances/psl211/psl211_models.v:1036-1042`).
- **(b)** The only sentence putting the two chiralities on one law is
  `psl211_sc_const_bound_probe.v:127-129`, and it is the conditional the lemma
  proves: a law **satisfying** the field sends them to one law. The lemma's
  hypothesis is `sc_const_prop psl211_alldecks_params ideal`. Nothing asserts
  the equality unconditionally.
- **(c)** "Leakage" occurs at `psl211_sc_const_probe.v:25` and `:160`, at
  `STATUS.md:315`, `:323`, `:462`, `:490-493`. Every one is a denial of leakage
  tied to `psl211_alldecks_static_indep` (`psl211_models.v:503`, hypothesis
  `#|C| <= 5`, and the coalition here is three seats). None presents the
  refutation of the field as a proof of leakage, and none presents it as the
  no-leakage fact: that fact is always named as the separate theorem about the
  all-decks law.

The reason clause is sound at its source: `psl211_alldecks_row x = nth [::]
(psl211_class_tbl x.1) (val x.2.1.1)` (`instances/psl211/psl211_alldecks.v:116-123`),
so the chirality does select the table the block line indexes, and no pair of
run arguments moves the secret without moving the laid deck.

## 3. The fix pass's own item-6 list

Five items, each checked against the lemma it sits on.

1. **`psl211_samechir_view` names chirality true at both deck descriptions**
   (`psl211_sc_const_probe.v:241-242`). True. `psl211_samechir_raw_countE`
   decides `psl211_samechir_raw_count (psl211_perdeck_seq true) = 1` and
   `psl211_samechir_raw_count psl211_samechir_seq = 0`;
   `psl211_perdeck_seqE true` (`psl211_models.v:822-823`) ties the first to
   `psl211_alldecks_seq (true, psl211_perdeck_deal)` and `psl211_samechir_seqE`
   ties the second to `psl211_alldecks_seq (true, psl211_samechir_deal)`. The
   "card 0 to every seat outside the coalition" clause is right too: for
   `val i >= 3`, `nth 0 [:: 3; 2; 4] (val i)` is the default 0 and
   `psl211_code12 0` is `ord0`, which is what `psl211_perdeck_raw_view`
   (`psl211_models.v:847-850`) returns off the coalition.
2. **"block index" replaced by "block line"**. Applied at
   `psl211_dealt_sc_const_probe.v:23` and at the three sites in `STATUS.md`.
   One site is left: `psl211_deck_diag.v:9`. See R3-5.
3. **"proves the same-chirality failure at the field type" reworded**
   (`psl211_sc_const_probe.v:161-162`). True and now correct.
   `psl211_samechir_law_neq` is a `!=` of the two `fdistmap`s, which is the
   field's equation negated at one pair of run arguments, not a
   `~ sc_const_prop` statement. The reading named, cards 3, 2 and 4 at the three
   seats, is `psl211_samechir_view`.
4. **Value judgement removed** (`psl211_sc_const_bound_probe.v:315-321`). True,
   the block now ends "what this theorem excludes is a range of epsilon and not
   the arm".
5. **The `psl211_rows.v` replacement text carries the reprice caveat**
   (`STATUS.md:458-459`, "a row over this model that publishes its certificate's
   own bound publishes at least `1/660`"). True.

One positive finding beyond the list, which strengthens an argued claim round 2
left half-open. The occupancy argument needs every deck description to lay a
deck of twelve distinct cards, and the tree proves it for every description:
`psl211_alldecks_uniq (x : psl211_inputT) : uniq (psl211_alldecks_layout x)`
(`instances/psl211/psl211_alldecks.v:421-429`), through `ad_uniq_gen` and
`psl211_tbl_ok_mirrorT` / `psl211_tbl_ok_hexadT`
(`instances/psl211/psl211_blocks.v:346-351`, `psl211_tbl_ok` being 132 rows,
each a strictly ascending six-list below twelve). So "the uniform law on the
whole of `{perm 'I_12}` satisfies the constancy field" rests on a compiled fact
about the tables, not on an unchecked one. What stays unproved in Rocq is the
separate claim that the parametrization enumerates the valid decks once each.

## 4. SF8 as applied

**What is excluded.** `PortProp` (`manifest/pgg_tableau.v:363-369`) publishes
`odflt (cert_eps cert) (c R)` for a `SpectralDecay` port. `RepricePayload`
(`:610-614`) obliges a `conclude` to prove
`cert_eps cert = odflt (cert_eps cert) (c R)`. So today's published number is
`cert_eps cert` in every case, `cert_eps cert = sw_bound_eps (sc_b cert) +
sw_bound_eps (sc_b cert)` (`:345-347`), and
`psl211_alldecks_no_spectral_cert` makes that at least
`(#|pgg_G psl211_M|%:R)^-1`. The cardinal is 660 by `psl211_card`
(`instances/psl211/psl211_closure.v:703`), so "at least 1/660" is right.

**The weaker-`conclude` remark is right.** `SpectralPropAt cert c`
(`manifest/pgg_tableau.v:333-339`) is a variation distance bounded above by `c`,
so weakening the obligation in the direction the text names, from the equality
to `cert_eps cert <= odflt (cert_eps cert) (c R)`, forces the published number
to be at least `cert_eps` and the exclusion carries over. The text is explicit
about which weakening it means, which is what keeps the claim true.

**The marking is present at every place the remark appears**: the source comment
at `psl211_sc_const_bound_probe.v:310-313`, the answer paragraph at
`STATUS.md:28-32`, and the dedicated section at `:657-665`, which closes "That
second half is argued here and compiled nowhere." The SF8 disposition row at
`:639` restates only the compiled half, correctly.

One repair, R3-3: three of these four places abbreviate the obligation as
`cert_eps cert = c R`, which does not typecheck, `c R` being an `option R`.

## 5. SF3 as applied, and the log

`audit-soundness/audit_diag.log.txt` read end to end against
`audit-soundness/audit_diag.v`.

| quantity | `audit_diag.v` | log | what the text says |
|---|---|---|---|
| distinct readings at `(true, psl211_perdeck_deal)` | `:62` | `:56`, `= 660` | `psl211_sc_const_probe.v:243-247`, `STATUS.md:336`: 660 |
| L1 gap, two chiralities at block line 0 | `:66-68` | `:59`, `= 360` | `psl211_sc_const_probe.v:166`, `STATUS.md:335`: 360 of 660 |
| L1 gap, two block lines at chirality true | `:73-75` | `:62`, `= 600` | `psl211_sc_const_probe.v:165`, `STATUS.md:334`: 600 of 660 |

`audit_d0` is `(ord0, 1%g, 1%g)`, which is `psl211_perdeck_deal`
(`psl211_models.v:789`), and `audit_d1` is `(@Ordinal 132 1 isT, 1%g, 1%g)`,
which is `psl211_samechir_deal`. Every number the text quotes is the number the
log prints. The six recorded decks of `psl211_deck_diag.v:3-8` are reproduced at
log `:29-45` and agree entry for entry.

The derived numbers are consistent with each other: 660 distinct readings at
each of two deck descriptions with an L1 gap of 600 gives 300 readings exclusive
each way and 360 shared, and the `10/11` floor is 600/660, which is 600 times
the proved floor of 1/660. Both are labelled diagnostics at
`STATUS.md:338-343`, `:566-567` and `:716-717`.

**Labels.** Every occurrence of 660 distinct readings, of 600/660 and of 10/11
carries a label and none is called a theorem. `STATUS.md:290` gives provenance
rather than the word "diagnostic", which is enough because it names the L1 gap
and its source. One occurrence of 360 carries no label at all and misstates what
the number counts: `STATUS.md:633`. That is R3-1.

## 6. Mechanical checks

- **Line width.** Python over bytes, not `awk`. No line of the four `.v` files
  exceeds 80 bytes. Every banner rule is 79 bytes in all four files, so the
  claim at `STATUS.md:556-559` and change-log item 9 holds.
- **Banned vocabulary.** Word-boundary scan, case-insensitive, over the four
  `.v` files and `STATUS.md` for the three barred terms of the project's
  vocabulary rule and their inflections, nine forms in all: zero hits.
- **`Print Assumptions`.** 13 in the sources, split 4 / 7 / 2 / 0, matching
  `STATUS.md:72-77` exactly, including the per-file breakdown and the
  identification of `psl211_dealt_raw_countE` as the `Closed under the global
  context` one. The axiom content itself I did not re-derive, no compiler being
  run; round 2 read it off the fix pass's logs and the brief records a clean
  recompile.
- **Rendered comments.** Scanned every `(** ... *)` block for status words,
  "key", "headline", "used by", and positional pointers. One hit:
  `psl211_dealt_sc_const_probe.v:75`, which is R3-4. Every other "below" is
  numeric, as in "below the threshold" or "below twelve".

## 7. Findings

### BLOCKING

**R3-1. `STATUS.md:633` and `STATUS.md:703`. A measured number restated in a
form that is false, unlabelled, and certified clean three sections later.**

Current, `STATUS.md:633`:

> | SF2 | `psl211_perdeck_fiber_true0`: "which is the whole of the per-deck asymmetry" replaced, 360 of the 660 cuts separate the two chiralities at this deck description, so one reading is the whole of what the refutation spends, not the whole of the asymmetry |

The measured quantity is `audit_l1gap`, which is
`\sum_v |mult_true(v) - mult_false(v)|` over the two 660-entry reading lists, and
it is 360. It is not a count of cuts drawn from the 660. Under the further
diagnostic that each chirality's 660 cuts give 660 distinct readings, 360 splits
as 180 cuts at each chirality whose reading the other chirality never produces;
and that further diagnostic was measured at chirality true only
(`audit_diag.v:62`), so even 180 is not established. There is no set of 360 of
the 660 cuts that the sentence can name. The probe's own comment at
`psl211_sc_const_probe.v:165-166` and `STATUS.md:335` both get it right, writing
it as an L1 gap.

The sentence also carries no label, while `STATUS.md:702-705` certifies:

> Checked and found clean: nothing in the four files or here says the spectral
> arm cannot be closed at all; 360/660, 600/660 and 10/11 are labelled
> `vm_compute` diagnostics at every occurrence; the unexcluded range reads
> `1/1320` in epsilon and `1/660` in the published number everywhere.

That claim is false of `:633`, which is the contradiction. The wording came
verbatim from round 2's own SF2 text, so it is an inherited error and not one
the fix pass invented; the replacement comment the same audit proposed drops the
number, which is why the `.v` file is clean.

Replacement for `STATUS.md:633`:

> | SF2 | `psl211_perdeck_fiber_true0`: "which is the whole of the per-deck asymmetry" replaced. The L1 gap of the two chiralities' reading multiplicity vectors at this deck description is 360 over 660 cuts, a `vm_compute` diagnostic of `audit-soundness/audit_diag.v` recorded at `audit-soundness/audit_diag.log.txt:59` and not a theorem, so one reading is the whole of what the refutation spends, not the whole of the asymmetry |

Replacement for the second clause of `STATUS.md:703-704`:

> every occurrence of 360/660, 600/660 and 10/11 names the quantity an L1 gap
> and names its source, the `vm_compute` diagnostic or the auditor's
> measurement, and none of them is called a theorem;

### SHOULD-FIX

**R3-2. `STATUS.md:25-26`, `:442`, `:457-458`. "within `1/1320`" against
"`1/1320` or more" at `:155-156`.**

`psl211_alldecks_sc_const_false_close` takes `var_dist <= eps` and
`eps + eps < (#|pgg_G psl211_M|%:R)^-1`, so an ideal at variation distance
exactly `1/1320` is not covered. `STATUS.md:155-156` puts that ideal correctly
in the not-excluded set. The three "within `1/1320`" sites read as inclusive and
therefore claim the boundary point in both directions. The `.v` files are exact
throughout, writing "below" and "once twice epsilon stays below". `:457-458` is
the text a landing would copy into `instances/psl211/psl211_rows.v`, so it
should be exact.

Replacements:

- `:25-26`: "and at every ideal closer than variation distance / `1/1320` to
  the group-uniform law."
- `:441-443`: "and at every ideal closer than `1/1320` to the / group-uniform
  law."
- `:457-458`: "> support is exactly the shuffle group and at every ideal closer
  than / > `1/1320` to the group-uniform law,"

**R3-3. `psl211_sc_const_bound_probe.v:304-305` and `:311-312`,
`STATUS.md:15-16` and `:663`. `cert_eps cert = c R` does not typecheck.**

`c R` is an `option R`. The obligation is
`cert_eps cert = odflt (cert_eps cert) (c R)`, which `STATUS.md:659-660` writes
correctly. The shorthand is worst at `psl211_sc_const_bound_probe.v:304-305`,
where the previous clause has just written `odflt (cert_eps cert) (c R)` as the
published number.

Replacement for `psl211_sc_const_bound_probe.v:300-308`:

    (** psl211_alldecks_no_spectral_cert — no spectral certificate over the
        all-decks run of the twelve-card chirality instance carries a shuffle
        bound epsilon below 1/1320, the hypothesis holding twice that epsilon
        below the reciprocal 1/660 of the group order. A row publishes
        odflt (cert_eps cert) (c R) at its own reprice coordinate c, and the
        obligation of conclude is today the equality of cert_eps cert with
        that published number, so what this excludes is every published
        number equal to cert_eps: at least 1/660, against a shuffle whose
        single-card marginal error this instance proves to be exactly zero. *)

Replacement for the source comment at `psl211_sc_const_bound_probe.v:310-313`:

    (* Argued and not compiled: the exclusion survives a weaker conclude. The
       proposition a row carries is SpectralPropAt cert c, a variation distance
       bounded above by c, so an obligation weakened from that equality to
       cert_eps cert <= odflt (cert_eps cert) (c R) could only let a row
       publish a number larger than cert_eps, never a smaller one. *)

`STATUS.md:15-16`: write ``the equality `cert_eps cert = odflt (cert_eps cert)
(c R)` (`RepricePayload`, `:610-614`)``. `STATUS.md:663`: write ``an obligation
weakened to `cert_eps cert <= odflt (cert_eps cert) (c R)` ``.

**R3-4. `psl211_dealt_sc_const_probe.v:75-77`. SF10's sentence survives in a
rendered comment at a second site.**

Current `:72-77`:

    (** psl211_dealt_decktbl b — the encoder deck of chirality b as a twelve-entry
        position-to-code table: the heart codes 0 to 5 ascend along the
        representative row of the system b names and the club codes 6 to 11
        ascend along its complement. Only raw nat data is counted below, the
        ordinal enumeration going through an opaque decision that does not
        reduce. *)

The last sentence is the reduction warning SF10 had moved out of the rendered
comment of `psl211_perdeck_coalition_le3`, plus a positional pointer. Same
sentence, second file.

Replacement:

    (** psl211_dealt_decktbl b — the encoder deck of chirality b as a
        twelve-entry position-to-code table: the heart codes 0 to 5 ascend
        along the representative row of the system b names and the club codes
        6 to 11 ascend along its complement. *)
    (* Only raw nat data is counted from here on, the ordinal enumeration
       going through an opaque decision that does not reduce. *)

**R3-5. `psl211_deck_diag.v:9`. "Block index" against the file-wide "block
line".**

The fix pass swept five sites and recorded them; this is a sixth, in the fourth
`.v` file, which change-log item 10 left untouched. The referent is the same,
the first coordinate of a deck description.

Current (80 bytes):

    (* Block index zero of either chirality's table is therefore not the          *)

Replacement, also 80 bytes, one space added for the closing column:

    (* Block line zero of either chirality's table is therefore not the           *)

### NOTE

**N3-1. `psl211_sc_const_probe.v:89-90`, "The run argument carries the
secret".** `sc_const_prop` is stated over an arbitrary `E : ExecutionParams A`,
and `ExecutionParams` says of its own first field
(`protocol/pgg_instance.v:282-284`) "It need not be the secret carrier". What is
generic is that `ex_expected : ex_inputT -> pga_secretT A` makes the secret a
function of the run argument, which is what the "at least constancy in the
secret" clause needs. "The run argument determines the secret" would be exact.
Both modes this probe treats satisfy the stronger reading anyway:
`dealt_secret_params` sets `ex_inputT := pga_secretT A` with `ex_expected := id`
(`:398-401`), `pga_secretT psl211_algebra` is `bool` (`psl211_exec.v:85`), and
the all-decks carrier has the secret as `fst` (`psl211_alldecks.v:107-109`).

**N3-2. `STATUS.md:284-286`** names the two decks without their chirality, which
is the imprecision the fix pass repaired in `psl211_samechir_view`. The
preceding paragraph at `:276-281` establishes chirality true for both, so the
context supplies it.

**N3-3. `STATUS.md:432` cites `psl211_rows.v` "lines 40-45"** for the passage a
landing rewrites. The quoted text runs from line 40 to the first sentence of
line 44; line 45 begins a different clause. Inherited from round 1.

**N3-4. The 1/660 in the English is never tied to its lemma.** The theorems are
stated at `(#|pgg_G psl211_M|%:R)^-1`; the cardinal is `psl211_card`
(`instances/psl211/psl211_closure.v:703`), which the probe imports and never
names. One citation in the `psl211_alldecks_no_spectral_cert` comment would let
a reader check the number without searching.

**N3-5. `psl211_dealt_sc_const_probe.v` header has a ragged right margin**,
lines of 78, 79 and 80 bytes mixed, against the uniform 79 of the other two
headers. Cosmetic, pre-existing, and not claimed otherwise by `STATUS.md`, whose
formatting claim is only that no line exceeds 80 bytes and that every banner
rule is 79. Both hold.

## 8. Scratch record

No file written outside this one, and no Rocq process started. All counting was
done with inline Python over bytes and with grep: line widths and banner widths,
the banned-vocabulary scan, the `Print Assumptions` census, the rendered-comment
scan for status words and positional pointers, and the label sweep over 660,
360/660, 600/660 and 10/11. `audit-soundness/audit_diag.log.txt` was read
against `audit-soundness/audit_diag.v` line by line for section 5.
