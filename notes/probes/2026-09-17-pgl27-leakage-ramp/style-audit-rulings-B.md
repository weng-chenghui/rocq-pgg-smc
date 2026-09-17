# Style audit B: pgl27_table_bridge.v, pgl27_view_census.v

Auditor: rocq-auditor on Opus, read-only, 2026-09-17, at commit 4c2a264.
Verdict: PASS-WITH-FIXES. 5 blocking, 6 should, 7 nit. Line numbers refer to
HEAD f202e9f (these two files are unchanged since 4c2a264).

| ID | Where | Finding | Coordinator ruling |
|---|---|---|---|
| B1 | census 118-163 | pgl27_view_eq_codes_{harmonic,equianharmonic,five,six} are hypothesis-free instantiations of pgl27_view_eq_codes, unused | KEEP. They are the evidence the design note cites for claim C6 and the user asked for a copy of the probed code. List them in the header. The deletion is surfaced to the user as a recommendation |
| B2 | census 714-744 | Four dead Local lemmas pgl27_code_ambiguous_samples_* | DELETE |
| B3 | bridge 15-16, 48-57 | pgl27_table_row_ok and pgl27_group_table_rows_ok are unused | KEEP public. They are claim C1 of the design note. Reword the comment so it says the row certificate is independent of the perm_eq route that the bridge itself uses |
| B4 | census header 20-27 | Header lists 3 of 15 public results | APPLY the auditor's header, extended with pgl27_view_eq_codes_*, pgl27_masked_view_eq, pgl27_view_outside and the seven-position siblings added below |
| B5 | census 759-760 | Local eqb_trueE reproves mathcomp eqb_id | APPLY: delete it, use eqb_id at both call sites |
| S1 | census 315-317 | Scopes opened mid-file, one hypothesis in two spellings | APPLY: move the three Local Open Scope lines right after `Import GRing.Theory Num.Theory.`, write `(x < 8)%N` everywhere |
| S2 | census 655-681 | card_pgl27_code_ambiguous_true has two unused uniq premises | APPLY: drop them and fix the one caller |
| S3 | census 372-466 | pgl27_table_ambiguousP repeats two derivations four times | APPLY: hoist Hout and the Hcomp/Hcr/Hvc/Heq chain above the split. If a hoisted form does not typecheck after honest diagnosis, keep the original proof and report |
| S4 | both | Both files reach Local names of pgl27_mixing.v by qualified name; census duplicates a bridge derivation | APPLY the re-export layer in pgl27_table_bridge.v: `pgl27_ptbl`, `pgl27_ptbl_inj`, `pgl27_ptbl_mem`; reuse pgl27_ptbl_mem inside pgl27_table_perm_surj; census drops its Local pgl27_ptbl_mem, uses the bridge names, and drops pgl27_mixing from its Require if the build allows. pgl27_mixing.v is NOT edited |
| S5 | bridge 59-60, 97-98 | Type-shape and non-type-honest second sentences | APPLY the auditor's texts |
| S6 | census 49-50, 55-56, 254-255, 269-270, 285-286, 300-301 | Missing domain position, omitted content of the definitions | APPLY the auditor's texts |
| S7 | census 358, 468, 483, 490 and about sixteen Local helpers | No statement comment | APPLY the four given texts; one declarative line for each remaining Local helper |
| S8 | census 38 | variation_dist and entropy imported, unused | APPLY, build-checked |
| N1 | census 633 | Stray two-space indent | APPLY |
| N2 | census 581, 594, 610, 626, 655, 685 | Unannotated binders | APPLY |
| N3 | census 592 | Bare `Local Opaque pgl27_group_table.` | APPLY the plain comment |
| N4 | census 165, 576, 746 | Local names against MathComp grammar | APPLY for the three Local ones: map_uniq_inj_in, pgl27_code_view_row, uniform_pair_massE. Public pgl27_masked_view_eq keeps its name |
| N5 | census 472-481 | Nine-line pair injectivity | APPLY if it compiles, else keep |
| N6 | census 60-68 | R is a phantom parameter of pgl27_ambiguous_views | APPLY the appended sentence |
| N7 | bridge 28-32 | Family import block partly unused | SKIP. The block is uniform across instances/pgl27 |
| D1 | census after 313 | No seven-position sibling | APPLY: add pgl27_conditional_view_inj_seven (auditor's text) and pgl27_ambiguous_probability_sevenE in the siblings' form; pgl27_mutual_info.v uses the former in pgl27_reachable_view_entropy_sevenE. No pgl27_view_eq_codes_seven |

The auditor's full replacement texts for B4, S5, S6, S7, N3, N6 and D1 are
quoted in the fix agent's prompt and applied verbatim unless a line exceeds 80
columns or a name changed under S4 or N4.

## Replacement texts for audit B

### B4 header Key results (extend with the kept and the new lemmas)
```
(* Key results:                                                               *)
(*   pgl27_view_eq_codes == two masked views are equal exactly when their     *)
(*     listed coordinates are equal                                           *)
(*   pgl27_view_codesE == the listed coordinates of a protocol view are the   *)
(*     restricted composite of the shuffle and deal tables                    *)
(*   pgl27_conditional_view_inj == a repetition-free census view list makes   *)
(*     the conditional view map injective on the shuffle group                *)
(*   pgl27_ambiguous_probabilityE == the ambiguous-view event has probability *)
(*     pgl27_collisions S over 336                                            *)
(*   pgl27_conditional_view_inj_{harmonic, equianharmonic, five, six} and     *)
(*     pgl27_ambiguous_probability_{harmonic, equianharmonic, five, six}E ==  *)
(*     the same two results with that representative's side conditions        *)
(*     discharged by computation                                              *)
```
### S5, bridge 59-60
```
(** The PGL(2,7) shuffle whose table is census row [k]. It is the map along
    which every count over the 336 census rows is read as a count over the
    shuffle group the protocol samples from. *)
```
### S5, bridge 97-98
```
(** The shuffle named by census index [k] has census row [k] as its table.
    Row and shuffle therefore send each card position to the same place, so a
    statement proved about one transfers verbatim to the other. *)
```
### S6, census 49-50
```
(** The set of card positions named by the entries of [S], the coalition
    whose masked card values are the protocol observation. Entries of [S] at
    least eight name no position and repeated entries name one, which is why
    the results below assume every entry of [S] is below eight. *)
```
### S6, census 55-56
```
(** The coordinates of the masked view [v] at the positions listed by [S], in
    the order [S] lists them. It carries a coalition observation into the
    sequence form the nat collision census counts, so census multiplicities
    become multiplicities of protocol observations. *)
```
### S6, census 254-255, and the same shape for equianharmonic, five-position, six-position, seven-position
```
(** For each fixed orbit secret, distinct shuffles give the harmonic
    coalition distinct observations. A harmonic observation therefore pins
    down the shuffle once the secret is known, so its posterior on the secret
    is carried entirely by which secrets can produce it. *)
```
### S7, above pgl27_code_ambiguous
```
(** Census row [u.2] dealt under secret [u.1] restricts to an observation of
    [S] that both secrets can produce. It is the collision event of the nat
    census, stated per row rather than as a count. *)
```
### S7, above pgl27_table_sample
```
(** The protocol sample named by a secret and a census index. It transports
    the uniform law on the 2 * 336 table samples to the uniform law on secret
    and shuffle that the protocol actually runs. *)
```
### S7, above pgl27_ambiguous_samples
```
(** The secret-and-shuffle pairs whose coalition observation is reachable
    under both orbit secrets. Its cardinality over the 2 * 336 executions is
    the probability that one observation leaves the secret undetermined. *)
```
### S7, above pgl27_code_ambiguous_samples
```
(** The secret-and-row pairs satisfying the census collision event, the nat
    counterpart of pgl27_ambiguous_samples. *)
```
### N3, plain comment above `Local Opaque pgl27_group_table.`
```
(* Sealing the 336-row table keeps the cardinality proofs below from
   expanding it during conversion. *)
```
### N6, pgl27_ambiguous_views
```
(** An ambiguous view is reachable under both orbit-class secrets. Such a
    view leaves the Boolean secret undetermined by the coalition. The real
    carrier [R] indexes the distribution the view map is typed against and
    does not change which views this set contains. *)
```
### D1
```
Lemma pgl27_conditional_view_inj_seven (R : realType) (b : bool) :
  {in pgg_G pgl27_M &,
    injective
      (fun g => pgl27_view R
        (pgl27_code_coalition rep_seven) (b, g))}.
Proof.
case: b.
- apply: pgl27_conditional_view_inj; first by vm_compute.
  by move/andP: pgl27_views_uniq_seven => [].
- apply: pgl27_conditional_view_inj; first by vm_compute.
  by move/andP: pgl27_views_uniq_seven => [].
Qed.
```
Note on wording: S6 and S7 use "observation" for what a coalition sees. Audit A
and audit C fix the word as "view". Apply these texts with "view" in place of
"observation" wherever the object is the coalition view, so the six files use
one word.
