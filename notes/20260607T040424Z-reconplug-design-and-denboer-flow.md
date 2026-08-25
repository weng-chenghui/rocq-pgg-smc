# Reconstruction plug (`ReconPlug`) design, den Boer flow, and the plug-in mechanism

Note date: 20260607T040424Z

> **CORRECTION (post-audit).** Two parts of this note were found wrong by the
> v3->v4 adversarial re-audit and are superseded by the v4 merge spec
> (`docs/superpowers/specs/2026-06-07-pgg-protocol-merge-design.md`, §5b) and the
> audit note `20260607T*-gate-results-and-merge-decisions.md`:
> 1. **`rp_content` is a FIXED face map `face : 'I_5 -> 'I_5`, NOT `encode_bool ∘
>    fc_arrange`.** The latter is secret-dependent and type-incoherent
>    (`fc_arrange : bool -> bool -> seq bool`). The secret arrangement lives in
>    `ts_encode`/the starts (a uniq card-identity permutation); `content` is the
>    deck's fixed face readout. Reading `content (rho w (start_i))` then yields
>    face values, so the wire reveals faces not identities (faithful) and stays
>    `'I_5`. The Part 2 diagram lines "rp_content = encode_bool ∘ arrange" and
>    "STAGE 0b ... builds ReconPlug.rp_content = encode_bool ∘ arrange" are wrong
>    in that assignment; the arrangement is the encode, content is `face`.
> 2. **The den Boer rebuild is MEDIUM, not LOW.** Rebuilding the scheme over
>    `'I_5` plus proving the NET-NEW `ts_recon_perm_invariant` (three-consec
>    rotation-invariance) is real work, not a "one-case bijection." The rest of
>    this note (the bare-plug architecture, no-genus/no-curve for den Boer, the
>    plug-in mechanism, the 4-field record, recovery outside the session) stands.

Captures the agreed reconstruction-layer design for the protocol merge: the
pluggable `ReconPlug` record, the den Boer stage-flow under it, and how the plug
attaches to the piSMC program. Companion to the merge spec
(`docs/superpowers/specs/2026-06-07-pgg-protocol-merge-design.md`, Option C) and
the recovery survey (`20260607T015612Z-concrete-recovery-mechanisms-survey.md`).

Legend in the diagram: `[C]` canonical general-protocol component, `[E]` existing
code reused, `[N]` new (small) glue.

---

## Part 1: The `ReconPlug` design

Two pluggable slots, kept separate:

- Security slot: the monodromy group (`MonodromyReprWithGeneratorType`).
- Reconstruction slot: the `ReconPlug` (below).

The reconstruction plug, after dropping the recon-symmetry fields (they only
carried information when the recoverable scope was a proper subgroup of the
shuffle scope, which was the retired wreath case; every retained instance has
recover-scope = shuffle-scope = `pgg_G`):

```coq
Record ReconPlug (M : MonodromyReprType) := MkReconPlug {
  rp_scheme    : ThresholdScheme 'I_N 'I_N ;          (* the recovery scheme *)
  rp_content   : 'I_N -> 'I_N ;                        (* readout; id for position model *)
  rp_monodromy : pgg_gT M -> {perm 'I_(ts_T' rp_scheme).+1} ;
  rp_recon_invariant :
    @ts_recon_perm_invariant _ (pgg_G M) _ _ rp_scheme rp_monodromy ;  (* over the FULL group *)
}.
```

The optional genus/tradeoff certificate stays a separate decoration; an instance
that wants the security-threshold-tradeoff narrative wraps its plug:

```coq
Record CoveringScheme (M : MonodromyReprType) := MkCoveringScheme {
  cs_plug : ReconPlug M ;
  cs_data : CoveringData M ;
  cs_gap  : ts_T (rp_scheme cs_plug) <= ts_k (rp_scheme cs_plug) + 2 * cd_genus cs_data ;
}.
Notation cs_scheme cs := (rp_scheme (cs_plug cs)).    (* transparent back-compat *)
```

Design facts:

- Monomorphic `'I_N 'I_N` (Option C). `bool` is encoded as `{0,1} ⊂ 'I_5`; the
  wire stays `'I_N`, so no `pgg_data` change and no duality re-proof.
- Correctness (`pgg_hidden_invariant_perm`) and the profile (`run_*`) consume the
  bare `ReconPlug`. Only `cover_tradeoff`/rigidity consume `CoveringScheme`.
- den Boer plugs a bare `ReconPlug`, no `CoveringScheme`, no genus, no curve
  axiom. The AG-curve covering (genus>0) remains the shelved, unused path.

---

## Part 2: den Boer stage flow under the new design

```
  a : bool (Alice)            b : bool (Bob)
       │  Commit<dealer> a         │  Commit<dealer> b
       ▼                           ▼
  STAGE 0a  INPUT COMMITMENT  (generic stage)
     M=2 input-commitment stage                              [N]
     Commit / RecvCommit (from FCCommit/FCRecvCommit,
       five_card_session_types.v:119)                        [E]
       │ dealer holds (a,b)
       ▼
  STAGE 0b  ASSEMBLE (encode)
     fc_arrange a b   five_card_program.v:65                 [E]
     encode_bool : bool -> {0,1} ⊂ 'I_5                      [N]
     builds ReconPlug.rp_content : 'I_5 -> 'I_5
            (= encode_bool ∘ arrange)                        [N]
     layout is ts_valid (= fc_correct @ k=0)                 [E]
       │ secret s = encode_bool(a∧b) : 'I_5 ; layout : 5.-tuple 'I_5
       ▼
  STAGE 1  SPLIT / DEAL  (dealer, virtual)
     sample word w (the cut); announce letter
     exchange_dealer  card_exchange_pismc.v:210              [C]
       deals dealt_hand_content (rp_content plug) W j         [C+N]
     perm_table / word_eval                                  [C]
     group Z_5 = FiveCard_M (fc_sigma)                       [E]
       │ each party: its column (content values) + the letter w
       ▼
  STAGE 2  COMPUTE / SHUFFLE  (by parties)
     party selects the announced letter -> its dealt value
     exchange_player  card_exchange_pismc.v:227              [C]
     (relays an 'I_5 value; content already baked in Stage 1)
       │ 5 revealed 'I_5 values (shuffled face values)
       ▼
  STAGE 3  COLLECT  (verifier)
     exchange_verifier card_exchange_pismc.v:237             [C]
     buffer -> 5.-tuple 'I_5
       │ collected : 5.-tuple 'I_5
       ▼
  STAGE 4  RECOVER  (ts_recon, outside piSMC)
     run_recover = ReconPlug.rp_scheme.ts_recon              [C+N]
       = encode_bool ∘ fc_three_consec ∘ map decode_bool
         fc_three_consec  five_card_program.v:93             [E]
       │ recovered s' : 'I_5 ∈ {0,1}
       ▼
  STAGE 5  CORRECTNESS  (proof, over the FULL group G)
     pgg_hidden_invariant_perm : s' = s                      [C]
       pgg_sharing_framework.v:284 (no recon-group;
       invariance over pgg_G M)
     needs ReconPlug.rp_monodromy (Z_5 cut -> share perm)    [N]
       and ReconPlug.rp_recon_invariant
         (three-consec invariant over Z_5 = G)               [N] audit-verified
       and ts_valid (Stage 0b)                               [E]
     reduces to fc_correct                                   [E]
     NO CoveringScheme · NO genus · NO recon-group
       │ s' = encode_bool(a∧b)
       ▼
  STAGE 6  DECODE TO AND
     decode_bool s' := (s' == 1) = a && b : bool             [N]
     one-case bijection, reuses fc_correct                   [E]
       ▼
   a && b : bool   ← final result

  den Boer ReconPlug (one value, 4 fields):
    rp_scheme          : ThresholdScheme 'I_5 'I_5   (three-consec wrapper)  → Stage 4
    rp_content         : 'I_5 -> 'I_5  (arrangement readout, {0,1})          → Stage 0b/1
    rp_monodromy       : pgg_gT -> {perm 'I_5}  (cut on share slots)         → Stage 5
    rp_recon_invariant : ts_recon_perm_invariant over pgg_G (= Z_5)          → Stage 5

  SECURITY (parallel, not on the recovery path):
    fc_security_uniform : eps = 0   five_card_security.v                     [E]
```

---

## Part 3: How the `ReconPlug` plugs into the piSMC program

The piSMC program is parameterized by the plug. The plug appears at three points;
the program is otherwise identical across instances (this is the pluggability).

1. Dealer applies `rp_content` when building the dealt table. The readout is baked
   in here (the dealer knows the arrangement; the players and verifier never need
   it):

   ```coq
   (* generalized dealt hand: dealer applies the plug's content readout *)
   Definition dealt_hand_content (content : 'I_N -> 'I_N) (W : seq gT) (i : 'I_T)
       : seq 'I_N :=
     [seq content (rho w (tnth starts i)) | w <- W].

   Definition exchange_dealer (plug : ReconPlug M) PI W P_idx : sproc ... :=
     \pi{ ... ForList players ... =>
            Deal<player j> #(dealt_hand_content (rp_content plug) W j) ;
          ... ; Finish }.
   ```

   Position model uses `rp_content = id`, recovering today's
   `dealt_hand = [rho w (start_i)]` definitionally.

2. Player and verifier are content-agnostic and UNCHANGED. They relay/collect
   plain `'I_N` values; the content readout is already in the dealt value, so the
   wire and the `native_compute` duality proofs are untouched:

   ```coq
   exchange_player   (* relays the looked-up 'I_N value *)
   exchange_verifier (* collects the T revealed 'I_N values *)
   ```

3. Recovery applies `rp_scheme`, outside the session (as today):

   ```coq
   Definition run_recover (plug : ReconPlug M) (collected : T.-tuple 'I_N) : 'I_N :=
     ts_recon (rp_scheme plug) collected.
   ```

The bundle that makes plugging explicit is the profile, which carries the plug as
a field; `run_*` thread it, so swapping the plug swaps the whole reconstruction:

```coq
Record MonodromyProfile (R : realType) := MkMonodromyProfile {
  mp_M        : MonodromyReprWithGeneratorType ;
  mp_PI       : PGGInterface mp_M ;
  mp_security : SecurityWitness R mp_M ;
  mp_plug     : ReconPlug mp_M ;                 (* the pluggable scheme *)
}.

Definition run_dealer mp W P_idx := exchange_dealer (mp_plug mp) (mp_PI mp) W P_idx.
Definition run_party  mp i        := exchange_player  (mp_PI mp) i.
Definition run_verifier mp        := exchange_verifier (mp_PI mp) (enum 'I_T).
Definition run_recover_p mp coll  := run_recover (mp_plug mp) coll.
```

Plugging a concrete instance is then constructing the profile with that
instance's `ReconPlug`. The SAME `run_dealer`/`run_party`/`run_verifier`/
`run_recover_p` serve every instance; only `mp_plug` (and `mp_M`/`mp_PI`/
`mp_security`) differ:

```coq
(* den Boer: plug the bare three-consec ReconPlug *)
Definition den_boer_plug : ReconPlug FiveCard_M :=
  MkReconPlug fc_recon_scheme fc_content fc_cut_perm fc_recon_invariant.
Definition den_boer_profile R : MonodromyProfile R :=
  MkMonodromyProfile FiveCard_PI fc_security_uniform den_boer_plug.

(* s5x5: plug the product sum-mod ReconPlug (content = id) *)
Definition s5x5_plug : ReconPlug R_s5x5 :=
  MkReconPlug s5x5_ts id s5x5_monodromy s5x5_perm_compatible.
Definition s5x5_profile R : MonodromyProfile R :=
  MkMonodromyProfile s5x5_PI s5x5_security s5x5_plug.
```

The correctness proof side plugs the same value: `pgg_hidden_invariant_perm`
consumes `rp_monodromy` and `rp_recon_invariant` from `mp_plug`, over the full
`pgg_G M`. So one program, one correctness lemma, and the instance is selected
entirely by which `ReconPlug` is plugged into the profile.
```
