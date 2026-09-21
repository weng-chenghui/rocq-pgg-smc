# Rulings on the audit of the dealer-dealt manifest-paths probe (2026-09-21)

Probe: `LEDGER.md` (Opus rocq-prover, M1 to M9 all GO; the main session
recompiled the new file and the fidelity file from source, no error). Audit:
`AUDIT.md` (one Opus auditor, read-only, GO-WITH-CHANGES, D1 to D21; saved by
the main session from the hand-back). Rulings by the main session. Where a
row says ACCEPT with no text, the auditor's replacement is the text to land.

| finding | ruling |
|---|---|
| departure 1 of the probe | ACCEPT: the two `_pathE` equate the published path with the manifest's typed path, as every other `_pathE` of the tree does and as the twelfth path did; the fidelity file keeps the two equations with the spelled right-hand sides |
| D1, D2, D3, D4 | ACCEPT |
| D5 | ACCEPT, AMENDED. The auditor's "agree in its other three" is a count the main session cannot verify. Land: "so the limitation is about this model's privacy at the card-identity observer and not about two inputs alone. At Path 12 the two run arguments are the two chiralities of one deal, a deck description being a chirality and a deal, so the limitation there is at one fixed deal." The lander checks the type of the all-decks run argument (`psl211_inputT`) before landing the sentence, and writes what the type is if it is not a chirality and a deal |
| D6, D7 | ACCEPT |
| D8 | ACCEPT: the corrected comment and the `Timeout 60 Check` of `dealt_observed_recovers` in both files; the compiler arbitrates the right-hand side, and the pin is not dropped |
| D9, D10, D11, D12, D13 | ACCEPT |
| D14 | ACCEPT |
| D15 | NO CHANGE: `dealt_secret` follows the facade's prefix rule and the all-decks alias `secret`; the shadowing is inside the module and harmless. The facade header says so in one clause |
| D16, D20 | the landing record states the fourth edit (the deleted source comment about the sealed closure table, correct because the new file seals nothing before that lemma) and saves the closure output |
| D17 | KEEP all five: the four coordinate equations make the adapter legible and the spec names them; `psl211_colour_of_reading_collides` is the recorded reason the post-processing runs one way |
| D18 | ACCEPT: the landing's fidelity file adds `Check (name : statement)` for the thirteen declarations that leave `psl211_reading_constancy.v` |
| D19 | ACCEPT: the dealer-dealt Check block of the manifest gets its own banner in the file's style, and is not filed under the transfer heading |
| D21 | ACCEPT: `psl211_dealt_observed_recovers` is added to `instances/psl211/psl211_models.v` beside its all-decks twin and the facade aliases it, so both halves of the facade have one shape (this widens the landing's closure to what requires `psl211_models.v`; one pass) |
