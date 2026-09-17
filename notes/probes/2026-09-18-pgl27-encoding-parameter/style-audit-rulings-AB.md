# Coordinator rulings on style audits A and B (2026-09-18)

Criterion for unused declarations (user, 2026-09-17): a declaration stays only
if the paper will claim it or later work needs it as a premise. The probe
copies under `notes/probes/` are the record of anything deleted.

Paper check: `paper-wadt2026/main.tex:1378-1399` claims the orbit census, the
collision counts m, and the leakage values. It cites no `_neq` lemma, no
`collision_ratio` lemma and no `views_uniq` lemma. The real-valued closed
forms now carry the rational values in the kernel, so the nat ratio
identities no longer support any claim.

## Audit A

| id | ruling |
|----|--------|
| T1 | ACCEPT. Header: no statement names a deck pair; two proofs use `orbit_encode` as a witness for a fact about positions alone. |
| T2 | ACCEPT. Rename `pgl27_enc_view_mutual_info_ge_one` to `pgl27_enc_view_mutual_info1_card_ge`; update callers and headers. |
| T3 | ACCEPT. Prefix the declaration comments with the declaration name, as the sibling files do. |
| T4 | ACCEPT the proposed comment for `pgl27_leak_coalitionE`. |
| T5 | MODIFIED. `lib/proba_entropy_ext.v` must not be edited (rebuild cost). Hoist `mutual_info_RV_le_entropy` above `Variable e`. |
| T6 | ACCEPT. Two sections: positions-only block, then the block over `e`. |
| E1 | REJECT. The fixed-pair twin in the frozen file `pgl27_secrecy.v` is `pgl27_view_leakage_le`; the generic name mirrors it. |
| E2 | `enc_code_size`: Local if used in the file, otherwise delete. `enc_code_uniq`: delete (unused, not a paper claim, no later premise). Update the header. |
| E3 | ACCEPT. |
| E4 | REJECT. Keep `@PGL27Encoding`. |
| R7-1, R5-1, R7-4 | SUPERSEDED: all `pgl27_r7_collision_ratio_*` and `pgl27_r5_collision_ratio_*` are DELETED (unused; the closed forms carry the values). Remove their header entries. |
| R7-2, R5-2 | SUPERSEDED: all six `_neq` lemmas are DELETED (unused, not claimed; the strict inequalities the paper could claim are `pgl27_r7_view_mutual_info_k6_lt1` and `pgl27_r5_view_mutual_info_k4_lt1`). Remove header entries. |
| R7-3 | ACCEPT the proposed header text. |
| R7-6 | `pgl27_r7_views_uniq_three`, `pgl27_r5_views_uniq_three`: DELETE. `pgl27_r7_collisions_three`, `pgl27_r5_collisions_three`: KEEP (row of the census table the paper quotes). |
| R5-3 | DELETE `pgl27_r5_views_uniq_six`, `pgl27_r5_views_uniq_seven` if no file uses them. |
| R5-4 | ACCEPT: keep both counts, add one source comment on derivability from the five-position count. |
| R5-5 | KEEP public. |
| R5-6 | `pgl27_r5_classK` public. `pgl27_r5_deck_ok`, `pgl27_r5_codeE`, `pgl27_r7_codeE`: Local unless a later file uses them. |
| R5-7 | ACCEPT the added sentence. |
| C1 | ACCEPT. One term, "code table": census parameter `deal` becomes `code`; `code_deal_r7`, `code_deal_r5` become `code_table_r7`, `code_table_r5`; prose follows. |

## Audit B

| id | ruling |
|----|--------|
| A1 | ACCEPT (must-fix). |
| A2 | ACCEPT: `pgl27_view_outside`, `pgl27_view_codesE` Local, header entries dropped. |
| A3 | ACCEPT. |
| A4 | ACCEPT. |
| A5 | REJECT (no change). |
| B1 | DELETE `pgl27_code_comp_rowE` and its header entry. |
| B2, B3 | ACCEPT. |
| C1 | ACCEPT: say that a statement for every fixed pair is not a statement about the dealer that draws from all valid decks, because there the deck is itself random and carries information. |
| C2 | ACCEPT. |
| C3 | ACCEPT: Local, header entry dropped. |
| C4 | ACCEPT. |
