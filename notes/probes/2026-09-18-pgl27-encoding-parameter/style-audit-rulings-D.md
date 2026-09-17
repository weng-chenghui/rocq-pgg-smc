# Coordinator rulings on style audit D (2026-09-18)

| id | ruling |
|----|--------|
| D1 | ACCEPT (must-fix): both files adopt the `(** name — ... *)` convention. |
| D2 | ACCEPT: `pgl27_r7_view_mutual_info_ge7E`, `pgl27_r5_view_mutual_info_ge5E` become Local; `_determines` stays public. |
| D3 | ACCEPT. |
| D4 | ACCEPT option 2: `pgl27_r7_view_mutual_info_card_ge4`, `pgl27_r5_view_mutual_info_card_ge4`. Update `pgl27_encoding_compare.v` if it cites them. |
| D5 | ACCEPT if the single target still builds. |
| D6 | ACCEPT the proposed header text. |
| D7, D11 | ACCEPT the proposed comments. |
| D8 | ACCEPT. |
| D9 | ACCEPT. |
| D10 | ACCEPT: name the numbers. |
| D12 | ACCEPT: fix in `_r5` (two sizes, five and six, lie between the thresholds; wait, check: the thresholds are 5 and 7, the sizes strictly between are 6 only, and the sizes at which the two pairs differ are 5 and 6; state whichever the sentence means, precisely). |
| D13 | ACCEPT. |
| D14 | ACCEPT. |
