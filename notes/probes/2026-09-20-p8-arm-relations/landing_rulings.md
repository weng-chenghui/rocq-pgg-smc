# Main session's rulings on the two audits of the landing

Reports: `audit-landing-soundness.md` (W1 to W13), `audit-landing-naming.md`
(X1 to X28). Every finding is ACCEPTED with the auditor's replacement unless
amended here. Where W and X overlap (W1/X4, W3/X8, W7/X20, W11/X7, W12/X12,
W13/X1, W6/X14) one edit serves both; take the wording that the statement
supports, and if the two replacements differ take the one that says less.

| id | Ruling |
|---|---|
| W1, W2, X4 | CODE. The instance docstrings are made true by landing the bridge, not only by rewording. In `instances/pgl27/pgl27_models.v` and `instances/kim2025/five_card_models.v`, one lemma each whose statement is the generic product hypothesis at the instance, in its exact shape: `fdistmap (fun u => (arg_read u, sa.(sa_cut) u)) (sa_sampleP sa) = (fdistmap arg_read (sa_sampleP sa)) \`x (sa_cut_dist sa)` with `sa` the model's adapter and `arg_read` the reading of the existing `_arg_readE` lemma. Names: `pgl27_word_arg_cut_marginals_prodE`, `kim_biased_arg_cut_marginals_prodE`. Proof from the existing `_arg_cut_prodE`, `fdist_prod1` (or the tree's first-marginal lemma), `fdistmap_comp` and the model's cut-law lemma (`pgl27_word_cut_distE`; the five-card one: find it). The two model files keep importing no tableau, framework or manifest module: `sa_cut_dist` is in `security/pgg_sample_adapter.v`. If a needed lemma lives above the model file, STOP on that fact and report; then the docstrings are reworded by X4's text instead. The docstrings of the two existing `_arg_cut_prodE` lemmas say what those lemmas are (the joint law with the model's named factors) and point at the new lemma for the hypothesis's shape. |
| W5 | ACCEPTED, and adjusted to W2's outcome: the "Not claimed." paragraph says the construction is not instantiated at a production model; the instance files hold the product hypothesis at two models and the numbers a construction there would carry. |
| W8 | Try `exact: kim_biased_exact_le_eps`; keep the shorter proof only if it compiles at once. |
| W10 | The fidelity file gains projection checks for the five definitions (the fields the docstrings claim), closed by `erefl`/`reflexivity`. |
| W11, X7 | CODE. `var_dist_xx` is dropped from `lib/var_dist_supp.v` with its index entry: nothing in production uses it and the consumer it served was not landed (the owner's rule: an unused declaration stays only if a paper claims it or later work needs it; the probe copy is the record). |
| X15 | CODE, renames of two lemmas this landing added (uncommitted, no other user): `kim_biased_proximity_eps_sw_bound_exactE` -> `kim_biased_proximity_eps_cert_exact_sw_boundE`; `kim_biased_proximity_eps_le_sw_bound` -> `kim_biased_proximity_eps_le_cert_sw_bound`; the two index entries say which certificate. |
| X18 | CODE. The new file is renamed `lib/fdist_prod_cst_cond.v` (the section's name), header line widened to cover the constant-variable independence lemma; `_CoqProject` line and the one import follow. |
| X13 | "reading" stays the coalition's static reading; `arg_read` is "the finite coordinate `arg_read` takes off the sample point" everywhere in the landing. |
| X19 | Regroup the import block as the report gives it. |
| X22 | Not landed. |
| X21, X23, X27, X28 | No change. |
