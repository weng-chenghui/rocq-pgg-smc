# Proof plan: leak_k3, leak_k2_d2, leak_k2_adj

File: `pgg-smc/instances/denboer1989/five_card_leakage.v`
Build: `make -j1 pgg-smc/instances/denboer1989/five_card_leakage.vo`

Status: 4/7 proven (`H_secret`, `leak_k1`, `leak_k4`, `leak_k5`). The three below
are `Admitted`. They ARE provable (exact math, full infotheo machinery, only the
standard boolp axioms already used). What remains is a mechanical grind, ~150–250
`rocq_check` steps each, through the conditional-entropy machinery.

Model (already in file): `Omega = bool*bool*'I_5` (20 outcomes), `P = fdist_uniform`,
`arr w = fc_shuffle k (fc_arrange a b)` (heart=true, size 5), `Secret w = a && b`,
`ViewA A w = colours at A as (size A)-tuple bool`. Leak = `'I(Secret; ViewA A)`.

## Ground-truth count tables (heart=true=1, club=false=0)

Joint counts over the 20 outcomes; `n_v` = view count, then (Secret=true : false).

leak_k3, ViewA [::0;1;2]  (8 view-tuples; (0,0,0) has count 0):
  [f;f;t] n=1  T1 F0   determined T
  [f;t;f] n=3  T0 F3   determined F
  [f;t;t] n=4  T1 F3   SPLIT  P(T|v)=1/4   <- H[Secret|v]=H_secret
  [t;f;f] n=1  T1 F0   determined T
  [t;f;t] n=6  T0 F6   determined F
  [t;t;f] n=4  T1 F3   SPLIT  P(T|v)=1/4   <- H[Secret|v]=H_secret
  [t;t;t] n=1  T1 F0   determined T
  => H(Secret|View3) = (4/20+4/20)*H_secret = (2/5)*H_secret
  => leak_k3 = H_secret - (2/5)H_secret = (3/5)*H_secret = 6/5 - 9/20 log3   (FIELD only)

leak_k2_adj, ViewA [::0;1]:
  [f;f] n=1  T1 F0   determined T
  [f;t] n=7  T1 F6   P(T|v)=1/7   -> H2(1/7)
  [t;f] n=7  T1 F6   P(T|v)=1/7   -> H2(1/7)
  [t;t] n=5  T2 F3   P(T|v)=2/5   -> H2(2/5)
  => H(Secret|View) = (7/20)H2(1/7)+(7/20)H2(1/7)+(5/20)H2(2/5)
  => leak_k2_adj = H_secret - that = 27/10 - 1/4 log5 - 7/10 log7   (log3 cancels)

leak_k2_d2, ViewA [::0;2]:
  [f;f] n=3  T0 F3   determined F
  [f;t] n=5  T2 F3   P(T|v)=2/5   -> H2(2/5)
  [t;f] n=5  T2 F3   P(T|v)=2/5   -> H2(2/5)
  [t;t] n=7  T1 F6   P(T|v)=1/7   -> H2(1/7)
  => H(Secret|View) = (1/2)H2(2/5)+(7/20)H2(1/7)
  => leak_k2_d2 = 5/2 - 3/20 log3 - 1/2 log5 - 7/20 log7

Binary-entropy closed forms (log = log2), to prove as helper lemmas:
  H2(p) := -p log p - (1-p) log(1-p)
  H2(1/4) = 2 - 3/4 log3            (= H_secret, already proven)
  H2(1/7) = log7 - 6/7 - 6/7 log3
  H2(2/5) = log5 - 2/5 - 3/5 log3

## Shared reduction (all three)

    rewrite mutual_info_RVE.              (* I = H(`p_Secret) - H(Secret|View) *)
    (* now compute H(Secret|View) *)

Then EITHER `centropy_RVE'` (sum over view-tuples; recommended) OR `centropy_RVE`
(double sum over (view,secret) cells).

## Recommended recipe: per-view via centropy_RVE'

    rewrite centropy_RVE'.
    (* H(Secret|View) = \sum_(a : (size A).-tuple bool) Pr[View=a] * H[Secret|View=a] *)

Step 1 — enumerate the view-tuple sum.  There is NO one-line lemma for
`\sum_(a : n.-tuple bool)`. Extract the few contributing views with `bigD1` and
zero the rest:
    rewrite (bigD1 [tuple of [:: false;true;true]]) //=
            (bigD1 [tuple of [:: true;true;false]]) //=.
    rewrite big1 ?addr0; last first.
      move=> a /andP[Ha1 Ha2].
      (* residual views: show the term is 0 *)
      (* case-bash a into 3 bools: case/tupleP: a => a0 /tupleP[a1 /tupleP[a2 a']];
         rewrite (tuple0 a'); then case: a0; case: a1; case: a2 //=;
         each residual is either Pr[View=a]=0 or H[Secret|View=a]=0 *)
For leak_k2 the residual is over 4 tuples (2 contributing), even simpler.

Step 2 — `Pr[View=a]`.  Reuse the `count_pr` lemma pattern already inside
`leak_k1`: `pfwd1 X x = #|preim X (pred1 x)|%:R / 20%:R`, and the
`card_view`-style count (`-sum1_card`, `eq_bigl`, `big_mkcond`, `stepO`,
`!big_ord_recl big_ord0`, `stepBB`, `!big_bool`, `case`). Lift `count_pr`,
`stepO`, `stepBB` to TOP-LEVEL lemmas first so all three proofs share them.

Step 3 — `H[Secret|View=a]` for a contributing view a (the crux):
    have Hpr : (`p_[%ViewA A, Secret])`1 a != 0.   (* = Pr[View=a] = n_v/20 != 0 *)
    rewrite (centropy1_RVE Hpr).
    (* H[Secret|View=a] = `H (jfdist_cond `p_[%ViewA A, Secret] a) *)
  Now show the conditional fdist equals an explicit Bernoulli(n_T/n_v) on bool:
    have -> : jfdist_cond `p_[%ViewA A, Secret] a = <explicit bool fdist>.
      apply: fdist_ext => b; rewrite jfdist_condE //.
      (* jfdist_cond PQ a b = jcPr (fdistX PQ) [set b] [set a]
         = Pr[Secret=b | View=a] = joint_count(a,b) / view_count(a)
         via jfdist_cond.jPr_Pr / jProduct_rule and count_pr;
         case: b and plug the two ratios from the table *)
    (* then `H of that Bernoulli = H2(ratio): rewrite /entropy big_bool and the
       log algebra, exactly like the H_secret proof (logV, logDiv, log4...) *)
  For k3 the ratio is 1/4 so this `H = H_secret` (reuse it; no new log algebra).
  For k2 prove H2(1/7), H2(2/5) as separate helper lemmas (same log technique as
  H_secret, with log7 / log5 instead of log4).

Step 4 — assemble.
  leak_k3: H_secret - (2/5)H_secret = (3/5)H_secret = 6/5 - 9/20 log3.  Pure field:
    `set L := log 3; field` won't close (no field on R here) — use ring_scope
    rewrites: factor H_secret = 2 - 3/4 L, multiply, collect. Small.
  leak_k2_*: substitute the H2 closed forms, then collect log3 (cancels), log5,
    log7 with the rational coefficients. Heaviest algebra; mirror H_secret's
    `mulrBr/opprD/mulrDl` manipulation.

## Obstacles, ranked

1. **View-tuple sum enumeration** (Step 1). No library one-liner. Use
   `bigD1`×(contributing) + `big1` + `case/tupleP` bash on the residual. ~20–40
   steps. Cleaner for k2 (4 tuples) than k3 (8).
2. **Conditional fdist = explicit Bernoulli** (Step 3). The real core: compute
   `jcPr = joint/marginal` from counts and prove the bool-fdist equality. Needs
   `jfdist_condE`, `jfdist_cond.jPr_Pr`/`jproduct_rule`, and `count_pr`. Fiddly;
   ~40–80 steps per distinct ratio. ALTERNATIVE if this stalls: use
   `centropy_RVE` (double sum) and reindex to a sum over `Omega` (enumerable by
   `stepO`), where determined outcomes give `jcPr=1` (log 0, vanish) via
   `jfdist_cond.jPr_comp_eq1`; this trades the fdist-equality for a bigop reindex
   `\sum_a\sum_b (fdistmap [%View,Secret] P)(a,b) g = \sum_w P w * g(View w,Secret w)`
   (prove via `partition_big` on the joint map).
3. **Binary-entropy closed forms** H2(1/7), H2(2/5) (Step 3c, k2 only). Same log
   algebra as H_secret; ~30–50 steps each. Check `lib/binary_entropy_function.v`
   first — it may already give `H2` and a closed form to specialise.
4. **Final log collection** (Step 4). k3 trivial (field-style). k2 heavy but
   mechanical: collect log3(=0), log5, log7 coefficients.

## Key infotheo lemmas (verified present)

mutual_info_RVE, centropy_RVE', centropy_RVE, centropy1_RVE, centropyE,
jfdist_cond.jfdist_condE, jfdist_cond.jPr_Pr, jfdist_cond.jproduct_rule,
jfdist_cond.jPr_comp_eq1 (determined -> jcPr=1), fdistmapE, big_bool, big_ord_recl,
realType_ln: logV, logM, logDiv, log4 (and prove log7/log5 analogues inline).
Reuse from the file: count_pr, stepO, stepBB, the card_* enumeration pattern,
H_secret, fc_correct, fc_arrange_size.

## Suggested fresh-session chunking

- Session A: lift `count_pr`/`stepO`/`stepBB` to top-level + prove `H2_oneseven`
  (H2(1/7)) and `H2_twofifth` (H2(2/5)) helper lemmas + a per-view helper
  `condent_view : Pr[View=v]!=0 -> H[Secret|View=v] = H2(n_T/n_v)`. (Infrastructure.)
- Session B: `leak_k3` (cleanest; collapses to (3/5)H_secret).
- Session C: `leak_k2_d2` then `leak_k2_adj` (share the H2 helpers).

Each session: `rocq_start(file, leak_kX)`, build with `rocq_check`, `make -j1` at
the end, `rocq_assumptions` to confirm no new axioms. Never `rewrite !` on nat
arith; never `lia`. If a session prefers automation, a `rocq-prover` agent can run
the same recipe — the bottleneck is obstacle 2, so hand it this plan.
