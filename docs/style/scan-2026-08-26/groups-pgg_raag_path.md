# Scan sub-report: groups/pgg_raag_path.v (274 lines; 76 findings, 32 A)

Highest-severity content (from the groups scanner's deep-dive fork):

- DOMAIN-HONESTY [R2|A]: header line 11 asserts the RAAG presentation
  <g_0..g_m | g_i g_j = g_j g_i, |i-j|>=2> but the object built,
  <<[set tperm i i.+1]>>, is the FULL SYMMETRIC GROUP S_(m+2) (a proper
  quotient: involutions + braid relations). Line 14 claims "commute iff
  |i-j| >= 2" but only -> is proved (converse only for the pair (0,1)).
  A domain expert reading only the header misidentifies the group.
- PROOF-RELEVANT STATEMENTS [E1|A]: Ordinal (Hm : 1 < T) embeds the
  proof term in statements (:195,:236), making i1/I definitionally
  proof-relevant; downstream only works by reusing the same Hm. Fix +
  the repeated 0 < m premise (4 statements, 2 binder shapes): one
  Section path_adjacent_pair with Hypothesis m_gt0, Let i0 := ord0,
  Let i1 — retires 4 E1 + 3 E3 + 5 R5 findings at once.
- [E3|A]: tnth (@pgg_sigmas M_path) i 14x forcing 2-line commutation
  statements -> Local Notation 'g_i; mathcomp's `commute` is
  definitionally the raw x*y=y*x equation written 3x (E4);
  Ordinal (isT : 0 < T) is literally ord0.
- [R2|A]: 21 banned template-slot lines; 10 uncommented declarations
  incl. path_comm (the file's central object); one "Used by:" claim
  provably stale (path_traces_lb has 0 uses tree-wide).
- [R8|A]: Let T := m.+1 (T = mathcomp Type convention; sibling uses Tg);
  path_Hcomm H-prefix leaking into lemma names (-> path_genC);
  path_ prefix collides with mathcomp seq.path.
- [R5|B] x11 incl. five `by ...; exact:` (mathcomp PR #41), a
  rewrite /= that destroys and rebuilds the statement's lets.
- [R7|C]: 10 bare Lemmas with zero external uses -> Local/Fact.
- Density 0.28 findings/line — A-heavy skew from comment defects, not
  formatting (mechanically clean file).
