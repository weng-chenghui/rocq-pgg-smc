# Implicit-Knowledge Review

Candidate reviewed:
`candidate-main.tex`

Review scope: all 225 non-footnote units in the accepted rewrite table.

Coverage:

| Content type | Reviewed |
|---|---:|
| Abstract paragraph | 1 |
| Prose paragraph | 108 |
| Statement | 27 |
| Table cell | 51 |
| Diagram text | 18 |
| Caption | 12 |
| List item | 8 |
| Total | 225 |

Each unit was checked for five reader needs:

1. a new object says what it represents;
2. a construction exposes its input, action, and result;
3. a result exposes the assumptions or prior facts that make it usable;
4. the reader can see why the block appears and what follows from it; and
5. a detailed block states its meaning for correctness, privacy, recovery,
   security, efficiency, trust, or another domain-level concern.

## Findings and proposed solutions

| Finding | Unit | Reader problem | Proposed solution |
|---|---|---|---|
| IK-01 | `W-02-P010` | The paper defines coalition privacy in words, but later statements introduce the symbol for independence without explicitly binding that notation. | Add one sentence: `I write $S\mathrel{\perp}V_C$ for this independence.` |
| IK-02 | `W-03-DIA008` | The architecture figure says that the derived protocol exposes `characters`. This is a formal-development term, and the surrounding prose does not tell a paper reader that it means the profile's privacy threshold. | Replace the node text with `participants, privacy threshold, round-trip lemma`. This names the three derived objects directly. |
| IK-03 | `W-03-STM003` | The data-processing theorem uses the pushforward notation $f_*P$ without defining what distribution it denotes. | Define it before the theorem: $f_*P$ is the distribution of $f(a)$ when $a$ is sampled from $P$. |
| IK-04 | `W-04-P003` | The biased-cut formula gives a strict interval for $\varepsilon$ but does not say why that interval makes the formula a valid dealing distribution. | State that the five displayed weights sum to one and that the interval makes every weight positive. |
| IK-05 | `W-04-STM002` | The seven-cut proposition ends with kernel-status narration but does not explain the security role of its endpoint bound. | Keep only the mathematical claim inside the proposition. After it, state that the bound is the profile's quantitative shuffle witness and measures how closely one player's card endpoint follows the uniform-cut ideal. Then record the kernel check outside the statement. |
| IK-06 | `W-05-STM002` | The decoder definition partitions cross-ratio values into two sets without explaining why no other field value can occur. A reader must know that the cross ratio of four distinct points is neither zero nor one. | Before defining $\kappa$, state that distinctness excludes zero and one, so the five listed values exhaust the possible elements of $\mathbb F_7$. |
| IK-07 | `W-06-P007` | The leakage identity $1-m/336$ appears after a collision count, but the paragraph does not explain why overlap becomes residual uncertainty about the secret. | Explain that a shared observation is compatible with both secrets, while a nonshared observation identifies one secret. Under the uniform deals, the nonshared fraction is therefore $1-m/336$. |
| IK-08 | `W-07-P005` | Endpoint-transfer notation uses $h_\#P$ without telling the reader that this is the distribution obtained after applying the endpoint map $h$. | Define $h_\#P$ in the lead-in as the distribution of $h(g)$ when $g$ is sampled from $P$. |
| IK-09 | `W-08-P003` | The trust-base table uses the code label `boolp`, while the prose names three classical principles without connecting the label to them. | State that `boolp` is the table's shorthand for the three classical principles named in the paragraph. |
| IK-10 | `W-10-P001` | The conclusion calls $r$ the `reconstruction threshold`, while the abstract, main text, figure, and theorem call it the `recovery threshold`. A reader may infer that these are different parameters. | Use `recovery threshold` in the conclusion. |

## No-change disposition

The other 215 units need no change under these tests. In particular, the
remaining detailed statements already obtain their conceptual meaning from an
immediately preceding or following paragraph. Short table cells, diagram
labels, captions, displays, and procedural steps were not expanded merely
because they are brief.

