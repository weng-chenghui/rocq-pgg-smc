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
| IK-02 | `W-03-DIA008` | The architecture figure says that the derived protocol exposes `characters`. This is a formal-development term. Calling the derived value a privacy threshold would also be off by one: `profile_k=4` is a cutoff, while the paper's largest private coalition size is $t=3$. | Replace the node text with `participants, privacy cutoff $k$, round-trip lemma`. Explain nearby that coalitions of size below $k$ satisfy scheme privacy, so the $\PG$ value $k=4$ gives the paper's threshold $t=k-1=3$. |
| IK-03 | `W-03-STM003` | The data-processing theorem uses the pushforward notation $f_*P$ without defining what distribution it denotes. | Define it before the theorem: $f_*P$ is the distribution of $f(a)$ when $a$ is sampled from $P$. |
| IK-04 | `W-04-P003` | The biased-cut formula gives a strict interval for $\varepsilon$ but does not say why that interval makes the formula a valid dealing distribution. | State that the five displayed weights sum to one and that the interval makes every weight positive. |
| IK-05 | `W-04-STM002` | The seven-cut proposition does not explain the security role of its endpoint bound. The first rewrite also put this witness inside the profile and conflated a fixed card's destination with a player. | Keep only the mathematical claim inside the proposition. After it, state that this separate shuffle witness bounds the destination distribution of any fixed card after seven biased cuts against the uniform distribution. |
| IK-06 | `W-05-STM002` | The decoder definition introduces $A$ without saying that it ranges over $\Omega_4$. It also partitions cross-ratio values without explaining why no other field value can occur. | Start with `For $A\in\Omega_4$, write $A=\{a<b<c<d\}$`. Then state that distinctness excludes zero and one, so the cross ratio lies in $\{2,3,4,5,6\}$, before defining $\kappa$. |
| IK-07 | `W-06-P007` | The leakage identity $1-m/336$ appears after a collision count, but the paragraph does not explain why overlap becomes residual uncertainty about the secret. | Explain that a shared observation is compatible with both secrets, while a nonshared observation identifies one secret. Under the uniform deals, the nonshared fraction is therefore $1-m/336$. |
| IK-08 | `W-07-P005` | Endpoint-transfer notation uses $h_\#P$ without telling the reader that this is the distribution obtained after applying the endpoint map $h$. The generic theorem earlier writes the same operation as $f_*P$. | Define $h_\#P$ in the lead-in as the distribution of $h(g)$ when $g$ is sampled from $P$, and explicitly connect $f_*P$ with the later $f_\#P$ notation. |
| IK-09 | `W-08-P003` | The trust-base table uses the code label `boolp`, while the prose names three classical principles without connecting the label to them. | State that `boolp` is the table's shorthand for the three classical principles named in the paragraph. |
| IK-10 | `W-10-P001` | The conclusion calls $r$ the `reconstruction threshold`, while the abstract, main text, figure, and theorem call it the `recovery threshold`. A reader may infer that these are different parameters. | Use `recovery threshold` in the conclusion. |
| IK-11 | `W-03-P001` and connected architecture blocks | The draft repeatedly treats the shuffle law, marginal bound, and certificate as fields of `MonodromyProfile`. The formal record contains only the group/action, secret type, run layout, and reconstruction plug. The security evidence is separate. | Rewrite the architecture paragraph, bridge table, figure, obligations, five-card listing, and instance transitions so that `MonodromyProfile` determines the executable protocol and decoder, while `ShuffleMarginalBound` and `ShuffleCertificateBundle` separately supply quantitative shuffle evidence. |
| IK-12 | `W-04-P003` | The biased-cut distribution uses $a^k$ without defining $a$ or saying what the exponent does to the deck. | Before the formula, state that $a$ is the one-position cyclic cut and that $a^k$ rotates the deck by $k$ positions. |
| IK-13 | `W-04-P005` and `W-04-P006` | The leakage and input-hiding claims do not state their probability experiment. A reader cannot infer which inputs and cuts are random or why the secret entropy has its displayed value. | State that the experiment is uniform on the 20 triples $(a,b,k)$, with two uniform Boolean inputs and one uniform cyclic cut, before presenting leakage and conditional input hiding. |

## Independent audit, round 1

The independent audit checked all 225 units and the first ten applied changes.
It rejected IK-02 and IK-05 as inaccurate, found IK-06 incomplete, requested a
notation link for IK-08, and identified IK-11 through IK-13. These findings are
incorporated above and remain open until the corrected candidate passes the
second audit.

The second audit accepted the mathematical corrections but found three
residual presentation errors. It required the explicit $\varepsilon$ parameter
in the displayed certificate signature, a precise account of which data come
from Equation 1, and a distinction between the $\PG$ uniform
certificate bundle and the separate word-shuffle theorem. The candidate now
contains those corrections. The final audit checked all 225 units and every
IK-01 through IK-13 solution. Its verdict was Spec PASS and Quality PASS, with
no remaining finding.

## No-change disposition

All remaining units need no change under these tests. In particular, the
remaining detailed statements already obtain their conceptual meaning from an
immediately preceding or following paragraph. Short table cells, diagram
labels, captions, displays, and procedural steps were not expanded merely
because they are brief.
