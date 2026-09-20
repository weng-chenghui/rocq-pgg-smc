# Brief shared by the prose agents (two barred nouns, each site says what the thing is)

Repository /Users/cheng-huiweng/Projects/coq/rocq-pgg-smc, branch
feat/tableau-extensions-probe. COMMENTS ONLY. The parent commit is the one named
in your prompt.

Read first, in full: `notes/probes/2026-09-20-security-property-rename/prose_sheet.md`.
It is the ruling: what the things are, the seven cases of the first barred
noun, the three cases of "port", the five rules. Then read, in
`manifest/pgg_tableau.v`, the declarations `SecurityEvidence`,
`SecurityProperty`, `evidence_property`, `EvidenceProp`, `ExactWitness`,
`IndistinguishabilityCert`, `IdealProximityCert`, `certify_exact`,
`certify_indistinguishability`, `certify_idealproximity`, and the three tail
lemmas: every site is decided against them.

Your report, and every file you write, never writes the first barred noun (the
three-letter word; say "the first barred noun"); when you quote an OLD line,
replace the noun by `[N1]` and "port" by `[N2]`, altering nothing else.

Hard rules. You edit only comment text, only in the files of YOUR group (other
agents edit the other groups at the same time). No code token changes. You
compile nothing and start no Rocq process. Never run `make`. No git command
that writes. Never edit a file of the forward closure of
`instances/psl211/psl211_endpoints.v` (`instances/psl211/psl211_exec.v` holds
one site: list it for the owner, do not edit). Nothing under `notes/probes/` is
deleted. Python for searches.

Work. For EVERY comment occurrence of either noun in your files (word-boundary,
any inflection, any case): read the declaration or header paragraph, decide the
case, rewrite as far as the case requires and no further (every claim,
hypothesis, number, quantifier, named lemma of the old sentence survives).
Where the sheet's verb rule shows the OLD sentence was already untrue (a
property "takes", a certificate "publishes", a path "proves"), make it true and
list it. Twins in sibling files say one thing one way: before you finish, grep
your own new phrases and make the same sentence read the same in each file of
your group. Index entries of `*_propertyE` lemmas: case 7 of the sheet.

Layout: at most 80 BYTES (an em-dash is three); boxed lines exactly 80 bytes
with a space before the closing delimiter; `==` columns and continuation
columns kept; docstrings 4-space continuation; banners one content line;
re-flow the paragraph, no orphan short line.

Finish with a scan of your files' comments: zero occurrences of either noun.
Report, written to `notes/probes/2026-09-20-security-property-rename/prose_<group>.md`
and returned: per file the count per case; EVERY rewritten sentence as OLD
(placeholders) and NEW verbatim with the case number and, where a declaration
decided it, the fact; the sentences that were already untrue and how you made
them true; sentences you could not make true (for the main session); the final
scan. No ids made of a capital L followed by a digit. You stop silently at
about 120 tool calls: hand back by call 95 with the exact state; never leave a
file half done.
