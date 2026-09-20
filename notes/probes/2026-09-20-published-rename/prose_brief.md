# Brief shared by the four prose agents (layer F)

Repository /Users/cheng-huiweng/Projects/coq/rocq-pgg-smc, branch
feat/tableau-extensions-probe, parent commit c07f6a8. COMMENTS ONLY.

Read first, in full: `notes/probes/2026-09-20-published-rename/prose_sheet.md`
(the four senses, the composite phrases, the six rules). It is the ruling.

Hard rules. You edit only comment text, only in the files of YOUR group (three
other agents are editing the other groups at the same time: never touch, never
re-flow, never "fix" a file outside your list). No code token changes. You
compile nothing and run no Rocq process. Never run `make`. No git command that
writes (no add, commit, stash, checkout, reset). Never edit a file of the
forward closure of `instances/psl211/psl211_endpoints.v`. Nothing under
`notes/probes/` is deleted. Python for searches (zsh expands `--include=*.v`).

Work. For EVERY comment occurrence of row / rows / Row / Rows in your files,
read the declaration or header paragraph it sits in, decide the sense (1
program, 2 finished program, 3 manifest path, 4 a row of a matrix, table,
trace: unchanged), and replace the noun and nothing else. The comment's words
must stay the same in number and order: `check_prose.py` compares them position
by position and lists any other change as OTHER CHANGE. Layout: at most 80
bytes; boxed lines stay exactly 80 bytes with a space before the closing
delimiter ("program" is four bytes longer than "row" and "path" one: re-flow
the paragraph, keep table cells' column bars where they are when the cell has
room, wrap inside the cell when it has not); docstrings keep their 4-space
continuation; no orphan short line mid-paragraph; no name touches `==`.

Sentences you may NOT repair. If, once the right noun is in place, a sentence is
false, ambiguous between two senses, or says that a manifest path publishes,
proves or draws something, or calls a model a program: make the one-for-one
noun change that is least wrong, and LIST the sentence in your report with the
declaration that shows the problem. The main session rules on those.

Check. `python3 notes/probes/2026-09-20-published-rename/check_prose.py c07f6a8`
prints one line per changed file of the whole tree; the lines of YOUR files
must say SAME and must print no LONG, BOX, BARRED or OTHER CHANGE. Ignore lines
about files of other groups. Use `-v` to read your replacements in context.

Report, written to `notes/probes/2026-09-20-published-rename/prose_<group>.md`
and returned as your final message: per file, the counts (program, path,
unchanged) and, for every unchanged occurrence, a three-word reason class
(matrix row, deck-table row, trace row, file name...); every occurrence whose
sense you found hard, with the sentence, the declaration and your choice; the
list of sentences under "may NOT repair"; the final checker lines of your
files. Your report does not quote the project's barred vocabulary and uses no
ids made of a capital L followed by a digit. You stop silently at about 120
tool calls: hand back by call 95 with the exact state if unfinished (which
files are complete, which are untouched; never leave a file half done).
