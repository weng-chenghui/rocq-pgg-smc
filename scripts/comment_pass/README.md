# The comment pass toolkit

Seven tools and one shared module, for a pass that changes the comments of
the tree, or renames identifiers, and proves afterwards that it changed
nothing else. The tools replace the scripts that were written again for each
pass under `notes/probes/`. They are Python 3 with the standard library only,
and every one of them takes `--root DIR`, so a pass can be rehearsed on
copies before it is made on the tree.

Nothing here starts a Rocq process except `compile_closure.py` and
`fail_recheck.py`, and both of those run every compile through the lock
wrapper named by `--lock`.

## The unit: a comment paragraph

Every tool works on comment paragraphs, never on lines. A paragraph is one
of these.

| kind | what it is |
|---|---|
| `box-prose` | a run of non-blank lines of a boxed header, at one indent |
| `box-index` | one `name == description` entry with its continuation lines |
| `banner` | the content line of a three-line section banner |
| `table` | a boxed segment whose lines are columns, with bars or without |
| `docstring` | a paragraph of a `(** ... *)` comment |
| `plain` | a paragraph of a `(* ... *)` comment |

A paragraph is named by its own words, not by its line number, because the
lines move as the earlier paragraphs of the same file are rewritten. Two
streams of a file are the invariants of a comment pass: the code tokens with
the comments removed, and the words of the paragraphs. A comment pass leaves
the first identical and changes the second only where the sheet says so.

## The sheet

`inventory.py` writes a TSV with one row per paragraph that holds a hit, and
the writers and the auditors fill the last three columns.

| column | filled by | meaning |
|---|---|---|
| `id` | the tool | the row number, stable within one sheet |
| `file` | the tool | the path of the file, relative to the root |
| `first_line`, `last_line` | the tool | the lines the paragraph occupies, counted from one |
| `kind` | the tool | one of the six kinds above |
| `declaration` | the tool | the identifier of the first declaration under the paragraph, or `header` |
| `hits` | the tool | how many of the given words the paragraph holds |
| `old_text` | the tool | the paragraph's words, one space between them, no decoration |
| `case` | a writer | which case of the pass this paragraph is |
| `new_text` | a writer | the words the paragraph is to hold, one space between them |
| `fact` | a writer | the fact about the declaration that decides the wording |

A row with an empty `new_text` is a site nobody changed, and the tools skip
it.

## The tools

**`common.py`** holds what the rest share: the comment and code splitter,
which follows nested comments and knows a string of the code from a comment;
the paragraph model and the layout; the frozen list; the git helpers; and
the width of a line in bytes, since an em-dash is three of them.

**`inventory.py WORDS... [--paths P...] [-o sites.tsv] [--frozen]`** finds
every occurrence of the given words in the comments of the tracked `.v` files
outside `notes/` and `legacy/` and outside the frozen closure. The match is
by whole word and case-insensitive, and the inflections are given on the
command line, one by one: the tool does no stemming. With `--frozen` the
hits inside the frozen closure are written to a second file, for the owner
to read, because the pass never writes those files.

**`apply_tsv.py sites.tsv [--base REV] [--dry-run]`** applies the sheet. It
finds each paragraph by its `old_text`, refuses the whole run when a row's
old text does not match exactly once, and writes nothing in that case. The
rows of one file are applied from the bottom up. With `--base` a row is
refused as well when the base does not hold that paragraph, which catches a
sheet that was written against an older tree.

**`reflow.py FILE... [--all] [--base REV] [--dry-run]`** lays paragraphs out
again. A boxed line is exactly 80 bytes, `(*` and `*)` included, with at
least one space before the closing delimiter. An index entry keeps the `==`
column and the continuation column of its own header, and a name too long to
sit before the `==` column stands alone on its line. A banner keeps its two
star lines. A table keeps its columns. A docstring continues at four spaces
and a plain comment at three. No word is ever split, so a hyphenated word
stays whole. A last line that holds one word only because the closing
delimiter did not fit is rebalanced against the line above it. Only the
paragraphs whose words differ from the base are touched, unless `--all` is
given. The pass is idempotent and leaves the words of every paragraph
unchanged. A paragraph that sets two spaces after a sentence keeps them:
the gap is doubled after a word ending a sentence when the next word does not
start in lower case, so an abbreviation in mid-sentence keeps its single
space. `--all` lays out every paragraph by these rules, so on a file that was
laid out by hand on a grid of its own (a 77-byte box, an index with two `==`
columns, a list inside a prose paragraph) it rewrites lines nobody edited:
use it only on a file this tool laid out before, and edit such places line by
line.

**`check_pass.py sites.tsv --base REV [--words W...]`** is the audit of an
applied pass. For every file that differs from the base it checks that the
code tokens are identical, that the sequence of comment paragraphs is the
base's sequence with the sheet's rows substituted and nothing else, that no
line over 80 bytes is new, that a boxed line is exactly 80 bytes with a space
before its closing delimiter, that the words of `--words` are gone, that no
file of the frozen closure was written, and that the owner's barred words are
absent from the new lines. The paragraph sequences are aligned with difflib,
so each region that does not match is printed once, with the base text and
the found text under each other. It prints `ALL OK` or the problems, and its
exit code follows.

**`rename.py build|apply|check MAP.tsv`** renames identifiers. `build`
checks that the map is injective, that every old name occurs in the tree,
and that no new name is already an identifier, and with `--probe FILE.v` it
writes a file of `Locate` commands over the new names, to be compiled once
before anything is applied. `apply` substitutes whole identifier tokens in
the code and in the comments, never a substring, lays the paragraphs it
touched out again, and lists the code lines that grew past 80 bytes: a code
line is broken by a human, never by a tool. `--comment-only OLD=NEW`
substitutes a pair inside comments alone, for the prose name of a renamed
family. `check --base REV` requires the base text with the map applied to
equal the working copy as code tokens and as comment paragraphs, and
`--move OLD NEW` tells it where a renamed file moved to.

**`closure.py [FILES...|--changed REV] [-o ORDER.txt]`** takes the reverse
closure of the touched files over the Require graph and prints it in an order
where a file comes after everything it requires. A file of the frozen closure
met on the way stops the run and nothing is written.

**`compile_closure.py ORDER.txt [--dry-run] [--resume LOG] [--lock PATH]`**
compiles the order one file at a time through the lock wrapper, with the
flags of `_CoqProject`. The cap is 1500 seconds a file, measured in CPU time
where the platform gives the CPU time of a child and in wall time otherwise,
which the first line of the run says. The run stops at the first failure and
`--resume` reads its own log to skip what is done.

**`fail_recheck.py --ids MAP.tsv|--names N... [--dry-run]`** finds every
recorded `Fail` command that holds one of the given identifiers and compiles
it once more without the word `Fail`, in the context its own file gives it,
so that the reason for the rejection is read and not assumed. The scratch
files and their `.vo` go under `--out`, so no production `.vo` is touched.

**`selftest.py`** copies four production files at HEAD into a scratch
directory and exercises the tools on the copies. It writes no file of the
repository and starts no Rocq process.

## The procedure of a pass

1. `inventory.py` writes the sheet. The hits inside the frozen closure go to
   the owner in a separate file and are not part of the pass.
2. Writers fill `case`, `new_text` and `fact`, at most 100 rows each, and
   never edit a `.v` file.
3. Auditors read the sheet against the declarations and rule on each row.
   The main session settles what the auditors disagree on.
4. One agent runs `apply_tsv.py`, then `reflow.py` if any paragraph outside
   the sheet needs it, then `check_pass.py --base REV`. The audit comes
   before the application, and the application is minutes of work.
5. One recompile for the whole batch: `closure.py --changed REV` and
   `compile_closure.py`. With the code tokens identical the compile cannot
   change, so it runs once at the end of the batch.
6. After a rename, `fail_recheck.py` re-reads every recorded rejection that
   holds a renamed identifier.

## What the layout does not reproduce

The running text of the tree is wrapped by hand at widths between about 65
and 80 bytes, with no one width that fits every paragraph, so `reflow.py`
fills to 80 and changes most docstrings and plain comments it is told to lay
out again. This is why it only touches the paragraphs whose words changed
unless `--all` is given. A boxed segment whose lines hold an inner run of
three spaces or more is kept as it stands, because its columns carry meaning
that the word stream does not record; the same holds for a boxed table with
bars and for the licence block at the top of a file.
