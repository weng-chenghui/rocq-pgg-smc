#!/usr/bin/env python3
"""Prove that staged/ is the probe copies with their Require sentences rewritten.

Five checks per staged file.

  (a) Comment-stripped, and with every ``From ... Require ...`` sentence
      dropped whole (a sentence may span several physical lines), the staged
      file is line-for-line the probe copy.  Nothing outside the import block
      moved.
  (b) The staged file's Require sentences, whitespace-normalized, are the
      permanent block.  For five_card_mixing.v and five_card_rows.v the
      permanent block is read out of STATUS.md's fenced blocks in section
      "Import rewrite at cp time"; for pgg_analysis_manifest.v and
      pgg_analysis_client.v it is the production file's own sentences;
      for five_card_analysis.v it is production's sentences plus the single
      five_card_mixing sentence STATUS.md spells; for var_dist_supp.v, which
      is new and whose block STATUS.md leaves unchanged, it is the probe
      copy's own sentences.
  (c) The string kim_landing_probe occurs nowhere in the file, comments
      included.
  (d) No line longer than 80 bytes that is not byte-identical to some line of
      the production file at the same permanent path.  A new file has no such
      production file, so there the check is that no line exceeds 80 bytes.
  (e) The raw byte difference between probe copy and staged file, as a unified
      diff, so a reader sees every physical line that changed.

Exit status 0 iff every check of every file passes.
"""

import difflib
import os
import re
import sys

PROBE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(PROBE)))
STATUS = os.path.join(PROBE, "STATUS.md")

# probe basename -> (permanent relative path, is the permanent file new?)
FILES = [
    ("var_dist_supp.v", "lib/var_dist_supp.v", True),
    ("five_card_mixing.v", "instances/kim2025/five_card_mixing.v", True),
    ("five_card_analysis.v", "instances/kim2025/five_card_analysis.v", False),
    ("pgg_analysis_manifest.v", "manifest/pgg_analysis_manifest.v", False),
    ("pgg_analysis_client.v", "manifest/pgg_analysis_client.v", False),
    ("five_card_rows.v", "instances/kim2025/five_card_rows.v", False),
]

failures = []


def fail(msg):
    failures.append(msg)
    print("    FAIL " + msg)


# ---------------------------------------------------------------- lexing ----

def strip_comments(text):
    """Remove (* ... *) comments, nesting-aware, keeping every newline."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i:i + 2]
        if depth == 0 and two == '"':
            pass
        if depth == 0 and text[i] == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 1
            out.append(text[i:j + 1])
            i = j + 1
            continue
        if two == "(*":
            depth += 1
            i += 2
            continue
        if two == "*)" and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth > 0:
            if text[i] == "\n":
                out.append("\n")
            i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def require_spans(lines):
    """Index ranges of the lines each ``From ... Require ...`` sentence covers."""
    spans = []
    i = 0
    while i < len(lines):
        s = lines[i].strip()
        if s.startswith("From ") and " Require " in s:
            j = i
            while j < len(lines) and not lines[j].rstrip().endswith("."):
                j += 1
            spans.append((i, min(j, len(lines) - 1)))
            i = j + 1
        else:
            i += 1
    return spans


def require_sentences(text):
    """Whitespace-normalized ``From ... Require ...`` sentences of a text."""
    lines = strip_comments(text).split("\n")
    out = []
    for a, b in require_spans(lines):
        out.append(re.sub(r"\s+", " ", " ".join(lines[a:b + 1])).strip())
    return out


def without_requires(text):
    lines = strip_comments(text).split("\n")
    drop = set()
    for a, b in require_spans(lines):
        drop.update(range(a, b + 1))
    return [l for k, l in enumerate(lines) if k not in drop]


# --------------------------------------------------- STATUS.md extraction ----

def status_blocks():
    """Fenced blocks of section "Import rewrite at cp time", keyed by file."""
    lines = open(STATUS, encoding="utf-8").read().split("\n")
    start = next(k for k, l in enumerate(lines)
                 if l.startswith("## Import rewrite at cp time"))
    end = next((k for k in range(start + 1, len(lines))
                if lines[k].startswith("## ")), len(lines))
    section = lines[start:end]
    names = [n for n, _, _ in FILES]
    blocks, k, last = {}, 0, None
    while k < len(section):
        for n in names:
            if "`" in section[k] and n in section[k] \
                    and not section[k].startswith("```"):
                last = n
        if section[k].startswith("```"):
            j = k + 1
            while j < len(section) and not section[j].startswith("```"):
                j += 1
            if last is not None:
                blocks.setdefault(last, []).append("\n".join(section[k + 1:j]))
            k = j + 1
            continue
        k += 1
    return blocks


BLOCKS = status_blocks()


def expected_sentences(name, rel, is_new, probe_text):
    if name == "var_dist_supp.v":
        return require_sentences(probe_text), "the probe copy's own sentences"
    if name in ("five_card_mixing.v", "five_card_rows.v"):
        return (require_sentences(BLOCKS[name][0]),
                "STATUS.md's fenced block for " + name)
    prod = open(os.path.join(REPO, rel), encoding="utf-8").read()
    if name == "five_card_analysis.v":
        return (require_sentences(prod) + require_sentences(BLOCKS[name][0]),
                "production's sentences + STATUS.md's added sentence")
    return require_sentences(prod), "production's own sentences"


# ----------------------------------------------------------------- checks ----

print("check_staged.py: six staged files against their probe copies\n")

for name, rel, is_new in FILES:
    probe_path = os.path.join(PROBE, name)
    staged_path = os.path.join(PROBE, "staged", rel)
    prod_path = os.path.join(REPO, rel)
    probe_b = open(probe_path, "rb").read()
    staged_b = open(staged_path, "rb").read()
    probe_t = probe_b.decode("utf-8")
    staged_t = staged_b.decode("utf-8")

    print("=" * 78)
    print("staged/%s   (probe copy %s)" % (rel, name))
    print("=" * 78)

    # (a)
    pa, sa = without_requires(probe_t), without_requires(staged_t)
    if pa == sa:
        print("  (a) OK   outside Require sentences, %d comment-stripped lines"
              " are identical" % len(sa))
    else:
        fail("(a) the two differ outside their Require sentences")
        for l in list(difflib.unified_diff(pa, sa, "probe", "staged",
                                           lineterm=""))[:40]:
            print("        " + l)

    # (b)
    got = require_sentences(staged_t)
    want, source = expected_sentences(name, rel, is_new, probe_t)
    if got == want:
        print("  (b) OK   %d Require sentences equal %s" % (len(got), source))
    else:
        fail("(b) Require sentences differ from %s" % source)
        for l in difflib.unified_diff(want, got, "expected", "staged",
                                      lineterm=""):
            print("        " + l)

    # (c)
    if b"kim_landing_probe" in staged_b:
        fail("(c) kim_landing_probe occurs in the staged file")
    else:
        print("  (c) OK   no occurrence of kim_landing_probe")

    # (d)
    if os.path.exists(prod_path):
        prod_lines = set(open(prod_path, "rb").read().split(b"\n"))
        note = "not in production " + rel
    else:
        prod_lines = set()
        note = "no production file at " + rel + ", so none is allowed"
    long_new = [(k + 1, l) for k, l in enumerate(staged_b.split(b"\n"))
                if len(l) > 80 and l not in prod_lines]
    if long_new:
        fail("(d) %d line(s) over 80 bytes and %s" % (len(long_new), note))
        for k, l in long_new[:10]:
            print("        %d (%d bytes): %s" % (k, len(l), l.decode()))
    else:
        total_long = sum(1 for l in staged_b.split(b"\n") if len(l) > 80)
        print("  (d) OK   %d line(s) over 80 bytes, every one of them %s"
              % (total_long,
                 "byte-identical to a production line"
                 if prod_lines else "absent (file is new)"))

    # (e)
    print("  (e) raw byte diff, probe copy -> staged file:")
    d = list(difflib.unified_diff(probe_t.split("\n"), staged_t.split("\n"),
                                  "probe/" + name, "staged/" + rel,
                                  lineterm=""))
    if not d:
        print("        (no difference: the staged file is the probe copy"
              " byte for byte)")
    for l in d:
        print("        " + l)
    print()

print("=" * 78)
if failures:
    print("RESULT: %d check(s) failed" % len(failures))
    for f in failures:
        print("  - " + f)
    sys.exit(1)
print("RESULT: all checks passed for all six staged files")
