#!/usr/bin/env python3
"""Shared parts of the comment pass toolkit.

Holds the comment/code splitter, the paragraph model of the tree's comment
conventions, the deterministic layout of a paragraph, the frozen list, the
git helpers and the byte width.  Every other tool of scripts/comment_pass/
imports this module and nothing else.

The unit every tool works on is a comment PARAGRAPH: a maximal run of
non-blank comment lines inside one comment, or one index entry of a boxed
header with its continuation lines, or one banner.  A paragraph carries its
words, its kind and the layout numbers of its own file, so that new words can
be laid out again without a second reading of the file.
"""
import os
import re
import subprocess
import sys

BOX_WIDTH = 80          # a boxed comment line is exactly this many bytes
BOX_BODY = 76           # the bytes between (* and *)
BOX_FILL = 75           # the widest body that keeps a space before *)
LINE_LIMIT = 80         # the widest line of any kind

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
DECL = re.compile(
    r"^\s*(?:Global\s+|Local\s+|Program\s+|#\[[^\]]*\]\s*)*"
    r"(Definition|Lemma|Theorem|Corollary|Proposition|Remark|Fact|Record|"
    r"Inductive|CoInductive|Variant|Fixpoint|CoFixpoint|Instance|Class|"
    r"Structure|Notation|Axiom|Hypothesis|Parameter|Variable|Example|Let|"
    r"Canonical|Module|Section|Ltac)\s+([A-Za-z_][A-Za-z0-9_']*)")

# The owner's barred vocabulary, and a name made of a capital letter and a
# digit, which the owner reads as a word length.
# The last two alternatives are the nouns barred on 2026-09-20 for a constructor
# of the security-evidence type and for that type; they are spelled here only
# so that a check can find them.
BARRED = re.compile(
    r"\b(apex|gate|gates|gated|gating|posit|posits|posited|positing)\b"
    r"|\bL[0-9]|\b(a" r"rms?|po" r"rts?)\b", re.I)

# The frozen closure: psl211_endpoints.v and the files that reach it, as
# measured on 2026-09-20.  No tool of this toolkit writes one of these files
# and no compile order may hold one.
FROZEN_MODULES = set("""algebraic_rigidity card_exchange_pismc cover_tradeoff
covering_scheme graded_resource input_encoding perm_exchange perm_uniform
pgg_algebra_syntax pgg_collusion_bound pgg_execution_plug
pgg_input_commitment pgg_instance pgg_interface pgg_monodromy_profile
pgg_observed_execution pgg_raag pgg_run pgg_security_solver
pgg_session_types pgg_sharing_framework pgg_sum_mod pgl_bound pismc
psl211_blocks psl211_closure psl211_endpoints psl211_exec psl211_group
psl211_orbit psl211_profile psl211_scheme smc_interpreter
smc_session_types transitivity_privacy""".split())

SKIP_DIRS = ("notes/", "legacy/", ".claude/", "scripts/")


def bw(s):
    """The width of a string in bytes; an em-dash is three of them."""
    return len(s.encode("utf-8"))


def is_frozen(path):
    return os.path.basename(path)[:-2] in FROZEN_MODULES


# ---------------------------------------------------------------- the tree

class Tree:
    """The tracked .v files of a repository root, or of a directory of
    copies.  A directory that git does not track is walked instead, so the
    tools run unchanged on the test copies."""

    def __init__(self, root=None):
        self.root = os.path.abspath(root or os.getcwd())
        self.git = self._is_git()

    def _is_git(self):
        p = subprocess.run(["git", "-C", self.root, "rev-parse",
                            "--show-toplevel"], capture_output=True, text=True)
        return p.returncode == 0 and os.path.samefile(
            p.stdout.strip(), self.root)

    def files(self, skip=SKIP_DIRS):
        if self.git:
            out = subprocess.check_output(
                ["git", "-C", self.root, "ls-files", "*.v"]).decode().split()
        else:
            out = []
            for d, _, fs in os.walk(self.root):
                for f in fs:
                    if f.endswith(".v"):
                        out.append(os.path.relpath(
                            os.path.join(d, f), self.root))
        return sorted(f for f in out if not f.startswith(skip))

    def read(self, rel):
        with open(os.path.join(self.root, rel), encoding="utf-8") as fh:
            return fh.read()

    def write(self, rel, text):
        with open(os.path.join(self.root, rel), "w", encoding="utf-8") as fh:
            fh.write(text)


class Base:
    """The text a file had before the pass.  The spec is a git revision, or a
    directory holding copies of the files under their own relative paths."""

    def __init__(self, spec, tree):
        self.spec, self.tree = spec, tree
        self.dir = spec if spec and os.path.isdir(spec) else None

    def read(self, rel):
        if self.dir:
            p = os.path.join(self.dir, rel)
            if not os.path.exists(p):
                return None
            with open(p, encoding="utf-8") as fh:
                return fh.read()
        p = subprocess.run(["git", "-C", self.tree.root, "show",
                            f"{self.spec}:{rel}"],
                           capture_output=True, text=True)
        return p.stdout if p.returncode == 0 else None

    def files(self):
        if self.dir:
            return Tree(self.dir).files()
        out = subprocess.check_output(
            ["git", "-C", self.tree.root, "ls-tree", "-r", "--name-only",
             self.spec]).decode().split("\n")
        return sorted(f for f in out
                      if f.endswith(".v") and not f.startswith(SKIP_DIRS))


def add_root_arg(ap):
    ap.add_argument("--root", default=None,
                    help="the repository root, or a directory of copies")


# -------------------------------------------------- code and comment split

def comment_spans(text):
    """[(start, end)] of the top-level comments, delimiters included.

    Nesting-aware, and string-aware outside a comment: a (* inside a string
    literal of the code opens no comment."""
    spans, depth, i, start, in_str = [], 0, 0, 0, False
    n = len(text)
    while i < n:
        c = text[i]
        if in_str:
            if c == '"':
                in_str = False
            i += 1
        elif depth == 0 and c == '"':
            in_str = True
            i += 1
        elif text.startswith("(*", i):
            if depth == 0:
                start = i
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
            if depth == 0:
                spans.append((start, i))
        else:
            i += 1
    if depth:
        spans.append((start, n))
    return spans


def comment_mask(text):
    """A bool per character, true inside a comment, delimiters included."""
    mask = [False] * len(text)
    for a, b in comment_spans(text):
        for k in range(a, b):
            mask[k] = True
    return mask


def split(text):
    """(code, comments): the other part blanked, the line breaks kept."""
    mask = comment_mask(text)
    code = "".join(("\n" if c == "\n" else " ") if m else c
                   for c, m in zip(text, mask))
    com = "".join(c if m else ("\n" if c == "\n" else " ")
                  for c, m in zip(text, mask))
    return code, com


def code_tokens(text):
    return split(text)[0].split()


def comment_words(text):
    """Every word of the comments, the delimiters included."""
    return split(text)[1].split()


def prose_words(text):
    """The words of the comment paragraphs: the delimiters, the padding and
    the star lines of the boxes left out.  This is the stream a layout pass
    must leave untouched."""
    return [w for p in paragraphs(text)[1] for w in p.words]


# ------------------------------------------------------------- paragraphs

class Para:
    """One comment paragraph: its place, its kind, its words and the layout
    numbers its own file uses."""

    def __init__(self, kind, first, last, words, layout, block):
        self.kind = kind
        self.first = first          # 1-based, the first line it occupies
        self.last = last            # 1-based, the last line it occupies
        self.words = words
        self.layout = layout
        self.block = block          # the block index it belongs to
        self.raw = None             # table paragraphs keep their own bodies

    @property
    def text(self):
        return " ".join(self.words)


class Block:
    """A run of comment lines laid out together: a padded box, or one
    multi-line comment, or a comment sharing its line with code."""

    def __init__(self, kind, first, last):
        self.kind = kind            # box | multi | inline
        self.first, self.last = first, last
        self.paras = []
        self.layout = {}


def _isbox(line):
    return (line.startswith("(*") and line.rstrip().endswith("*)")
            and len(line.rstrip()) > 4
            and "(*" not in line[2:-2] and "*)" not in line[2:-2])


def _stars(body):
    return body.strip() != "" and set(body.strip()) <= set("*")


def _indent(s):
    return len(s) - len(s.lstrip())


ENTRY = re.compile(r"^\s+\S.*?\s+== ")
# A boxed segment whose lines hold an inner run of three spaces or more is
# a column layout, with or without bars: its words keep their places.
COLUMN = re.compile(r"^\s*\S.*?\S\s{3,}\S")


def _index_columns(bodies):
    """(entry indent, == column) of a boxed header block, or None.

    The entry indent is read off the entry lines alone, never off the prose
    of the same box, which sits at its own smaller indent."""
    alone = [b.index("==") for b in bodies if b.lstrip().startswith("==")]
    inline = [(_indent(b), b.index("==")) for b in bodies if ENTRY.match(b)]
    cols = alone + [c for _, c in inline]
    if not cols:
        return None
    eq = max(set(cols), key=cols.count)
    ents = [i for i, c in inline if c == eq]
    for k, b in enumerate(bodies):
        if k and b.lstrip().startswith("==") and b.index("==") == eq:
            prev = bodies[k - 1]
            if prev.strip() and not prev.lstrip().startswith("=="):
                if _indent(prev) < eq:
                    ents.append(_indent(prev))
    if not ents:
        return None
    return max(set(ents), key=ents.count), eq


def paragraphs(text, path=""):
    """(blocks, paras) of one file.  Every comment word of the file belongs
    to exactly one paragraph; the box decoration belongs to none."""
    lines = text.split("\n")
    spans = comment_spans(text)
    starts = [0]
    for ln in lines:
        starts.append(starts[-1] + len(ln) + 1)

    def line_of(pos):
        lo, hi = 0, len(lines) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if starts[mid] <= pos:
                lo = mid
            else:
                hi = mid - 1
        return lo

    # Which lines are a full-line box line, and which comment spans are
    # whole-line comments.
    boxline = [False] * len(lines)
    info = []
    for a, b in spans:
        la, lb = line_of(a), line_of(b - 1)
        pre = lines[la][:a - starts[la]]
        post = lines[lb][b - starts[lb]:]
        whole = pre.strip() == "" and post.strip() == ""
        if la == lb and whole and _isbox(lines[la]):
            boxline[la] = True
        info.append((la, lb, whole, pre, text[a:b]))

    blocks, i, n = [], 0, len(lines)
    while i < n:
        if boxline[i]:
            j = i
            while j < n and boxline[j]:
                j += 1
            run = lines[i:j]
            if (any(_stars(x[2:-2]) for x in run)
                    or sum(bw(x) == BOX_WIDTH for x in run) >= 3):
                blocks.append(_box_block(run, i, path))
                i = j
                continue
        i += 1
    covered = set()
    for b in blocks:
        covered |= set(range(b.first, b.last + 1))
    for la, lb, whole, pre, body in info:
        if la in covered:
            continue
        blocks.append(_text_block(la, lb, whole, pre, body))
    blocks.sort(key=lambda b: b.first)
    for k, b in enumerate(blocks):
        for p in b.paras:
            p.block = k
    return blocks, [p for b in blocks for p in b.paras]


def _box_block(run, off, path):
    """One padded box: its paragraphs are the banners, the prose segments,
    the tables and the index entries."""
    blk = Block("box", off, off + len(run) - 1)
    bodies = [x.rstrip()[2:-2].rstrip() for x in run]
    cols = _index_columns([b for b in bodies if b.strip()])
    blk.layout = {"index": cols}
    segs, cur = [], []
    for k, b in enumerate(bodies):
        if _stars(b):
            if cur:
                segs.append(("content", cur))
                cur = []
            segs.append(("stars", [k]))
        elif not b.strip():
            if cur:
                segs.append(("content", cur))
                cur = []
            segs.append(("blank", [k]))
        else:
            cur.append(k)
    if cur:
        segs.append(("content", cur))
    for s, (tag, ks) in enumerate(segs):
        if tag != "content":
            continue
        prev = segs[s - 1][0] if s else None
        nxt = segs[s + 1][0] if s + 1 < len(segs) else None
        seg = [bodies[k] for k in ks]
        if prev == "stars" and nxt == "stars":
            p = Para("banner", off + ks[0] - 1, off + ks[-1] + 1,
                     " ".join(x.strip() for x in seg).split(),
                     {"indent": _indent(seg[0])}, None)
            blk.paras.append(p)
        elif cols and any("==" in x for x in seg):
            blk.paras.extend(_index_paras(seg, ks, off, cols))
        elif (any("|" in x for x in seg)
              or sum(1 for x in seg if COLUMN.match(x)) >= 2):
            p = Para("table", off + ks[0], off + ks[-1],
                     " ".join(x.strip() for x in seg).split(), {}, None)
            p.raw = seg
            blk.paras.append(p)
        else:
            ps = _prose_paras(seg, ks, off)
            if off == 0 and s == 0 and nxt == "stars":
                for p in ps:          # the licence block of the tree
                    p.raw = seg
            blk.paras.extend(ps)
    return blk


def _prose_paras(seg, ks, off):
    """A prose segment of a box.  A segment whose lines do not share one
    indent is a list: each line at the smallest indent opens an item of its
    own, and the deeper lines continue it."""
    ind = [_indent(x) for x in seg]
    base = min(ind)
    rest = [i for i in ind if i != base]
    cont = max(set(rest), key=rest.count) if rest else base
    if not rest:
        return [Para("box-prose", off + ks[0], off + ks[-1],
                     " ".join(x.strip() for x in seg).split(),
                     {"base": base, "cont": cont}, None)]
    out, cur = [], []
    for k, (x, i) in enumerate(zip(seg, ind)):
        if i == base and cur:
            out.append(cur)
            cur = []
        cur.append(k)
    if cur:
        out.append(cur)
    return [Para("box-prose", off + ks[g[0]], off + ks[g[-1]],
                 " ".join(seg[k].strip() for k in g).split(),
                 {"base": base, "cont": cont}, None) for g in out]


def _index_paras(seg, ks, off, cols):
    ent, eq = cols
    out, cur = [], []

    def flush():
        if not cur:
            return
        a, b = cur[0], cur[-1]
        text = " ".join(seg[k - ks[0]].strip() for k in cur)
        out.append(Para("box-index", off + a, off + b, text.split(),
                        {"ent": ent, "eq": eq}, None))
        del cur[:]

    for k in ks:
        b = seg[k - ks[0]]
        ind = _indent(b)
        if ind == ent:
            flush()
            cur.append(k)
        elif ind < eq and ind != ent:
            flush()
            out.extend(_prose_paras([b], [k], off))
        else:
            if not cur:
                cur.append(k)
            else:
                cur.append(k)
    flush()
    return out


def _text_block(la, lb, whole, pre, span):
    """A comment written as running text: a docstring, a plain comment, or a
    comment sharing its line with code.  span is the comment itself, its two
    delimiters included."""
    blk = Block("multi" if whole else "inline", la, lb)
    col = len(pre)
    opener = "(**" if span.startswith("(**") else "(*"
    inner = span[len(opener):]
    if inner.rstrip().endswith("*)"):
        inner = inner.rstrip()[:-2]
    body = inner.split("\n")
    ind = [_indent(x) for x in body[1:] if x.strip()]
    # the mode, not the minimum: one shallower line must not move the column
    cont = (max(set(ind), key=lambda i: (ind.count(i), -i)) if ind
            else col + len(opener) + 1)
    blk.layout = {"col": col, "opener": opener, "cont": cont, "pre": pre,
                  "whole": whole}
    paras, cur, kfirst = [], [], 0
    for k, x in enumerate(body):
        if x.strip():
            if not cur:
                kfirst = k
            cur.append(x)
        elif cur:
            paras.append((kfirst, k - 1, cur))
            cur = []
    if cur:
        paras.append((kfirst, len(body) - 1, cur))
    kind = "docstring" if opener == "(**" else "plain"
    if not whole:
        kind = "plain"
    for a, b, chunk in paras:
        blk.paras.append(Para(kind, la + a, la + b,
                              " ".join(x.strip() for x in chunk).split(),
                              {}, None))
    return blk


# ----------------------------------------------------------------- layout

def _join(cur, w):
    return cur + w if (not cur or cur.endswith(" ")) else cur + " " + w


def wrap(words, first, cont, limit, tail="", floor=None):
    """Greedy fill by bytes, then one rebalance so that the last line does
    not hold a single short word while the line above has room.  Never splits
    a word, so a hyphenated word stays whole."""
    if not words:
        return [first.rstrip() + tail]
    groups = [[]]
    for k, w in enumerate(words):
        pref = first if len(groups) == 1 else cont
        cand = _join(pref + " ".join(groups[-1]) if groups[-1] else pref, w)
        extra = bw(tail) if k == len(words) - 1 else 0
        if groups[-1] and bw(cand) + extra > limit:
            groups.append([w])
        else:
            groups[-1].append(w)
    if len(groups) >= 2 and len(groups[-1]) == 1 and len(groups[-2]) >= 2:
        # An orphan the closing delimiter alone pushed down: the word itself
        # would have fitted on the line above.  Rebalance the two lines.
        above = (first if len(groups) == 2 else cont) + " ".join(groups[-2])
        moved = [groups[-2][-1]] + groups[-1]
        if (bw(above + " " + groups[-1][0]) <= limit
                and bw(cont + " ".join(moved)) + bw(tail) <= limit):
            groups[-2] = groups[-2][:-1]
            groups[-1] = moved
    out = []
    for k, g in enumerate(groups):
        pref = first if k == 0 else cont
        line = (pref + " ".join(g)).rstrip()
        extra = bw(tail) if k == len(groups) - 1 else 0
        if (floor is not None and len(g) == 1 and k and bw(line) + extra > limit
                and not cont.strip()):
            # One word too long for the continuation column: set it at the
            # deepest indent that still fits, never above the floor.
            room = limit - extra - bw(g[0])
            line = " " * max(floor, min(len(cont), room)) + g[0]
        out.append(line)
    out[-1] += tail
    return out


def boxline(body):
    pad = BOX_BODY - bw(body)
    return "(*" + body + " " * max(pad, 1) + "*)"


def render_para(para, words=None):
    """The lines of one paragraph, laid out by the rules of its kind."""
    w = para.words if words is None else words
    if para.raw is not None and w == para.words:
        return [boxline(x.rstrip()) for x in para.raw]
    L = para.layout
    if para.kind == "banner":
        ind = " " * L["indent"]
        return [boxline(x) for x in
                wrap(w, ind, ind, BOX_FILL, floor=L["indent"])]
    if para.kind == "table":
        return [boxline(x.rstrip()) for x in para.raw]
    if para.kind == "box-prose":
        return [boxline(x) for x in
                wrap(w, " " * L["base"], " " * L["cont"], BOX_FILL,
                     floor=L["base"])]
    if para.kind == "box-index":
        ent, eq = L["ent"], L["eq"]
        if "==" not in w:
            return [boxline(x) for x in
                    wrap(w, " " * ent, " " * (eq + 3), BOX_FILL, floor=eq)]
        cut = w.index("==")
        name, desc = " ".join(w[:cut]), w[cut + 1:]
        cont = " " * (eq + 3)
        if ent + bw(name) + 1 <= eq:
            first = " " * ent + name + " " * (eq - ent - bw(name)) + "== "
            return [boxline(x) for x in
                    wrap(desc, first, cont, BOX_FILL, floor=eq)]
        out = [boxline(" " * ent + name)]
        out += [boxline(x) for x in
                wrap(desc, " " * eq + "== ", cont, BOX_FILL, floor=eq)]
        return out
    raise ValueError(para.kind)


def render_block(blk, new_words=None):
    """The lines of a running-text block, so that the shared opener and the
    closing delimiter stay in one place."""
    new_words = new_words or {}

    def words_of(p):
        return new_words.get(id(p), p.words)

    L = blk.layout
    ind = " " * L["col"]
    opener, cont = L["opener"], " " * L["cont"]
    lines = []
    for k, p in enumerate(blk.paras):
        first = (L["pre"] + opener + " ") if k == 0 else cont
        tail = " *)" if k == len(blk.paras) - 1 else ""
        if k:
            lines.append("")
        lines += wrap(words_of(p), first, cont, LINE_LIMIT, tail,
                      floor=L["col"])
    return lines


def block_lines(blk, lines, new_words=None):
    """The replacement lines of a block, given the file's current lines."""
    new_words = new_words or {}
    if blk.kind == "inline":
        return None                    # never laid out again
    if blk.kind != "box":
        return render_block(blk, new_words)
    out, prev = [], blk.first
    for p in blk.paras:
        out += lines[prev:p.first]
        if id(p) not in new_words:
            out += lines[p.first:p.last + 1]
        elif p.kind == "banner":
            out.append(lines[p.first])
            out += render_para(p, new_words[id(p)])
            out.append(lines[p.last])
        else:
            out += render_para(p, new_words[id(p)])
        prev = p.last + 1
    out += lines[prev:blk.last + 1]
    return out


def splice(lines, edits):
    """edits: [(first, last, [lines])] over disjoint 0-based line ranges."""
    res, i = [], 0
    for first, last, new in sorted(edits):
        res += lines[i:first]
        res += new
        i = last + 1
    res += lines[i:]
    return res


def relayout(text, blocks, wanted):
    """Lay the given paragraphs out again.  blocks come from paragraphs(text)
    and wanted maps id(para) to its new words, or to None to keep them."""
    lines = text.split("\n")
    edits = []
    for blk in blocks:
        if not any(id(p) in wanted for p in blk.paras):
            continue
        new = block_lines(blk, lines,
                          {id(p): (wanted[id(p)] or p.words)
                           for p in blk.paras if id(p) in wanted})
        if new is not None:
            edits.append((blk.first, blk.last, new))
    return "\n".join(splice(lines, edits))


# ------------------------------------------------------------ declarations

def declaration_after(text, last_line, header_block_last):
    """The identifier of the first declaration under a paragraph, or the word
    header when the paragraph sits in the file's own header box."""
    if header_block_last is not None and last_line <= header_block_last:
        return "header"
    code = split(text)[0].split("\n")
    for line in code[last_line + 1:]:
        m = DECL.match(line)
        if m:
            return m.group(2)
    return "header"


def header_last_line(blocks, text):
    """The last line of the file's own header box, or None."""
    code = split(text)[0].split("\n")
    for blk in blocks:
        if blk.kind != "box":
            continue
        if any(l.strip() for l in code[:blk.first]):
            return None
        return blk.last
    return None


# ------------------------------------------------------------------- misc

def read_tsv(path):
    rows = []
    with open(path, encoding="utf-8") as fh:
        head = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            if not line.strip():
                continue
            cells = line.rstrip("\n").split("\t")
            cells += [""] * (len(head) - len(cells))
            rows.append(dict(zip(head, cells)))
    return head, rows


def write_tsv(path, head, rows):
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("\t".join(head) + "\n")
        for r in rows:
            fh.write("\t".join(str(r.get(c, "")) for c in head) + "\n")


def die(msg):
    print(msg)
    sys.exit(1)
