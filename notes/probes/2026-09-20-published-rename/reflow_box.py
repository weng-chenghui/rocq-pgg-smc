#!/usr/bin/env python3
"""Re-lays out the boxed comment blocks the rename disturbed.

A box line is (* ... *) padded to exactly 80 bytes.  Only a paragraph that no
longer has every line at 80 bytes with a space before the closing delimiter is
touched; the rest stay byte-identical.  Words keep their order.
"""
import sys
import collections

W = 75          # greatest content width that keeps a space before *)


def isbox(l):
    return (l.startswith("(*") and l.endswith("*)") and len(l) > 4
            and "(*" not in l[2:] and "*)" not in l[:-2]
            and (not l.startswith("(**") or banner(l)))


def regions(lines):
    """Index set of the lines that sit in a padded box block."""
    inside, i, n = set(), 0, len(lines)
    while i < n:
        if not isbox(lines[i]):
            i += 1
            continue
        j = i
        while j < n and isbox(lines[j]):
            j += 1
        run = lines[i:j]
        if any(banner(x) for x in run) or sum(len(x) == 80 for x in run) >= 3:
            inside |= set(range(i, j))
        i = j
    return inside


def banner(l):
    return set(l) <= set("(*)")


def box(body):
    assert len(body) <= 76, body
    return "(*" + body.ljust(76) + "*)"


def fill(words, prefix, cont):
    """Greedy fill; the first line starts with prefix, the rest with cont."""
    out, cur = [], prefix
    for w in words:
        t = cur + w if (not cur or cur.endswith(" ")) else cur + " " + w
        if len(t) > W and cur.strip():
            out.append(cur.rstrip())
            cur = " " * cont + w
        else:
            cur = t
    out.append(cur.rstrip())
    return out


def indent(b):
    return len(b) - len(b.lstrip())


def prose(bodies):
    ind = [indent(b) for b in bodies]
    base = min(ind)
    if all(i == base for i in ind):
        return fill(" ".join(b.strip() for b in bodies).split(),
                    " " * base, base)
    cont = collections.Counter(i for i in ind if i != base).most_common(1)[0][0]
    out, chunk = [], []
    for b, i in zip(bodies, ind):
        if i == base and chunk:
            out += fill(" ".join(x.strip() for x in chunk).split(),
                        " " * base, cont)
            chunk = []
        chunk.append(b)
    out += fill(" ".join(x.strip() for x in chunk).split(), " " * base, cont)
    return out


def index(bodies, report, where):
    ind = [indent(b) for b in bodies]
    cols = [b.index("==") for b in bodies if b.lstrip().startswith("==")]
    if not cols:
        cols = [b.index("==") for b in bodies if "==" in b]
    eq = collections.Counter(cols).most_common(1)[0][0]
    ent = collections.Counter(i for i in ind if i < eq).most_common(1)[0][0]
    out, chunk = [], []

    def flush():
        if not chunk:
            return
        text = " ".join(x.strip() for x in chunk)
        if " == " in text:
            name, desc = text.split(" == ", 1)
            name, desc = name.rstrip(), desc.lstrip()
            if ent + len(name) + 1 <= eq:
                out.extend(fill(desc.split(),
                                " " * ent + name.ljust(eq - ent) + "== ",
                                eq + 3))
            else:
                out.append(" " * ent + name)
                report.append((where, name))
                out.extend(fill(desc.split(), " " * eq + "== ", eq + 3))
        else:
            out.extend(fill(text.split(), " " * ent, eq + 3))
        del chunk[:]

    for b, i in zip(bodies, ind):
        if i < eq and i != ent:
            flush()
            out.append(b)
        elif i == ent:
            flush()
            chunk.append(b)
        else:
            chunk.append(b)
    flush()
    return out


def run(path, report, base):
    text = open(path, encoding="utf-8").read()
    old = open(base, encoding="utf-8").read().split("\n")
    lines = text.split("\n")
    assert len(old) == len(lines), (path, len(old), len(lines))
    inside = regions(lines)
    out, i = [], 0
    while i < len(lines):
        l = lines[i]
        if i not in inside or banner(l) or not l[2:-2].strip():
            out.append(l)
            i += 1
            continue
        j = i
        while (j < len(lines) and j in inside and not banner(lines[j])
               and lines[j][2:-2].strip()):
            j += 1
        bodies = [x[2:-2].rstrip() for x in lines[i:j]]
        if lines[i:j] == old[i:j]:
            out.extend(lines[i:j])
        elif any("|" in b for b in bodies):
            out.extend(box(b) for b in bodies)
        elif any("==" in b for b in bodies):
            out.extend(box(b) for b in index(bodies, report, f"{path}:{i+1}"))
        else:
            out.extend(box(b) for b in prose(bodies))
        i = j
    new = "\n".join(out)
    if new != text:
        open(path, "w", encoding="utf-8").write(new)
        return True
    return False


if __name__ == "__main__":
    rep = []
    base_dir = None
    args = sys.argv[1:]
    if args and args[0].startswith("--base="):
        base_dir = args.pop(0).split("=", 1)[1]
    for p in args:
        b = base_dir + "/" + p if base_dir else None
        print(("CHANGED " if run(p, rep, b) else "same    ") + p)
    for w, n in rep:
        print("  wrapped index entry", w, n)
