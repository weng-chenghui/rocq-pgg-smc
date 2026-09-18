from collections import Counter, deque
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[3]
BLOCKS = ROOT / "instances/psl211/psl211_blocks.v"


def table(source: str, name: str) -> list[tuple[int, ...]]:
    start = source.index(f"Definition {name}")
    end = source.index("].", start)
    body = source[start:end]
    return [
        tuple(map(int, re.findall(r"\d+", row)))
        for row in re.findall(r"\[::([^]]+)\]", body)
    ]


def compose(p: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(p[q[i]] for i in range(12))


def closure(generators: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    identity = tuple(range(12))
    seen = {identity}
    todo = deque([identity])
    while todo:
        p = todo.popleft()
        for generator in generators:
            q = compose(generator, p)
            if q not in seen:
                seen.add(q)
                todo.append(q)
    return sorted(seen)


def layout(block: tuple[int, ...]) -> tuple[int, ...]:
    block_set = set(block)
    complement = tuple(i for i in range(12) if i not in block_set)
    result = [0] * 12
    for rank, position in enumerate(block):
        result[position] = rank
    for rank, position in enumerate(complement):
        result[position] = 6 + rank
    return tuple(result)


def view(deck: tuple[int, ...], cut: tuple[int, ...], coalition: tuple[int, ...]):
    return tuple(deck[cut[i]] for i in coalition)


source = BLOCKS.read_text()
mirror = table(source, "psl211_mirror_tbl")
hexad = table(source, "psl211_hexad_tbl")
r4 = (3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8)
m6 = (3, 2, 4, 1, 5, 0, 9, 8, 10, 7, 11, 6)
group = closure([r4, m6])
print("table sizes", len(mirror), len(hexad), "group", len(group))

for size in range(1, 6):
    coalition = tuple(range(size))
    for index, (left, right) in enumerate(zip(mirror, hexad)):
        left_count = Counter(view(layout(left), g, coalition) for g in group)
        right_count = Counter(view(layout(right), g, coalition) for g in group)
        if left_count != right_count:
            witness = min(set(left_count) | set(right_count),
                          key=lambda v: (left_count[v] == right_count[v], v))
            print("counter", size, index, witness,
                  left_count[witness], right_count[witness])
            raise SystemExit

print("no counterexample through coalition size five")
