#!/usr/bin/env python3
"""Rename the tracked Rocq Tableau source surface to Verifolio.

The source census for this migration found only two spellings to replace:
``Tableau`` in Rocq type and constructor names, and ``tableau`` in lower-case
identifiers, module names, paths, and comments.  The script edits tracked Rocq
sources plus ``_CoqProject``.  Historical material under ``notes/``, ``docs/``,
and ``legacy/`` is intentionally left unchanged.

The default is a dry run.  Pass ``--apply`` to write the checked rename.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


EXCLUDED_PREFIXES = ("notes/", "docs/", "legacy/")
TEXT_REPLACEMENTS = (("Tableau", "Verifolio"), ("tableau", "verifolio"))
HISTORICAL_PATH = re.compile(r"(?:notes|docs|legacy)/[A-Za-z0-9_./-]+")


@dataclass(frozen=True)
class Edit:
    path: Path
    old_text: str
    new_text: str


@dataclass(frozen=True)
class Move:
    source: Path
    destination: Path


def git_root(start: Path) -> Path:
    result = subprocess.run(
        ["git", "-C", str(start), "rev-parse", "--show-toplevel"],
        check=True,
        capture_output=True,
        text=True,
    )
    return Path(result.stdout.strip()).resolve()


def tracked_files(root: Path) -> list[Path]:
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z"],
        check=True,
        capture_output=True,
    )
    return [Path(raw.decode()) for raw in result.stdout.split(b"\0") if raw]


def in_source_scope(relative: Path) -> bool:
    name = relative.as_posix()
    if name.startswith(EXCLUDED_PREFIXES):
        return False
    return relative.suffix == ".v" or name == "_CoqProject"


def replace_unprotected(text: str) -> str:
    for old, new in TEXT_REPLACEMENTS:
        text = text.replace(old, new)
    return text


def replace_spelling(text: str) -> str:
    pieces: list[str] = []
    start = 0
    for match in HISTORICAL_PATH.finditer(text):
        pieces.append(replace_unprotected(text[start : match.start()]))
        pieces.append(match.group(0))
        start = match.end()
    pieces.append(replace_unprotected(text[start:]))
    return "".join(pieces)


def renamed_path(relative: Path) -> Path:
    return Path(replace_spelling(relative.as_posix()))


def plan(root: Path) -> tuple[list[Edit], list[Move]]:
    edits: list[Edit] = []
    moves: list[Move] = []
    tracked = tracked_files(root)

    for indexed_relative in tracked:
        if not in_source_scope(indexed_relative):
            continue
        relative = indexed_relative
        absolute = root / relative
        if not absolute.exists():
            worktree_relative = renamed_path(indexed_relative)
            worktree_path = root / worktree_relative
            if worktree_relative == indexed_relative or not worktree_path.exists():
                continue
            relative = worktree_relative
            absolute = worktree_path
        old_text = absolute.read_text(encoding="utf-8")
        new_text = replace_spelling(old_text)
        if new_text != old_text:
            edits.append(Edit(relative, old_text, new_text))

        destination = renamed_path(relative)
        if destination != relative:
            moves.append(Move(relative, destination))

    sources = {move.source for move in moves}
    destinations: set[Path] = set()
    for move in moves:
        if move.destination in destinations:
            raise ValueError(f"duplicate destination: {move.destination}")
        destinations.add(move.destination)
        destination = root / move.destination
        if destination.exists() and move.destination not in sources:
            raise ValueError(f"destination already exists: {move.destination}")

    return edits, moves


def remove_empty_old_directories(root: Path, moves: list[Move]) -> None:
    directories = {
        parent
        for move in moves
        for parent in move.source.parents
        if parent != Path(".")
    }
    for relative in sorted(directories, key=lambda path: len(path.parts), reverse=True):
        try:
            (root / relative).rmdir()
        except OSError:
            pass


def apply_plan(root: Path, edits: list[Edit], moves: list[Move]) -> None:
    for edit in edits:
        (root / edit.path).write_text(edit.new_text, encoding="utf-8")

    for move in sorted(moves, key=lambda item: len(item.source.parts), reverse=True):
        source = root / move.source
        destination = root / move.destination
        destination.parent.mkdir(parents=True, exist_ok=True)
        source.rename(destination)

    remove_empty_old_directories(root, moves)


def report(edits: list[Edit], moves: list[Move], apply: bool) -> None:
    action = "applied" if apply else "dry run"
    print(f"{action}: {len(edits)} content file(s), {len(moves)} path rename(s)")
    for move in moves:
        print(f"{move.source} -> {move.destination}")
    for edit in edits:
        upper = edit.old_text.count("Tableau")
        lower = edit.old_text.count("tableau")
        print(f"content {edit.path}: Tableau={upper}, tableau={lower}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        help="repository root; defaults to the repository containing this script",
    )
    parser.add_argument(
        "--apply",
        action="store_true",
        help="write the rename; without this option the script only reports it",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        root = args.root.resolve() if args.root else git_root(Path(__file__).parent)
        edits, moves = plan(root)
        report(edits, moves, args.apply)
        if args.apply:
            apply_plan(root, edits, moves)
        return 0
    except (OSError, subprocess.CalledProcessError, UnicodeError, ValueError) as error:
        print(f"rename aborted: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
