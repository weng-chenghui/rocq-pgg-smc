#!/usr/bin/env python3
"""Tests the one-time Tableau to Verifolio source rename."""

from __future__ import annotations

import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("rename_tableau_to_verifolio.py")


class RenameVerifolioTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="verifolio-rename-")
        self.root = Path(self.tmp.name)
        files = {
            "_CoqProject": (
                "manifest/pgg_tableau.v\n"
                "instances/demo/tableau/demo_tableau.v\n"
            ),
            "manifest/pgg_tableau.v": (
                "Record TableauAt := MkTableau { tableau_at : nat }.\n"
                "Notation Tableau := TableauAt.\n"
            ),
            "instances/demo/tableau/demo_tableau.v": (
                "From demo Require Import pgg_tableau.\n"
                "Definition demo : Tableau := MkTableau 0.\n"
            ),
            "instances/demo/consumer.v": (
                "From demo Require Import demo_tableau.\n"
                "Check tableau_at.\n"
                "(* notes/archive_tableau.v records the earlier design. *)\n"
            ),
            "notes/archive_tableau.v": "Check Tableau.\n",
            "docs/tableau.md": "Historical Tableau design.\n",
        }
        for relative, content in files.items():
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
        subprocess.run(["git", "init", "-q"], cwd=self.root, check=True)
        subprocess.run(["git", "add", "-A"], cwd=self.root, check=True)

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def run_script(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["python3", str(SCRIPT), "--root", str(self.root), *args],
            capture_output=True,
            text=True,
        )

    def test_dry_run_reports_without_writing(self) -> None:
        result = self.run_script()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("manifest/pgg_tableau.v -> manifest/pgg_verifolio.v", result.stdout)
        self.assertTrue((self.root / "manifest/pgg_tableau.v").exists())
        self.assertFalse((self.root / "manifest/pgg_verifolio.v").exists())

    def test_apply_renames_source_content_and_paths(self) -> None:
        result = self.run_script("--apply")
        self.assertEqual(result.returncode, 0, result.stderr)

        core = self.root / "manifest/pgg_verifolio.v"
        instance = self.root / "instances/demo/verifolio/demo_verifolio.v"
        self.assertTrue(core.exists())
        self.assertTrue(instance.exists())
        self.assertIn("Record VerifolioAt", core.read_text(encoding="utf-8"))
        self.assertIn("verifolio_at", core.read_text(encoding="utf-8"))
        self.assertIn("pgg_verifolio", instance.read_text(encoding="utf-8"))
        self.assertIn(
            "demo_verifolio",
            (self.root / "instances/demo/consumer.v").read_text(encoding="utf-8"),
        )
        self.assertIn(
            "notes/archive_tableau.v",
            (self.root / "instances/demo/consumer.v").read_text(encoding="utf-8"),
        )
        self.assertIn("pgg_verifolio.v", (self.root / "_CoqProject").read_text())

        self.assertEqual(
            (self.root / "notes/archive_tableau.v").read_text(),
            "Check Tableau.\n",
        )
        self.assertEqual(
            (self.root / "docs/tableau.md").read_text(),
            "Historical Tableau design.\n",
        )

        second_run = self.run_script()
        self.assertEqual(second_run.returncode, 0, second_run.stderr)
        self.assertIn("dry run: 0 content file(s), 0 path rename(s)", second_run.stdout)

    def test_collision_stops_before_writing(self) -> None:
        destination = self.root / "manifest/pgg_verifolio.v"
        destination.write_text("occupied\n", encoding="utf-8")

        result = self.run_script("--apply")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("destination already exists", result.stderr)
        self.assertTrue((self.root / "manifest/pgg_tableau.v").exists())
        self.assertEqual(destination.read_text(), "occupied\n")


if __name__ == "__main__":
    unittest.main()
