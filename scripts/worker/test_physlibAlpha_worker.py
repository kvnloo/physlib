"""Tests of the axiom check in `physlibAlpha_worker.py` (step 10, safety checks).

Each case is a file of a small Lean project made in a temporary folder, using only Lean's core
library and the toolchain in Physlib's `lean-toolchain`, so no Mathlib build is needed. Run from
the root of a Physlib checkout, with `lake` (elan) installed:

    python3 -m unittest scripts/worker/test_physlibAlpha_worker.py -v
"""

from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import physlibAlpha_worker as worker  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]

# The cheats a text search for `sorry` misses or is fooled by, and the honest cases it must let
# through. Each value is the text of one file, `PhyslibAlpha/<key>.lean`.
CASES = {
    # A review comment on the worker: the agent removes a comment that mentions sorry and adds a
    # `by sorry`, so the number of times `sorry` appears in the file is unchanged.
    "CommentSwappedForBySorry": """
theorem add_zero' (n : Nat) : n + 0 = n := by sorry
""",
    # `sorry`, `admit`, `axiom` and `native_decide` only in comments and docstrings: nothing to catch.
    "SorryOnlyInComments": """
/-! This file once had a `sorry`; we admit that `native_decide` and an `axiom` were tried. -/

-- TODO: remove the sorry below once it is proved
/-- Proved without sorry. Fields admit a zero. -/
theorem add_zero' (n : Nat) : n + 0 = n := rfl
""",
    "BySorry": """
theorem two_eq_two : 2 = 2 := by sorry
""",
    "TermSorry": """
theorem two_eq_two : 2 = 2 := sorry
""",
    "Admit": """
theorem two_eq_two : 2 = 2 := by admit
""",
    "SorryInsideHave": """
theorem lt_succ' (n : Nat) : n < n + 1 := by
  have h : n < n + 1 := by exact sorry
  exact h
""",
    # The main theorem has no `sorry` of its own; a helper lemma does.
    "SorryInHelperLemma": """
theorem helper (n : Nat) : n ≤ n + 1 := by sorry

theorem main' (n : Nat) : n ≤ n + 1 := helper n
""",
    # The word `sorry` never appears next to the proof: a macro produces it.
    "SorryFromMacro": """
macro "trust_me" : tactic => `(tactic| sorry)

theorem two_eq_two : 2 = 2 := by trust_me
""",
    "SorryInDefinition": """
def answer : Nat := sorry
""",
    "PrivateSorry": """
private theorem hidden : 2 = 2 := by sorry
""",
    "NewAxiom": """
axiom everything : ∀ p : Prop, p

theorem false_proof : 1 = 2 := everything _
""",
    "NativeDecide": """
theorem big : 2 ^ 10 = 1024 := by native_decide
""",
    # Honest proofs, including ones using the standard axioms (`Classical.choice` via `by_cases`).
    "Honest": """
theorem add_zero' (n : Nat) : n + 0 = n := rfl

theorem em' (p : Prop) : p ∨ ¬p := by
  by_cases h : p
  · exact Or.inl h
  · exact Or.inr h

theorem two_pow : 2 ^ 10 = 1024 := by decide
""",
}

# What the check must report for each case: (declaration, axiom) pairs, without the case's namespace.
EXPECTED = {
    "CommentSwappedForBySorry": [("add_zero'", "sorryAx")],
    "SorryOnlyInComments": [],
    "BySorry": [("two_eq_two", "sorryAx")],
    "TermSorry": [("two_eq_two", "sorryAx")],
    "Admit": [("two_eq_two", "sorryAx")],
    "SorryInsideHave": [("lt_succ'", "sorryAx")],
    "SorryInHelperLemma": [("helper", "sorryAx"), ("main'", "sorryAx")],
    "SorryFromMacro": [("two_eq_two", "sorryAx")],
    "SorryInDefinition": [("answer", "sorryAx")],
    "PrivateSorry": [("hidden", "sorryAx")],
    "NewAxiom": [("everything", "everything"), ("false_proof", "everything")],
    # Lean 4.35 makes `native_decide` add an auxiliary axiom for its compiled check.
    "NativeDecide": [("big", "big._native.native_decide.ax_1_1")],
    "Honest": [],
}


@unittest.skipUnless(shutil.which("lake"), "needs lake (elan) on the PATH")
class AxiomCheckTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.folder = tempfile.TemporaryDirectory()
        project = Path(cls.folder.name)
        shutil.copy(ROOT / "lean-toolchain", project / "lean-toolchain")
        (project / "lakefile.toml").write_text('name = "AxiomCheckTest"\n\n[[lean_lib]]\nname = "PhyslibAlpha"\n')
        (project / "PhyslibAlpha").mkdir()
        for name, text in CASES.items():
            (project / "PhyslibAlpha" / f"{name}.lean").write_text(f"namespace {name}\n{text}\nend {name}\n")
        modules = [f"PhyslibAlpha.{name}" for name in CASES]
        built = subprocess.run(["lake", "build", *modules], cwd=project, capture_output=True, text=True)
        if built.returncode != 0:
            raise RuntimeError(f"the test project did not build:\n{built.stdout}\n{built.stderr}")
        cls.project = project

    @classmethod
    def tearDownClass(cls) -> None:
        cls.folder.cleanup()

    def test_cases(self) -> None:
        for name, expected in EXPECTED.items():
            with self.subTest(case=name):
                found = worker.axiom_check(self.project, [f"PhyslibAlpha.{name}"])
                pairs = sorted(
                    (decl.split(".")[-1], axiom.removeprefix(f"{name}."))
                    for decl, axioms in found for axiom in axioms
                )
                self.assertEqual(pairs, sorted(expected), found)

    def test_several_modules_at_once(self) -> None:
        found = worker.axiom_check(self.project, ["PhyslibAlpha.Honest", "PhyslibAlpha.BySorry"])
        self.assertEqual(found, [("BySorry.two_eq_two", ["sorryAx"])])

    def test_no_modules(self) -> None:
        self.assertEqual(worker.axiom_check(self.project, []), [])

    def test_unbuilt_module_fails_closed(self) -> None:
        with self.assertRaises(worker.WorkerError):
            worker.axiom_check(self.project, ["PhyslibAlpha.DoesNotExist"])


class ModuleNameTest(unittest.TestCase):
    def test_module_name(self) -> None:
        self.assertEqual(worker.module_name("PhyslibAlpha/Foo/Bar.lean"), "PhyslibAlpha.Foo.Bar")
        self.assertEqual(worker.module_name("PhyslibAlpha.lean"), "PhyslibAlpha")


if __name__ == "__main__":
    unittest.main()
