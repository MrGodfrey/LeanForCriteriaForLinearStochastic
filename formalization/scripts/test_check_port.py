"""The axiom gate must reject incomplete output and forbidden dependencies."""
import unittest
from check_port import inspect_axioms

class AxiomGateTests(unittest.TestCase):
    def test_standard_axioms_and_empty_closure(self):
        output = "'a' depends on axioms: [propext, Classical.choice, Quot.sound]\n'b' does not depend on any axioms"
        self.assertEqual(set(inspect_axioms(output, ["a", "b"])), {"a", "b"})

    def test_rejects_sorry_custom_axioms_and_bad_inventory(self):
        outputs = ["'a' depends on axioms: [sorryAx]", "'a' depends on axioms: [MyAxiom]",
                   "", "'a' depends on axioms: []\n'a' depends on axioms: []",
                   "'a' depends on axioms: []\n'b' depends on axioms: []"]
        for output in outputs:
            with self.subTest(output=output), self.assertRaises(ValueError):
                inspect_axioms(output, ["a"])

if __name__ == "__main__":
    unittest.main()
