import logging
from unittest import TestCase

from autosledgi.isabelle.proof import Proof
from tests import init_log, reset_log

best = Proof(prover='', proof='', is_done=False, time=0.5, method='simp')
medium = Proof(prover='', proof='', is_done=False, time=1, method=None)
subpar = Proof(prover='', proof='', is_done=False, time=2, method='metis')
worst = Proof(prover='', proof='', is_done=False, time=None, method='smt')


class TestProof(TestCase):

    @classmethod
    def setUpClass(cls):
        init_log(logging.INFO)

    @classmethod
    def tearDownClass(cls):
        reset_log()

    def test_sort(self):
        self.assertEqual(
            [best, medium, subpar, worst],
            sorted([worst, best, subpar, medium])
        )

    def test_reverse_sort(self):
        self.assertEqual(
            [worst, subpar, medium, best],
            sorted([worst, best, subpar, medium], reverse=True)
        )
