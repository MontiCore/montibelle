import logging
from unittest import TestCase

from autosledgi.isabelle.utils import SledgehammerParams
from tests import init_log, reset_log


class TestSledgehammerParams(TestCase):

    @classmethod
    def setUpClass(cls):
        init_log(logging.INFO)

    @classmethod
    def tearDownClass(cls):
        reset_log()

    def test_defaults(self):
        tsc = SledgehammerParams()
        self.assertEqual('sledgehammer []', tsc.gen_sledgehammer_cmd())

    def test_timeout(self):
        tsc = SledgehammerParams(timeout=5)
        self.assertEqual('sledgehammer [timeout=5]', tsc.gen_sledgehammer_cmd())

    def test_isar_proofs(self):
        tsc = SledgehammerParams(isar_proofs=True)
        self.assertEqual('sledgehammer [isar_proofs=true]', tsc.gen_sledgehammer_cmd())
        tsc = SledgehammerParams(isar_proofs=False)
        self.assertEqual('sledgehammer [isar_proofs=false]', tsc.gen_sledgehammer_cmd())

    def test_max_facts(self):
        tsc = SledgehammerParams(max_facts=5)
        self.assertEqual('sledgehammer [max_facts=5]', tsc.gen_sledgehammer_cmd())

    def test_provers(self):
        tsc = SledgehammerParams(provers=['a', 'b', 'c'])
        self.assertEqual('sledgehammer [provers="a b c"]', tsc.gen_sledgehammer_cmd())

    def test_multiple(self):
        tsc = SledgehammerParams(timeout=5, provers=['a', 'b', 'c'], isar_proofs=True, max_facts=5)
        self.assertEqual('sledgehammer [timeout=5, isar_proofs=true, max_facts=5, provers="a b c"]', tsc.gen_sledgehammer_cmd())
