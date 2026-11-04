import logging
import time
from unittest import IsolatedAsyncioTestCase

import asyncio

from autosledgi import prove, SledgehammerParams
from tests import init_log, copy_res, get_result, get_copy, reset_log
from autosledgi.isabelle import TheoFile

class ParallelTestCase(IsolatedAsyncioTestCase):

    @classmethod
    def setUpClass(cls):
        init_log(logging.INFO)

    @classmethod
    def tearDownClass(cls):
        reset_log()

    async def test_NoProof(self):
        copy_res('no_proof_found')
        theory_path = get_copy('no_proof_found', 'false_lemma')
        status = await prove.process([theory_path], 
            finder_params=SledgehammerParams(timeout=1),
            use_quickcheck=False)
        self.assertTrue(status)
        self.assertEqual(status, prove.Status.UNKNOWN,
                "Expected to neither find a proof nor a counterexample.")
        expected, actual = get_result('no_proof_found', 'false_lemma')
        self.assertEqual(expected, actual)

    async def test_NoProofParallel(self):
        copy_res('no_proof_found')
        theory_path = get_copy('no_proof_found', 'false_lemma')
        status = await prove.process([theory_path],
            finder_params=SledgehammerParams(timeout=1), 
            parallel_mode=True,
            use_quickcheck=False)
        self.assertTrue(status)
        self.assertEqual(status, prove.Status.UNKNOWN, 
                "Expected to neither find a proof nor a counterexample.")
        expected, actual = get_result('no_proof_found', 'false_lemma')
        self.assertEqual(expected, actual)
