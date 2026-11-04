import logging
import time
from unittest import IsolatedAsyncioTestCase, expectedFailure

import asyncio

from autosledgi import prove, SledgehammerParams
from tests import init_log, copy_res, get_result, get_copy, reset_log

class WithoutNamesTestCase(IsolatedAsyncioTestCase):

    @classmethod
    def setUpClass(cls):
        init_log(logging.INFO)
        copy_res('test_without_lemma_names')

    @classmethod
    def tearDownClass(cls):
        reset_log()

    async def test_WithoutNames(self):
        theory_path = get_copy('test_without_lemma_names', "WithoutNames")
        status = await prove.process([theory_path], 
            finder_params=SledgehammerParams(timeout=2, provers=['e']))
        self.assertTrue(status)
        self.assertEqual(status, prove.Status.VERIFIED, 
            "Expected to verify the theory.")

    async def test_WithoutNames_Pll(self):
        theory_path = get_copy('test_without_lemma_names', "WithoutNames_Pll")
        status = await prove.process([theory_path],
            finder_params=SledgehammerParams(timeout=2, provers=['e']),
            parallel_mode=True)
        self.assertTrue(status)
        self.assertEqual(status, prove.Status.VERIFIED,
                "Expected to verify the theory." )

    def tearDown(self):
        time.sleep(1)
