import logging
import time
from unittest import IsolatedAsyncioTestCase, expectedFailure, skip

import asyncio

from autosledgi import prove, SledgehammerParams
from tests import init_log, copy_res, get_result, get_copy, reset_log
from autosledgi.isabelle import TheoFile, theory

class ParallelTestCase(IsolatedAsyncioTestCase):

    @classmethod
    def setUpClass(cls):
        init_log(logging.INFO)
        copy_res('parallel')

    @classmethod
    def tearDownClass(cls):
        reset_log()

    async def test_OneLemma(self):
        theory_path = get_copy('parallel', 'OneLemma')
        status = await prove.process([theory_path], 
            finder_params=SledgehammerParams(timeout=2, provers=['e']),
            parallel_mode=True)
        self.assertTrue(status)
        self.assertEqual(status, prove.Status.VERIFIED,
                "Expected to verify the theory." )

    async def test_TwoSimpleLemmata(self):
        theory_path = get_copy('parallel', 'TwoSimpleLemmata')
        status = await prove.process([theory_path],
            finder_params=SledgehammerParams(timeout=4, provers=['e']),
            parallel_mode=True)
        self.assertTrue(status)
        self.assertEqual(status, prove.Status.VERIFIED, 
            "Expected to verify the theory." )

    async def test_TwoSubgoals(self):
        theory_path = get_copy('parallel', 'TwoSubgoals')
        status = await prove.process([theory_path],
            finder_params=SledgehammerParams(timeout=10), parallel_mode=True)
        self.assertTrue(status)
        self.assertEqual(status, prove.Status.VERIFIED,
                "Expected to verify the theory." )

    async def test_TwoComplexLemmata(self):
        theory_path = get_copy('parallel', 'TwoComplexLemmata')
        status = await prove.process([theory_path],
            finder_params=SledgehammerParams(timeout=5), parallel_mode=True)
        self.assertTrue(status)
        self.assertEqual(status, prove.Status.VERIFIED,
            "Expected to verify the theory." )


    async def test_Complex(self):
        theory_path = get_copy('parallel', 'Complex')
        status = await prove.process([theory_path],
            finder_params=SledgehammerParams(timeout=20), parallel_mode=True)
        self.assertTrue(status)
        self.assertEqual(status, prove.Status.VERIFIED,
                "Expected to verify the theory." )

    def tearDown(self):
        time.sleep(1)
