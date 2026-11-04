import logging
import time
from unittest import IsolatedAsyncioTestCase

import asyncio

from autosledgi import prove, SledgehammerParams
from tests import init_log, copy_res, get_result, get_copy, reset_log

class SimpleTestCasePll(IsolatedAsyncioTestCase):

    @classmethod
    def setUpClass(cls):
        init_log(logging.INFO)
        copy_res('simple')

    @classmethod
    def tearDownClass(cls):
        reset_log()

    async def test_MultipleSledgehammer(self):
        theory_path = get_copy('simple', 'MultipleSledgehammer')
        status = await prove.process([theory_path], 
            finder_params=SledgehammerParams(timeout=1), parallel_mode=True)
        self.assertTrue(status)
        self.assertEqual(status,prove.Status.FAILED,
            "Expected FAILED when multiple sledgehammer lines appear above \
            the same autosledgi annotation." )
        expected, actual = get_result('simple', 'MultipleSledgehammer')
        self.assertEqual(expected, actual)

    async def test_BadContext(self):
        theory_path = get_copy('simple', 'BadContext')
        success = await prove.process([theory_path], 
            finder_params=SledgehammerParams(timeout=1), parallel_mode=True)
        self.assertTrue(success)
        expected, actual = get_result('simple', 'BadContext')
        self.assertEqual(expected, actual)

    async def test_BadContext2(self):
        theory_path = get_copy('simple', 'BadContext2')
        success = await prove.process([theory_path], 
            finder_params=SledgehammerParams(timeout=1), parallel_mode=True)
        self.assertTrue(success)
        expected, actual = get_result('simple', 'BadContext2')
        self.assertEqual(expected, actual)

    async def test_SingleSubgoal(self):
        theory_path = get_copy('simple', 'SingleSubgoal')
        success = await prove.process([theory_path], 
            finder_params=SledgehammerParams(timeout=1), parallel_mode=True)
        self.assertTrue(success)
        expected, actual = get_result('simple', 'SingleSubgoal')
        self.assertEqual(expected, actual)

    async def test_MultipleGoals(self):
        theory_path = get_copy('simple', 'MultipleSubgoals')
        success = await prove.process([theory_path], 
            finder_params=SledgehammerParams(timeout=1, provers=['cvc4']),
            parallel_mode=True)
        self.assertTrue(success)
        expected, actual = get_result('simple', 'MultipleSubgoals')

    def tearDown(self):
        time.sleep(1)

