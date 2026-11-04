import logging
import time
import unittest

from autosledgi import prove, SledgehammerParams
from tests import init_log, copy_res, get_copy, reset_log


class RecursiveTestCasePll(unittest.IsolatedAsyncioTestCase):

    @classmethod
    def setUpClass(cls):
        init_log(logging.INFO)
        copy_res('recursive')

    @classmethod
    def tearDownClass(cls):
        reset_log()

    async def test_recursive(self):
        theory_path = get_copy('recursive')
        success = await prove.process([theory_path], finder_params=SledgehammerParams(timeout=1), parallel_mode=True)
        self.assertTrue(success)

    def tearDown(self):
        time.sleep(1)
