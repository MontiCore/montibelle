import logging
from unittest import IsolatedAsyncioTestCase

from autosledgi import test
from autosledgi.test import logger
from tests import init_log, copy_res, reset_log, get_copy, get_result


class ValueTest(IsolatedAsyncioTestCase):

    @classmethod
    def setUpClass(cls):
        init_log(logging.INFO)
        copy_res('value')

    @classmethod
    def tearDownClass(cls):
        reset_log()

    async def test_Value(self):
        theory_path_value1 = get_copy('value', 'Value1')
        theory_path_value2 = get_copy('value', 'Value2')

        self.assertTrue(await test.process([theory_path_value1]))

        self.assertFalse(await test.process([theory_path_value2]))

        self.assertFalse(await test.process([theory_path_value1, theory_path_value2]))

    async def test_Value_Pll(self):
        theory_path_value1 = get_copy('value', 'Value1')
        theory_path_value2 = get_copy('value', 'Value2')
        
        self.assertTrue(await test.process([theory_path_value1],
            parallel_mode=True))

        self.assertFalse(await test.process([theory_path_value2], 
            parallel_mode=True))

        self.assertFalse(await test.process(
            [theory_path_value1, theory_path_value2], 
            parallel_mode=True))
