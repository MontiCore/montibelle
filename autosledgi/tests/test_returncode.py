import logging
import os
import unittest
from unittest import TestCase
from unittest.mock import patch

from autosledgi import main
from tests import reset_log, init_log, get_copy, copy_res
from tests.resources import get_resource


class TestReturncode(TestCase):
    """
    Prüft, dass der Return-Code != 0 ist, wenn kein Beweis gefunden wurde
    """

    @classmethod
    def setUpClass(cls):
        init_log(logging.INFO)
        copy_res('returncode')

    @classmethod
    def tearDownClass(cls):
        reset_log()

    def test_fail(self):
        """
        Should fail and thus return code 1
        """
        theory = get_copy('returncode', 'Fail')
        with unittest.mock.patch('sys.argv', ['autosledgi', 'prove', '-s', 'HOL', os.path.abspath(theory)]):
            code = main()
        self.assertEqual(1, code)

    def test_fail_Pll(self):
        """
        Should fail and thus return code 1
        """
        theory = get_copy('returncode', 'Fail_Pll')
        with unittest.mock.patch('sys.argv', ['autosledgi', 'prove', '-s', 'HOL', '-m', os.path.abspath(theory)]):
            code = main()
        self.assertEqual(1, code)
