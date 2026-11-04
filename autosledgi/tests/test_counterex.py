import logging
import os
import unittest
from unittest import TestCase
from unittest.mock import patch

from autosledgi import main, Status
from tests import reset_log, init_log, get_copy, copy_res
from tests.resources import get_resource


class TestCounterex(TestCase):
    """
    Prüft Gegenbeispielfindung
    """

    @classmethod
    def setUpClass(cls):
        copy_res('counterex')

    @classmethod
    def tearDownClass(cls):
        reset_log()

    def test_Status(self):
        """
        Tests the class (enum) "Status" and its ordering
        """
        self.assertGreater(Status.UNKNOWN, Status.VERIFIED, 'Anything goes wrong, the system cannot be verified')
        self.assertGreater(Status.FAILED, Status.UNKNOWN, 'A fail contains more information then unknown status')
        self.assertGreater(Status.DISPROVEN, Status.FAILED, 'A single counterexample is more important than failures')

    def test_fail(self):
        """
        Should fail and thus return code 1
        """
        theory = get_copy('counterex', 'Counter')
        with unittest.mock.patch('sys.argv', ['autosledgi', 'prove', '-s', 'HOL', os.path.abspath(theory)]):
            code = main()
        self.assertEqual(3, code)

    def test_fail_Pll(self):
        """
        Should fail and thus return code 1
        """
        theory = get_copy('counterex', 'Counter_Pll')
        with unittest.mock.patch('sys.argv', ['autosledgi', 'prove', '-s', 'HOL', '-m', os.path.abspath(theory)]):
            code = main()
        self.assertEqual(3, code)
