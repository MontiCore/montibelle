import logging
from os import path
from unittest import TestCase

from tests import init_log, reset_log, setup_modulepath


class TestUtils(TestCase):

    @classmethod
    def setUpClass(cls):
        cls.log = init_log(logging.INFO)

    @classmethod
    def tearDownClass(cls):
        reset_log()

    def test_to_shell_path(self):
        from autosledgi.isabelle.utils import to_shell_path
        t = to_shell_path("/cygdrive/c/Users/myuser/.isabelle/Isabelle2023/etc/settings")
        expected = path.normpath("/Users/myuser/.isabelle/Isabelle2023/etc/settings")
        self.assertEqual(t, expected)
