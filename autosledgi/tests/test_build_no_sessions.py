import os
import tempfile
from unittest import TestCase
from unittest.mock import patch

from autosledgi import main


class TestBuildNoSessions(TestCase):
    """
    Prüft, dass `autosledgi build` ohne Sessions sauber abbricht (#91)
    """

    def setUp(self):
        self.cwd = os.getcwd()
        self.tmp = tempfile.TemporaryDirectory()
        os.chdir(self.tmp.name)

    def tearDown(self):
        os.chdir(self.cwd)
        self.tmp.cleanup()

    @patch('subprocess.check_output')
    def test_no_root(self, check_output):
        with patch('sys.argv', ['autosledgi', 'build']), self.assertLogs(level='WARNING') as logs:
            code = main()
        self.assertEqual(code, 1)
        check_output.assert_not_called()
        self.assertIn('No session directories found. Is this the right path?', logs.output[0])

    @patch('subprocess.check_output', return_value=b'')
    def test_root_in_cwd(self, check_output):
        open('ROOT', 'w').close()
        with patch('sys.argv', ['autosledgi', 'build']):
            code = main()
        self.assertEqual(code, 0)
        self.assertIn(f'-d {os.path.abspath(".")}', check_output.call_args.args[0])

    @patch('subprocess.check_output')
    def test_hover_no_root(self, check_output):
        with patch('sys.argv', ['autosledgi', 'hover']), self.assertLogs(level='WARNING') as logs:
            code = main()
        self.assertEqual(code, 1)
        check_output.assert_not_called()
        self.assertIn('No session directories found. Is this the right path?', logs.output[0])
