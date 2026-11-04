import os
import tempfile
from unittest import TestCase
from unittest.mock import patch, AsyncMock

from autosledgi import main
from autosledgi.isabelle.client_server import IsabelleServer, StartSessionCmd, UseTheoriesCmd, \
    IsabelleServerStopSessionCommand
from autosledgi.isabelle.process_parser import IsabelleProcessingStatus


class TestArec(TestCase):
    """
    Prüft, dass `autosledgi arec` die Theorie ohne Absturz verarbeitet (#106)
    """

    def setUp(self):
        self.cwd = os.getcwd()
        self.tmp = tempfile.TemporaryDirectory()
        os.chdir(self.tmp.name)
        open('demo_arec.thy', 'w').close()

    def tearDown(self):
        os.chdir(self.cwd)
        self.tmp.cleanup()

    def run_arec(self, *messages):
        parsers = {}
        for line, msg in enumerate(messages):
            parsers[line] = IsabelleProcessingStatus()
            parsers[line].process(msg)

        with patch('sys.argv', ['autosledgi', 'arec']), \
                patch('subprocess.check_output', return_value=b''), \
                patch.object(IsabelleServer, 'start', AsyncMock(return_value=True)), \
                patch.object(IsabelleServer, 'shutdown', AsyncMock()), \
                patch.object(StartSessionCmd, 'exec', AsyncMock(return_value=('id', False))), \
                patch.object(UseTheoriesCmd, 'exec', autospec=True, return_value=(parsers, False)) as use_theories, \
                patch.object(IsabelleServerStopSessionCommand, 'exec', AsyncMock()):
            code = main()
        return code, use_theories.call_args.args[0].command

    def test_no_counterexample(self):
        code, command = self.run_arec('Nitpick found no counterexample', 'val it = false: bool')
        self.assertEqual(code, 0)
        self.assertIn(os.path.abspath('demo_arec'), command)

    def test_counterexample(self):
        code, _ = self.run_arec('Nitpick found a counterexample:', 'val it = true: bool')
        self.assertEqual(code, 1)
