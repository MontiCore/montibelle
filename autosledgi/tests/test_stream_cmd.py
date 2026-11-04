import json
import logging
from types import SimpleNamespace
from unittest import TestCase

from autosledgi.isabelle import UseTheoriesStreamCmd
from autosledgi.isabelle.proof import Proof, is_good_enough
from tests import init_log, reset_log

TASK = "task-1"
theory = SimpleNamespace(fpath="/tmp/Test.thy")
fast = lambda p: p.get_time() is not None and p.get_time() <= 100


class FakeServer:

    def __init__(self):
        self.written = []

    def write_raw_command(self, command):
        self.written.append(command)


def note(line, message, task=TASK, kind="pide_message"):
    return json.dumps({"kind": kind, "task": task, "line": line, "message": message})


class UseTheoriesStreamCmdTest(TestCase):

    @classmethod
    def setUpClass(cls):
        init_log(logging.INFO)

    @classmethod
    def tearDownClass(cls):
        reset_log()

    def make(self, watch_lines, accept=fast):
        cmd = UseTheoriesStreamCmd("session", [theory], watch_lines, accept)
        cmd.taskid = TASK
        cmd.server = FakeServer()
        return cmd

    def cancels(self, cmd):
        return [c for c in cmd.server.written if c.startswith("cancel")]

    def test_command_name(self):
        self.assertTrue(self.make([3]).command.startswith("use_theories_stream "))

    def test_cancels_on_accepted_proof(self):
        cmd = self.make([3])
        cmd.__process_note__(note(4, "Sledgehammering..."))
        self.assertEqual(self.cancels(cmd), [])
        cmd.__process_note__(note(4, "cvc5: Try this: by simp (0.1 ms)"))
        self.assertEqual(self.cancels(cmd), [f'cancel {json.dumps({"task": TASK})}'])
        self.assertTrue(cmd.cancelled)
        self.assertEqual([p.get_proof() for p in cmd.outputParsers[3].get_proofs()], [["by simp"]])

    def test_cancels_only_once(self):
        cmd = self.make([3])
        cmd.__process_note__(note(4, "cvc5: Try this: by simp (0.1 ms)"))
        cmd.__process_note__(note(4, "e: Try this: by auto (0.2 ms)"))
        self.assertEqual(len(self.cancels(cmd)), 1)

    def test_no_cancel_for_rejected_proof(self):
        cmd = self.make([3])
        cmd.__process_note__(note(4, "cvc5: Try this: by (metis foo) (1.2 s)"))
        self.assertEqual(self.cancels(cmd), [])
        self.assertFalse(cmd.cancelled)
        self.assertEqual(len(cmd.outputParsers[3].get_proofs()), 1)

    def test_waits_for_all_watched_lines(self):
        cmd = self.make([3, 7])
        cmd.__process_note__(note(4, "cvc5: Try this: by simp (0.1 ms)"))
        self.assertEqual(self.cancels(cmd), [])
        cmd.__process_note__(note(8, "cvc5: Try this: by auto (0.3 ms)"))
        self.assertEqual(len(self.cancels(cmd)), 1)

    def test_ignores_unwatched_line(self):
        cmd = self.make([3])
        cmd.__process_note__(note(8, "cvc5: Try this: by simp (0.1 ms)"))
        self.assertEqual(self.cancels(cmd), [])

    def test_ignores_other_tasks_and_kinds(self):
        cmd = self.make([3])
        cmd.__process_note__(note(4, "cvc5: Try this: by simp (0.1 ms)", task="task-2"))
        cmd.__process_note__(note(4, "cvc5: Try this: by simp (0.1 ms)", kind="writeln"))
        self.assertEqual(self.cancels(cmd), [])
        self.assertEqual(cmd.outputParsers, {})

    def test_empty_watch_never_cancels(self):
        cmd = self.make([])
        cmd.__process_note__(note(4, "cvc5: Try this: by simp (0.1 ms)"))
        self.assertEqual(self.cancels(cmd), [])

    timed_out = "verit: Try this:\n  by (metis foo\n    bar) (> 1.0 s, timed out)"

    def test_waits_after_timed_out_proof(self):
        cmd = self.make([3], accept=is_good_enough)
        cmd.__process_note__(note(4, self.timed_out))
        self.assertEqual(self.cancels(cmd), [])
        self.assertFalse(cmd.cancelled)
        self.assertEqual(len(cmd.outputParsers[3].get_proofs()), 1)

    def test_cancels_on_preplayed_proof_after_timed_out_one(self):
        cmd = self.make([3], accept=is_good_enough)
        cmd.__process_note__(note(4, self.timed_out))
        cmd.__process_note__(note(4, "cvc5: Try this: by simp (15 ms)"))
        self.assertEqual(len(self.cancels(cmd)), 1)


class IsGoodEnoughTest(TestCase):

    def test_requires_preplay_time(self):
        self.assertTrue(is_good_enough(Proof("e", "by simp", "simp", 15, False)))
        self.assertFalse(is_good_enough(Proof("e", "by simp", "simp", None, False)))
