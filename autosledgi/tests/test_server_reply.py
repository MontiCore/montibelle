import asyncio
import json
import logging
from types import SimpleNamespace
from unittest import IsolatedAsyncioTestCase

from events import Events

from autosledgi.isabelle import UseTheoriesCmd
from autosledgi.isabelle.client_server import IsabelleServerCommand
from tests import init_log, reset_log


class FakeServer(Events):

    def __init__(self, error_body):
        super().__init__()
        self.__events__ = ("onNOTE", "onOK", "onERROR", "onFINISHED", "onFAILED")
        self.error_body = error_body

    def write_raw_command(self, command):
        asyncio.get_running_loop().call_soon(self.onERROR, json.dumps(self.error_body))


class ServerReplyTest(IsolatedAsyncioTestCase):

    @classmethod
    def setUpClass(cls):
        init_log(logging.INFO)

    @classmethod
    def tearDownClass(cls):
        reset_log()

    async def test_error_with_plain_message(self):
        ans, error = await asyncio.wait_for(IsabelleServerCommand("unknown {}").exec(FakeServer("Bad command")), 1)
        self.assertTrue(error)
        self.assertEqual(ans, {"message": "Bad command"})

    async def test_error_with_object(self):
        ans, error = await asyncio.wait_for(IsabelleServerCommand("unknown {}").exec(FakeServer({"message": "Bad"})), 1)
        self.assertTrue(error)
        self.assertEqual(ans, {"message": "Bad"})

    async def test_use_theories_fails_on_unknown_command(self):
        cmd = UseTheoriesCmd("session", [SimpleNamespace(fpath="/tmp/Test.thy")], command="use_theories_stream")
        parsers, error = await asyncio.wait_for(cmd.exec(FakeServer('Bad command "use_theories_stream"')), 1)
        self.assertTrue(error)
        self.assertEqual(parsers, {})
