import time
import asyncio
import json
import logging
import os
import re
from functools import reduce
from json import JSONDecodeError

from autosledgi.isabelle.theory import TheoFile
from events import Events
import psutil

from autosledgi.isabelle.process_parser import IsabelleProcessingStatus
from autosledgi.isabelle.utils import isabelle_command, cygpath, cygpaths
import random, string

log = logging.getLogger(__name__)


class IsabelleServer(Events):

    def __init__(self):
        super().__init__()
        self.__events__ = ("onNOTE", "onOK", "onERROR", "onFINISHED", "onFAILED", "onOUT")
        self.__server_started__ = asyncio.Event()
        self.__server_stopped__ = asyncio.Event()
        self.__error__ = False
        self.__proc__ = None
        self.__listener__ = None

    def __get_random_string__(self, length):
        letters = string.ascii_lowercase
        result_str = ''.join(random.choice(letters) for i in range(length))
        return result_str

    async def start(self):
        """
        Start the Isabelle server
        """
        if self.__proc__ is not None:
            await self.__server_started__.wait()
            return

        self.__server_started__.clear()
        self.__server_stopped__.set()

        server_name = "as_" + self.__get_random_string__(10)
        cmd = isabelle_command(f"isabelle server -c -n {server_name}")

        self.__proc__ = await asyncio.create_subprocess_shell(cmd,
                                                              stdout=asyncio.subprocess.PIPE,
                                                              stderr=asyncio.subprocess.STDOUT,
                                                              stdin=asyncio.subprocess.PIPE)

        self.__listener__ = asyncio.create_task(
            self.__listenToStream__(self.__proc__.stdout)
        )

        await self.__server_started__.wait()

        return not self.__error__

    def write_raw_command(self, command):
        self.__proc__.stdin.write(command.encode("utf-8") + b"\n")
        self.onOUT(command)
        log.debug("[in]: {}".format(command))

    async def __listenToStream__(self, reader):
        output = list()
        data = b''

        while not reader.at_eof() and not self.__listener__.cancelled():
            try:
                while b'\n' not in data:
                    data += await reader.read(1024)
                data_split = data.split(b'\n', 1)
                text = data_split[0].decode("utf-8").rstrip()
                data = data_split[1]

                if text.startswith("OK"):
                    self.__server_started__.set()
                    self.__server_stopped__.set()
                    self.onOK(text[3:] or "{}")

                elif text.startswith("ERROR"):
                    self.onERROR(text[5:])

                elif text.startswith("FINISHED"):
                    self.onFINISHED(text[8:])

                elif text.startswith("FAILED"):
                    self.onFAILED(text[6:])

                elif text.startswith("NOTE"):
                    self.onNOTE(text[4:])

                elif text.startswith('/bin/sh: line 1: isabelle: command not found'):
                    self.__error__ = True
                    self.__server_started__.set()
                    self.__server_stopped__.set()
                    raise FileNotFoundError("Cloud not start isabelle: command not found.")

                if len(text.strip()):
                    self.onOUT(text)
                    output.append(text)
                    log.debug("[out] {}".format(text))

            except RuntimeError:
                pass

            except asyncio.CancelledError:
                self.kill()
                return output

            except JSONDecodeError:
                self.kill()
                return output

            except FileNotFoundError as ex:
                log.error(ex)
                self.kill()
                return output

            except Exception as ex:
                log.error(ex)

        return output

    async def wait_for_close(self):
        await self.__proc__.wait()

    async def shutdown(self):
        self.__server_stopped__.clear()
        self.write_raw_command("shutdown")
        await self.__server_stopped__.wait()
        self.__listener__.cancel()

        self.kill()
        self.__proc__ = None

    def kill(self):
        try:
            parent = psutil.Process(self.__proc__.pid)
            for child in parent.children(recursive=True):
                try:
                    child.kill()
                except:
                    pass

            parent.kill()
            self.__proc__.kill()
        except:
            pass


class IsabelleServerCommand(Events):
    """Base class to construct Isabelle server commands"""

    def __init__(self, command):
        super().__init__(events=("onNOTE", "onFINISHED"))
        self.command = command
        self.taskid = None
        self.start_time = None
        self.end_time = None
        self.finalError = False
        self.finalMsg = dict()
        self.notes = list()

    def __process_note__(self, body):
        note = json.loads(body)
        if type(note) == type(dict()):
            if "task" in note.keys():
                if self.taskid == note["task"]:
                    self.notes.append(note["message"])
                    self.onNOTE(note["message"])
                    return note

        return None

    async def exec(self, server: IsabelleServer):
        """
        Send the command to the specified IsabelleServer
        """
        first_result = asyncio.Event()
        async_result = asyncio.Event()

        def on_result(body, error, sync):
            body = json.loads(body)
            if not isinstance(body, dict):
                body = {"message": body}

            self.finalMsg = body
            self.finalError = error

            if sync:
                if self.taskid:
                    return

                if "task" in body.keys():
                    self.taskid = body["task"]

                self.start_time = time.time()
                first_result.set()
            else:
                if self.taskid == body.get("task"):
                    async_result.set()

        server.onOK += lambda body: on_result(body, error=False, sync=True)
        server.onERROR += lambda body: on_result(body, error=True, sync=True)
        server.onFINISHED += lambda body: on_result(body, error=self.finalError, sync=False)
        server.onFAILED += lambda body: on_result(body, error=True, sync=False)
        server.onNOTE += lambda body: self.__process_note__(body)

        server.write_raw_command(self.command)

        await first_result.wait()

        if "task" not in self.finalMsg.keys():
            self.end_time = time.time()
            self.onFINISHED(self.finalMsg, self.finalError)
            return self.finalMsg, self.finalError

        await async_result.wait()

        self.end_time = time.time()
        self.onFINISHED(self.finalMsg)

        return self.finalMsg, self.finalError

    def get_start_time(self):
        return self.start_time

    def get_execution_time(self):
        if self.end_time:
            return self.end_time - self.start_time

        elif self.start_time:
            return time.time() - self.start_time

        else:
            return 0


class IsabelleServerEcho(IsabelleServerCommand):

    def __init__(self, message):
        super().__init__(f'echo {{"message": "{message}"}}')


class IsabelleServerBuildCommand(IsabelleServerCommand):

    def __init__(self, session, dirs=list(), include_sessions=False, verbose=False, quick_and_dirty=True,
                 kodkod_scala=False, options=list()):
        super().__init__("")

        args = dict()
        args["session"] = session
        args["dirs"] = cygpaths(dirs)
        args["include_session"] = include_sessions
        args["verbose"] = verbose

        options.append(str.lower(f"quick_and_dirty={quick_and_dirty}"))
        options.append(str.lower(f"kodkod_scala={kodkod_scala}"))

        args["options"] = options

        self.command = f"session_build {json.dumps(args)}"


class StartSessionCmd(IsabelleServerCommand):

    def __init__(self, session: str,
                 dirs: list[str] = None,
                 include_sessions: list[str] = None,
                 verbose: bool = None,
                 quick_and_dirty: bool = None):
        args = {'session': session}
        if dirs:
            args["dirs"] = cygpaths(dirs)
        if include_sessions is not None:
            args["include_session"] = include_sessions
        if verbose is not None:
            args["verbose"] = verbose
        if quick_and_dirty is not None:
            args["options"] = [f"quick_and_dirty={str(quick_and_dirty).lower()}"]

        super().__init__(f"session_start {json.dumps(args)}")

    async def exec(self, server):
        ans, error = await super().exec(server)

        if error:
            if "message" in ans.keys():
                msg = ans["message"]
                msg = msg.replace('\"', '"')

                return msg, error
            else:
                return "Unknown error. Please review log.", error
        else:
            return ans["session_id"], error
        

class UseTheoriesCmd(IsabelleServerCommand):
    """Used to Pass a list of Theory files to the server, and then return a
    dictionary of IsabelleProcessingStatus parsers, each representing the 
    processing of one line.

    Constructor Args:
    [theories] (TheoFile):  the theory files to process. Correct parsing only
                            tested/used with a singular file
    session_id (str):       id of an already opened Isabelle server session

    Returns:
    success and parser for each encountered line
    """

    def __init__(self, session_id, theories: list[TheoFile], command: str = "use_theories"):
        super().__init__("")
        self.__events__ = ("onNOTE", "onFINISHED", "onSTATUS")

        self.outputParsers = dict()
        args = dict()
        args["session_id"] = session_id
        args["theories"] = list(map(lambda theory_file: cygpath(theory_file.fpath).replace(".thy", ""), theories))

        self.command = f"{command} {json.dumps(args)}"
        self.cancelled = False

        self.theories = dict()
        self.total_theories = 1

    def __process_note__(self, body):
        note = super().__process_note__(body)
        if not note:
            return

        if "message" in note:
            matches = re.match("Loading ([0-9]+) theories ...", note["message"])
            if matches:
                self.total_theories = int(matches[1])
                log.info(f'Begin processing {self.total_theories} theories')

            if "percentage" in note:
                log.debug(f'Theory {note["theory"]}: {note["percentage"]}%')
                self.theories[note["theory"]] = int(note["percentage"])
                total_percentage_loaded = reduce(lambda result, value: result + value,
                                                 self.theories.values()) / self.total_theories

                log.info(f"Processing theories {str(total_percentage_loaded)}%.. ({self.theories})")

                if total_percentage_loaded >= 100:
                    log.info("Finished processing theories.")

        return note

    async def exec(self, server):
        ans, error = await super().exec(server)
        if self.cancelled:
            return self.outputParsers, False
        if error:
            log.error(ans["message"])
            return self.outputParsers, error

        self.outputParsers = dict()

        for node in ans["nodes"]:
            if "messages" in node:
                messages = node["messages"]

                for msg in messages:

                    msg_text = msg["message"]
                    line = (msg["pos"])["line"]
                    log.debug(f"For line {line} " +
                                  f"following msg was found: {msg_text}")

                    self.__add_message__(line, msg_text)

        return self.outputParsers, error

    def __add_message__(self, line, msg_text):
        if not (line-1) in self.outputParsers:
            self.outputParsers.update({(line-1): \
                                       IsabelleProcessingStatus()})
            log.debug("Added IsabelleProcessingStatus parser "
                + f"for line {line}")

        self.outputParsers[line-1].process(msg_text)


class UseTheoriesStreamCmd(UseTheoriesCmd):

    def __init__(self, session_id, theories: list[TheoFile], watch_lines, accept):
        super().__init__(session_id, theories, command="use_theories_stream")
        self.watch_lines = set(watch_lines)
        self.accept = accept
        self.server = None

    def __process_note__(self, body):
        note = super().__process_note__(body)
        if not note or note.get("kind") != "pide_message" or self.cancelled:
            return note

        self.__add_message__(note["line"], note["message"])

        if self.watch_lines and all(map(self.__accepted__, self.watch_lines)):
            log.info("Good enough proof found, cancelling Sledgehammer.")
            self.cancelled = True
            self.server.write_raw_command(f'cancel {json.dumps({"task": self.taskid})}')

        return note

    def __accepted__(self, line):
        return line in self.outputParsers and any(map(self.accept, self.outputParsers[line].get_proofs()))

    async def exec(self, server):
        self.server = server
        return await super().exec(server)


class IsabelleServerPurgeTheoriesCommand(IsabelleServerCommand):

    def __init__(self, session_id, theories, all=False):
        super().__init__("")

        args = dict()
        args["session_id"] = session_id
        args["theories"] = list(map(lambda theory_file: cygpath(theory_file.fpath).replace(".thy", ""), theories))
        args["all"] = all

        self.command = f"purge_theories {json.dumps(args)}"


class IsabelleServerStopSessionCommand(IsabelleServerCommand):

    def __init__(self, session_id):
        super().__init__(f'session_stop {{"session_id": "{session_id}"}}')
