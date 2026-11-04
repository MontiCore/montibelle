"""
The python interface for value

currently supports detecting if the output string contains "True"\n  :: "bool".

@author: Fangcheng Zuo
"""
import logging

import asyncio
import os
import re
from os.path import abspath, exists
from typing import List

from autosledgi.isabelle import IsabelleServer, TheoFile, StartSessionCmd, UseTheoriesCmd, \
     IsabelleServerStopSessionCommand

logger = logging.getLogger(__name__)

async def process(theories: List[str] = None,
                  session: str = "HOLCF",
                  session_directories: [str] = None,
                  parallel_mode: bool = False):
    res = []

    if theories is None:
        logger.debug('Defaulting theories to ["."]')
        theories = ['.']
    if isinstance(theories, str):
        logger.warning('Expected a list. Future invocations might break!')
        theories = [theories]
    theories = [abspath(p) for p in theories]

    if session_directories is None:
        if exists(abspath('ROOT')) or exists(abspath('ROOTS')):
            logger.debug('Defaulting session directories to ["."]')
            session_directories = [os.path.abspath('.')]
    else:
        session_directories = [os.path.abspath(p) for p in session_directories]

    to_be_processed = set()
    for path in theories:
        if path.endswith('.thy'):
            to_be_processed.add(path)
        else:
            for dirpath, _, filenames in os.walk(path, onerror=logger.error):
                for filename in filenames:
                    if filename.endswith('.thy'):
                        to_be_processed.add(os.path.join(dirpath, filename))
    logger.debug(f'Gathered all theories: {to_be_processed}')

    if len(to_be_processed) > 0:
        server = IsabelleServer()
        if not await server.start():
            from autosledgi import Status
            return Status.UNKNOWN

        start_session = StartSessionCmd(session, session_directories, include_sessions=None, verbose=True,
                                            quick_and_dirty=True)
        start_session.onNOTE += lambda msg: logger.info(msg)
        message, error = await start_session.exec(server)

        if error:
            logger.error("Session start error.")
            logger.error(message)

            await server.shutdown()
            logger.info('Shutting down...')
            await asyncio.sleep(2)
        else:
            logger.info("Session started.")
            session_id = message

            for theory_path in to_be_processed:
                theory = TheoFile(theory_path)
                use_theories_cmd = UseTheoriesCmd(session_id, [theory])
                result, error = await use_theories_cmd.exec(server)

                if result is None:
                    logger.error("UseTheoriesCmd returned None, unable to proceed.")
                else:
                    tmp_for_logger = ""
                    tmp_for_res = ""
                    for line in result:
                        tmp_for_logger += \
                            result[line].get_cleaned_out() + " "
                        tmp_for_res += result[line].get_raw_out() + " "

                    logger.info(f"{theory_path}: {tmp_for_logger}")
                    res.append(bool(re.search('"True"\n  :: "bool"', tmp_for_res)))

            await IsabelleServerStopSessionCommand(session_id).exec(server)

        await server.shutdown()
        logger.info('Shutting down...')
        await asyncio.sleep(2)

        return all(res)
    else:
        logger.info('Nothing to do here')
