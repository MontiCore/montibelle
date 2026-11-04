#!/usr/bin/env python
# -*- coding: utf-8 -*-
# pylint: disable=no-member

"""
The python interface for AREC

THIS VERSION IS FOR INTERNAL USE ONLY! DO NOT REDISTRIBUTE!

@author: Martin Josmann
"""
import os
import logging

from autosledgi.isabelle import utils, client_server, TheoFile
from autosledgi.isabelle.client_server import IsabelleServer
from autosledgi.isabelle.process_parser import IsabelleProcessingStatus
from autosledgi.isabelle.utils import cygpath, cygpaths, start, stop

logger = logging.getLogger(__name__)


async def process(theories: [str],
                  session: str,
                  session_directories: [str]) -> bool:
    """Process a AREC theories

            Args:
                theories (string array): Theory files or directories containing theories
                session (str): The session that should be used as a foundation.
                session_directories (string array): Additional session directories
            Returns:
                true iff arec produced viable output
    """
    server = client_server.IsabelleServer()
    await server.start()
    success = True

    for theory_path in theories:
        if theory_path.endswith("arec.thy"):
            success = success and await _process(theory_path,
                                                 session,
                                                 session_directories,
                                                 server)
        else:
            for dirpath, dirnames, filenames in os.walk(theory_path, onerror=logging.getLogger().error):
                for filename in filenames:
                    if filename.endswith("arec.thy"):
                        success = success and await _process(os.path.join(dirpath, filename),
                                                             session,
                                                             session_directories,
                                                             server)
    await server.shutdown()
    return success


async def _process(theory_path: str,
                   session: str,
                   session_directories: [str],
                   server: IsabelleServer) -> bool:
    """Process an AREC theory

            Args:
                theory_path (str): Name of the theory file
                session (str): The session that should be used as a foundation.
                session_directories (string array): Additional session directories
                server (IsabelleServer): a running isabelle server
            Returns:
                true iff arec produced viable output
            """

    logger.info("Starting Batch Processing of Theory %s", theory_path)

    logger.debug("Build session for multipass run")
    timer = start("build Heaps")
    utils.call_isabelle_build_heap(session=session,
                                   session_directories=session_directories)
    stop(timer)

    logger.debug("Calling Isabelle Process on %s (%s)", theory_path, session)

    start_session = client_server.StartSessionCmd(
        session,
        session_directories,
        verbose=False).exec(server)
    session_id, error = await start_session

    if error:
        logger.error("Something bad happened while starting the session. Review logfile for more information.")
        return False

    timer = start("Isabelle Process")

    process_theory = client_server.UseTheoriesCmd(
        session_id,
        [TheoFile(os.path.abspath(theory_path))]
    )

    parsers, error = await process_theory.exec(server)

    isab_out = IsabelleProcessingStatus()
    for line in sorted(parsers):
        for msg in parsers[line].raw_out:
            isab_out.process(msg)

    if error:
        logger.error(isab_out.get_cleaned_out())
        logger.error("Something bad happened while executing Isabelle. Review logfile for more information.")
        return False

    stop_session = client_server.IsabelleServerStopSessionCommand(session_id)
    await stop_session.exec(server)

    logger.info("AREC Output:\n" + isab_out.get_arec_output())
    stop(timer)

    return isab_out.arec_passed()
