#!/usr/bin/env python

"""
HOVER watches a set of sessions and keeps their build images up to date

Author: Mathias Pfeiffer (mpfeiffer@se-rwth.de), Pascal Devant
"""
import asyncio
import logging
import os
import time

from watchgod import awatch, DefaultDirWatcher
import autosledgi.isabelle.utils as utils


class Sessions:
    """Representing sessions to be built"""

    def __init__(self, locations):
        """
        Parameters
        ----------
        locations: str[]
            location (absolute or relative poths) of sessions (i.e., ROOT files)
        """
        if locations is None and (os.path.exists('ROOT') or os.path.exists('ROOTS')):
            locations = [os.path.abspath('.')]
        self.locations = locations
        self.last_change = 0
        self.log = logging.getLogger("autosledgi.sessions")

    def build(self, target: str = None, groups: [str] = None):
        """Builds the sessions up to and including a target session.

        Parameters
        ----------
        target: str
            Session to build up to (and including)
        groups: [str]
            Session groups to include in the build

        Returns
        -------
        Success: bool
            When the build succeeded without errors, true. Otherwise, false.
        """
        if groups is None:
            groups = []

        self.log.info(f"Building sessions in {self.locations}{f' up to and including {target}' if target else ''}")

        success = utils.call_isabelle_build_heap(session=target,
                                                 groups=groups,
                                                 session_directories=self.locations)

        self.log.info(f'{"Succeeded" if success else "Failed"} building sessions in {self.locations} up to and'
                      f' including {target}')

        return success

    def check(self, target):
        """Checks whether the target session and all its descendants are up-to-date

        Parameters
        ----------
        target: str
            Session to check for (and all descendants)

        Returns
        -------
        state: bool
            True if up-to-date. False if the session or any of its descendants need rebuilding.
        """

        success = utils.call_isabelle_build_heap(session=target,
                                                 session_directories=self.locations)

        self.log.info(
            f"Testing sessions returned {success}. -> Sessions are {'up-to-date' if success else 'out-of-date'}")

        return success

    async def hover(self, target, reset_time=15):
        """ Hovers on a session. If file changes occure, the target session is rebuilt.

        Parameters
        ----------
        target: str
            Session to hover on (and all descendants)

        reset_time: number
            Time to wait for additional changes. If a change occurs during this time, the reset time will be reset.

        """
        if not self.locations:
            self.log.warning('No session directories found. Is this the right path?')
            self.log.info('Exiting')
            return False

        self.log.info("Starting hover on " + target)
        self.log.info("Starting initial build..")
        self.build(target)

        try:
            self.lock = asyncio.Lock()

            async def handle_file_change():
                watched_change = time.time()
                self.last_change = watched_change

                await asyncio.sleep(reset_time)

                if self.last_change != watched_change:
                    self.log.debug("Change overwritten -> Skip")
                    return

                self.log.info("Last Change: " + str(self.last_change), " Monitored Changed: " + str(watched_change))

                if self.last_change != watched_change:
                    self.log.debug("Build timer was reset by new file change.")
                    return

                if self.lock.locked():
                    self.log.debug("Already building -> Skip")
                    return

                await self.lock.acquire()

                try:
                    self.log.info(f'Checking for updates in {self.locations}')
                    if not self.check(target):
                        self.log.info("Sessions are not up-to-date. Building...")
                        self.build(target)
                finally:
                    self.lock.release()

            for location in self.locations:
                async for change in awatch(path=location, normal_sleep=0, min_sleep=5, watcher_cls=IsabelleWatcher):
                    self.log.debug(change)
                    asyncio.run_coroutine_threadsafe(handle_file_change(), loop=asyncio.get_event_loop())

        except KeyboardInterrupt:
            self.log.info("Hovering stopped by user")

        return True


class IsabelleWatcher(DefaultDirWatcher):
    def should_watch_file(self, entry: 'os.DirEntry[str]') -> bool:
        if entry.name.endswith('.thy'):
            return True
        elif entry.name == 'ROOTS' or entry.name == 'ROOT':
            return True

        return False
