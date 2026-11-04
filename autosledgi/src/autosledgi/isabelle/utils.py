#!/usr/bin/env python
# -*- coding: utf-8 -*-
# pylint: disable=no-member

"""Python interface for the theorem prover isabelle

THIS VERSION IS FOR INTERNAL USE ONLY! DO NOT REDISTRIBUTE!

@author: Jens Christoph Buerger, Pascal Devant, Martin Josmann
"""
import shutil
import subprocess
import os
import logging
import platform
import time
from os import path


ISABELLE_CMD = 'isabelle'
REG_AUTOSLEDGI = r'\(\*.*autosledgi.*\*\)'
REG_AUTOPSL_CUSTOM = r'\(\*.*autopsl \[(.+)\].*\*\)'
REG_AUTOPSL_DEFAULT = r'\(\*.*autopsl.*\*\)'
REG_THEORY_NAME = r'theory.* (\S*)'

log = logging.getLogger(__name__)


def cygpath(path: str) -> str:
    import platform
    if platform.system() == "Windows":
        return subprocess.run(["cygpath", "-u", "-a", str(path)], stdout=subprocess.PIPE).stdout.decode('utf-8').replace("\n", "")
    else:
        return path


def cygpaths(paths: list[str]) -> [str]:
    import platform
    if paths is None:
        return None
    if platform.system() == "Windows":
        return [cygpath(path) for path in paths]
    else:
        return paths


def isabelle_command(cmd: str) -> str:
    """Wraps the command in cygwin, if neccessary."""
    if platform.system() == "Windows":
        return "bash --login -c 'cd $(cygpath -u -a \"" + os.getcwd() + "\");" + cmd + "'"
    else:
        return cmd


def os_specific_path(directory: str) -> str:
    if platform.system() == "Windows":
        return "$(cygpath -u \"" + directory + "\")"
    else:
        return directory


def append_if_true(string1: str, condition: bool, string2: str) -> str:
    """Append string2 to string1 if condition is true, else do nothing"""
    if condition:
        return string1 + string2
    else:
        return string1


class SledgehammerParams:
    def __init__(self, timeout: int = None, isar_proofs: bool = None, max_facts: int = None, provers: str = None):
        """
        Args:
            timeout (int):      The timeout for the provers
            isar_proofs (bool): Enable/disable ISAR proofs
            max_facts (int):    Be careful with this! default is smart. Increasing might yield no more proofs!
            provers (str):      list of provers that should be used
        Note:
            None means use the default value
        """
        self.timeout = timeout
        self.isar_proofs = isar_proofs
        self.max_facts = max_facts
        self.provers = provers

    def gen_sledgehammer_cmd(self):
        """Generate the sledgehammer cmd string

        Returns:
            (str): The corresponding sledgehammer command
        """
        options = []
        if self.timeout is not None:
            options.append(f'timeout={self.timeout}')
        if self.isar_proofs is not None:
            options.append(f'isar_proofs={"true" if self.isar_proofs else "false"}')
        if self.max_facts is not None:
            options.append(f'max_facts={self.max_facts}')
        if self.provers is not None:
            options.append(f'provers="{" ".join(self.provers)}"')

        return f'sledgehammer [{", ".join(options)}]'


def call_isabelle_build_heap(session_directories: [str],
                             session: str = None,
                             verbose: bool = True,
                             procs: int = None,
                             groups=None,
                             test_only: bool = False,
                             export: bool = True,
                             quick_and_dirty: bool = True) -> bool:
    """Call the Isabelle build process (Optional: with additional sessions)

    Args:
        session_directories (string array): Additional session directories
        session (str): The session name defined in the ROOT file.
        verbose (bool): Enable the verbosity mode.
        procs (int): Number of simultaneous build processes.
        groups ([str]): select session group NAME.
        test_only (bool): no build -- test dependencies only
        soft_build (bool): only observe changes of sources, not build
        export (bool): export files from session specification into file-system
        quick_and_dirty (bool): set "-o quick_and_dirty=true"
    Returns:
        (str): The raw output from the isabelle build command.

    Throws:
        CalledProcessError: If something went wrong on the Isabelle side
    """
    if groups is None:
        groups = []
    log_session = f' session {session}' if session else ''
    log_groups = f' {"and " if session else ""}groups {groups}' if groups else ''
    log.info(f'Building{log_session}{log_groups} using {session_directories}')
    if not session_directories and not session:
        log.warning('No session directories found. Is this the right path?')
        log.info('Exiting')
        return False
    cmd = f"{ISABELLE_CMD} build"

    for session_directory in session_directories or []:
        if groups == [] and not session:
            cmd += f" -D {os_specific_path(session_directory)}"
        else:
            cmd += f" -d {os_specific_path(session_directory)}"

    if procs is not None and procs > 0:
        cmd += f' -j{procs}'
    cmd = append_if_true(cmd, quick_and_dirty, ' -o quick_and_dirty="true"')
    cmd = append_if_true(cmd, test_only, " -n")
    cmd = append_if_true(cmd, verbose, " -v")
    cmd = append_if_true(cmd, export, " -e")
    cmd = append_if_true(cmd, True, " -b")

    for group in groups:
        cmd = append_if_true(cmd, (group is not None), " -g " + str(group))
    if session:
        cmd += " " + session

    log.debug(f'Command: {cmd}')

    command = isabelle_command(cmd)

    try:
        res = subprocess.check_output(command, shell=True)

    except subprocess.CalledProcessError as error:
        log.error('An error occurred during session building: %s', str(error.output).replace('\\n', '\n'))
        log.info('See log for details')
        return False

    log.info('Finished session building')
    log.debug('Isabelle Build Output: \n' + str(res, "utf-8"))

    return True


class Timer:
    def __init__(self, name):
        self.start_time = time.perf_counter()
        self.name = name


def start(name: str) -> float:
    logging.getLogger("Timing").info(f"{name} started.")
    return Timer(name)


def stop(timer: Timer):
    logging.getLogger("Timing").info(f"{timer.name} took {time.perf_counter() - timer.start_time}s")


def get_roots_refs(dir: str, top_only=False) -> list[str]:
    """ Recursively finds all directories referenced in ROOTS files.

    Args:
        dir (str): The base folder that is searched for ROOTS files and referenced folders.
        top_only (bool): Directories which are already contained in another folder will be ignored.
    Returns:
        List of directories required by Isabelle.
    """

    if not os.path.isdir(dir):
        raise NotADirectoryError(dir + " is supposed to be a directory.")

    dir = os.path.abspath(dir)
    root_file = os.path.join(dir, "ROOT")
    dirs = []

    if os.path.exists(root_file):
        dirs = [dir]

    roots_file = os.path.join(dir, "ROOTS")
    if os.path.exists(roots_file):
        with open(roots_file, encoding='utf-8') as f:
            for line in f.readlines():
                line = line.strip()
                if not os.path.isabs(line):
                    line = os.path.abspath(os.path.join(dir, line))

                if os.path.exists(line):
                    dirs.extend(get_roots_refs(line, top_only=top_only))
                else:
                    logging.getLogger('').warning("Found non existing reference '" + line + "' in '" + roots_file + "'")

    if top_only:
        def has_prefix_in_list(x: str, xs: list[str]):
            xs.remove(x)
            return x.startswith(tuple(xs))

        dirs = list(filter(lambda d: not has_prefix_in_list(d, dirs.copy()), dirs))

    dirs = list(dict.fromkeys(dirs))

    return dirs


def get_isabelle_env(name):
    proc = subprocess.run(isabelle_command(f"isabelle getenv {name}"), capture_output=True, shell=True, text=True, encoding='utf-8')
    return proc.stdout.split('=', -1)[1].strip("\n").strip()


def to_shell_path(p: str) -> str:
    """
    Converts slashes to appropriate form (forward on unix vs backward on windows) and replaces "/cygwin/c/"-prefix.

    Background:
        Isabelle may run in a cygwin environment and thus its `getenv` command returns cygwin paths. i.e., paths
        starting with `/cygdrive/c/...`). Autosledgi on the other hand may run in a different shell, hence its paths do
        not start with `/cygdrive/c/`. If Autosledgi is not running inside cygwin, this function replaces the cgywin
        prefix with a general `/`.

    Args:
        p (str): The path to convert.
    """
    if "/cygdrive/" in p and "cygwin" not in platform.system().lower():
        return path.normpath(p.replace("/cygdrive/c/", "/"))
    else:
        return path.normpath(p)


def configure_home_of_project(project_home: str) -> str:
    """
    Configures Isabelle to use the provided directory as base for build artifacts. Heap images will be stored in a
    subfolder called "heaps", rendered browser information in "browser_information". Creates a backup of the settings
    file.

    Args:
        project_home (str): The base location for project-specific build artifacts. An extension to Isabelle's existing
                            ISABELLE_HOME and ISABELLE_HOME_USER.
    Returns:
        the location of the backup settings file
    """
    log.info(f'Setting project home to {project_home}')
    user_home = to_shell_path(get_isabelle_env("ISABELLE_HOME_USER"))

    os.makedirs(project_home, exist_ok=True)
    os.makedirs(path.join(user_home, "etc/"), exist_ok=True)

    settings = path.join(user_home, 'etc', 'settings')

    if not os.path.exists(settings):
        open(settings, "w").close()

    backup = shutil.copy(settings, path.join(user_home, 'etc', 'settings.original'))
    log.debug(f'Created settings backup in {backup}')

    cyg_project_home = cygpath(project_home)
    log.info(f'Writing {cyg_project_home} to {settings}')

    with open(settings, "a", newline='\n') as f:
        f.write(f"\nISABELLE_HEAPS={cyg_project_home}/heaps")
        f.write(f"\nISABELLE_BROWSER_INFO={cyg_project_home}/browser_info")

    return backup


def revert_home_of_project(backup: str = None) -> None:
    """
    Reverts Isabelle settings back to the original.

    Args:
        backup (str): The location of the backed-up settings file
    """
    if(backup is None):
        log.debug('No file path provided for reverting, determining default...')
        user_home = to_shell_path(get_isabelle_env("ISABELLE_HOME_USER"))
        backup = path.join(user_home, 'etc', 'settings.original')

    log.info(f'Reverting settings from {backup}')
    if os.path.exists(backup):
        settings = path.join(to_shell_path(get_isabelle_env("ISABELLE_HOME_USER")), 'etc', 'settings')
        os.remove(settings)
        shutil.move(backup, settings)
