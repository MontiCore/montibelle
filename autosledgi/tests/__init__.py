from logging import Logger


def setup_modulepath():
    """
    Sets the module path. This is neccessary, since unittest, our testing framework, is not (yet) able to read and
    unserstand the pyproject.toml-file and thus doesn't know where to find the main autosledgi module (hint: in 'src/').
    One could prepend the PYTHONPATH variable everytime he ran the tests through CLI:
    > PYHTONPATH=src python -m unittest
    But since this is very tedious...
    """
    import pathlib, os, sys

    root_dir = pathlib.Path(__file__).parent.parent.resolve()
    src_dir = os.path.join(os.path.abspath(root_dir), 'src')
    sys.path.append(os.path.normpath(src_dir))


def init_log(level=None, basename: str = None) -> Logger:
    """Initialize the log

    Args:
        level: CRITICAL = 50, FATAL=CRITICAL, ERROR = 40, WARNING = 30, WARN=WARNING, INFO = 20, DEBUG = 10, NOTSET = 0
    """
    import logging
    import sys
    import os
    from tests.resources import get_resource

    if level is None:
        level = logging.INFO

    console = logging.StreamHandler(stream=sys.stdout)

    def add_short_name(record):
        record.short_name = record.name.rsplit('.')[-1]
        return True

    console.addFilter(add_short_name)
    console.setFormatter(logging.Formatter(fmt='%(asctime)s %(short_name)-10s %(levelname)-8s %(message)s', datefmt='%m-%d %H:%M'))

    logger = logging.getLogger()
    logger.addHandler(console)
    logger.setLevel(level)

    if not basename is None:
        log_file = get_resource(os.path.join('tmp', 'logs', basename + '.log'))
        logger.debug(f'Setting up a file logger to {log_file}')
        os.makedirs(os.path.dirname(log_file), exist_ok=True)
        file = logging.FileHandler(filename=log_file, mode='w')
        file.setFormatter(logging.Formatter(
            fmt='%(asctime)s %(name)-12s %(levelname)-8s %(message)s',
            datefmt='%m-%d %H:%M'))
        logger.addHandler(file)

    return logger


def reset_log() -> None:
    """Removes all handlers as they seem to be shared between multiple test classes"""
    import logging
    logger = logging.getLogger()
    while logger.hasHandlers():
        logger.handlers[0].close()
        logger.removeHandler(logger.handlers[0])


def copy_res(basename: str):
    """Copies resources to a temporary location"""
    import os, shutil
    from tests.resources import get_resource

    src_dir = get_resource(basename)
    target_dir = get_resource(os.path.join('tmp', basename))
    if os.path.isdir(target_dir):
        shutil.rmtree(target_dir)
    shutil.copytree(src_dir,
                    target_dir,
                    ignore=lambda _, names: filter(lambda x: x.endswith('_expected.thy'), names))


def get_copy(dir: str, basename: str = None) -> str:
    """Determines location of the copied theory specified by a base directory and a file name. If no basename is
        specified, the location of the directory is returned instead.

    Args:
        dir         (str): A single directory name
        basename    (str): Theory file's basename, i.e., without '.thy'

    Returns:
         str: The location of the temporary file or folder to operate on, previously copied by copy_res
    """
    import os
    from tests.resources import get_resource

    if basename is None:
        return get_resource(os.path.join('tmp', dir))
    else:
        return get_resource(os.path.join('tmp', dir, f'{basename}.thy'))


def get_result(basename: str, file: str) -> (str, str):
    """
    Reads both expected and actual results

    Returns
        A tuple of expected and actual result (in this order) as strings
    """
    import os
    from tests.resources import get_resource

    with open(get_resource(os.path.join('tmp', basename, f'{file}.thy'))) as actual:
        with open(get_resource(os.path.join(basename, f'{file}_expected.thy'))) as expected:
            return expected.read(), actual.read()


