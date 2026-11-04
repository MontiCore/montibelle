#!/usr/bin/env python
# -*- coding: utf-8 -*-
# pylint: disable=no-member
import argparse
import logging
import os
import asyncio
import sys
from importlib.metadata import version

import autosledgi.cloudsledgi as cloudsledgi
import autosledgi.cloudsledgi.evaluate as evaluate

from autosledgi import arec, prove, hover, test
from autosledgi.isabelle import client_server, TheoFile
from autosledgi.isabelle.utils import configure_home_of_project, revert_home_of_project, SledgehammerParams
from autosledgi.prove import Status


def main() -> int:
    """
    Entrypoint to the application. See pyproject.toml's [project.scripts] table.
    """
    sys.stdout.reconfigure(encoding='utf-8', errors='replace')
    console = logging.StreamHandler(stream=sys.stdout)

    logging.addLevelName(21, 'CLOUD')
    console.addFilter(lambda e: e.levelname != 'CLOUD')

    def add_short_name(record):
        record.short_name = record.name.rsplit('.')[-1]
        return True

    console.addFilter(add_short_name)
    console.setFormatter(logging.Formatter('%(short_name)-10s: %(levelname)-8s %(message)s'))
    logging.getLogger(__name__).addHandler(console)

    parser = argparse.ArgumentParser(
        description='Automatic and unsupervised sledgehammer and PSL operations on Isabelle theories.'
    )

    shared = argparse.ArgumentParser(add_help=False)
    shared.add_argument('theories', nargs='*', default=['.'],
                        help='theories or directories containing theories, defaults to cwd')
    shared.add_argument('-d', '--dir', dest='dirs', metavar='DIR', action='append', default=None,
                        help='session directories (analogous to Isabelle´s `-d` option)')
    shared.add_argument('-s', '--session', metavar='SESSION', default='stream',
                        help='base logic (analogous to Isabelle´s `-l` option)')
    shared.add_argument('-l', '--log', metavar='LOG_FILE', default=None,
                        help='location of log file')
    shared.add_argument('-j', '--project', metavar='PROJECT_HOME', nargs='?', default=None, const='.isabelle',
                        help='define a project-specific directory for buid artifacts')
    shared.add_argument('-c', '--cloud', action='store_true', default=False,
                        help='submit job to cloud instead of doing it locally.')
    shared.add_argument('-v', '--verbose', action='count', default=0,
                        help='increase verbosity')

    subparser = parser.add_subparsers(dest='cmd', required=True)

    prove_parser = subparser.add_parser('prove', parents=[shared],
                                        description='Proof finding')
    prove_parser.add_argument('-p', '--provers', metavar='PROVER', nargs='+', default=None,
                              help='space-separated list of provers for sledgehammer')
    prove_parser.add_argument('-x', '--timeout', type=int, default=None,
                              help='hard limit for sledgehammer operations: kills Isabelle client directly.')
    prove_parser.add_argument('-t', '--prover-timeout', type=int, default=None,
                              help='(soft) limit for sledgehammer operations: value is passed to sledgehammer.')
    prove_parser.add_argument('-m', '--parallel', action='store_true', default = False,
                              help='operate in parallel mode')
    prove_parser.add_argument('--experimental', action='store_true', default=False,
                              help='stream sledgehammer results and take the first good enough proof')
    prove_parser.add_argument('--nitpick', dest='use_nitpick', action=argparse.BooleanOptionalAction, default = False,
                              help='enable/disable Nitpick counterexample search (default: disabled)')
    prove_parser.add_argument('--quickcheck', dest='use_quickcheck', action=argparse.BooleanOptionalAction, default = True,
                              help='enable/disable Quickcheck counterexample search (default: enabled)')

    arec_parser = subparser.add_parser('arec', parents=[shared],
                                       description='Find potential counterexamples for refinements using AREC')
    arec_parser.add_argument('-x', '--timeout', type=int, default=None,
                             help='hard limit for sledgehammer operations: kills Isabelle client directly.')

    build_parser = subparser.add_parser('build', parents=[shared],
                                        description='Build heap images')
    build_parser.add_argument('-g', '--group', action='append', default=['system'],
                              help='select session groups to be included')

    hover_parser = subparser.add_parser('hover', parents=[shared],
                                        description='Constantly rebuild heap images based on file changes')
    hover_parser.add_argument('-g', '--group', action='append', default=['system'],
                              help='select session groups to be included')

    eval_parser = subparser.add_parser('eval', parents=[shared],
                                       description='Cloud evaluation')
    eval_parser.add_argument('--config',
                             help='path to the evaluation config file')

    activate_parser = subparser.add_parser('activate', parents=[shared],
                                           description='Activate a local Isabelle environment')
    deactivate_parser = subparser.add_parser('deactivate', parents=[shared],
                                             description='Activate a local Isabelle environment')

    test_parser = subparser.add_parser('test', parents=[shared],
                                       description='Test if result matches expectation')

    args = parser.parse_args()

    logger = logging.getLogger(__name__)
    logger.setLevel(logging.DEBUG if args.verbose > 0 else logging.INFO)

    asyncio_logger = logging.getLogger('asyncio')
    if args.verbose > 2:
        asyncio_logger.setLevel(logging.DEBUG)
    elif args.verbose > 0:
        asyncio_logger.setLevel(logging.INFO)
    else:
        asyncio_logger.setLevel(logging.WARN)

    if args.log:
        log_file = os.path.abspath(args.log)
        logger.debug(f'Setting up a file logger to {log_file}')
        os.makedirs(os.path.dirname(log_file), exist_ok=True)
        file = logging.FileHandler(filename=log_file, mode='w', encoding='utf-8')
        file.setFormatter(logging.Formatter(fmt='%(asctime)s %(name)-12s %(levelname)-8s %(message)s',
                                            datefmt='%m-%d %H:%M'))
        logger.addHandler(file)

    logger.info(f'This is autosledgi {version("autosledgi")}')
    logger.debug(f'Parsed arguments: {args}')

    if args.cmd == 'activate':
        if not args.project:
            args.project = ".isabelle"

        backup_settings = configure_home_of_project(os.path.abspath(args.project))
        logger.info(f'Activated Isabelle environment at {args.project}, stored backup at {backup_settings}')
        return 0

    if args.cmd == 'deactivate':
        if not args.project:
            args.project = ".isabelle"

        revert_home_of_project()
        logger.info(f'Deactivated Isabelle environment')
        return 0

    if args.cmd == 'eval':
        return evaluate.eval(args)

    if args.cloud:
        return cloudsledgi.redirect_to_cloud(args)

    cloud_source_id = os.environ.get('CLOUD_SOURCE_ID', default=None)
    if cloud_source_id:
        cloudsledgi.pull_source_from_cloud(cloud_source_id)

    if args.project:
        backup_settings = configure_home_of_project(os.path.abspath(args.project))

    if args.cmd == 'build':
        session = hover.Sessions(args.dirs)
        return 0 if session.build(groups=args.group) else 1

    try:
        if args.cmd == 'hover':
            session = hover.Sessions(args.dirs)
            code = 0 if asyncio.run(session.hover(args.session)) else 1

        if args.cmd == 'prove':
            status = asyncio.run(prove.process(theories=args.theories,
                                               session=args.session,
                                               session_directories=args.dirs,
                                               timeout=args.timeout,
                                               finder_params=SledgehammerParams(timeout=args.prover_timeout,
                                                                                provers=args.provers,
                                                                                isar_proofs=True),
                                               parallel_mode=args.parallel,
                                               experimental=args.experimental,
                                               use_nitpick=args.use_nitpick,
                                               use_quickcheck=args.use_quickcheck))
            code = status.value

        if args.cmd == 'arec':
            success = asyncio.run(arec.process(theories=args.theories,
                                               session=args.session,
                                               session_directories=args.dirs))
            if success:
                code = 0
            else:
                code = 1

        if args.cmd == 'test':
            success = asyncio.run(test.process(theories=args.theories,
                                               session=args.session,
                                               session_directories=args.dirs))
            if success:
                code = 0
            else:
                code = 1

    except KeyboardInterrupt:
        logger.warning("Canceled by user")
        code = -2

    except InterruptedError:
        logger.warning("Received sigint")
        code = -3

    if cloud_source_id:
        success = cloudsledgi.push_results_to_cloud(args.theories)
        if success:
            code = 0
        else:
            code = 1

    if args.project:
        revert_home_of_project(backup_settings)

    logger.debug(f'Exiting with code {code}')
    return code
