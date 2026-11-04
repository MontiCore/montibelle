#!/usr/bin/env python
# -*- coding: utf-8 -*-
# pylint: disable=no-member

"""
The python interface for sledgehammer

THIS VERSION IS FOR INTERNAL USE ONLY! DO NOT REDISTRIBUTE!

@author: Jens Christoph Buerger, Pascal Devant, Martin Josmann
"""
import asyncio
import logging
import os
from enum import Enum
from functools import total_ordering
from os.path import exists, abspath, relpath
from typing import List
from time import time

from autosledgi.isabelle import IsabelleServer, TheoFile
from autosledgi.isabelle import StartSessionCmd, UseTheoriesCmd, UseTheoriesStreamCmd, IsabelleServerStopSessionCommand
from autosledgi.isabelle.proof import is_good_enough
from autosledgi.isabelle.utils import SledgehammerParams

logger = logging.getLogger(__name__)


@total_ordering
class Status(Enum):
    """
    Order is important! We use max() to find the most relevant summary when processing multiple annotations.
    Example: 3 annotations, 1 failed, 1 verified, 1 disproven. The most relevant is "disproven". Doesnt matter than 1
    failed outright. Fixing the 1 failing case doesnt change the fact that the overall thing is disproven. Only when all
    work will the result be "VERIFIED".
    """
    VERIFIED = 0
    UNKNOWN = 1
    FAILED = 2
    DISPROVEN = 3

    def __lt__(self, other):
        if self.__class__ is other.__class__:
            return self.value < other.value
        return NotImplemented


def use_theories_cmd(session_id: str, theory: TheoFile, watch_lines: List[int], experimental: bool):
    if experimental:
        return UseTheoriesStreamCmd(session_id, [theory], watch_lines, is_good_enough)
    return UseTheoriesCmd(session_id, [theory])


async def process_annotation(theory_file: TheoFile,
                             server: IsabelleServer,
                             finder_params: SledgehammerParams,
                             session_id: str = "",
                             use_nitpick: bool = False,
                             use_quickcheck: bool = True,
                             experimental: bool = False) -> Status:
    """
    Automatically sledgehammer a theory as good as possible

    Args:
        theory_file (TheoFile): The corresponding theory file object
        server (IsabelleServer): a running isabelle server
        finder_params (SledgehammerParams): Parameters for the proof finder
        session_id (str): The session id from isabelle server
        use_nitpick (bool): If true, run the `nitpick` counter-example search
        use_quickcheck (bool): If true, run the `quickcheck` counter-example search
        parallel_mode (bool): toggles the usage of parallel mode
        experimental (bool): stream sledgehammer results and take the first good enough proof

    Returns:
        Success
    """
    sledge_str: str = finder_params.gen_sledgehammer_cmd()
    sledge_str += ' quickcheck' if use_quickcheck else ''
    sledge_str += ' nitpick' if use_nitpick else ''

    next_line = theory_file.get_next_annotated_line()

    if next_line is None:
        logger.error(f'Erroneously called "{process_annotation.__name__}" again. No more annotations.')
        return Status.FAILED

    result = Status.VERIFIED
    current_goal = 1

    while True:
        logger.debug(f"Injecting line {next_line+1} with '{sledge_str}'")
        next_line = theory_file.insert_finder(next_line, sledge_str)
        theory_file.flush()

        if "sledgehammer" in theory_file.file[next_line - 1]  :
            logger.error("Found more than 1 sledgehammer string for an annotation")
            return Status.FAILED

        isabelle_out, error = await use_theories_cmd(session_id, theory_file, [next_line], experimental).exec(server)

        logger.debug(f"Received the following output from Isabelle: {"{" + \
            ", ".join(f"'{line+1}': " + \
            f"{isabelle_out[line].cleaned_out}" for line in isabelle_out) + "}"}")


        if error:
            logger.error(f'Executing "use_theories" for ${theory_file.fpath} on Isabelle server failed.')
            result = max(result, Status.FAILED)
            break
        
        elif not next_line in isabelle_out:
            logger.error(f"No status found for goal {current_goal},"
                         + f" with line {next_line+1}")
            result = max(result, Status.FAILED)
            break

        elif isabelle_out[next_line].is_proof_found():
            logger.info(f'{len(isabelle_out[next_line].get_proofs())} proof(s)'
                + f' found for goal {current_goal} in line {next_line+1}')
            selected_proof = sorted(isabelle_out[next_line].get_proofs())[0]
            logger.info(f"Chose {selected_proof.get_prover()} proof (time {selected_proof.get_time()}):"
                        + f" {selected_proof.get_proof()}")
            next_annotation = theory_file.insert_proof(next_line, selected_proof.get_proof())

            if selected_proof.get_is_done():
                logger.info('Detected finished proof. Cleaning up.')
                result = max(result, Status.VERIFIED)
                theory_file.deem_finished(next_annotation)
                break
            else:
                logger.info(f"Goal {current_goal} solved. Trying next goal..")
                current_goal += 1
                next_line = next_annotation

        elif isabelle_out[next_line].no_subgoals():
            logger.info(f"There is no subgoal left to solve. Closing proof.")
            next_line = theory_file.insert_proof(next_line, ['  done'])
            theory_file.deem_finished(next_line)
            result = max(result, Status.VERIFIED)
            break

        elif isabelle_out[next_line].bad_context_occured():
            logger.info(f"There is no goal to solve. We are done here.")
            theory_file.strip_bad_context(next_line)
            result = max(result, Status.VERIFIED)
            break

        elif isabelle_out[next_line].has_counterexample():
            logger.info("Counterexample found: ")
            logger.info(isabelle_out[next_line].get_counterexample_details())
            theory_file.mark_disproven(next_line, \
                isabelle_out[next_line].get_counterexample_details())
            result = max(result, Status.DISPROVEN)
            break

        elif isabelle_out[next_line].no_proof_found():
            logger.info(f'No proof found.')
            theory_file.mark_unsuccessfull(next_line)
            result = max(result, Status.UNKNOWN)
            break

        else:
            logger.info(f"Could not find proof in time or provers gave up.")
            theory_file.mark_unsuccessfull(next_line)
            result = max(result, Status.UNKNOWN)
            break

    theory_file.flush()
    return result

class Proof_Processing:
    start_line = current_line = None
    number_of_subgoals = 0
    status = None

    def __init__(self, line: int):
        self.start_line = self.current_line = line

def increase_current_lines(list: List[Proof_Processing], start_line: int, 
                           increase: int):
    """
    Erhoeht das Attribut current_line für alle Proof_Processings, die ab 
    start_line folgen.
        
    Args:
        list (List[Proof_Processing]): die Liste der Proof_Processings
        start_line (int): die erste betrachtete Zeile 
        increase (int): um wie viel die Zeilennummer erhoeht wird
    """
    for proof in list:
        if proof.current_line >= start_line:
            proof.current_line += increase

def get_final_result(list: List[Proof_Processing]) -> Status:
    """
    Bestimmt das insgesamte Ergebnis einer Menge von Proof_Processings.

    Args:
        list (List[Proof_Processing]): die Liste der Proof_Processings

    Returns:
        das Ergebnis als Status
    """
    result = Status.VERIFIED
    for proof in list:
        current_status = proof.status or Status.UNKNOWN
        result = max(current_status, result)
    return result

async def process_annotations_pll(theory: TheoFile,
                              server: IsabelleServer,
                              finder_params: SledgehammerParams,
                              session_id: str,
                              progress_callback=None,
                              use_nitpick: bool = False,
                              use_quickcheck: bool = True,
                              experimental: bool = False) -> Status:
    annotation_lines = theory.get_all_annotated_lines()
    total_annotations = len(annotation_lines)

    max_value_per_annotation = 1.0 / total_annotations
    done = 0.0
    proofs = list[Proof_Processing]()
    for line_num in annotation_lines:
        proofs.append(Proof_Processing(line_num))

    progress = True
    iteration = 0
    while progress:
        iteration += 1
        progress = False

        open_proofs = [proof for proof in proofs if not proof.status]
        if not open_proofs:
            logger.info(f"No lines left to prove.")
            return get_final_result(proofs)
        logger.info(f"Iteration {iteration}:"
            + f" Processing {len(open_proofs)} annotation(s).")
        logger.debug(f"The annotated lines are \
                     {str([proof.current_line+1 for proof in open_proofs])}.")

        sledge_str: str = finder_params.gen_sledgehammer_cmd()
        sledge_str += ' quickcheck' if use_quickcheck else ''
        sledge_str += ' nitpick' if use_nitpick else ''
        offset = 0
        for proof in open_proofs:
            if "sledgehammer" in theory.file[proof.current_line]:
                logger.debug(f"A sledgehammer annotation was already found in \
                             line {proof.current_line+1}")
            else:
                logger.debug(f"Injecting line {proof.current_line+1} with '{sledge_str}'")
                new_line_num=theory.insert_finder(proof.current_line, sledge_str)
                if(new_line_num != proof.current_line - 1): 
                    increase_current_lines(proofs, proof.current_line + 1, 1)
                theory.flush()
                if "sledgehammer" in theory.file[new_line_num - 1]:
                    logger.error("Found more than 1 sledgehammer string for an annotation")
                    return Status.FAILED
            proof.start_line = proof.current_line
        
        multiproofs, error = \
            await use_theories_cmd(session_id, theory,
                                   [proof.start_line for proof in open_proofs],
                                   experimental).exec(server)

        if error:
            logger.error(f'Executing "use_theories" for ${theory.fpath} on Isabelle server failed.')
            return max(Status.FAILED, get_final_result(proofs))
        
        logger.debug(f"Received the following output from Isabelle: {"{" + \
            ", ".join(f"'{line+1}': " + \
            f"{multiproofs[line].cleaned_out}" for line in multiproofs) + "}"}")

        ann_num = 0
        for proof in open_proofs:
            
            if not proof.start_line in multiproofs:
                logger.warning("No status found for annotated line" +
                    f" {proof.start_line+1}, with current line {proof.current_line+1}")
                return Status.FAILED
            isabelle_out = multiproofs[proof.start_line]
            
            ann_num += 1
            logger.info(f'Annotation {ann_num} (' +
                (f'originally line {proof.start_line+1}, now {proof.current_line+1}):'
                if proof.start_line != proof.current_line 
                else f'line {proof.current_line+1}):'))
            logger.debug(f'We read {isabelle_out.raw_out}.')

            iteration_value = 0.5 ** (proof.number_of_subgoals + 1)

            if isabelle_out.is_proof_found():
                progress = True
                logger.info(f"({ann_num}) " + 
                    f"{len(isabelle_out.get_proofs())} proof(s) found.")
                selected_proof = sorted(isabelle_out.get_proofs())[0]
                logger.info(f"({ann_num}) " +
                    f"Chose {selected_proof.get_prover()} proof " +
                    f"(time {selected_proof.get_time()}): " +
                    f"{selected_proof.get_proof()}")
                next_annotation = theory.insert_proof(proof.current_line, 
                                                      selected_proof.get_proof())
                increase_current_lines(proofs, proof.current_line, 
                                       len(selected_proof.get_proof()))
                proof.current_line += 1
                logger.info(f"({ann_num}) Proof for current subgoal inserted.")
                if selected_proof.get_is_done():
                    logger.info(f'({ann_num}) ' +
                        'Detected finished proof. Cleaning up.')
                    if progress_callback:
                        progress_callback(done, max_value_per_annotation * 2 * iteration_value * 100)
                        done += max_value_per_annotation * 2 * iteration_value * 100
                    proof.status = Status.VERIFIED
                    theory.deem_finished(next_annotation)
                else:
                    logger.info(f"({ann_num}) Subgoal solved.")
                    proof.number_of_subgoals += 1
                    if progress_callback:
                        progress_callback(done, max_value_per_annotation * iteration_value * 100)
                        done += max_value_per_annotation * iteration_value * 100

            elif isabelle_out.no_subgoals():
                progress = True
                logger.info(f"({ann_num}) " +
                    "There is no subgoal left to solve. Closing proof.")
                next_line = theory.insert_proof(proof.current_line, ['  done'])
                increase_current_lines(proofs, proof.current_line, 1)
                theory.deem_finished(next_line)
                proof.status = Status.VERIFIED
                if progress_callback:
                    progress_callback(done, max_value_per_annotation * 2 * iteration_value * 100)
                    done += max_value_per_annotation * 2 * iteration_value * 100

            elif isabelle_out.bad_context_occured():
                progress = True
                logger.info(f"({ann_num}) " +
                    "There is no more goals to solve. We are done here.")

                theory.strip_bad_context(proof.current_line)
                proof.status = Status.VERIFIED
                increase_current_lines(proofs, proof.current_line, -1)
                if progress_callback:
                    progress_callback(done, max_value_per_annotation * 2 * iteration_value * 100)
                    done += max_value_per_annotation * 2 * iteration_value * 100

            elif isabelle_out.has_counterexample():
                progress = True
                logger.info(f'({ann_num}) Counterexample found!')
                logger.info("Details: ")
                logger.info(isabelle_out.get_counterexample_details())
                theory.mark_disproven(proof.current_line)
                proof.status = Status.DISPROVEN

                if progress_callback:
                    logger.info(f'Progress: {done:.1f}%')

            elif isabelle_out.no_proof_found():
                logger.info(f'({ann_num}) No proof found.')

                if progress_callback:
                    logger.info(f'Progress: {done:.1f}%')

            else:
                logger.info(f"({ann_num}) " +
                    "Could not find proof in time or provers gave up.")
                theory.mark_unsuccessfull(proof.current_line)
                proof.status = Status.UNKNOWN

                if progress_callback:
                    logger.info(f'Progress: {done:.1f}%')

            theory.flush()
        theory.flush()

    for proof in proofs:
        if not proof.status:
            theory.mark_unsuccessfull(proof.current_line)
            logger.debug(f"Marked line {proof.current_line} as unsuccessful.")
            proof.status = Status.UNKNOWN
    theory.flush()

    logger.warning(f"No progress was made in the last iteration.")
    return get_final_result(proofs)



async def process(theories: List[str] = None,
                  session: str = "HOLCF",
                  session_directories: [str] = None,
                  timeout: int = None,
                  finder_params: SledgehammerParams = None,
                  parallel_mode: bool = False,
                  use_nitpick: bool = False,
                  use_quickcheck: bool = True,
                  experimental: bool = False) -> Status:
    """Process isabelle theories

    Args:
        theories ([str]): Theory files and/or directories containing theory files
        session (str): The session that should be used as a foundation.
        session_directories (string array): Additional session directories
        timeout (int): hard limit per annotation
        finder_params (SledgehammerParams): Parmeters for the sledgehammer command
        parallel_mode (bool): toggles the usage of parallel mode
        use_nitpick (bool): If true, run the `nitpick` counter-example search, default false
        use_quickcheck (bool): If true, run the `quickcheck` counter-example search, default true
        experimental (bool): stream sledgehammer results and take the first good enough proof
    Returns:
        true iff all lemmas in all files were solved
    """

    start_time = time()

    if parallel_mode: logger.info("Parallel mode will be used.")
    if experimental: logger.info("Experimental mode will be used.")

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

    if finder_params is None:
        finder_params = SledgehammerParams()

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
            return Status.UNKNOWN

        start_session = StartSessionCmd(session, session_directories, include_sessions=None, verbose=True,
                                        quick_and_dirty=True)
        start_session.onNOTE += lambda msg: logger.info(msg)
        message, error = await start_session.exec(server)

        res = Status.VERIFIED

        if error:
            logger.error("Session start error.")
            logger.error(message)
        else:
            logger.info("Session started.")
            session_id = message
            steps = 100 / len(to_be_processed)
            logger.info(f'Progress: {0}%')

            for number, theory_path in enumerate(to_be_processed):
                progress = steps * number
                theory = TheoFile(theory_path)
                if theory.get_nr_of_annotated_lines() > 0:
                    logger.info(f'Processing theory {relpath(theory_path)}')
                    tmp = await process_theory(theory,
                                               timeout,
                                               server,
                                               session_id,
                                               (progress, steps),
                                               finder_params=finder_params,
                                               parallel_mode=parallel_mode,
                                               use_nitpick=use_nitpick,
                                               use_quickcheck=use_quickcheck,
                                               experimental=experimental)
                    res = max(res, tmp[0])
                else:
                    logger.debug(f'Skipping theory {relpath(theory_path)} (no annotations)')

            await IsabelleServerStopSessionCommand(session_id).exec(server)

        await server.shutdown()

        logger.info(f'Processing Time: {round(time() - start_time)}s')

        logger.info('Shutting down...')
        await asyncio.sleep(2)

        return res
    else:
        logger.info('Nothing to do here')
        return Status.VERIFIED


async def process_theory(theory: TheoFile,
                         timeout: int,
                         server: IsabelleServer,
                         session_id: str,
                         progress_tuple: (int, int),
                         finder_params: SledgehammerParams,
                         parallel_mode: bool,
                         use_nitpick: bool,
                         use_quickcheck: bool,
                         experimental: bool = False) -> (Status, int):
    """Process a complete theory at once => resolve all autosledgi annotations in that theory

    Args:
        theory (TheoFile):                  the theory containing annotations
        timeout (int):                      hard timeout for each annotation
        server (IsabelleServer):            a running isabelle server
        session_id (str):                   id of the already opened Isabelle server session
        progress_tuple (int, int):          Gibt an wieviel Fortschritt bereits erreicht wurde und wieviel die aktuelle
                                            Theorie beitragen kann. Bei der 3. Theorie von 5 gesamt steht hier zB.
                                            (40,20), da 40% (2/5) bereits erledigt sind und die aktuelle 20% beitragen
                                            soll
        finder_params (SledgehammerParams): parameters for the automatic proof finder
        parallel_mode (bool): toggles the usage of parallel mode
        experimental (bool): stream sledgehammer results and take the first good enough proof
    Returns:
        success and number of annotations encountered
    """
    if parallel_mode:
        base_progress, progress_weight = progress_tuple

        annotation_lines = theory.get_all_annotated_lines()
        annotation_count = len(annotation_lines)

        if annotation_count == 0:
            logger.debug(f"Skipping {theory.fpath} as there is no annotation to solve.")
            return Status.VERIFIED, 0
        
        def progress_callback(done, annotation_progress):
            """Callback for progress updates from parallel processor"""
            overall_progress = base_progress + done + (progress_weight * annotation_progress / 100)
            logger.info(f'Progress: {overall_progress:.1f}%')

        try:
            result = await asyncio.wait_for(
                process_annotations_pll(
                    theory=theory,
                    server=server,
                    finder_params=finder_params,
                    session_id=session_id,
                    progress_callback=progress_callback,
                    use_nitpick=use_nitpick,
                    use_quickcheck=use_quickcheck,
                    experimental=experimental,
                ),
                timeout=timeout
            )

            return result, annotation_count

        except asyncio.TimeoutError:
            logger.warning(f'Processing theory {theory.fpath} timed out')
            return Status.UNKNOWN, annotation_count

    else:
        if theory.get_next_annotated_line() is None:
            logger.debug(f"Skipping {theory.fpath} as there is no annotation to solve.")
            return Status.VERIFIED, 0

        annotated_lines = theory.get_nr_of_annotated_lines()

        proof_success = Status.VERIFIED
        for i in range(annotated_lines):
            logger.info(f'Proving lemma {i + 1}/{annotated_lines}')
            try:
                tmp = await asyncio.wait_for(process_annotation(theory, server, finder_params, session_id,
                                                                use_nitpick=use_nitpick,
                                                                use_quickcheck=use_quickcheck,
                                                                experimental=experimental),
                                            timeout=timeout)
                proof_success = max(proof_success, tmp)
            except TimeoutError:
                logger.warning(f'Proving lemma {i + 1}/{annotated_lines} failed, timeout')
            logger.info(f'Progress: {format(progress_tuple[0] + (progress_tuple[1] / annotated_lines) * (i + 1), ".2f")}%')

        return proof_success, annotated_lines
