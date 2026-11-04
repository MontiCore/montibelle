import logging
import time
from unittest import IsolatedAsyncioTestCase, expectedFailure

import asyncio

from autosledgi import prove, SledgehammerParams
from tests import init_log, copy_res, get_result, get_copy, reset_log
from autosledgi.isabelle import TheoFile, theory

class LogPllTestCase(IsolatedAsyncioTestCase):

    @classmethod
    def setUpClass(cls):
        cls.logger = init_log(logging.INFO, 'log_parallel')
        copy_res('log_parallel')

    @classmethod
    def tearDownClass(cls):
        reset_log()
    
    async def test_Log(self):
        import os
        from tests.resources import get_resource
        from difflib import SequenceMatcher

        theory_path = get_copy('log_parallel', 'log_lemmas')
        status = await prove.process([theory_path],
            finder_params=SledgehammerParams(timeout=20),
            parallel_mode=True)
        self.assertTrue(status)

        rel_path = os.path.join('tmp', 'logs', 'log_parallel.log')
        with open(get_resource(rel_path), 'r') as file:
            output = [line.rstrip() for line in file]

        output = [str for str in output if not 'asyncio' in str]

        rel_path = os.path.join('tmp', 'log_parallel', 'expected_log.txt')
        with open(get_resource(rel_path), 'r') as file:
            expected = [line.rstrip() for line in file]

        for i in range(len(output)):
            self.assertRegex(output[i], '[0-9]{2}-[0-9]{2} [0-9]{2}:[0-9]{2} .*')
            output[i] = output[i][12:]

        similarity = 0
        loading_lines = False
        offset = 0
        max_length = max(len(expected), len(output))

        for i in range(len(output)):
            if i-offset >= len(expected): break

            if "Processing theories" in output[i]:
                if loading_lines: offset += 1
                else: loading_lines = True
            else: loading_lines = False

            if "Finished processing theories" in expected[i-offset] \
                and not "Finished processing theories" in output[i]:
                offset -= 1

            cur_sim = \
                SequenceMatcher(None, expected[i-offset], output[i]).ratio()
            similarity += cur_sim/max_length

            if((cur_sim!=1 and not loading_lines) or cur_sim < 0.95):
                self.logger.info(f"{i}: \"{output[i]}\"")
                self.logger.info(f"{i-offset} - expected " +
                    f"({round(cur_sim*100,2)}% similarity): " +
                    f"\"{expected[i-offset]}\"")

        self.logger.info(f'Resulting similarity: {round(similarity*100,2)}%')
        self.assertGreaterEqual(similarity, 0.85)

    def tearDown(self):
        time.sleep(1)
