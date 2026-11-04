from functools import partial
from unittest import mock

import tests.test_no_proof_found as no_proof_found
import tests.test_parallel as parallel
import tests.test_recursive as recursive
import tests.test_recursive_parallel as recursive_parallel
import tests.test_simple as simple
import tests.test_simple_parallel as simple_parallel
import tests.test_without_lemma_names as without_lemma_names
from autosledgi import prove

process = prove.process


def experimental(test_case):
    class Experimental(test_case):
        async def asyncSetUp(self):
            self.enterContext(mock.patch.object(prove, "process", partial(process, experimental=True)))

    Experimental.__name__ = Experimental.__qualname__ = test_case.__module__.split(".")[-1] + "_" + test_case.__name__ + "Experimental"
    return Experimental


SimpleTestCaseExperimental = experimental(simple.SimpleTestCase)
SimpleTestCasePllExperimental = experimental(simple_parallel.SimpleTestCasePll)
NoProofFoundTestCaseExperimental = experimental(no_proof_found.ParallelTestCase)
ParallelTestCaseExperimental = experimental(parallel.ParallelTestCase)
RecursiveTestCaseExperimental = experimental(recursive.RecursiveTestCase)
RecursiveTestCasePllExperimental = experimental(recursive_parallel.RecursiveTestCasePll)
WithoutNamesTestCaseExperimental = experimental(without_lemma_names.WithoutNamesTestCase)
