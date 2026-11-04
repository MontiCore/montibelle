import logging
import re
from enum import Enum

log = logging.getLogger('isabelle.proof')


class PStatus(Enum):
    OK = 1
    TIMEOUT = 2


def is_good_enough(proof: 'Proof') -> bool:
    return proof.get_time() is not None


class Proof:
    """Stores and handles apply/ISAR proofs"""

    def __init__(self, prover: str, proof: str, method: str, time: int, is_done: bool):
        self.prover = prover
        self.method = method
        self.time = time
        self.proof = proof
        self.is_done = is_done if is_done is not None else True if method == 'isar' else False

    def get_time(self):
        """Time in milliseconds to replay the proof"""
        return self.time

    def get_prover(self):
        """Get the prover that found the solution like z3, e or cvc4"""
        return self.prover

    def get_method(self):
        """return the proof mechanism like isar, simp, auto, or metis"""
        return self.method

    def get_proof(self) -> [str]:
        """returns the complete proof in a list of lines"""
        return re.split('\n', self.proof)

    def get_status(self):
        return PStatus.OK if self.time is not None else PStatus.TIMEOUT

    def get_is_done(self):
        """returns true when the proof is done."""
        return self.is_done

    def to_string(self):
        return f'Proof by {self.prover}/{self.method} in Time {self.time} with Status {self.status}:\n {self.proof}'

    def __eq__(self, other):
        return self.time == other.time and self.proof == other.proof and self.prover == other.prover \
               and self.method == other.method and self.is_done == other.is_done

    def __lt__(self, other):
        """
        Defines an order (<) on proofs. Lower being better here, s.t.
        sorted(proofs)[0] is always the best proof. Avoids SMT, prioritizes
        ISAR.
        """
        if not isinstance(other, Proof):
            return True
        elif self.time is not None and other.time is None:
            return True
        elif self.time is None and other.time is not None:
            return False
        elif self.time is None and other.time is None:
            if self.method == 'isar':
                return True
            elif self.method == 'smt':
                return False
            else:
                return other.method != 'isar'
        else:
            if self.method == 'smt':
                return other.method == 'smt' and self.time < other.time
            else:
                return other.method == 'smt' or self.time < other.time

    def __repr__(self):
        return str(self.__dict__)
