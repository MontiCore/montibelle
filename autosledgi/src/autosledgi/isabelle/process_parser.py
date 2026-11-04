import re
import logging
from typing import Dict, List

from autosledgi.isabelle.proof import Proof, PStatus


log = logging.getLogger('isabelle.parser')


class IsabelleProcessingStatus:
    """
    Represents the status of a potentially ongoing Isabelle client/server command, i.e., the state of the query.
    Processes results from the command line-by-line and updates its internal state accordingly.
    """

    def __init__(self):
        self.raw_out: List[str] = []
        self.cleaned_out: List[str] = []
        self.proofs: List[Proof] = []

    def __get_apply_script_results__(self, line: str) -> Dict:
        """
        Attempts to find apply script results

        Parameters:
            line (str): the "message" part of Isabelle server response (similar to what a user sees in the jEdit output)
        Returns:
            A dict containing "prover", "apply_proof", "apply_keyword", "apply_method", "apply_time", "apply_unit" if a
             proof was found. keyword is either "by", "apply" or None. If it is None, then the method is also None. If
             the method is present, it should be a prove method, e.g., "simp", "metis", etc. Returns an empty dict if
             not apply-script proof was found.
        """
        proof_regex = r'(?:using\s.*?)?(?P<apply_keyword>by|apply) (?:\()?(?P<apply_method>\w+).*?(\))?'

        time_regex = r'\((?P<apply_time>\d(?:[\d|\.]*)) (?P<apply_unit>\w+)\)'

        apply_regex = r'^(?P<prover>\w+): *Try this:\n? *(?P<apply_proof>' + proof_regex + r'|.*?) *(?:' + time_regex + r'|\(> [\d.]+ \w+, timed out\))?\n*(?:(?:\(No )?Isar proof.*)?$'

        res = re.search(apply_regex, line, re.DOTALL)
        if res is None:
            return {}
        else:
            return res.groupdict()

    def __get_isar_results__(self, line: str) -> Dict:
        """
        Attempts to find ISAR proof results.

        Parameters:
            line (str): the "message" part of Isabelle server response (similar to what a user sees in the jEdit output)
        Returns:
            A dict containing "isar_proof", "isar_time", "isar_unit" if a proof was found. Timing information might be
            None if preplay timed out. Empty dict if no ISAR proof was found.
        """
        time_regex = r'\((?P<isar_time>\d(?:[\d|\.]*)) (?P<isar_unit>\w+)\)'

        isar_regex = r'Isar proof(?: ' + time_regex + r'| \(.*?, timed out\))?:\n(?P<isar_proof>.*?qed)$'

        res = re.search(isar_regex, line, re.DOTALL)
        if res is None:
            return {}
        else:
            return res.groupdict()

    def process(self, line: str) -> None:
        """
        Parses and processes the "message" component of isabelle server responses, specifically those issues in
        response to a use-theories command

        Args:
            line (str)  Output of Isabelle server (line-by-line)
        """
        self.raw_out.append(line)

        if line.startswith("###") or line.startswith("?") or line.startswith("Enter") or line.startswith("Suc"):
            return

        self.cleaned_out.append(line)

        parsed = self.__get_apply_script_results__(line) | self.__get_isar_results__(line)

        for type in ['apply', 'isar']:
            if f'{type}_proof' in parsed:
                if type == 'isar':
                    method = 'isar'
                else:
                    method = parsed[f'{type}_method'] if f'{type}_method' in parsed else None

                time = None
                if f'{type}_time' in parsed and parsed[f'{type}_time'] is not None:
                    if parsed[f'{type}_unit'] == 'ms':
                        factor = 1
                    elif parsed[f'{type}_unit'] == 's':
                        factor = 1000
                    elif parsed[f'{type}_unit'] == 'm':
                        factor = 60*1000
                    elif parsed[f'{type}_unit'] == 'h':
                        factor = 60*60*1000
                    else:
                        log.error(f'Unknown {type} time unit: "{parsed[f"{type}_unit"]}". Skipping this proof.')
                        continue

                    time = int(float(parsed[f'{type}_time']) * factor)

                is_done = f'{type}_keyword' in parsed and parsed[f'{type}_keyword'] == 'by' or type == 'isar'
                prover = parsed['prover'] if 'prover' in parsed else None

                proof = Proof(prover=prover, proof=parsed[f'{type}_proof'], method=method, time=time, is_done=is_done)
                self.proofs.append(proof)

        if line == "done":
            log.info(f"PSL found a proof")

            def is_proof_line(line):
                for keyword in ["by", "apply", "subgoal", "done"]:
                    if line.startswith(keyword):
                        return True
                return False

            self.proofs.append(
                Proof("PSL", "\n".join(list(filter(is_proof_line, self.cleaned_out))), "PSL", 0, PStatus.OK)
            )

    def get_proofs(self):
        """the list of proofs found while parsing"""
        return self.proofs

    def get_raw_out(self):
        """the complete unfiltered output of isabelle process"""
        return "\n".join(self.raw_out)

    def get_cleaned_out(self) -> str:
        """cleaned version of the isabelle process output that removes outlines that are not relevant for parsing"""
        return "\n".join(self.cleaned_out)

    def is_proof_found(self):
        """Returns true if sledgehammer found at least one proof
        Note:
            The proof reconstruction (preplay) might still have failed!
        """
        return len(self.proofs) > 0

    def no_proof_found(self):
        """
        Gibt an, ob 'No proof found' ausgegeben wurde. Leider scheint Isabelle oder Sledgehammer das auch auszugeben,
        wenn ein Proof gefunden wurde. Deswegen gilt: Erst schauen, ob Beweise da sind (is_proof_found).

        Meine aktuelle Theorie lautet, dass der/die gefundene(n) Beweise erfolgreich
        preplayed werden müssen, damit Sledgehammer 'glaubt' einen Proof zu haben. Desweiteren glaube ich, dass ISAR-
        Proofs garnicht zählen.
        """
        return bool(re.search('No proof found', self.get_raw_out()))

    def has_counterexample(self) -> bool:
        """
        Returns is counterexamples were found by nitpick or quickcheck in the
        isabelle-processing log.
        """
        return bool(re.search('(Nitpick|Quickcheck) found a counterexample', self.get_raw_out()))

    def get_counterexample_details(self):
        """
        Returns the details of the counterexample found by quickcheck.
        That is mainly used for logging and disproven markers.
        """
        count_pattern = (
            r"(^(?:Quickcheck|Nitpick)" + re.escape(r" found a counterexample") + ".*"
            + r"((?:\n^ {2,}.*)+))"
        )

        quickcheck_match = (re.compile(count_pattern, re.MULTILINE)
                            .search(self.get_raw_out()))
        if quickcheck_match:
            return quickcheck_match.group(2)

        return None

    def bad_context_occured(self):
        return bool(re.search('(No proof state|Bad context for|empty sequence. no proof found.)', self.get_raw_out()))

    def no_subgoals(self):
        """Return True, if there are no subgoals"""
        return bool(re.search('No subgoal', self.get_raw_out()))

    def arec_passed(self):
        """Return True, if AREC produced viable output"""
        return bool(re.search('val it = false: bool', self.get_raw_out()))

    def get_arec_output(self):
        try:
            return (re.search("(?s)Nitpick.*\\n", self.get_raw_out())).group(0)
        except:
            return self.get_raw_out()
