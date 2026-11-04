import json
import time


class GoalStatistics:

    def __init__(self, id, found):
        self.id = id
        self.found = found
        self.proofs = []
        self.total_goals = 0

    def add_all_proofs(self, proofs):
        for proof in proofs:
            proof_entry = dict()
            proof_entry["prover"] = proof.get_prover()
            proof_entry["method"] = proof.get_method()
            proof_entry["status"] = str(proof.get_status())
            proof_entry["text"] = proof.get_proof()
            proof_entry["reconstructionTime"] = proof.get_time()
            self.proofs.append(proof_entry)


class LemmaStatistics:

    def __init__(self):
        self.goals = []

    def add_success(self, id) -> GoalStatistics:
        goal = GoalStatistics(id, found=True)
        self.goals.append(goal)
        return goal

    def start(self):
        self.start_time = time.perf_counter()

    def stop(self):
        self.total_execution_time = time.perf_counter() - self.start_time

    def set_solved(self, solved: bool):
        self.solved = solved


class TheoryStatistics:

    lemmas = []

    def add_lemma(self, lemma):
        if not self.lemmas:
            self.lemmas = []

        self.lemmas = self.lemmas.append(lemma)

    def start(self):
        self.start_time = time.perf_counter()

    def stop(self):
        self.total_execution_time = time.perf_counter() - self.start_time

    def dump(self, log_location):
        with open(log_location + "/statistics.json", 'w', encoding='utf-8') as f:
            res = json.dumps(self, default=lambda o: o.__dict__,
                             sort_keys=True, indent=4)
            json.dump(res, f, ensure_ascii=False, indent=4)

    def count_solved_lemmas(self):
        return len(list(filter(lambda x: x["solved"], self.lemmas)))

    def count_lemmas(self):
        return len(self.lemmas)
