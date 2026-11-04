import re

from typing import List
from autosledgi.isabelle.utils import REG_AUTOSLEDGI, REG_AUTOPSL_DEFAULT, REG_THEORY_NAME

def read_to_list(fpath):
    """Read a file into a list, each line is a new list element

    Args:
        fpath: The file path.

    Returns:
        A list containing each line
    """
    str_list = []
    with open(fpath, encoding='utf-8') as file:
        for rawline in file:
            line = rawline.rstrip('\n')
            str_list.append(line)
    return str_list


def write_list(str_list, fpath):
    """Write a string list to a file, each list element is put in a new Line

    Args:
        str_list (list of str): The string list that should be written.
        fpath (str): The file path where the list should be placed.
    """
    with open(fpath, 'w', encoding='utf-8') as fp:
        l1 = map(lambda x: x + '\n', str_list)
        fp.writelines(l1)


class TheoFile:
    """Class that represents theory files"""

    def __init__(self, fpath: str):
        """Opens and closes the file, stores its contents in a list"""
        self.fpath = fpath
        self.file = read_to_list(fpath)

    def get_next_annotated_line(self):
        for i, line in enumerate(self.file):
            if bool(re.search(REG_AUTOSLEDGI, line)) or bool(re.search(REG_AUTOPSL_DEFAULT, line)):
                return i
        return None

    def get_nr_of_annotated_lines(self):
        """Count annotations"""
        res = 0
        for i, line in enumerate(self.file):
            if bool(re.search(REG_AUTOSLEDGI, line)) or bool(re.search(REG_AUTOPSL_DEFAULT, line)):
                res = res+1
        return res
    
    def get_all_annotated_lines(self) -> List[int]:
        """Get all line numbers with autosledgi annotations"""
        lines = []
        for i, line in enumerate(self.file):
            if (re.search(REG_AUTOSLEDGI, line) or
                re.search(REG_AUTOPSL_DEFAULT, line)):
                lines.append(i)
        return lines

    def get_line(self, line: int):
        """get specific line of the file"""
        return self.file[line]

    def insert_finder(self, line: int, finder: str) -> int :
        """
        Inserts the provided proof finder into the desired line. Will never override lines. Instead, the line is
          pushed to line+1.
        Parameters:
            line    (int):      The line index. 0 denotes the very first line, len(file)-1 the last.
            finder  (str):      The proof finder ("sledgehammer [...]", PSL's "find_proof ...", etc.)
        """
        assert line >= 0
        assert line < len(self.file)
        before = len(self.file)

        if "sledgehammer" in self.file[line - 1] :
            return line - 1

        self.file[line:line] = [finder]

        assert len(self.file) == before + 1
        return line

    def insert_proof(self, line: int, proof: [str]) -> int:
        """
        Inserts the proof into the desired line. Does override the line.
        Parameters:
            line    (int):      The line index. 0 denotes the very first line, len(file)-1 the last.
            proof   ([str]):    the proof (["by simp"], ["apply ...", "apply ...", "done"], ...)
        Returns
            The line index of the annotation, that was moved back by inserting the proof.
        """
        assert line >= 0
        assert line < len(self.file)
        before = len(self.file)

        proof[0:0] = ["  (* Inserted automatically *)"]
        self.file[line:line+1] = proof

        assert len(self.file) == before+len(proof)-1
        return line + len(proof)

    def deem_finished(self, line: int):
        """
        Deems a proof finished. Removes trailing annotations, and inserts a comment saying as much.

        Parameters:
            line    (int):      The line index. 0 denotes the very first line, len(file)-1 the last.
        """
        assert line >= 0
        assert line < len(self.file)
        before = len(self.file)
        assert re.search(REG_AUTOSLEDGI, self.file[line])

        self.file[line:line+1] = ["  (* We are done here *)"]

        assert len(self.file) == before

    def mark_unsuccessfull(self, line: int):
        """
        Replaces finder and following annotation with sorry and comment saying we failed
        """
        assert line >= 0
        assert line+1 < len(self.file)
        before = len(self.file)
        assert re.search(REG_AUTOSLEDGI, self.file[line+1])

        self.file[line:line + 2] = ["  (* Sorry, could not find a proof automatically *)", "  sorry"]

        assert len(self.file) == before

    def mark_disproven(self, line: int, details=""):
        """
        Replaces finder and following annotation with oops and comment saying we failed.
        Effectively reduces the file length by one line.

        Parameters:
            line    (int): Line index where is finder was inserted in the .thy file
            details (str): Optional details about the disproof.
        """
        assert line >= 0
        assert line + 1 < len(self.file)
        assert re.search(REG_AUTOSLEDGI, self.file[line + 1])

        line_count_before = len(self.file)

        details = re.sub(pattern=r"\\<up>\\<(.*?)> ", repl=r"⟨\<\1>⟩ ", string=details)

        for expression, subst in [(r"\<Zcat> \<epsilon>", ""),
                                  ("\n", " "),
                                  ("  ", " "),
                                  (r"\<up>", "↑"),
                                  (r"\<surd>", "√"),
                                  (r"\<Zcat>", "⌒"),
                                  (r"\<epsilon>", "ε")]:
            details = details.replace(expression, subst)

        self.file[line:line + 2] = [f"  (* Disproven! Counterexample:{details} *)",
                                    "  oops"]
        self.flush()

        assert len(self.file) == line_count_before

    def strip_bad_context(self, line: int):
        """
        Deems a proof finished: removes finder, removes the trailing annotation, and inserts a "Done" comment.
        Effectively reduces file length by one line.
        Finder and annotation line is substituted by single line: (* we are ... *).

        Parameters:
            line    (int):  The line index of finder which is to be substituted.
                            Here 0 denotes the very first line, len(file)-1 the last.
        """
        assert line >= 0
        assert line+1 < len(self.file)
        before = len(self.file)
        assert re.search(REG_AUTOSLEDGI, self.file[line+1])

        self.file[line:line+2] = ["  (* We are done here *)"]

        assert len(self.file) == before-1

    def flush(self):
        """Writes the internal representation, i.e., the buffer, back to the original file"""
        write_list(self.file, self.fpath)
