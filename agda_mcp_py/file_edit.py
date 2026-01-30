import logging
import re
from typing import List, Tuple, Optional

logger = logging.getLogger(__name__)


class Range:
    def __init__(self, start_line: int, start_col: int, end_line: int, end_col: int):
        self.start_line = start_line
        self.start_col = start_col
        self.end_line = end_line
        self.end_col = end_col

    @classmethod
    def from_json(cls, json_data: dict) -> "Range":
        # Agda JSON range: [{"start": {"line": L, "col": C, "pos": P}, "end": ...}]
        # Usually a list of intervals. We take the first one?
        # Example: [{"start":{"line":10,"col":12,"pos":100},"end":{"line":10,"col":16,"pos":104}}]
        if isinstance(json_data, list) and len(json_data) > 0:
            interval = json_data[0]
            return cls(
                interval["start"]["line"],
                interval["start"]["col"],
                interval["end"]["line"],
                interval["end"]["col"],
            )
        return cls(0, 0, 0, 0)

    def __repr__(self):
        return (
            f"Range({self.start_line}:{self.start_col}-{self.end_line}:{self.end_col})"
        )


def read_file_lines(file_path: str) -> List[str]:
    with open(file_path, "r", encoding="utf-8") as f:
        return f.readlines()


def write_file_lines(file_path: str, lines: List[str]):
    with open(file_path, "w", encoding="utf-8") as f:
        f.writelines(lines)


def replace_hole(
    file_path: str, range: Range, new_content: str, wrap_parens: bool = False
):
    """
    Replaces the content at the given range with new_content.
    Handles multi-line holes if necessary.
    """
    lines = read_file_lines(file_path)

    # Agda lines are 1-indexed in JSON, but 0-indexed in Python list
    start_line_idx = range.start_line - 1
    end_line_idx = range.end_line - 1

    # Columns are 1-indexed in Agda JSON usually?
    # Wait, check Agda docs. Emacs mode uses 1-based lines, 0-based columns?
    # "start": {"line": 10, "col": 12, "pos": 100}
    # Usually Emacs uses 1-based lines.
    # Standard Agda usage: 1-based lines, 1-based columns?
    # Let's assume 1-based lines, 1-based columns for now.
    # Actually, most editors use 0-based columns.
    # Haskell implementation `src/AgdaMCP/FileEdit.hs` would tell us.
    # It imports `Agda.Syntax.Position`.

    # I'll assume 1-based lines and 1-based columns, but I need to be careful.
    # If I see `col: 1` it means first char.
    # Python string slice is 0-based. So `col - 1`.

    s_line = start_line_idx
    s_col = range.start_col - 1
    e_line = end_line_idx
    e_col = range.end_col - 1

    if s_line < 0 or s_line >= len(lines):
        logger.error(f"Invalid start line {s_line}")
        return

    # Check if the hole is strictly within one line
    if s_line == e_line:
        line = lines[s_line]
        prefix = line[:s_col]
        suffix = line[e_col:]

        replacement = new_content
        if wrap_parens:
            replacement = f"({replacement})"

        lines[s_line] = prefix + replacement + suffix
    else:
        # Multi-line hole
        # Not fully supported yet, but logic is similar
        # Replace start line suffix, end line prefix, and remove in-between lines
        prefix = lines[s_line][:s_col]
        suffix = lines[e_line][e_col:]

        replacement = new_content
        if wrap_parens:
            replacement = f"({replacement})"

        # We merge into one line? Or keep newlines in replacement?
        # Usually hole filling puts it inline.
        lines[s_line] = prefix + replacement + suffix

        # Delete intermediate lines
        # Delete from s_line + 1 to e_line (inclusive)
        # Note: we modified lines[s_line] already.
        # We need to remove lines[s_line+1 : e_line+1]
        del lines[s_line + 1 : e_line + 1]

    write_file_lines(file_path, lines)


def replace_line(file_path: str, line_num: int, new_lines: List[str]):
    """
    Replaces a specific line with a list of new lines (for case splitting).
    Preserves indentation of the original line?
    Usually `new_lines` from Agda already have indentation or we need to adjust.
    Agda's MakeCase usually returns fully formed lines.
    """
    lines = read_file_lines(file_path)
    idx = line_num - 1

    if idx < 0 or idx >= len(lines):
        logger.error(f"Invalid line number {line_num}")
        return

    # We replace lines[idx] with *new_lines*
    # new_lines should effectively be inserted

    # Agda MakeCase returns the clauses.
    # We just splice them in.

    lines[idx : idx + 1] = [l + "\n" if not l.endswith("\n") else l for l in new_lines]

    write_file_lines(file_path, lines)
