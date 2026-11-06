#!/usr/bin/env python3
"""mutate.py <file> <occurrence> <old> <new>: replace the <occurrence>-th (1-based) occurrence of the
text <old> in <file> by <new>. Fails if there are fewer occurrences, or if the text is unchanged."""
from pathlib import Path
import re
import sys


def position(text, occurrence, old, new):
    if occurrence < 1 or not old or old == new:
        raise ValueError("invalid occurrence or unchanged/empty mutation")
    pos = -1
    for _ in range(occurrence):
        pos = text.find(old, pos + 1)
        if pos < 0:
            raise ValueError(f"{old!r} occurs fewer than {occurrence} times")
    return pos


def check_lists(root, selected):
    count = 0
    for table in sorted((root / "tests/mutations").glob("*.tsv")):
        if selected and table.stem != selected:
            continue
        for row, line in enumerate(table.read_text().splitlines(), 1):
            if not line or line.startswith("#"):
                continue
            try:
                name, expected, source, occurrence, old, new = line.split("\t")
                if expected not in ("detect", "same"):
                    raise ValueError("unknown expected result")
                text = (root / source).read_text()
                end = re.search(r"^end Zlib\.[A-Za-z0-9_]+[ \t]*$", text, re.M)
                if end:
                    text = text[:end.end()] + "\n"
                position(text, int(occurrence), old, new)
            except (ValueError, OSError) as error:
                raise ValueError(f"{table.name}:{row}: {error}") from error
            count += 1
    if not count:
        raise ValueError("no selected mutations")
    print(f"mutation preflight: {count} cases apply to the translation snapshot")


def main():
    try:
        if len(sys.argv) == 4 and sys.argv[1] == "--check-lists":
            check_lists(Path(sys.argv[2]), sys.argv[3])
        else:
            path, occurrence, old, new = sys.argv[1:]
            source = Path(path)
            text = source.read_text()
            pos = position(text, int(occurrence), old, new)
            source.write_text(text[:pos] + new + text[pos + len(old):])
    except (ValueError, OSError) as error:
        sys.exit(f"mutate: {error}")


if __name__ == "__main__":
    main()
