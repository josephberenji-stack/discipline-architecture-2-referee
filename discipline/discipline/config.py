"""config.py -- where the suite looks, and what it skips.  One place, read by every check.

The suite runs over a PROJECT: a directory tree holding computation files, the documents
they cite, and the registers the checks keep.  Nothing in the suite hard-codes where that
tree is.  Every check that needs to know asks this module, and this module answers from
three sources in order:

  1. the environment
       DISCIPLINE_ROOTS     colon-separated project roots to search for cited files
       DISCIPLINE_SPACE     the working space: the directory whose documents rollover
                            watches and whose computation files baseline records
       DISCIPLINE_REGISTERS the directory holding NAMES.md, BASELINE.md, FROZEN.md,
                            PRIMITIVES-REGISTER.md, INDEPENDENT.md, PROJECT-LOG.md
       DISCIPLINE_GLOB      the pattern naming a computation file (default "*.py")
       DISCIPLINE_AUTHOR    the label the project log writes above a verbatim entry
                            (default "Author")
       DISCIPLINE_CITE_PREFIX
                            what a citation path is written relative to, if not the
                            project root itself (default: no prefix)
  2. a marker file `.discipline` in the working space or any directory above the file
     being checked -- the nearest one wins, and its directory is the space
  3. the directory of the file being checked

Directory names in SKIP are never walked by any check.  Add to the list here, in one
place, rather than in a check.
"""
import os
from pathlib import Path

MARKER = ".discipline"

# directories no check walks: tooling, build products, the suite's own code, and the
# canonical primitive texts (which are copied from, never counted as copies)
SKIP = {".git", "__pycache__", ".lake", "build", "node_modules", ".venv", "venv",
        ".DS_Store", "primitives", "discipline"}

# file suffixes the index and the citation check read
INDEXED = (".md", ".py", ".out", ".lean", ".v")


def _env_paths(name):
    v = os.environ.get(name, "")
    return [Path(p).resolve() for p in v.split(os.pathsep) if p]


def space(start=None):
    """The working space: the directory the suite treats as home for this run."""
    if os.environ.get("DISCIPLINE_SPACE"):
        return Path(os.environ["DISCIPLINE_SPACE"]).resolve()
    p = Path(start or ".").resolve()
    for anc in [p] + list(p.parents):
        if (anc / MARKER).exists():
            return anc
    return p if p.is_dir() else p.parent


def roots(start=None):
    """The project roots a citation may resolve into.  Always includes the space."""
    out = _env_paths("DISCIPLINE_ROOTS")
    sp = space(start)
    if sp not in out:
        out.append(sp)
    return out


def registers(start=None):
    """The directory holding the suite's registers."""
    if os.environ.get("DISCIPLINE_REGISTERS"):
        return Path(os.environ["DISCIPLINE_REGISTERS"]).resolve()
    return space(start) / "registers"


def glob_pattern():
    return os.environ.get("DISCIPLINE_GLOB", "*.py")


def author():
    return os.environ.get("DISCIPLINE_AUTHOR", "Author")


def cite_prefix():
    return os.environ.get("DISCIPLINE_CITE_PREFIX", "")


def skipped(path):
    """True if any component of the path is a skipped directory name."""
    return bool(SKIP & set(Path(path).parts))
