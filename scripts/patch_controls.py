"""Check actual patched TeX references without compiling another document."""
from collections import Counter
from pathlib import Path
import re
import tempfile

from verify import require, run_checked

ROOT = Path(__file__).resolve().parents[1]


def reference_errors(text):
    labels = Counter(re.findall(r"\\label\{([^}]+)\}", text))
    refs = set(re.findall(r"\\(?:ref|eqref|pageref|autoref)\{([^}]+)\}", text))
    return sorted(refs-labels.keys()), sorted(k for k, n in labels.items() if n > 1)


def check_patch_references(patch):
    parent = ROOT/".lake/patch-reference-checks"
    parent.mkdir(parents=True, exist_ok=True)
    target = Path(tempfile.mkdtemp(prefix="manuscript-", dir=parent))
    # Keep these small ignored text snapshots available for local review.
    for source in (ROOT/"upstream/manuscript").rglob("*.tex"):
        destination = target/source.relative_to(ROOT/"upstream/manuscript")
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(source.read_bytes())
    run_checked(["git", "apply", "--directory="+target.relative_to(ROOT).as_posix(), str(ROOT/patch)])
    text = "\n".join(p.read_text(encoding="utf-8") for p in sorted(target.rglob("*.tex")))
    missing, duplicate = reference_errors(text)
    require(not missing and not duplicate, "patched manuscript references: "+str((missing, duplicate)))
    label = r"\label{norm:matching}"
    require(text.count(label) == 1, "matching label is unique")
    broken, _ = reference_errors(text.replace(label, "", 1))
    require(broken == ["norm:matching"], "missing matching label negative control")
    return {"patch": patch, "tex_files": len(list(target.rglob("*.tex"))),
            "reference_labels_checked": len(set(re.findall(r"\\(?:ref|eqref|pageref|autoref)\{([^}]+)\}", text))),
            "missing_labels": missing, "duplicate_labels": duplicate,
            "removed_matching_label_rejected": True}
