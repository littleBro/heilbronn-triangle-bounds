"""Produce a reviewable source patch without modifying the pinned manuscript."""
from pathlib import Path
import difflib

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "upstream/manuscript/build/sections/03-norm-digits.tex"
PATCH_PATH = ROOT / "patches/ternary-packing.patch"

OLD_PARAMETERS = r"""T=\binom{M}{3},\qquad k=T^2+1."""
NEW_PARAMETERS = r"""T=\binom{M}{3},\qquad m=\lceil\log_2 T\rceil,\qquad k=3^m."""

OLD_POSITIONS = r"""For $0\le a<T$, designate positions in rows $1,2,3$, respectively, by
\begin{equation}\label{norm:positions}
 i_a=a,\qquad j_a=Ta,\qquad \ell_a=T^2-(T+1)a.
\end{equation}
These positions lie in $\{0,\ldots,k-1\}$ and are distinct within each
row: they lie respectively in the intervals $[0,T-1]$, $[0,T^2-T]$,
and $[1,T^2]$.  The only designated positions whose sum is $k-1$ are
the matched triples:
\begin{equation}\label{norm:matching}
 i_a+j_{a'}+\ell_{a''}=k-1
 \quad\Longleftrightarrow\quad a=a'=a''.
\end{equation}
To prove the forward implication, rewrite the equation as
$a+Ta'=(T+1)a''$.  Reduction modulo $T$, together with
$0\le a,a''<T$, gives $a=a''$; substitution then gives $a'=a''$.
The reverse implication follows from \eqref{norm:positions}."""

NEW_POSITIONS = r"""For $0\le a<T\le2^m$, write the padded binary expansion
$a=\sum_{v=0}^{m-1}\epsilon_v(a)2^v$ with $\epsilon_v(a)\in\{0,1\}$,
and put $u_a=\sum_{v=0}^{m-1}\epsilon_v(a)3^v$.
Designate positions in rows $1,2,3$, respectively, by
\begin{equation}\label{norm:positions}
 i_a=u_a,\qquad j_a=u_a,\qquad \ell_a=k-1-2u_a.
\end{equation}
Since $0\le2u_a\le3^m-1=k-1$, these positions lie in
$\{0,\ldots,k-1\}$.  Uniqueness of base-three expansion makes
$a\mapsto u_a$ injective, so the positions are distinct within each
row; different rows are permitted to use the same position.
The only designated positions whose sum is $k-1$ are the matched triples:
\begin{equation}\label{norm:matching}
 i_a+j_{a'}+\ell_{a''}=k-1
 \quad\Longleftrightarrow\quad a=a'=a''.
\end{equation}
Indeed, the equality is equivalent to $u_a+u_{a'}=2u_{a''}$.
Neither side has carries in base three: at each position it gives
$\epsilon_v(a)+\epsilon_v(a')=2\epsilon_v(a'')$.
All three binary digits are therefore equal at every position, which
implies $a=a'=a''$.  The converse follows by substitution.
In particular $m=384$ and $k=3^{384}$ for the fixed value $d=41$.
All subsequent uses of the positions require only this matching
identity, their range, and their distinctness within each row."""


def main():
    before = SOURCE.read_text(encoding="utf-8")
    assert before.count(OLD_PARAMETERS) == 1
    assert before.count(OLD_POSITIONS) == 1
    after = before.replace(OLD_PARAMETERS, NEW_PARAMETERS).replace(OLD_POSITIONS, NEW_POSITIONS)
    relative_path = "build/sections/03-norm-digits.tex"
    patch = "".join(difflib.unified_diff(
        before.splitlines(keepends=True), after.splitlines(keepends=True),
        fromfile="a/" + relative_path, tofile="b/" + relative_path,
    ))
    PATCH_PATH.parent.mkdir(exist_ok=True)
    PATCH_PATH.write_text(patch, encoding="utf-8", newline="\n")
    print(f"Generated {PATCH_PATH.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
