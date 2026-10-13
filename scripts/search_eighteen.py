"""Optional bounded exact packing search for T=25*18^6; no optimality claim."""
from pathlib import Path
import json

from search_packing import search, EVEN_DOMAINS, GENERAL_DOMAINS

ROOT = Path(__file__).resolve().parents[1]


def main():
    even = search(25*18**6, 27*23**9, EVEN_DOMAINS, 2)
    winner = even["best_improvement"]
    assert winner["k"] == str(15**7*19**4)
    general = search(25*18**6, int(winner["k"]), GENERAL_DOMAINS, 1)
    report = {"scope": "exact search only in the listed finite families; no global optimality claim",
              "even_alphabet_search": even, "odd_and_even_alphabet_search": general,
              "proof_boundary": "The witness has separate Lean proofs; the search procedure is not formalized."}
    (ROOT/"artifacts/eighteen-search.json").write_text(json.dumps(report, indent=2)+"\n",
                                                      encoding="utf-8", newline="\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
