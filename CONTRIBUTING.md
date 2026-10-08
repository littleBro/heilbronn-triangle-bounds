# Contributing and mathematical review

Corrections, independent reproduction and stronger conditional exponents are
welcome. Start with [the review guide](docs/review.md) and identify the exact
claim, inequality, theorem name or file that your contribution addresses.

For an improvement, give the exact integer or rational parameters, the proof of
the affected steps, and all downstream changes needed by the geometric argument.
Update the certificate generator, independent checker, Lean statements and note
where applicable. Supply a patch against the original pinned manuscript.
Keep the saved files under upstream/ unchanged and preserve earlier witnesses.

Run the complete local verification:

    python scripts/verify_all.py

Commit regenerated certificates and patches together with their sources.
Verification reports record the environment in which they ran. A numerical
example or a successful finite test does not prove a general mathematical claim.
If a new argument is only written, say so; if it relies on an upstream estimate,
identify that estimate.

Tests should exercise a mathematical identity, a producer invariant or a failure
mode. Include the expected failure for any negative control and distinguish
failure of a sufficient bound from impossibility of the construction.
Proofs must not add unchecked assumptions or omitted proof terms.

Keep the current result and its scope consistent across the README, certificate,
Lean theorem and note. Retain attribution to the original manuscript, classical
constructions and prior contributions; disclose substantial AI assistance.
Submissions are intended for inclusion under the repository's Apache-2.0 license.
Independent review and attribution corrections are welcome.
