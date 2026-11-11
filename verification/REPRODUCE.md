# Reproducing the selected proof

Use the full proof commit in SUBMISSION.json and the main branch of
https://github.com/Ghuffy1/erdos302-jsp-submission. Check that the selected commit
is an ancestor of main before reviewing it. A later evidence commit can add
reports while the selected mathematical version stays fixed.

## Environment

Install the official Elan toolchain manager and the version in lean-toolchain,
leanprover/lean4:v4.34.0. Python 3.10 or newer runs the verification helper.
The theorem prover is Lean. The helper only orchestrates commands, records
exit codes, checks hashes, and parses declaration audit output.

Clone into a fresh directory and check out the selected proof commit. Obtain
dependencies with the checked-in Lake lockfile and retrieve mathlib's cache.

```sh
git clone https://github.com/Ghuffy1/erdos302-jsp-submission.git
cd erdos302-jsp-submission
git checkout 1af724ea53a44310c5386062baa22849e6eddafd
lake exe cache get
python verification/verify.py
```

The checkout command selects the exact proof revision checked in the report.
The later evidence commit records that version in SUBMISSION.json.
Dependency acquisition may require network access. The verifier checks that
every actual dependency HEAD matches lake-manifest.json and has no tracked
changes. A fresh directory ensures project artifacts start empty. Dependency
caches remain a disclosed trust input, and fresh kernel replay checks imported
declarations using the pinned Lean kernel.

## Commands performed

```sh
lake build
lake env lean verification/StatementCheck.lean
lake env lean Erdos302/Solution.lean
lake env lean Erdos302/RationalEnclosure.lean
lake env lean Erdos302/CambieLowerBound.lean
lake env lean Erdos302Full.lean
lake env lean verification/CurrentAudit.lean
lake env lean verification/FullAudit.lean
lake env lean verification/ExpandedTargets.lean
lake env leanchecker --fresh --verbose verification.StatementCheck
```

All expected declarations must appear in both axiom audits. The accepted
foundation axioms are propext, Classical.choice, and Quot.sound. Missing
declarations, extra axioms, changed source, dependency mismatches, and nonzero
exit codes make the helper fail. Commands execute as argument arrays.

Pass --output PATH to choose a new evidence directory. Pass --lake PATH for a
trusted Lake executable. The verifier records unmodified output in that directory
and a separate machine-readable receipt. It clears inherited Lean search-path
overrides and uses process-local LEAN_NUM_THREADS=1. It changes no global setting.

The original-problem statement challenge was independently written against
positive integer intervals and rational reciprocals. Its bridge theorems are
checked. Fresh replay uses Lean's own kernel. Verification with an independently
implemented checker and independent human mathematical review are outstanding.

The supplied local check uses a dedicated checkout and an empty project build
directory with revision-checked dependency caches. It is host execution of the
team's reviewed sources. A hardened container or VM isolation audit is a separate
review level. The optional JSP workflow has additional isolation guidance.
