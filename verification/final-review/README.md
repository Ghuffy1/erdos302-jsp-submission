# Final verification passed

The final hosted run checked repository commit 6dad3951fb440de72973277bda68ba189d0f9e09. The selected
mathematical proof remains 1af724ea53a44310c5386062baa22849e6eddafd. All 69 mathematical source, build,
toolchain, lockfile, and verifier files selected for comparison are byte-identical
between those revisions. The later revision adds documentation and evidence.

[Hosted run](https://github.com/Ghuffy1/erdos302-jsp-submission/actions/runs/42989197741)

| Required judgment | Result |
| --- | --- |
| Original statement correspondence | Passed for exact positive-integer distinct-triple maxima, the asymptotic density, and the negative half-density answer |
| Actual execution | Passed on Linux-7.0.0-1019-azure-x86_64-with-glibc2.43 |
| Complete original asymptotic formulation | Covered with an effective finite-optimization specification of the limiting constant |
| Formal proof completeness | Both 372-declaration audits passed with only propext, Classical.choice, and Quot.sound |
| Fresh kernel replay | Passed under the pinned Lean 4.34.0 kernel |
| Source and dependencies | Unchanged sources and all nine locked dependency revisions verified |

## Actual execution

| Step | Exit | Seconds |
| --- | --- | --- |
| lean-version | 0 | 0.623 |
| lake-version | 0 | 0.067 |
| build | 0 | 278.538 |
| statement | 0 | 2.696 |
| solution | 0 | 3.541 |
| rational-enclosures | 0 | 3.733 |
| lower-bound | 0 | 4.083 |
| standalone | 0 | 69.507 |
| modular-axioms | 0 | 3.562 |
| standalone-axioms | 0 | 3.582 |
| expanded-targets | 0 | 3.385 |
| kernel-replay | 0 | 589.811 |

RESULTS.json contains the exact source hashes, dependency checks, commands and
axiom records. Each accompanying log matches its recorded SHA-256. The hosted
run checks the complete source in a fresh Linux runner, using official dependency
caches and the pinned compiler. The earlier Windows checks and documented
dependency-read retries remain in verification/REPORT.md.

The fresh replay uses Lean's own kernel. An independently implemented checker
and independent human mathematical review remain separate review levels.
The named formal targets cover the original asymptotic formulation. The paper's
two supplementary convergence corollaries have written mathematical proofs and
remain outside the named formalization targets. The numerical value of the
limiting density has an effective specification and has not been evaluated here.

## Publication and attribution

The paper passed a new twelve-page visual review, font-embedding check,
author/contact/AI-acknowledgment check, and byte-hash comparison. The repository
history passed a 119-blob sensitive-material scan and Git integrity checks.
The catalog patch was corrected so the attribution row stays inside its table.

Ghuffy1 is the repository owner and primary submitter. Ghuffy1, JENW1N,
H0W4RD-dev, and lkruer retain equal contribution credit. The September
density-limit argument and Cambie construction retain their mathematical credit.
The submission requests formalization review. Organizer acceptance, authorship
and identity confirmation, priority, and any award remain pending.

Final hosted verification completed at 2026-11-11T09:01:29.936234+00:00.
