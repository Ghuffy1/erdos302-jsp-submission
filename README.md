# ErdÅ‘s 302 â€” quantitative removal and full formalization

Will Howe, Grant Huffman, Jensen Kohlmeyer, and Liam Kruer, equal contributors.
Ghuffy1 is the repository owner and primary submission contact.

For the maximum size f(N) of a subset of {1,â€¦,N} avoiding
1/a = 1/b + 1/c in three distinct elements, the development proves the
existence of the density C, gives an effective finite-optimization description
of C, and proves an explicit uniform removal estimate. It also formalizes
Cambie's lower bound C â‰¥ 5/8 and the negative answer to the proposed value 1/2.

The density-limit framework and sieve argument come from the earlier September
manuscript. This submission supplies the accompanying full formal development
and quantitative refinement. Publication novelty and priority remain subject to
review. The numerical value of C has not been evaluated.

- [Mathematical paper](paper/erdos302.pdf)
- [Author and equal-contribution record](AUTHORS.md)
- [Prior work and source attribution](ATTRIBUTION.md)
- [Original statement and coverage](verification/COVERAGE.md)
- [Reproduction instructions](verification/REPRODUCE.md)
- [Final verification](verification/final-review/README.md)
- [Earlier verification evidence](verification/README.md)

## Main results

Let P_V be the primes through 2V. Let F_V(N) retain only forbidden triples
whose primitive coordinates are P_V-smooth, and let U_V be its limiting density.
For N,V â‰¥ 4 and every natural K, the proof gives

```text
0 â‰¤ F_V(N) âˆ’ f(N)
  â‰¤ N [500000 (561/500)^(âˆ’K)
       + 10^23 (20/13)^(3K) ((log V)^(âˆ’7/80) + (log N)^(âˆ’7/80))].

0 â‰¤ U_V âˆ’ C â‰¤ (10^23 + 561000) (log V)^(âˆ’1/140).
```

Each positive rational tolerance admits a finite rational enclosure of C.
The formal result describes the enclosures using finite extremal quantities.
The paper explains their evaluation by exhaustive finite optimization.

## Entry points

| Purpose | File | Declaration |
| --- | --- | --- |
| Original finite problem | Erdos302/Core.lean | NoUnitFractionTriple, IsMaxNoTripleCard |
| Full density theorem | Erdos302/Solution.lean | Erdos302.densityLimit |
| Uniform removal estimate | Erdos302/Solution.lean | Erdos302.removalEstimate |
| Effective approximation | Erdos302/Solution.lean | Erdos302.effectiveApproximation |
| Finite normalized rate | Erdos302/Solution.lean | Erdos302.uniform_finite_removal_rate |
| Rational enclosures | Erdos302/RationalEnclosure.lean | Erdos302.rational_enclosures |
| Cambie lower bound | Erdos302/CambieLowerBound.lean | Erdos302.claimedConstant_ge_five_eighths |
| Literal original-statement checks | verification/StatementCheck.lean | OriginalStatementCheck.full_density_as_stated |
| Self-contained proof | Erdos302Full.lean | All declarations above |

The final statements have no unproved analytic premises. Conditional helper
lemmas expose their assumptions, and the final proofs discharge them.

## Reproduction

The project uses Lean 4.34.0 and a commit-pinned mathlib. From a clean checkout
of the selected proof commit, with the pinned toolchain installed, run

```sh
lake exe cache get
python verification/verify.py
```

The verifier performs a clean-project build when used in a new checkout,
source checks, complete declaration axiom audits, and fresh Lean-kernel replay.
Its report records the actual commands and outcomes. Full instructions explain
the trusted dependency cache and the distinction between a fresh kernel replay
and an independently implemented checker.

## Prize review

The submission is open for review in [JSP PR 5564](https://github.com/TheJustinSunPrize/awards/pull/5564).

This is prepared for JSP-000254, corresponding to ErdÅ‘s problem 302. The full
mathematical argument accompanies the formalization for review. Maintainer
review, identity confirmation, attribution, priority, and award decisions remain
part of the prize process. Each contributor submits any personal claim through
their own account. The latest verification and submission details are recorded in SUBMISSION.json.
