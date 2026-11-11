# Original statement and coverage

The original problem asks for the asymptotic maximum f(N) when A is a subset
of the positive integers through N and 1/a = 1/b + 1/c has no solution in
three distinct members of A. It also asks about the proposed value 1/2.
The catalog entry is JSP-000254. Its numerical identifier differs from the
Erdős identifier. [Original source](https://www.erdosproblems.com/302)

| Requirement | Formal meaning and declaration | Coverage |
| --- | --- | --- |
| Positive integer interval | Finset.Icc 1 N, rational reciprocals, pairwise distinct a,b,c in OriginalStatementCheck.NoTriple | Full |
| Exact finite maximum | OriginalStatementCheck.MaxCard uses IsGreatest and is equivalent to Erdos302.IsMaxNoTripleCard | Full |
| Uniform asymptotic density | OriginalStatementCheck.full_density_as_stated covers every function selecting exact maxima for every N | Full |
| Effective specification of C | Erdos302.claimedConstant is the infimum of the finite-prime increment series. fixedPrimeLimit and rational_enclosures identify it through finite quantities | Full |
| Proposed value 1/2 | OriginalStatementCheck.original_half_question_as_stated and Erdos302.claimedConstant_ge_five_eighths | Full |
| Explicit removal estimate | OriginalStatementCheck.full_removal_as_stated for all natural N,V ≥ 4 and all natural K | Full |
| Effective logarithmic rate | OriginalStatementCheck.full_effective_rate_as_stated | Full |
| Arbitrary rational accuracy | Erdos302.rational_enclosures and OriginalStatementCheck.full_rational_enclosures_as_stated | Full |

All finite problem definitions include N=0, whose interval is empty. Asymptotic
statements use the natural numbers tending to infinity. Quantitative formulas
restrict N,V to at least 4, ensuring positive logarithms. K=0 is included.
The exact maximum predicate is a genuine maximum over all admissible subsets.
Its existence and identification with the development's extremal function are
proved. The primitive parametrization requires g,u positive, u<v, and coprime
u,v, and treats all ordered triples after swapping the two summands if needed.

The final density and removal theorems discharge the conditional helper
assumptions. The primitive classification, sieve estimates, exceptional-set
deletion, full dyadic range, and finite-prime limit are in the supplied sources.

## Paper correspondence

The paper's density limit, removal estimate, logarithmic rate, rational
enclosures, and lower construction correspond to the main formal results.
The paper also derives a fixed-prime finite-N error and a double-logarithmic
modulus for f(N)/N. Those two corollaries have mathematical proofs in the paper
and are outside the named formal targets. The formalization supplies the full
original asymptotic problem without those auxiliary corollaries.

The rational-enclosure theorem is an existence theorem using explicitly defined
finite extremal quantities. An extracted executable computing the numerical
constant is outside this submission's formal claim. The paper's exhaustive
finite-optimization description explains the mathematical effective procedure.
