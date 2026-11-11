## Submission type

- [ ] Mathematical solver information
- [x] Lean proof or formalization author information

This submission requests review of the complete formalization of Erdős 302.
The mathematical solution is supplied with the formalization and credited to its
prior sources. The accompanying paper develops the quantitative refinement.
The requested award role is Lean formalization. Original mathematical priority
is reserved for the earlier published work identified below.

## Problem

- The problem is JSP-000254, corresponding to Erdős problem 302.
- The original source is Erdős and Graham, *Old and New Problems and Results in
  Combinatorial Number Theory* (1980), p. 37, as recorded on the problem page.
- The proposal records a complete density-limit formalization, an effective
  specification of the limiting constant, and the known negative half-density
  answer. It also provides the explicit quantitative estimates.
- Related prize PRs are #301, #395, #2368, #3083, and #5077. PRs #301 and #395
  concern the known lower bound and half-density question. PR #5077 explicitly
  withdraws its full-scope claim. PRs #2368 and #3083 contain partial or mismapped
  source references. This submission includes the complete density-limit proof.
- No related claim issue was found in the November 11, 2026 query for this JSP ID.

[Original problem](https://www.erdosproblems.com/302)
[Catalog base](https://github.com/TheJustinSunPrize/awards/blob/f8801a856529dce27e738c6b305e46d76e7c387c/problems/catalog-0201-0300.md#JSP-000254)

## Formal statement

The earlier complete density-limit argument is the September 26, 2026 companion
manuscript, Sections 2–6 and Appendix B, with a dated arXiv version from
October 2, 2026. The submitted paper supplies a self-contained mathematical
argument and quantitative refinement. Mathematical review by the prize
maintainers is requested and remains pending.

[Earlier mathematical solution](https://github.com/uclanlp/continual-graph-memory/blob/23367c6568c344d9c4dbf59be3f39b39f5d54324/results/erdos_302.md)
[ArXiv version 1](https://arxiv.org/abs/2610.02945v1)
[Submitted mathematical paper](https://github.com/Ghuffy1/erdos302-jsp-submission/blob/1af724ea53a44310c5386062baa22849e6eddafd/paper/erdos302.pdf)

The formal statements are in verification/StatementCheck.lean. The principal
targets are OriginalStatementCheck.full_density_as_stated and
OriginalStatementCheck.original_half_question_as_stated. The first quantifies
over every function selecting the greatest size of an admissible subset of
{1,…,N}. Admissibility uses rational reciprocals and all three distinctness
conditions. The limiting constant is given by the finite-prime increment series
and infimum, with arbitrary-width rational enclosures. The second excludes the
value 1/2 using Cambie's 5/8 construction. The statement is proposed for review
against the original source and the fixed Formal Conjectures statement.

[Statement and bridges](https://github.com/Ghuffy1/erdos302-jsp-submission/blob/1af724ea53a44310c5386062baa22849e6eddafd/verification/StatementCheck.lean)
[Coverage matrix](https://github.com/Ghuffy1/erdos302-jsp-submission/blob/1af724ea53a44310c5386062baa22849e6eddafd/verification/COVERAGE.md)

## Proof submission

```json
[{
  "repository": "https://github.com/Ghuffy1/erdos302-jsp-submission",
  "branch": "main",
  "commit": "1af724ea53a44310c5386062baa22849e6eddafd"
}]
```

The primary submission account and repository owner is Ghuffy1. The proof entry
is Erdos302/Solution.lean, with Erdos302.densityLimit, Erdos302.removalEstimate,
and Erdos302.effectiveApproximation. Erdos302/RationalEnclosure.lean establishes
the rational enclosures. Erdos302/CambieLowerBound.lean establishes the known
lower construction. Erdos302Full.lean contains the complete combined source.
All final hypotheses are discharged in these sources.

[Proof entry](https://github.com/Ghuffy1/erdos302-jsp-submission/blob/1af724ea53a44310c5386062baa22849e6eddafd/Erdos302/Solution.lean)
[Self-contained source](https://github.com/Ghuffy1/erdos302-jsp-submission/blob/1af724ea53a44310c5386062baa22849e6eddafd/Erdos302Full.lean)

## Reproduction

Lean is pinned to leanprover/lean4:v4.34.0. mathlib is pinned to
5ed2965256430c3649e86755f9576b54eca72435. lake-manifest.json pins all nine
dependencies. From a fresh checkout of the selected commit, run

```sh
lake exe cache get
python verification/verify.py
```

The verifier checks the dependency revisions, performs the project build,
checks the main source files and original-statement bridges, audits all 372
public theorem and lemma declarations in both source forms, prints expanded
main targets, and runs a fresh kernel replay of verification.StatementCheck.
The observed axioms and actual results accompany the verification report.

[Reproduction instructions](https://github.com/Ghuffy1/erdos302-jsp-submission/blob/c2b36876636bec89ffd2dd420ec101adf1bcb6e9/verification/REPRODUCE.md)
[Axiom audit](https://github.com/Ghuffy1/erdos302-jsp-submission/blob/1af724ea53a44310c5386062baa22849e6eddafd/verification/CurrentAudit.lean)

## Final pre-submission verification

The final hosted check passed for repository commit 6dad3951fb440de72973277bda68ba189d0f9e09, whose 69 proof,
build, toolchain, dependency-lock and verifier files are identical to the selected
mathematical proof at 1af724ea53a44310c5386062baa22849e6eddafd. It completed a fresh Linux build, all explicit
source and statement checks, both 372-declaration axiom audits, and a fresh
replay by the pinned Lean 4.34.0 kernel. All twelve execution steps returned exit 0.
All tracked sources and all nine dependency revisions were unchanged afterward.
Only propext, Classical.choice and Quot.sound appeared in the axiom audits.

[Successful hosted run](https://github.com/Ghuffy1/erdos302-jsp-submission/actions/runs/42989197741)
[Final report and raw evidence](https://github.com/Ghuffy1/erdos302-jsp-submission/blob/82fb20ccb8ec1fcaf48fac4b79d89656849a765a/verification/final-review/README.md)
[Machine-readable results](https://github.com/Ghuffy1/erdos302-jsp-submission/blob/82fb20ccb8ec1fcaf48fac4b79d89656849a765a/verification/final-review/RESULTS.json)

The earlier Windows verification is retained with its documented dependency-read
retries. The fresh replay uses Lean's own kernel. Independent human review and
an independently implemented external checker are outstanding. The paper's two
supplementary convergence corollaries have written proofs and lie outside the
named formal targets. The original asymptotic formulation is covered. Its limiting
constant has an effective finite-optimization specification, with no claimed
numerical decimal evaluation.

## Attribution

Will Howe (H0W4RD-dev), Grant Huffman (Ghuffy1), Jensen Kohlmeyer (JENW1N), and
Liam Kruer (lkruer) are equal contributors to the team's submitted work.
Ghuffy1 is the primary submitter and repository owner. Personal confirmations
of identity and contribution remain part of the prize review.

The September manuscript receives credit for the density-limit framework and
sieve. Stijn Cambie receives credit for the lower construction. The Formal
Conjectures Authors receive credit for the adapted finite predicates.
ChatGPT (OpenAI) provided substantial assistance in development and checking.
No independent human verifier is claimed. The team has a shared professional
relationship as coauthors. Further personal conflict disclosures remain each
applicant's responsibility.

[Authorship record](https://github.com/Ghuffy1/erdos302-jsp-submission/blob/c2b36876636bec89ffd2dd420ec101adf1bcb6e9/AUTHORS.md)
[Detailed attribution](https://github.com/Ghuffy1/erdos302-jsp-submission/blob/c2b36876636bec89ffd2dd420ec101adf1bcb6e9/ATTRIBUTION.md)

## Submission checklist

- [x] The catalog patch changes the permitted status, proof and source-attribution fields.
- [x] The submitted source covers the complete original asymptotic problem and the half-density question.
- [x] The mathematical solution and prior attribution accompany the formalization.
- [x] Ghuffy1 submits the team's own formalization from the original owner repository, with all co-contributors and prior sources credited.
- [x] The awards patch contains catalog text and references only.

External acceptance, attribution, identity, priority, and award decisions remain
subject to the official process.
