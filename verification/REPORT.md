# Verification passed

The selected proof commit 1af724ea53a44310c5386062baa22849e6eddafd covers the original asymptotic density
question for distinct reciprocal triples and the proposed value 1/2. Its
unmodified clean-source build sequence, explicit source checks, complete declaration axiom
audits, and fresh Lean-kernel replay passed. The full scope is described below.

| Required judgment | Result | Evidence |
| --- | --- | --- |
| Does the proof address the specified original problem? | Yes | Original positive-integer interval, rational reciprocals, all distinctness conditions, exact maxima and arbitrary N are preserved in StatementCheck.lean |
| Did the selected commit pass verification? | Yes | Every command in the execution table returned exit 0. Input hashes and dependency revisions were unchanged |
| Does it fully resolve the original asymptotic formulation? | Yes, with C specified by finite-prime optimization and arbitrary-width rational enclosures | densityLimit, rational_enclosures and the negative half-density theorem |
| Does it meet the mathematical and Lean completeness checks applied here? | Meets | Full original-statement bridges, discharged analytic hypotheses, and standard axioms only |

This judgment concerns the identified mathematical and formal scope. The prize
organizers retain responsibility for acceptance, identity, attribution, priority,
and award decisions.

## Pinned sources

The source repository is https://github.com/Ghuffy1/erdos302-jsp-submission, branch main. The selected proof commit is
1af724ea53a44310c5386062baa22849e6eddafd. The enclosing evidence commit adds this report and its logs after
verification. The precise evidence revision is supplied in the submission draft.

The official rules snapshot is f8801a856529dce27e738c6b305e46d76e7c387c.
The problem is JSP-000254, corresponding to Erdős problem 302. There is no
submitted awards PR at this private-preparation stage. The complete original
problem page was retrieved on November 11, 2026, and the Formal Conjectures
statement was inspected at 2f91d251c07fbbaf9435166d47c11e884a08a6cf.

[Original problem](https://www.erdosproblems.com/302)
[Fixed formal statement](https://github.com/google-deepmind/formal-conjectures/blob/2f91d251c07fbbaf9435166d47c11e884a08a6cf/FormalConjectures/ErdosProblems/302.lean)
[Selected proof](https://github.com/Ghuffy1/erdos302-jsp-submission/tree/1af724ea53a44310c5386062baa22849e6eddafd)

## Mathematical correspondence

For each N, the exact maximum is taken over all subsets of {1,…,N} with no
three pairwise distinct elements a,b,c satisfying 1/a = 1/b + 1/c. Reciprocals
are rational. The independent restatement uses IsGreatest and checks equivalence
with the supplied maximum predicate. The density theorem quantifies over every
function selecting these exact maxima. Zero and the empty interval are allowed
in the finite definitions, while quantitative estimates use N,V ≥ 4.

The proof classifies all primitive triples as
(guv, gu(u+v), gv(u+v)), with g,u positive, u<v and coprime u,v. The smooth/rough
decomposition supplies the fixed-prime series. The exceptional-set estimate,
finite sieve and dyadic count prove the unconditional removal estimate. The
limiting constant is the infimum of finite-prime values, and the explicit rate
gives rational enclosures of every positive rational width. The known Cambie
construction proves C ≥ 5/8 and excludes C=1/2.

The fully expanded main declarations were checked in ExpandedTargets.lean.
The final theorems discharge the assumptions exposed by conditional helper
lemmas. COVERAGE.md maps the individual original requirements to declarations.
Both forms of the source audit cover all 372 public theorem and lemma declarations.

The constant has an effective finite-optimization specification. Its numerical
decimal has not been evaluated. The paper's extra fixed-prime finite-size
bound and double-logarithmic convergence corollary have written proofs and
lie outside the named formal targets. The rational-enclosure formalization is
an existence theorem over finite extremal quantities. An extracted executable
for evaluating the density is outside its stated claim.

## Environment and execution

The observed platform is Windows-10-10.0.19045-SP0, AMD64. Lean is pinned to
leanprover/lean4:v4.34.0. The compiler reports source commit
293d5d0c0c3f3dded4688b3ccd6a33939ac5102b. The dedicated build sequence started
with an empty project build directory. A transient dependency-read failure
required a same-source retry, which reused successfully checked objects from
that attempt. Both attempts and their identical source hashes are recorded.
Every dependency was checked out at its locked
revision in a dedicated directory. The official cache tool obtained matching
dependency artifacts. Its preparation log is included.

The environment uses a dedicated local host checkout. It clears inherited Lean
search-path overrides and sets LEAN_NUM_THREADS=1 for its own processes.
Hardened container or VM isolation was outside this execution. The complete
optional JSP isolated-workflow claim is therefore not made. The supplied
method follows the published verification evidence requirements and reports
its actual trust boundaries.

| Step | Exit code | Seconds | Evidence |
| --- | --- | --- | --- |
| lean-version | 0 | 2.484 | [log](evidence/lean-version.log) |
| lake-version | 0 | 0.062 | [log](evidence/lake-version.log) |
| build | 0 | 735.906 | [log](evidence/build.log) |
| statement | 0 | 19.219 | [log](evidence/statement.log) |
| solution | 0 | 26.922 | [log](evidence/solution.log) |
| rational-enclosures | 0 | 20.172 | [log](evidence/rational-enclosures.log) |
| lower-bound | 0 | 18.343 | [log](evidence/lower-bound.log) |
| standalone | 0 | 61.578 | [log](evidence/standalone.log) |
| modular-axioms | 0 | 18.984 | [log](evidence/modular-axioms.log) |
| standalone-axioms | 0 | 21.860 | [log](evidence/standalone-axioms.log) |
| expanded-targets | 0 | 23.718 | [log](evidence/expanded-targets.log) |
| kernel-replay | 0 | 1352.250 | [log](evidence/kernel-replay.log) |

The machine-readable results include tracked-source SHA-256 values before
execution and confirm unchanged inputs afterward. Explicit source checks cover
the full proof entry, rational enclosures, lower bound, statement bridges, and
self-contained file. The main result and supporting sources also belong to
the default build. The standalone file hash is
494d21b536c7d4d87e8b4f2a79c242da820cfc25049b53c10f01034252cc9d4b.

## Dependencies

| Dependency | Observed locked commit | Tracked working tree |
| --- | --- | --- |
| mathlib | `5ed2965256430c3649e86755f9576b54eca72435` | Clean |
| plausible | `118aa17ee84656b8bd727fef7c458ee8c833385c` | Clean |
| LeanSearchClient | `ddf04cf3949fa556442341e87d47f9f6e6074707` | Clean |
| importGraph | `e928b72544873815af278d38681b31c0293588e3` | Clean |
| proofwidgets | `106ff4fafc74ef4ac99d81dbf3ab399118f497a5` | Clean |
| aesop | `355695d523e41d0554926416cba2a2b3544fbbc9` | Clean |
| Qq | `6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259` | Clean |
| batteries | `f2effa3d803fda822b1f97b806c47cf2adfbcbc2` | Clean |
| Cli | `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204` | Clean |

## Axioms and checker scope

Every expected declaration appeared in both axiom audits. All transitive
axioms are among propext, Classical.choice and Quot.sound. The audits report
zero missing declarations and zero unexpected axioms. The source scan found
no placeholder, custom-axiom declaration, native-decision axiom, or kernel
bypass in the supplied mathematical source.

Fresh replay checked the imported environment of verification.StatementCheck
using the same pinned Lean kernel. It adds a kernel-checking level to the
elaboration and axiom audits. An independently implemented external checker
and independent human mathematical review remain outstanding. The manually
triggered GitHub workflow is supplied for later reproduction and has not been
run remotely.

## Initial environment failure

The first attempt used a shared dependency cache. Its log records missing
dependency object files. That attempt was stopped after these failures, and
its runner ended with exit 1. No successful build is attributed to that attempt.
The dedicated build then encountered transient reads of two dependency object
files. Both files were present, were read successfully, and were hashed. Its
failed build log is also retained. The same-source retry completed using
dedicated dependency checkouts and refreshed official cache artifacts at the
same revisions. The mathematical source and selected proof commit were
unchanged. All final commands then passed.

Raw logs are retained privately. Shared logs replace only private filesystem
roots with named aliases. LOG_PROVENANCE.json records both the original and
shared SHA-256 values, so their identities are explicit.

## Attribution and review status

The density-limit framework and sieve argument are credited to the September
2026 companion manuscript. Cambie receives credit for the lower construction.
The four authors named in AUTHORS.md receive equal team-supplied contribution
credit for this submission. ChatGPT (OpenAI) assisted in development and checking.

The prepared award role is Lean formalization. Mathematical novelty of the
quantitative refinement and public priority of the formalization remain for
independent assessment. Personal author confirmations, the coauthor ownership
route, prize review, and any award are pending. This report makes no recipient
or payment determination.

Verification completed at 2026-11-11T08:40:18.431577+00:00.
