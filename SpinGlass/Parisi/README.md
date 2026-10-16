# Parisi formula formalization

This directory formalizes the finite-volume Parisi functional, the Guerra upper
bound, and Talagrand's Chapter 14 lower bound. The four theorems in
[ParisiLowerBound.lean](ParisiLowerBound.lean) are complete, with their original
statements and field, profile and covariance assumptions preserved. The reference
is [Talagrand, Vol. II](../../Notes/Talagrand-spin-glass-II.pdf), Sections 14.5-14.10.

The lower-bound proof proceeds through strict MIN parameters, the coupled main
estimate, concentration, overlap localization, the exact cascade interpolation
identity, and Gronwall comparison. Field truncation retains the original finite
second moment assumption. The convergence and liminf corollaries keep the
additional assumptions required by the existing Guerra upper-bound API.

## Start here

| Need | Entry point |
| --- | --- |
| Import the complete development | `import SpinGlass.Parisi` |
| Apply the lower bound or convergence theorem | [ParisiLowerBound.lean](ParisiLowerBound.lean) |
| Find an exact declaration owner | [INDEX.md](INDEX.md) |
| Use generic analytic tools | [Analytic module guide](Docs/ANALYTIC.md) |
| Check mathematical and editing contracts | [AGENTS.md](AGENTS.md) |
| Understand dependencies | [Architecture](Docs/ARCHITECTURE.md) |
| Review validation and maintenance work | [Editing plan](Docs/EDITING_PLAN.md#next-task) |

Proof leaves import their declaration owners directly, for example:

```lean
import SpinGlass.Parisi.Minimizer.Full
import SpinGlass.Parisi.Analytic.Mass.Bounds
```

[Analytic.lean](Analytic.lean) imports the generic analytic topic modules. The
former `ARISTOTLE.lean` import is replaced by `SpinGlass.Parisi.Analytic`; all 215
original analytic declaration names and the `SpinGlass.Aristotle` namespaces
remain unchanged. Proof leaves import the topic that owns their declaration.

Follow the [minimal API and milestone review rules](AGENTS.md#minimal-api-and-proof-obligations)
before opening a PR. Review new objects and properties against Mathlib and the
existing SpinGlass/Common layers, and verify theorem strength against the source.
The [consolidation backlog](Docs/EDITING_PLAN.md#consolidation-backlog) records
specific candidates; the earlier name-preservation audit was a reorganization
check and does not settle those mathematical API questions.

The [2026-10-16 shared API refinement](Docs/EDITING_PLAN.md#shared-api-refinement)
moves generic Cole-Hopf translations and array concatenation to Common, derives
full-domain derivative measurability from its within-domain theorem, and
simplifies the concrete log-cosh nonvanishing proof. Shared declarations now
live in `ProbabilityTheory`; their exact owners are in the index.

Keep edits focused here, with generic API moves and necessary consumer updates
as described in [AGENTS.md](AGENTS.md#work-efficiently). The local
[.parisi-lean.ps1](.parisi-lean.ps1) build wrapper supports working here and runs
Lake from the repository root with the existing shared cache.

## Module layout

| Directory or file | Responsibility |
| --- | --- |
| [Analytic.lean](Analytic.lean), Analytic/ | Mathlib-only analytic tools, grouped by mathematical topic |
| Analytic/Mass/ | Mass transform definitions, derivatives and estimates |
| Analytic/Gaussian/ | Gaussian integrability, differentiation, curvature and split responses |
| Analytic/Heat/ | Heat operator, Taylor estimates, backward derivatives, jets and split identities |
| Tree/ | Gaussian tree fields, branches, pair levels and cascade limits |
| Guerra/ | One-copy interpolation and the upper bound |
| Field/ | I.i.d. field laws, moment assumptions, averaged functionals and continuity |
| Minimizer/ | Closed-domain compact minima and strict MIN extraction |
| Minimizer/QVariation/ | Concrete overlap derivatives and stationarity |
| Variational/ | Parameter continuity, level deletion, near minima and split variations |
| Coupled/ | Two-copy comparisons, coupling gains and the uniform main estimate |
| Concentration/ | Gaussian and bounded-field fluctuations of physical pressures and masses |
| Localization/ | Overlap partitions, meeting-mass localization and second moments |
| Interpolation/ | Exact finite/cascade remainder identities, averaging and lower comparison |
| [ParisiInf.lean](ParisiInf.lean) | Variational infimum and optimized upper bound |
| [ParisiLowerBound.lean](ParisiLowerBound.lean) | Eventual lower bounds, convergence and liminf |

[Field/FieldMoments.lean](Field/FieldMoments.lean) owns
`NondegenerateExternalFieldLaw` and its elementary consequences, independently
of overlap differentiation. The compact-minimization layer uses parameter and
recursion owners; strict mass extraction imports stationarity explicitly.
Shared finite-gap and overlap-deletion lemmas keep the coupled and minimizer
proofs focused on their mathematical comparisons.

## Validation

The 2026-10-16 refinement passed the complete project, analytic library and
lower-bound capstone build with 3863 jobs. The transitive foundation audit of
fifteen affected public helpers and all four capstone theorems uses only
`propext`, `Classical.choice` and `Quot.sound`. The changed Lean owners have no
warnings; existing warnings elsewhere remain. Exact commands and results are
in [the maintenance record](Docs/EDITING_PLAN.md#shared-api-refinement).

The complete repository, analytic library and capstone build passed on
2026-10-14 with 3863 jobs, covering all 311 Parisi modules present at that time. The source
review preserves all 215 analytic declaration names, namespaces, normalized
signatures and complete proof or definition bodies. The foundation audit also
passed for all 2,874 public Parisi declarations, including the four capstone
theorems, with only standard Lean foundations and no errors. Full results are
recorded in the editing plan.

Before the analytic filename refinement, the complete repository and capstone
build passed on 2026-10-13 with 3860 jobs, covering all then-current 308 Parisi
modules. All 2,874 public source declarations passed the standard-foundation
axiom audit. That record describes the preceding source state.
Run from the repository root:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File SpinGlass/Parisi/.parisi-lean.ps1 build SpinGlass Common SpinGlass.Parisi.Analytic SpinGlass.Parisi.ParisiLowerBound
git diff --check
rg -n '\b(sorry|admit|axiom|unsafe)\b' SpinGlass/Parisi --glob '*.lean'
```

Or, from `SpinGlass/Parisi/`:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File ./.parisi-lean.ps1 build SpinGlass.Parisi.ParisiLowerBound
```

Compilation, source scans and transitive `#print axioms` checks serve different
purposes. The latest commands and results are recorded in
[the editing plan](Docs/EDITING_PLAN.md#next-task). Earlier proof milestones and
validation records remain there; they do not describe open proof obligations.

## External-field semantics

The one-site law is a probability measure μh on the reals. Site coordinates have
product law `externalFieldVecLaw` N μh, independent of Gaussian disorder and cascade
marks. Every replica uses the same realized site vector.

| Object | Meaning |
| --- | --- |
| siteFieldMixedPSpinFreeEnergy | Free energy for a realized site vector |
| iidFieldMixedPSpinFreeEnergy | Free energy averaged over the i.i.d. site vector |
| randomFieldParisiX₀, `randomFieldParisiFunctional` | One-site recursion and functional averaged over the law |
| `randomFieldParisiInf` | Infimum over admissible functional values |
| `sharedReplicaSiteField` | Shared realized field in the coupled model |
| randomFieldPairSiteY₀ | Coupled one-site expectation with shared field |

The integrability results for the functional and upper bound use a finite first
absolute moment. The lower-bound theorem assumes a finite second moment;
`NondegenerateExternalFieldLaw` additionally requires positive second moment.
None of these means the field must be Gaussian or almost surely nonzero.

The book's field conditions should be read at their Chapter 14 source:

| Source | Field condition or qualification |
| --- | --- |
| (14.65), printed p. 363 | Site fields are i.i.d. copies of a random variable $h$ |
| Before Theorem 14.5.2, p. 373 | The nonzero-field branch means $\mathbb E h^2>0$ |
| After (14.123), p. 381 | Random fields need not be Gaussian; the displayed concentration proof is completed only for deterministic fields, with further work indicated for random fields |

The displayed model definition (14.65) does not itself state a finite-second-
moment hypothesis. That integrability assumption is explicit in the current
Lean lower-bound contract. Preserve it, and do not attribute extra boundedness
or Gaussian assumptions to Chapter 14 or import them from a different chapter.

Constant fields are Dirac-law specializations. Older results named
integral_mixedPSpinFreeEnergy_le_... average a spatially constant field; use
iidFieldMixedPSpinFreeEnergy_le_... for independent site fields.
`integral_siteAverage_parisiFunctional` connects realized site sums to the
law-level functional.

The capstone keeps covariance positive semidefiniteness separate from
TalagrandXiCondition. Its convergence and liminf corollaries also retain the
upper-bound API's global differentiability and derivative-at-zero hypotheses.
Consult their exact signatures before applying them.
