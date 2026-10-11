# Parisi formula formalization

This directory develops the finite-volume Parisi functional, the Guerra upper
bound, and Talagrand's Chapter 14 route to the lower bound. The goal is to finish
the existing theorems in [ParisiLowerBound.lean](ParisiLowerBound.lean) without
changing their claims. The reference is
[Talagrand, Vol. II](../../Notes/Talagrand-spin-glass-II.pdf), Sections 14.5-14.10.

The proof checks on 2026-10-11, using Lean 4.34.0-rc2, leave one `sorry` in
this directory, in the nondegenerate eventual lower bound. Closed-competitor
infimum comparisons, both split near-minimality inequalities, and concrete
mass derivatives now compile. The root split and fourth-order regularity of the
actual suffix are proved. The variance response, its squared spatial moments,
fixed-prefix propagation, probability-law variance derivatives, and concavity
also compile, with one-sided variance endpoints. The root and nonroot inner-mass
responses are identified with the actual split functional. Their U/f calculus,
q-stationarity and nonroot left endpoint from fixed-level mass minimality compile
in [ParisiSplitResponse.lean](Variational/ParisiSplitResponse.lean).
[ParisiMassPropagation.lean](Variational/ParisiMassPropagation.lean) proves a
uniform Taylor remainder through the full ordered mass prefix and field average.
[ParisiQuantitativeMass.lean](Variational/ParisiQuantitativeMass.lean) identifies
that remainder with the actual functional and proves the root and nonroot
inner-mass square-root estimates, including their endpoint comparisons. Their
constants depend only on ξ and are selected before MIN parameters. The mirror
outer-mass bridge, uniform spatial and overlap curvature estimates, main estimate,
concentration, localization, and interpolation lower comparison remain open.
The general lower bound and convergence corollaries are assembled
but depend on the open theorem; this is not yet a proof of the Parisi formula.

[ARISTOTLE.lean](ARISTOTLE.lean) supplies compiled standalone analytic lemmas for
mass and Gaussian split calculus, quantitative variations, field truncation,
bounded differences, localization, and endpoint arguments. Its
[status and application guide](Docs/ARISTOTLE.md) records the hypotheses,
validation evidence, and remaining bridges to the actual Parisi model.

## Start here

| Need | Document |
| --- | --- |
| Agent rules and validation | [AGENTS.md](AGENTS.md) |
| Find a declaration or module | [INDEX.md](INDEX.md) |
| Dependencies and current evidence | [Architecture](Docs/ARCHITECTURE.md) |
| Continue with a bounded task | [Editing plan](Docs/EDITING_PLAN.md#next-task) |
| Use the standalone analytic lemmas | [ARISTOTLE guide](Docs/ARISTOTLE.md) |

## Module layout

| Directory or file | Responsibility |
| --- | --- |
| Tree/ | Gaussian tree fields, branches, pair levels, and cascade limits |
| Guerra/ | One-copy interpolation and the upper bound |
| Coupled/ | Two-copy interpolation, coupling bounds, and derivatives |
| Field/ | I.i.d. field laws, averaged functionals, and field continuity |
| Minimizer/ | Closed-domain compact minima and strict MIN extraction |
| Minimizer/QVariation/ | Concrete overlap derivatives and stationarity |
| Variational/ | Continuity, level deletion, near minima, and split variations |
| [ParisiInf.lean](ParisiInf.lean) | Variational infimum and optimized upper bound |
| [ParisiLowerBound.lean](ParisiLowerBound.lean) | Lower-bound target and reductions |
| [ARISTOTLE.lean](ARISTOTLE.lean) | Mathlib-only analytic lemmas; concrete mass calculus now consumes them |

Use owning modules in proof files, for example:

```lean
import SpinGlass.Parisi.Minimizer.Full
```

The convenience import SpinGlass.Parisi currently excludes the capstone.
It reaches ARISTOTLE through the mass-variation modules. Build the capstone
explicitly; successful compilation alone does not discharge its proof hole.

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
