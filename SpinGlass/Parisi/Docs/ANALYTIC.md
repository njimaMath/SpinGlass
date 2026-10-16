# Parisi analytic library

[Analytic.lean](../Analytic.lean) is the convenience import for the generic
analytic library. Its 215 public source declarations live in 27 mathematical
topic owners under [Analytic](../Analytic/). The inventory consists
of 199 lemmas/theorems and 16 definitions, abbreviations or structures. Every
original name and statement is preserved in `SpinGlass.Aristotle` or
`SpinGlass.Aristotle.Heat`, including the `Heat.Jet` namespace. The two heat tactic
macros and the continuity attribute are also preserved.

The topics depend only on Mathlib and other Analytic topics. They do not import
Parisi recursion, minimizer, coupled, field, concentration or interpolation
modules. The completed project bridges and lower bound remain in those owners;
see [INDEX.md](../INDEX.md) and the [current editing plan](EDITING_PLAN.md).

Replace the historical `SpinGlass.Parisi.ARISTOTLE` import with:

```lean
import SpinGlass.Parisi.Analytic
```

Proof leaves should import the relevant topic, for example:

```lean
import SpinGlass.Parisi.Analytic.Mass.Bounds
import SpinGlass.Parisi.Analytic.IntegralDifferentiation
```

## Reuse and consolidation

The inventory below describes the current organization. Preserving names and
bodies during the earlier move from `ARISTOTLE.lean` did not resolve possible
overlap with the existing shared analysis library. Before adding or extending
an analytic definition, compare it with
[HeatSemigroup.lean](../../../Common/Mathlib/Probability/Distributions/Gaussian/HeatSemigroup.lean),
[ColeHopf.lean](../../../Common/Mathlib/Probability/Distributions/Gaussian/ColeHopf.lean),
[CascadeColeHopf.lean](../../../Common/Mathlib/Probability/PointProcess/CascadeColeHopf.lean)
and the pinned Mathlib API.

Prefer the existing object and derive a corollary on it. Where a local formula
is useful, prove its identification and all required analytic side conditions
before treating it as a derivative, heat operator or tilted expectation. Move
missing general facts to their natural Common/Mathlib owner without importing
Parisi there; migrate consumers and delete redundant definitions and proofs.
Retain compatibility wrappers only when justified by actual consumers.

The [2026-10-16 shared API pass](EDITING_PLAN.md#shared-api-refinement) resolves
the small translation and concatenation duplicates from QVariation in these
Common owners. `coleHopf_comp_const_add` specializes the general translation
identity; full-domain derivative measurability specializes the within-domain
result. The broader Heat and mass-transform comparisons remain in the backlog.

The current Mathlib-only topic boundary is an organization record, not a reason
to maintain a second heat or Cole-Hopf theory. Reuse a shared lower layer or
move the generic result there, keeping the import graph acyclic. Apply the
[minimal API rules](../AGENTS.md#minimal-api-and-proof-obligations) and record
outcomes in the [consolidation backlog](EDITING_PLAN.md#consolidation-backlog).

## Topic owners

Module names in this table are relative to `SpinGlass.Parisi.Analytic`. Public
names in the last column are relative to `SpinGlass.Aristotle`. Counts include
source definitions and structures, excluding generated structure projections.

| Module | Declarations | Main entry points |
| --- | ---: | --- |
| [Infimum](../Analytic/Infimum.lean) | 4 | `sInf_le_of_reduced_minimum`, `lower_bound_on_closure`, `near_minimum_competitor`, `abs_sInf_range_sub_le` |
| [Mass.Basic](../Analytic/Mass/Basic.lean) | 7 | `logLaplace`, `massTransform`, `tiltedMean`, `massTransform_add_const`, `massTransform_scale_two`, `massTransform_neg_mass`, `massTransform_dirac` |
| [Mass.Derivatives](../Analytic/Mass/Derivatives.lean) | 18 | `hasDerivAt_logLaplace`, `hasDerivAt_tiltedMean`, `hasDerivAt_massTransform_zero`, `analyticOnNhd_massTransform`, `hasDerivAt_tiltedVariance` |
| [Mass.Bounds](../Analytic/Mass/Bounds.lean) | 5 | `abs_tiltedMean_pow_le`, `abs_deriv_deriv_massTransform_le`, `uniform_mass_second_derivative_bound`, `abs_massTransform_sub_le`, `massTransform_deriv_bound` |
| [IntegralDifferentiation](../Analytic/IntegralDifferentiation.lean) | 1 | `hasDerivWithinAt_integral_Icc` |
| [Convexity](../Analytic/Convexity.lean) | 1 | `concaveOn_integral_weighted` |
| [Lipschitz](../Analytic/Lipschitz.lean) | 2 | `lipschitz_of_iteratedDeriv`, `abs_sub_le_of_abs_deriv_le_one` |
| [Gaussian.Integrability](../Analytic/Gaussian/Integrability.lean) | 2 | `integrable_gaussian_exp_abs`, `integrable_gaussianReal_of_abs_le_exp` |
| [Gaussian.Differentiation](../Analytic/Gaussian/Differentiation.lean) | 4 | `hasDerivAt_gaussianPDFReal_zero`, `integral_mul_gaussianReal`, `exp_mul_abs_add_le`, `hasDerivAt_integral_gaussian_add` |
| [Gaussian.Curvature](../Analytic/Gaussian/Curvature.lean) | 4 | `integral_exp_mul_comp_add_le`, `integral_deriv_deriv_mul_exp_lower`, `gaussian_mass_curvature_lower` |
| [Gaussian.Split](../Analytic/Gaussian/Split.lean) | 24 | `gaussianLayer`, `splitMassResponse`, `splitSpatialMoment`, their variance derivatives and concavity |
| [Heat.Basic](../Analytic/Heat/Basic.lean) | 29 | `Heat.heat`, `Heat.UExp`, `Heat.hasDerivAt_heat`, `Heat.continuous_heat`, `Heat.heat_heat`, `Heat.heat_lower` |
| [Heat.Taylor](../Analytic/Heat/Taylor.lean) | 10 | `Heat.abs_taylor3_le`, `Heat.taylorConst`, `Heat.heat_short_time` |
| [Heat.Backward](../Analytic/Heat/Backward.lean) | 5 | `Heat.tendsto_heat_quotient`, `Heat.hasDerivWithinAt_heat_backward` |
| [Heat.Jet](../Analytic/Heat/Jet.lean) | 36 | `Heat.Jet`, `Heat.PosLow`, `Heat.Jet.mul`, `Heat.Jet.exp`, `Heat.hfam`, `Heat.jet_iteratedDeriv` |
| [Heat.Split](../Analytic/Heat/Split.lean) | 5 | `Heat.backward_gradSq`, `Heat.backward_entropy`, `Heat.backward_variance` |
| [Taylor](../Analytic/Taylor.lean) | 2 | `abs_taylor_one_le`, `abs_taylor_two_le` |
| [Variation](../Analytic/Variation.lean) | 5 | `split_slope_ge_neg_sqrt`, `curvature_ge_of_cubic_remainder`, `exists_quadratic_gain`, `exists_strict_gain_of_deriv_ne_zero` |
| [Profile](../Analytic/Profile.lean) | 3 | `lipschitz_deriv_of_monotone_second`, `lipschitz_deriv_even_extension`, `convex_remainder_bounds` |
| [Hyperbolic](../Analytic/Hyperbolic.lean) | 10 | `abs_deriv_ge_mul_tanh`, `integral_tanh_sq_pos`, `integral_sq_ge_tanh_sq`, `inv_cosh_sq_add_lower` |
| [Compactness](../Analytic/Compactness.lean) | 4 | `finite_witnesses_uniform_gap`, `uniform_gap_of_compact_witnesses`, `uniform_gap_to_quadratic`, `finite_uniform_positive_coefficient` |
| [FieldTruncation](../Analytic/FieldTruncation.lean) | 11 | `clip`, `clipped_law_nondegenerate`, `tendsto_integral_clip_error`, `tendsto_integral_sq_clip_error`, `map_pi_clip`, `abs_integral_lipschitz_coupling` |
| [FinitePartition](../Analytic/FinitePartition.lean) | 2 | `abs_log_sum_exp_sub_le`, `abs_normalized_log_partition_field_sub_le` |
| [BoundedDifferences](../Analytic/BoundedDifferences.lean) | 6 | `integral_exp_le_of_bounded_differences`, `bounded_differences_mgf` |
| [Concentration](../Analytic/Concentration.lean) | 4 | `mgf_prod_of_section_and_mean_bounds`, `integral_capped_exp_le_of_mgf`, `integral_weight_mul_le_of_small_event` |
| [Localization](../Analytic/Localization.lean) | 6 | `pressure_gap_of_overlap_distance`, `eventually_uniform_finite_overlap_sum`, `localized_joint_second_moment`, `weighted_localization_sum` |
| [Interpolation](../Analytic/Interpolation.lean) | 5 | `gronwall_zero_initial`, `eventually_uniform_small_of_differential_inequality`, `endpoint_lower_of_derivative_bound`, `eventual_lower_of_uniform_approximation` |

The Mass sequence is `Basic -> Derivatives -> Bounds`, separating definitions
and elementary identities from calculus and quantitative estimates. The generic
point-mass identity `massTransform_dirac` belongs to Mass.Basic. General weighted
integral concavity and derivative-to-Lipschitz estimates have their own
Convexity and Lipschitz owners.

The Heat sequence is `Basic -> Taylor -> Backward -> Jet -> Split`, reflecting
Gaussian integration, short-time expansion, variance differentiation, jet
families and split differentiation. `Gaussian.Split` combines `Heat.Split` with
`Mass.Bounds`; mass estimates themselves do not depend on heat calculus.
`Gaussian.Differentiation` reuses `Heat.Basic`. `Gaussian.Curvature` combines that
calculus with `Hyperbolic` and mass calculus. `Profile` imports ordinary
Taylor estimates. The remaining topics are independent branches with direct
Mathlib imports.

Keep filename and dependency boundaries mathematical: a basic module owns
definitions, later modules own their derivatives or bounds, and the umbrella
only imports the topic modules. The preserved `SpinGlass.Aristotle` declaration
namespace is an API compatibility choice; it does not determine source owners.

## Proof contracts and applications

The mass transform integrates one layer under a probability measure. Its
exponential envelope usually comes from the Gaussian increment; it is not an
extra exponential-moment assumption on the external-field law. Centering removes
an additive field from the uniform mass constants. At zero mass, the derivative
is half the variance, and analyticity removes the apparent quotient singularity.

The heat operator clamps negative variances through `Real.toNNReal`. Variance
identities on nonnegative intervals use admissible within-set derivatives,
including endpoints. Four-jets carry the stated spatial regularity and growth
bounds; `PosLow` supplies the lower bounds needed for quotients and logarithms.

The profile estimates reach zero without assuming positive second derivative
there, and use evenness to extend to negative overlaps. The positive bounded
field moment follows from nondegeneracy under the probability law.

Compactness turns local witnesses into a finite common gap. The localization
lemmas retain one volume threshold across their parameter type and bound joint
branch moments without dividing by branch probability. Interpolation and
truncation tools keep the cutoff and approximation choices before the volume
threshold. Applying a generic theorem still requires identifying the actual
recursion, pressure or field law in its project-specific owner.

Search exact declarations recursively:

```text
rg -n 'theorem hasDerivAt_massTransform_zero|theorem bounded_differences_mgf' SpinGlass/Parisi/Analytic
rg -n 'PARISI_LB_' SpinGlass/Parisi/Analytic
```

## Historical refinement and validation

The first reorganization compared every original public declaration with its
new owner: all 215 names and normalized source signatures agreed. Three
duplicate proofs reused established tools:
`Heat.integrable_exp_abs_gaussian` uses `integrable_gaussian_exp_abs`,
`exp_mul_abs_add_le` uses `Heat.exp_abs_affine_le`, and
`hasDerivAt_integral_gaussian_add` uses `Heat.hasDerivAt_heat`. Eleven no-op
`pi_norm` invocations were removed from the split differentiation proofs, and
deprecated Mathlib aliases were updated. The former compatibility umbrella
retained its original thirteen direct Mathlib imports for existing consumers.

That umbrella and its then-current 24 owners passed the explicit build on
2026-10-13 with Lean 4.34.0-rc2 (3199 jobs). Existing unused-hypothesis and style
linter warnings remain. Run from the repository root with the configured shared
Mathlib cache to validate the current module:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File SpinGlass/Parisi/.parisi-lean.ps1 build SpinGlass.Parisi.Analytic
git diff --check
rg -n '\b(sorry|admit|axiom|unsafe)\b' SpinGlass/Parisi/Analytic --glob '*.lean'
```

Validation on 2026-10-13 also checked all 215 declarations with `#print axioms`
in a temporary importing Lean file, including all 199 theorems and the three
simplified proofs. Only `propext`, `Classical.choice` and `Quot.sound` occur.
The source scan found no proof holes, project axioms or unsafe declarations.
`git diff --check`, topic whitespace and documentation-link checks passed.
All 215 original public source signatures agreed with their then-current owners.

## Current refinement validation

The follow-up refinement renames the umbrella to Analytic.lean, groups mass
and Gaussian modules by mathematical topic, and separates generic concavity
and Lipschitz tools from Gaussian specializations. Independent source review
verifies all 215 original names and namespaces, normalized signatures, and
complete proof or definition bodies. Local imports resolve, the graph is acyclic,
and all 27 owner counts and local documentation links check against the source.
The focused Mass.Bounds build and direct Lean checks of Convexity and Lipschitz
passed. The complete repository, analytic library and lower-bound capstone build
passed on 2026-10-14 with 3863 jobs, covering all 311 current Parisi modules.
The foundation audit checked all 2,874 public Parisi declarations, including
the four capstone theorems: 2,859 use only `propext`, `Classical.choice` and
`Quot.sound`; fifteen use no axioms, and there were no audit errors. Exact build
commands and results are recorded in
[the editing plan](EDITING_PLAN.md#analytic-topic-refinement).
