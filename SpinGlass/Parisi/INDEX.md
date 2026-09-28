# Parisi declaration index

Paths below are relative to this directory. Search the exact symbol in its owner,
then read the signature and nearby proof. Status and next tasks live in
[Architecture](Docs/ARCHITECTURE.md) and [Editing plan](Docs/EDITING_PLAN.md).
Import module names follow paths: Minimizer/Full.lean becomes
SpinGlass.Parisi.Minimizer.Full.

## Current proof frontier

| Declaration | Owner | Use |
| --- | --- | --- |
| `exists_randomFieldParisiMIN` | [Minimizer/Full.lean](Minimizer/Full.lean) | Near-infimum value, strict parameters, q-minimum, closed fixed-level minimum |
| `closedRandomFieldParisiFunctional`, `parisiParameterDomain` | [Minimizer/Compact.lean](Minimizer/Compact.lean) | Zero-mass extension and compact domain |
| `exists_closedRandomFieldParisiMinimum_of_fixed_levels` | [Minimizer/Compact.lean](Minimizer/Compact.lean) | Attain a closed minimum |
| `exists_strictM_closedRandomFieldParisiMinimum` | [Minimizer/StrictMass.lean](Minimizer/StrictMass.lean) | Reduce a closed competitor through a minimum |
| `closedRandomFieldParisiFunctional_eq` | [Minimizer/Compact.lean](Minimizer/Compact.lean) | Identify the closed and ordinary functionals for admissible masses |
| `splitParisiMassLeft`, `splitParisiMassRight`, `splitParisiOverlap` | [Variational/ParisiMVariation.lean](Variational/ParisiMVariation.lean) | Existing split constructors |
| `closedRandomFieldParisiFunctional_split_matching_mass`, `closedRandomFieldParisiFunctional_split_right_matching_mass` | [Variational/ParisiMVariation.lean](Variational/ParisiMVariation.lean) | Matching-mass identities |
| `closedRandomFieldParisiFunctional_split_left_endpoint`, `closedRandomFieldParisiFunctional_split_right_endpoint_any_mass` | [Variational/ParisiMVariation.lean](Variational/ParisiMVariation.lean) | Endpoint identities |
| `splitParisiOverlap_mem_domain`, `splitParisiMassLeft_mem_domain`, `splitParisiLeft_mem_parameterDomain` | [Variational/ParisiMVariation.lean](Variational/ParisiMVariation.lean) | Left-split admissibility already available |

The right split takes an index in `Fin` k; the left split takes `Fin` (k + 1).
Check terminal cases before sharing a proof between orientations.

## Standalone analytic lemmas

Owner: [ARISTOTLE.lean](ARISTOTLE.lean); import
`SpinGlass.Parisi.ARISTOTLE`. Task-level names below use namespace
`SpinGlass.Aristotle`; heat helpers use its `Heat` subnamespace. The
[application guide](Docs/ARISTOTLE.md) records conclusions, assumptions,
validation, and concrete bridges still needed. These tools do not change the
project proof frontier above until their hypotheses and identifications are
proved for the Parisi model.

| Task | Declaration lookup |
| --- | --- |
| Closed competitor and MIN tolerance | `sInf_le_of_reduced_minimum`, `near_minimum_competitor` |
| Mass derivatives and uniform Taylor constant | `hasDerivAt_massTransform`, `hasDerivAt_massTransform_zero`, `uniform_mass_second_derivative_bound` |
| Field-average differentiation within an interval | `hasDerivWithinAt_integral_Icc` |
| Heat calculus | `Heat.hasDerivWithinAt_heat_backward`, `Heat.hasDerivWithinAt_heat_time`, `Heat.Jet` |
| Single-layer split response and concavity | `hasDerivWithinAt_splitMassResponse`, `hasDerivWithinAt_splitSpatialMoment`, `concaveOn_splitMassResponse` |
| Quantitative variations and coupling | `split_slope_ge_neg_sqrt`, `curvature_ge_of_cubic_remainder`, `exists_quadratic_gain` |
| Profile remainder and first-overlap inputs | `convex_remainder_bounds`, `gaussian_mass_curvature_lower`, `integral_tanh_sq_pos` |
| Uniform compact-region gain | `finite_witnesses_uniform_gap`, `finite_uniform_positive_coefficient` |
| Field truncation and variational stability | `clipped_law_nondegenerate`, `map_pi_clip`, `integral_average_clip_error`, `abs_sInf_range_sub_le` |
| Field mean fluctuations and pressure gap | `bounded_differences_mgf`, `mgf_prod_of_section_and_mean_bounds`, `integral_capped_exp_le_of_mgf` |
| Joint overlap localization | `eventually_uniform_finite_overlap_sum`, `localized_joint_second_moment`, `weighted_localization_sum` |
| Interpolation and final transfer | `eventually_uniform_small_of_differential_inequality`, `eventual_lower_of_cutoff_estimates`, `eventual_lower_of_uniform_approximation` |

## Overlap variation and MIN dependencies

| Declaration or role | Owner |
| --- | --- |
| `coleHopfIterateDeriv`, `coleHopfSplitMoment` | [Minimizer/QVariation/ColeHopf.lean](Minimizer/QVariation/ColeHopf.lean) |
| `qUpdate`, `TalagrandXiCondition`, `ParisiMAdmissible`, `ParisiQAdmissible` | [Minimizer/QVariation/Parameters.lean](Minimizer/QVariation/Parameters.lean) |
| `parisiLogCoshTerminal` | [Minimizer/QVariation/Terminal.lean](Minimizer/QVariation/Terminal.lean) |
| `parisiRecGauss_eq_coleHopfIterate`, `parisiQSuffix` | [Minimizer/QVariation/Recursion.lean](Minimizer/QVariation/Recursion.lean) |
| `parisiQMoment`, `hasDerivAt_parisiX₀_qUpdate` | [Minimizer/QVariation/Derivative.lean](Minimizer/QVariation/Derivative.lean) |
| `randomFieldParisiQMoment`, `NondegenerateExternalFieldLaw`, `IsRandomFieldParisiQMinimizer` | [Minimizer/QVariation/RandomField.lean](Minimizer/QVariation/RandomField.lean) |
| `randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin` | [Minimizer/QVariation/RandomField.lean](Minimizer/QVariation/RandomField.lean) |
| `iidExternalFieldParisiQ_strict_chain_and_eq_moment_of_isMin` | [Minimizer/QVariation/RandomField.lean](Minimizer/QVariation/RandomField.lean) |
| `exists_randomFieldParisiFunctional_lt_inf_add_of_talagrand` | [Variational/ParisiMin.lean](Variational/ParisiMin.lean) |
| Overlap continuity; mass continuity | [Variational/ParisiParameterContinuity.lean](Variational/ParisiParameterContinuity.lean), [Variational/ParisiMassContinuity.lean](Variational/ParisiMassContinuity.lean) |
| Level deletion; fixed-mass overlap minima | [Variational/ParisiLevelReduction.lean](Variational/ParisiLevelReduction.lean), [Variational/ParisiCompactMin.lean](Variational/ParisiCompactMin.lean) |
| Strict overlap reduction; strict mass reduction | [Minimizer/StrictOverlap.lean](Minimizer/StrictOverlap.lean), [Minimizer/StrictMass.lean](Minimizer/StrictMass.lean) |

## Field, Guerra, and coupled APIs

| Declaration or role | Owner |
| --- | --- |
| `externalFieldVecLaw`, `sharedReplicaSiteField` | [Field/RandomExternalField.lean](Field/RandomExternalField.lean) |
| `randomFieldParisiFunctional`, `integral_siteAverage_parisiFunctional` | [Field/RandomFieldFunctional.lean](Field/RandomFieldFunctional.lean) |
| `randomFieldParisiInf`, `iidFieldMixedPSpinFreeEnergy_le_randomFieldParisiInf` | [ParisiInf.lean](ParisiInf.lean) |
| `logCoshRec` | [Guerra/LogCosh.lean](Guerra/LogCosh.lean) |
| Initial endpoint and overlap identities | [Guerra/Initial.lean](Guerra/Initial.lean), [Guerra/Overlap.lean](Guerra/Overlap.lean) |
| Integrated Guerra bound and monotonicity | [Guerra/Bound.lean](Guerra/Bound.lean), [Guerra/Monotone.lean](Guerra/Monotone.lean) |
| Fixed-weight and finite-volume bounds | [Guerra/GuerraFixedWeights.lean](Guerra/GuerraFixedWeights.lean), [Guerra/GuerraBound.lean](Guerra/GuerraBound.lean) |
| Coupled scheme, interpolation, endpoint | [Coupled/CoupledScheme.lean](Coupled/CoupledScheme.lean), [Coupled/CoupledInterpolation.lean](Coupled/CoupledInterpolation.lean), [Coupled/CoupledEndpoint.lean](Coupled/CoupledEndpoint.lean) |
| `coupled_bound_coupling_siteField`, `coupled_bound_coupling_zero_siteField` | [Coupled/CoupledProp.lean](Coupled/CoupledProp.lean) |
| `randomField_coupling_rhs_zero_eq` | [Coupled/CoupledLambdaZero.lean](Coupled/CoupledLambdaZero.lean) |
| First coupling derivative and field integration | [Coupled/Derivative/First.lean](Coupled/Derivative/First.lean) |
| `hasDerivAt_randomFieldPairSiteY₀_coupling_zero` | [Coupled/Derivative/Zero.lean](Coupled/Derivative/Zero.lean) |
| `pairSiteY₀_le_taylor`, `pairSiteY₀''_nonneg`, `pairSiteY₀''_le_one` | [Coupled/CoupledSecondDeriv.lean](Coupled/CoupledSecondDeriv.lean) |
| Zero-second-moment law identification; field continuity | [Field/ExternalFieldZero.lean](Field/ExternalFieldZero.lean), [Field/FieldContinuity.lean](Field/FieldContinuity.lean) |
| Eventual lower bound, convergence, liminf | [ParisiLowerBound.lean](ParisiLowerBound.lean) |

## Tree and probability infrastructure

| Role | Start here |
| --- | --- |
| Gaussian tree construction and laws | [Tree/TreeField.lean](Tree/TreeField.lean), [Tree/TreeCov.lean](Tree/TreeCov.lean), [Tree/TreeFieldLaw.lean](Tree/TreeFieldLaw.lean) |
| Pair branches and overlap levels | [Tree/PairLevels.lean](Tree/PairLevels.lean), [Tree/PairTreeField.lean](Tree/PairTreeField.lean) |
| Branch averages and limiting laws | [Tree/BranchAverages.lean](Tree/BranchAverages.lean), [Tree/BranchLimit.lean](Tree/BranchLimit.lean) |
| `levelBoundLaw`; `tendsto_truncLevelBoundLaw` | [Tree/LevelBound/Basic.lean](Tree/LevelBound/Basic.lean), [Tree/LevelBound/Convergence.lean](Tree/LevelBound/Convergence.lean) |
| Finite Gibbs calculus and concentration candidates | [FiniteGibbs](../FiniteGibbs/), [Poincare.lean](../Poincare.lean), [Common probability](../../Common/Mathlib/Probability/) |

## Old-name lookup

These are historical names, not current import targets.

| Old basename | Current owner |
| --- | --- |
| `ParisiFullMin` | Minimizer/Full.lean |
| `ParisiCompactMin` | Variational/ParisiCompactMin.lean for fixed-mass q-minima; Minimizer/Compact.lean for joint closed-domain minima |
| `ParisiQDeriv` | Minimizer/QVariation/; use RandomField.lean for the law-level theorem |
| `ParisiLevelReduction`, `ParisiMVariation` | Variational/ with the same basenames |
| `CoupledDeriv` | Coupled/Derivative/First.lean, Transport.lean, Zero.lean |
| `GuerraParisi` | Guerra/Initial.lean, Overlap.lean, Bound.lean, Monotone.lean |
| `LevelBoundLaw` | Tree/LevelBound/Basic.lean, Convergence.lean |

## Focused search

From the repository root:

```text
rg -n '^theorem exists_randomFieldParisiMIN' SpinGlass/Parisi/Minimizer/Full.lean
rg -n 'split.*mem_|^theorem closedRandomFieldParisiFunctional_split' SpinGlass/Parisi/Variational/ParisiMVariation.lean
rg -n '14\.239|14\.283' SpinGlass/Parisi/Docs/talagrand-reference.txt
```

Use equation numbers in the extract to locate source pages; verify formulas in
the PDF because text extraction can damage exponents, signs, and indexing.
