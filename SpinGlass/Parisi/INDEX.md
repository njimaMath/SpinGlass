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
| `randomFieldParisiInf_le_closedRandomFieldParisiFunctional`, `randomFieldParisiFunctional_sub_lt_closed_of_near_inf` | [Minimizer/Full.lean](Minimizer/Full.lean) | Global comparison with closed competitors at any level count |
| `closedRandomFieldParisiFunctional`, `parisiParameterDomain` | [Minimizer/Compact.lean](Minimizer/Compact.lean) | Zero-mass extension and compact domain |
| `exists_closedRandomFieldParisiMinimum_of_fixed_levels` | [Minimizer/Compact.lean](Minimizer/Compact.lean) | Attain a closed minimum |
| `exists_strictM_closedRandomFieldParisiMinimum` | [Minimizer/StrictMass.lean](Minimizer/StrictMass.lean) | Reduce a closed competitor through a minimum |
| `closedRandomFieldParisiFunctional_eq` | [Minimizer/Compact.lean](Minimizer/Compact.lean) | Identify the closed and ordinary functionals for admissible masses |
| `splitParisiMassLeft`, `splitParisiMassRight`, `splitParisiOverlap` | [Variational/ParisiMVariation.lean](Variational/ParisiMVariation.lean) | Existing split constructors |
| `closedRandomFieldParisiFunctional_split_matching_mass`, `closedRandomFieldParisiFunctional_split_right_matching_mass` | [Variational/ParisiMVariation.lean](Variational/ParisiMVariation.lean) | Matching-mass identities |
| `closedRandomFieldParisiFunctional_split_left_endpoint`, `closedRandomFieldParisiFunctional_split_right_endpoint_any_mass` | [Variational/ParisiMVariation.lean](Variational/ParisiMVariation.lean) | Endpoint identities |
| `splitParisiLeft_mem_parameterDomain`, `splitParisiRight_mem_parameterDomain` | [Variational/ParisiMVariation.lean](Variational/ParisiMVariation.lean) | Both split orientations are closed-domain competitors |
| `randomFieldParisiInf_le_split_left`, `randomFieldParisiInf_le_split_right`, `randomFieldParisiFunctional_sub_lt_split_left_of_near_inf`, `randomFieldParisiFunctional_sub_lt_split_right_of_near_inf` | [Variational/ParisiMVariation.lean](Variational/ParisiMVariation.lean) | Global split comparison and quantitative MIN tolerance |
| `coleHopfMassDeriv`, `hasDerivAt_coleHopf_mass`, `exists_uniform_coleHopf_mass_second_derivative_bound` | [Variational/ParisiMassDerivative.lean](Variational/ParisiMassDerivative.lean) | Concrete local mass calculus including zero; uniform single-layer Taylor constant |
| `analyticAt_coleHopf_mass`, `exists_uniform_coleHopf_mass_taylor_bound`, `exists_uniform_integral_coleHopf_mass_taylor_bound` | [Variational/ParisiMassDerivative.lean](Variational/ParisiMassDerivative.lean) | Actual analytic extension and field-independent single-layer remainders |
| `coleHopfIterateMassDeriv`, `hasDerivAt_coleHopfIterate_mass_layer`, `hasDerivWithinAt_integral_integral_coleHopfIterate_mass_layer` | [Variational/ParisiMassDerivative.lean](Variational/ParisiMassDerivative.lean) | Cascade transport and averaging over the field and root Gaussian |
| `randomFieldParisiMassMoment`, `closedParisiX₀_mass_update_eq`, `hasDerivWithinAt_closedRandomFieldParisiFunctional_mass_update` | [Variational/ParisiMassRecursion.lean](Variational/ParisiMassRecursion.lean) | Actual closed-functional mass-coordinate derivative and theta correction |
| `ParisiMAdmissible.eventually_mass_update`, `randomFieldParisiMassMoment_sub_theta_eq_zero_of_isMinOn` | [Variational/ParisiMassRecursion.lean](Variational/ParisiMassRecursion.lean) | Fixed-level mass stationarity from actual coordinate variations |
| `splitParisiLeftMassDeriv`, `splitParisiRightMassDeriv`, `hasDerivWithinAt_closedRandomFieldParisiFunctional_split_left_mass`, `hasDerivWithinAt_closedRandomFieldParisiFunctional_split_right_mass` | [Variational/ParisiMVariation.lean](Variational/ParisiMVariation.lean) | Actual inserted-mass derivatives with one-sided mass endpoints |
| `splitParisiLeftMassDeriv_left_endpoint`, `splitParisiRightMassDeriv_right_endpoint` | [Variational/ParisiMVariation.lean](Variational/ParisiMVariation.lean) | Derivatives vanish at the empty inserted interval |
| `splitParisiRootMass`, `splitParisiRootOverlap`, `splitParisiRoot_mem_parameterDomain`, `closedRandomFieldParisiFunctional_split_root_zero_mass`, `hasDerivWithinAt_closedRandomFieldParisiFunctional_split_root_mass` | [Variational/ParisiRootMVariation.lean](Variational/ParisiRootMVariation.lean) | Initial interval, root identities, competitor comparison, and mass derivative |
| `closedRandomFieldParisiFunctional_split_root_upper_mass`, `closedRandomFieldParisiFunctional_split_root_zero_le_upper_of_isMin` | [Variational/ParisiRootMVariation.lean](Variational/ParisiRootMVariation.lean) | Root upper-mass endpoint identity and comparison, including k=0 |
| `parisiQSuffix_spatial_regular_four`, `iteratedDeriv_coleHopf_one_two_bounds` | [Variational/ParisiSpatialRegularity.lean](Variational/ParisiSpatialRegularity.lean) | Actual suffix C4 regularity and bounded jets; one-layer spatial bounds uniform in variance |
| `coleHopfSplitMassResponse`, `coleHopfSplitSpatialMoment`, `hasDerivAt_coleHopfIterate_split_mass_of_pos`, `exists_uniform_coleHopfSplitMassResponse_bound` | [Variational/ParisiVarianceResponse.lean](Variational/ParisiVarianceResponse.lean) | Actual local response, matching-mass baseline, zero-mass branch, and variance-ceiling envelope |
| `hasDerivWithinAt_integral_parisiQSuffix_splitMassResponse_comp`, `hasDerivWithinAt_integral_parisiQSuffix_splitSpatialMoment_comp`, `concaveOn_integral_parisiQSuffix_splitMassResponse_comp` | [Variational/ParisiVarianceAveraging.lean](Variational/ParisiVarianceAveraging.lean) | Concrete local variance calculus under any fixed probability law |
| `coleHopfIterateSplitMassResponse`, `coleHopfIterateSplitSpatialMoment`, `hasDerivWithinAt_integral_parisiQSuffix_prefixSplitMassResponse_comp`, `hasDerivWithinAt_integral_parisiQSuffix_prefixSplitSpatialMoment_comp`, `concaveOn_integral_parisiQSuffix_prefixSplitMassResponse_comp` | [Variational/ParisiVariancePropagation.lean](Variational/ParisiVariancePropagation.lean) | Fixed-prefix variance calculus and field/shift averaging; suffix assumptions discharged |
| `exists_uniform_coleHopfIterateSplitMassResponse_bound` | [Variational/ParisiVariancePropagation.lean](Variational/ParisiVariancePropagation.lean) | Response bound independent of preceding level count, masses, and variances |
| `closedParisiX₀_split_root_eq`, `closedParisiX₀_split_right_eq`, `splitParisiRootMassDeriv_eq_U`, `splitParisiRightMassDeriv_eq_U` | [Variational/ParisiSplitResponse.lean](Variational/ParisiSplitResponse.lean) | Exact root and nonroot inner-mass split arrays and actual functional derivatives |
| `parisiRootU`, `parisiRightU`, `parisiRootf`, `parisiRightf` | [Variational/ParisiSplitResponse.lean](Variational/ParisiSplitResponse.lean) | Concrete U/f of (14.238)-(14.239), including field/root product law |
| `hasDerivWithinAt_parisiRootU`, `hasDerivWithinAt_parisiRightU`, `concaveOn_parisiRootU`, `concaveOn_parisiRightU` | [Variational/ParisiSplitResponse.lean](Variational/ParisiSplitResponse.lean) | One-sided variance calculus and concavity after all averages |
| `derivWithin_parisiRootU_zero_of_isMin`, `derivWithin_parisiRightU_zero_of_isMin`, `parisiRightf_left_endpoint_eq_zero_of_isMinOn` | [Variational/ParisiSplitResponse.lean](Variational/ParisiSplitResponse.lean) | U'(0)=q_r from actual q-moments; f left endpoint from fixed-level mass minimality |
| `coleHopfIterateTiltLog`, `abs_coleHopfIterateTiltLog_sub_le_of_sup`, `abs_cascadeTiltDensity_gaussian_sub_le_of_sup` | [Variational/ParisiMassPropagation.lean](Variational/ParisiMassPropagation.lean) | Telescoping density perturbation independent of the ordered prefix length |
| `exists_uniform_coleHopfIterateMassDeriv_lipschitz_bound`, `exists_uniform_integral_coleHopfIterate_mass_taylor_bound` | [Variational/ParisiMassPropagation.lean](Variational/ParisiMassPropagation.lean) | Uniform propagated mass remainder, including arbitrary finite-first-moment field shifts |
| `exists_uniform_closedRandomFieldParisiFunctional_mass_update_taylor_bound`, `exists_uniform_splitParisiRoot_mass_taylor_bound`, `exists_uniform_splitParisiRight_mass_taylor_bound` | [Variational/ParisiQuantitativeMass.lean](Variational/ParisiQuantitativeMass.lean) | Actual functional Taylor bounds with constants selected before parameters |
| `closedRandomFieldParisiFunctional_split_right_upper_mass`, `closedRandomFieldParisiFunctional_split_right_matching_le_upper_of_isMinOn` | [Variational/ParisiQuantitativeMass.lean](Variational/ParisiQuantitativeMass.lean) | Nonroot upper endpoint identity and fixed-level closed comparison |
| `exists_uniform_parisiRootf_lower_bound`, `exists_uniform_parisiRightf_lower_bound`, `parisiVar_le_total_variance` | [Variational/ParisiQuantitativeMass.lean](Variational/ParisiQuantitativeMass.lean) | Root/nonroot inner-mass (14.264) with coefficients depending only on ξ |
| `measurable_derivWithin_param_Icc_of_measurableOn` | [MeasurableParamDeriv.lean](../../Common/Mathlib/Analysis/Calculus/MeasurableParamDeriv.lean) | Measurability from admissible difference quotients at either endpoint |

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
