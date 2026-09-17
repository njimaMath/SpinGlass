# Chapter 14 lower-bound gap map

The theorem statements in `ParisiLowerBound.lean` are preserved. This map records
which parts can be reused and which parts still require proofs.

| Book statement | Existing Lean interface | Missing result |
| --- | --- | --- |
| (14.83), (14.84), (14.89) | `randomFieldParisiX₀`, `randomFieldParisiFunctional`, `randomFieldParisiFunctional_eq_integral` | None: the outer site-law expectation is present. |
| Guerra bound (14.90) | `iidFieldMixedPSpinFreeEnergy_le_randomFieldParisiInf` | None under its explicit global differentiability hypotheses. |
| Definition 14.5.3, Lemma 14.5.5 | `exists_randomFieldParisiFunctional_lt_inf_add_of_talagrand`, `bddBelow_randomFieldParisiSet_of_talagrand`; fixed-q mass continuity in `continuousOn_parisiFunctional` | Joint continuity on the closed parameter domain, compact minimization, and removal of redundant levels to obtain strict MIN parameters. Approximation of the infimum alone does not prove MIN. |
| Proposition 14.7.5, (14.222) | `randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin`, `iidExternalFieldParisiQ_strict_chain_and_eq_moment_of_isMin` | Existence of the minimizer used as input; mass-coordinate variational consequences. |
| Proposition 14.6.3 | `coupled_bound_coupling_siteField`, `coupled_bound_coupling_zero_siteField`, `coupled_bound` | Integrable adapters for the shared i.i.d. site-field law and the particular MIN interpolation. |
| Coupled endpoint and lambda calculus | `CoupledLambdaZero`, `CoupledEndpoint`, `CoupledDeriv`, `pairSiteY₀_le_taylor` | The uniform strict improvement needed in the cases of Sections 14.8–14.10. The lambda Taylor bound alone is insufficient. |
| Theorem 14.5.7, (14.112) | Coupled bounds above | All seven main-estimate cases and a constant uniform in volume, interpolation time, and realizable constrained overlap. |
| Proposition 14.5.8 | Finite Gibbs concentration machinery outside Parisi | A constrained partition-ratio estimate with the required disorder law and integrability. |
| Proposition 14.5.6, (14.110), (14.111) | `gibbsPair`, `integral_gibbsPair_eq`, `integral_pairAvg` | Overlap localization from the main estimate and concentration, summed over the finite overlap range. |
| Theorem 14.5.4, (14.107) | `guerraBound`, `guerraBound_eq`, `integral_guerraBound`; tree/cascade limits in `BranchLimit`, `LevelBoundLaw` | The exact derivative remainder, localization-based differential inequality, and convergence on each fixed interval below one. The existing upper bound does not provide a reverse inequality. |
| (14.109), Theorem 14.5.2 | `eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_nondegenerate` | Endpoint comparison and the limit of interpolation times approaching one, after Theorem 14.5.4. |
| Theorem 14.5.1, zero second moment | `externalFieldLaw_eq_dirac_zero_of_second_moment_eq_zero`, `abs_mixedPSpinFreeEnergy_sub_field_le`, `abs_parisiInf_sub_field_le`; Dirac compatibility in `RandomFieldFunctional`, `RandomExternalField`, `ParisiInf` | None in the reduction itself. Its input nondegenerate lower bound still contains a placeholder. |

The tree kernels and branching conventions are already supplied by `TreeCov`,
`TreeField*`, `TreeTrace`, `CoupledTrace`, `PairLevels`, `CoupledLevels`,
`CoupledInterpolation`, `CoupledScheme`, `CoupledFixedWeights`,
`CoupledBoundLaw`, and `BranchAverages`. New adapters must reuse those
conventions. Two replicas share one external-field vector at each disorder
realization.
