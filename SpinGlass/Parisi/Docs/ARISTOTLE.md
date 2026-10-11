# ARISTOTLE: proved analytic tools and application guide

## Status and scope

[ARISTOTLE.lean](../ARISTOTLE.lean) is a compiled standalone Mathlib-only analytic
library. Verified inventory on 2026-09-28: 199 lemmas/theorems and 16
definitions, abbreviations, or structures; every theorem has a checked proof.
There are no `sorry`, `admit`, or project axiom declarations in this file.
Validation results are recorded below.

The public task-level results use namespace `SpinGlass.Aristotle`. Gaussian
heat calculus uses `SpinGlass.Aristotle.Heat`. Import the file explicitly:

```lean
import SpinGlass.Parisi.ARISTOTLE
```

Use qualified names, such as `SpinGlass.Aristotle.near_minimum_competitor`.
As of 2026-10-11, [ParisiMassDerivative.lean](../Variational/ParisiMassDerivative.lean)
imports this leaf and consumes the mass-transform bounds and integral derivative
theorem. [ParisiMassRecursion.lean](../Variational/ParisiMassRecursion.lean) identifies
the actual closed-functional mass derivative, and ParisiMVariation consumes it
for both insertions. The U/f calculus, seven main-estimate cases, Proposition
14.5.8, localization, and lower-bound capstone remain open.
The sole existing Parisi proof hole remains in
[ParisiLowerBound.lean](../ParisiLowerBound.lean).

## Proved results by task

Search the tags in the source to find stable section boundaries. Names in this
table are relative to `SpinGlass.Aristotle`, including the `Heat.` prefix.

| Source tag | Main declarations | Proved conclusion and assumptions |
| --- | --- | --- |
| `PARISI_LB_INFIMUM` | `sInf_le_of_reduced_minimum`, `lower_bound_on_closure`, `near_minimum_competitor`, `abs_sInf_range_sub_le` | Compare a closed competitor with an infimum via an attained minimum whose value belongs to a bounded-below set; alternatively extend a bound by continuity to a closure. Combine global comparison with MIN tolerance. A uniform perturbation of a nonempty bounded-below family perturbs its infimum by the same amount. |
| `PARISI_LB_MASS` | `hasDerivAt_logLaplace`, `hasDerivAt_tiltedMean`, `hasDerivAt_massTransform`, `hasDerivAt_massTransform_zero`, `hasDerivAt_massTransform_deriv`, `analyticOnNhd_massTransform` | Differentiate logarithmic Laplace transforms and exponential tilts under a probability law and an exponential envelope. Extend the mass transform analytically across zero; its derivative there is half the variance. The explicit second-derivative formula away from zero is also proved. |
| `PARISI_LB_MASS` | `massTransform_add_const`, `uniform_mass_second_derivative_bound`, `abs_massTransform_sub_le`, `hasDerivWithinAt_integral_Icc` | Centering removes additive constants from mass derivatives. A common centered exponential envelope gives a uniform second-derivative bound on $[0,1]$. Uniform input perturbations control the transform. An integrable derivative bound and one integrable base value permit differentiation of an average within a nontrivial closed interval. |
| `PARISI_LB_HEAT` | `Heat.heat_zero`, `Heat.continuous_heat`, `Heat.hasDerivAt_heat`, `Heat.heat_heat`, `Heat.heat_short_time`, `Heat.hasDerivWithinAt_heat_backward`, `Heat.hasDerivWithinAt_heat_time` | Gaussian smoothing, spatial differentiation, the semigroup law at nonnegative times, a short-time Taylor estimate, and variance differentiation within the admissible interval. Continuity, derivative, and exponential-growth hypotheses are explicit. |
| `PARISI_LB_HEAT` | `Heat.UExp`, `Heat.Jet`, `Heat.jet_iteratedDeriv`, `Heat.Jet.mul`, `Heat.Jet.exp`, `Heat.backward_entropy`, `Heat.backward_gradSq`, `Heat.backward_variance` | Exponential bounds and jets through order four support the entropy, squared-gradient, and variance calculations used by the split lemmas. Positive exponential lower bounds control denominators. |
| `PARISI_LB_SPLIT` | `gaussianLayer`, `splitMassResponse`, `splitSpatialMoment`, `hasDerivWithinAt_splitMassResponse`, `hasDerivWithinAt_splitSpatialMoment`, `concaveOn_splitMassResponse`, `concaveOn_integral_weighted` | Actual single-layer Gaussian integral identities: the variance derivative of the inserted-mass response is half the first squared spatial moment; the first moment's derivative is minus the second. Concavity follows, including zero mass and admissible variance endpoints. A fixed nonnegative weighted integral preserves concavity. |
| `PARISI_LB_VARIATION` | `abs_taylor_one_le`, `abs_taylor_two_le`, `split_slope_ge_neg_sqrt`, `curvature_ge_of_cubic_remainder`, `exists_quadratic_gain`, `exists_strict_gain_of_deriv_ne_zero` | Taylor errors from Lipschitz first/second derivatives; a slope lower bound of order $\sqrt{\varepsilon}$ from near-minimality, endpoint comparison, and a quadratic remainder; the two interval-length cases for curvature; quadratic or strict coupling improvement under the stated Taylor/derivative hypotheses. |
| `PARISI_LB_PROFILE` | `lipschitz_deriv_of_monotone_second`, `lipschitz_deriv_even_extension`, `convex_remainder_bounds` | First-derivative Lipschitz control up to zero from a nonnegative monotone second derivative on $(0,1]$, extension to negative overlaps by evenness, and a nonnegative covariance remainder bounded by $L(u-q)^2/2$. No positive second derivative at zero is required. |
| `PARISI_LB_PROFILE` | `gaussian_mass_curvature_lower`, `abs_deriv_ge_mul_tanh`, `integral_tanh_sq_pos`, `integral_sq_ge_tanh_sq` | A concrete Gaussian layer propagates a $\cosh^{-2}$ curvature lower bound. A derivative comparison gives a squared-moment lower bound after averaging. Positive finite field second moment implies a positive bounded $\tanh^2$ moment. |
| `PARISI_LB_COMPACTNESS` | `finite_witnesses_uniform_gap`, `uniform_gap_of_compact_witnesses`, `uniform_gap_to_quadratic`, `finite_uniform_positive_coefficient` | Continuous pointwise strict witnesses on a compact set yield a uniform positive gap and finitely many witnesses, including an empty compact region. Convert that gap to a quadratic overlap penalty and combine finitely many coefficients under a monotonicity hypothesis. |
| `PARISI_LB_TRUNCATION` | `clip`, `tendsto_integral_clip_error`, `tendsto_integral_sq_clip_error`, `clipped_law_nondegenerate`, `map_pi_clip` | Coordinatewise clipping has the product of the clipped site laws; positive clipping preserves positive finite second moment. Clipping errors tend to zero in $L^1$ or $L^2$ under the corresponding moment assumption. |
| `PARISI_LB_TRUNCATION` | `abs_normalized_log_partition_field_sub_le`, `integral_average_clip_error`, `abs_integral_lipschitz_coupling`, `abs_sInf_range_sub_le` | For a finite nonempty spin system at positive volume, normalized log partition functions differ by at most the mean site-field error when spin coefficients have absolute value at most one. Its product-law average equals the one-site error. Coupled integrable Lipschitz observables and uniformly close variational families have corresponding stability bounds. |
| `PARISI_LB_CONCENTRATION` | `bounded_differences_mgf`, `mgf_prod_of_section_and_mean_bounds`, `integral_capped_exp_le_of_mgf`, `integral_weight_mul_le_of_small_event` | Product-coordinate bounded differences give a centered exponential-moment bound. Conditional section bounds and mean-fluctuation bounds combine. A negative extensive mean plus an extensive sub-Gaussian bound makes a capped exponential small. A square-integrable weight can be separated from a bounded terminal factor. |
| `PARISI_LB_LOCALIZATION` | `pressure_gap_of_overlap_distance`, `eventually_uniform_finite_overlap_sum`, `localized_joint_second_moment`, `weighted_localization_sum` | Translate a quadratic pressure penalty into a gap; exponential estimates survive sums over at most $2N+1$ overlaps with one threshold uniform in the auxiliary parameter. A small joint bad-event mass bounds its restricted second moment; finite branch sums retain an explicit error budget. |
| `PARISI_LB_ENDPOINT` | `gronwall_zero_initial`, `eventually_uniform_small_of_differential_inequality`, `endpoint_lower_of_derivative_bound`, `eventual_lower_of_cutoff_estimates`, `eventual_lower_of_uniform_approximation` | Zero-initial-gap Gronwall, eventual uniform control on a fixed time interval, passage to time one using interior derivative bounds and endpoint continuity, removal of the time cutoff, and transfer of eventual lower bounds through volume-uniform approximation. |

## Single-layer identities and their limits

For the source's probability measure $\mu$ and random variable $X$, write
$L(m)=\log\int e^{mX}\,d\mu$ and
$T(m)=L(m)/m$ for $m\ne0$, with $T(0)=\int X\,d\mu$.
The functions are `logLaplace` and `massTransform`; `tiltedMean` is expectation
under the normalized exponential tilt. The proved formulas are
$T'(m)=(m\mathbb E_m X-L(m))/m^2$ for $m\ne0$ and
$T'(0)=(\mathbb E X^2-(\mathbb E X)^2)/2$.
The envelope $\int e^{a|X|}\,d\mu<\infty$ is needed locally for $|m|<a$.
It concerns the variable of one recursion layer, not the external-field law.

`uniform_mass_second_derivative_bound` assumes a single measurable nonnegative
envelope $Y$ with $\int e^{2Y}\,d\mu<\infty$. It gives $M>0$ independent of
$X$ and its additive center $c$ whenever $|X-c|\le Y$ almost everywhere.
To use it uniformly in the realized field, first center the concrete recursion
and prove a field-independent Gaussian envelope.

For $A\in C^4(\mathbb R)$ with derivatives of orders one through four uniformly
bounded, $m\in[0,1]$, total variance $a>0$, and $v\in[0,a]$, the split results
give
$\frac{d}{dv}\operatorname{splitMassResponse}(v)
=\operatorname{splitSpatialMoment}(1,v)/2$ and
$\frac{d}{dv}\operatorname{splitSpatialMoment}(1,v)
=-\operatorname{splitSpatialMoment}(2,v)$.
Both are `HasDerivWithinAt` statements on $[0,a]$, so the endpoints require
no two-sided differentiation across a clamped variance. Zero total variance
needs its own degenerate identity; the derivative theorems assume $a>0$.

The curvature propagation lemma assumes $A\in C^2$, $|A'|\le1$, $A''\le1$,
and $A''(x)\ge\alpha/\cosh^2 x$ with $\alpha\ge0$. For a layer of variance
$v\ge0$ and mass $m\in[0,1]$, it proves the lower bound
$\alpha e^{-2v}/\cosh^2 x$ for the layer's second spatial derivative.
Iterating this estimate through the actual recursion, preserving the derivative
bounds and symmetry, is still required for Lemma 14.7.15's uniform first-overlap
bound. Positivity of a single field moment alone does not prove that bound.

## How to use these results next

### Closed competitors and split near-minimality

The concrete global-infimum comparison is now
`randomFieldParisiInf_le_closedRandomFieldParisiFunctional` in
[Minimizer/Full.lean](../Minimizer/Full.lean), compiled on 2026-10-11. It uses
the following reduction route. In
[Minimizer/Compact.lean](../Minimizer/Compact.lean), use
`exists_closedRandomFieldParisiMinimum_of_fixed_levels` to attain a minimum.
Apply the reductions
`exists_strictM_closedRandomFieldParisiMinimum` and
`exists_strictQ_closedRandomFieldParisiMinimum_of_strictM` from
[Minimizer/StrictMass.lean](../Minimizer/StrictMass.lean).
They preserve its value, possibly lowering the level count.

Identify that value with the ordinary functional by
`closedRandomFieldParisiFunctional_eq`, then establish membership with
`randomFieldParisiFunctional_mem_parisiSet` from
[ParisiInf.lean](../ParisiInf.lean). Obtain boundedness from
`bddBelow_randomFieldParisiSet_of_talagrand` in
[Variational/ParisiMin.lean](../Variational/ParisiMin.lean).
Apply `sInf_le_of_reduced_minimum` with the original attained minimum as `y`:
only its value must belong to the ordinary admissible set after reduction.

In [Variational/ParisiMVariation.lean](../Variational/ParisiMVariation.lean),
use `splitParisiLeft_mem_parameterDomain` to specialize that comparison.
The scalar assembly is already available:

```lean
example {P I ε Φ : ℝ} (hnear : P < I + ε) (hcompetitor : I ≤ Φ) :
    P - ε < Φ :=
  SpinGlass.Aristotle.near_minimum_competitor hnear hcompetitor
```

Fixed-level `IsMinOn` is used to compare the minimum with a competitor at the
same level count. The global infimum compares different counts after insertion.
Both split orientations now have domain membership and infimum/tolerance
specializations in ParisiMVariation. ParisiRootMVariation now supplies the
initial interval's constructor, identities, comparison, and mass derivative.

### Mass variations and the main estimate

The mass-transform identification and first derivative propagation are now
proved by ParisiMassDerivative and ParisiMassRecursion. The derivative bounds
used in field averaging are independent of the realized field and require only
a finite first moment of its law. The single-layer second-mass derivative
bound is also specialized to the actual suffix. ParisiMassPropagation proves
uniform full-prefix Taylor control by telescoping the logarithmic cascade-density
perturbation for ordered masses. Its constant is independent of prefix length.
ParisiQuantitativeMass specializes this to actual mass-coordinate updates and
root/nonroot inner-mass split functionals, after the field/root product average.

ParisiSpatialRegularity now verifies the $C^4$ and bounded-derivative hypotheses
for the actual suffix. ParisiVarianceResponse identifies the analytic quantities
with the actual Cole-Hopf response and moments, including zero mass.
ParisiVarianceAveraging and ParisiVariancePropagation consume
`hasDerivWithinAt_integral_Icc` with proved moment domination, and
`concaveOn_integral_weighted` with the matching-mass baseline weight fixed in
variance. Their actual-suffix specializations remove all regularity hypotheses
from the caller. ParisiSplitResponse now identifies the actual root and nonroot
inner-mass split arrays, field/root averages, U/f derivatives and q-stationarity.
It proves U'(0)=q_r and f(q_r)=f'(q_r)=0. The nonroot f left endpoint follows from
fixed-level mass stationarity in ParisiMassRecursion. The mirror outer-mass
orientation still needs a separate bridge. The mass Taylor remainder comes from
the separate ordered-prefix estimate, not from the variance-response envelope.

For (14.264), supply `split_slope_ge_neg_sqrt` with the split near-minimum bound,
the endpoint comparison from fixed-level minimality, and a uniform quadratic
Taylor upper bound. Its conclusion is $s\ge-2\sqrt{M\varepsilon}$.
The concrete root/nonroot inner-mass consumers now discharge these inputs:
`exists_uniform_parisiRootf_lower_bound` and
`exists_uniform_parisiRightf_lower_bound` give $f\ge-4\sqrt{M\varepsilon}$,
since each concrete f is twice its inserted-mass derivative.
For (14.283), `curvature_ge_of_cubic_remainder` gives
$-c\le2\delta/\rho^2+2M\rho$.
Taking $\delta$ of order $\sqrt{\varepsilon}$ and
$\rho=\varepsilon^{1/6}$ gives the intended curvature scale. Its additional
condition is $\rho\le q-a$ or $f(a)=0$; the first-level and higher-level
arguments must supply the appropriate branch and actual Taylor remainder.

Combine these inputs with the existing coupled Taylor lemmas using
`exists_quadratic_gain` or `exists_strict_gain_of_deriv_ne_zero`.
For far regions, supply continuous strict witnesses on the correct compact set,
then use `finite_witnesses_uniform_gap`, `uniform_gap_to_quadratic`, and
`finite_uniform_positive_coefficient`. The seven case proofs, including negative
overlaps and zero time, remain project obligations. Choose the MIN tolerance
after the cutoff and before selecting MIN; prove every required uniformity.

### Bounded fields and approximation of the general law

`bounded_differences_mgf` proves
$\mathbb E e^{t(F-\mathbb E F)}\le
\exp(t^2\sum_i c_i^2/8)$ from global coordinate oscillations at most $c_i$.
For a clipped law, formulate the observable on clipped inputs so those
oscillations hold for all real coordinate updates. Prove measurability and
the oscillation bound for the actual conditional mean of the logarithmic
weighted product in (14.116)-(14.121).

Combine this with the conditional Gaussian bound via
`mgf_prod_of_section_and_mean_bounds`, proving the product-integrability
hypothesis. Identify the centering function with the conditional mean.
`integral_capped_exp_le_of_mgf` then bounds the capped exponential by
$e^{-aN/2}+e^{-a^2N/(8C)}$ when the mean is at most $-aN$ and the centered
exponential moments have variance proxy $CN$. The actual cascade weights,
terminal factor, and negative mean still need identification and estimates.

For truncation, use `clipped_law_nondegenerate` at positive cutoff and
`map_pi_clip` to identify the site product law. Prove the averaged finite-volume
continuity bound using `abs_normalized_log_partition_field_sub_le` and
`integral_average_clip_error`. The displayed partition lemma has spin coefficient
bound one; two-replica coefficients need rescaling or a separate bound.
Use `abs_massTransform_sub_le` and `abs_integral_lipschitz_coupling` through the
recursion to establish a law-level functional error uniform in admissible
parameters. Apply `abs_sInf_range_sub_le` to the same nonempty admissible family,
with boundedness below for both laws. These concrete free-energy and infimum
continuity theorems are not yet supplied by this standalone file.

Finally use `tendsto_integral_clip_error` along natural-number cutoffs and
`eventual_lower_of_uniform_approximation`. That transfer requires both errors
bounded by the same vanishing sequence uniformly in volume, and a completed
eventual lower bound for each approximating law. The approximation index is
fixed before the volume threshold. This route keeps boundedness out of the
final finite-second-moment contract.

### Localization, interpolation, and the endpoint

`pressure_gap_of_overlap_distance` uses the bad-overlap threshold
$2K(\psi-\varphi+\varepsilon)\le(u-q)^2$. Supply the actual main estimate
and constrained-mass estimate, then invoke
`eventually_uniform_finite_overlap_sum` with the realizable-overlap cardinality
bound. Its parameter type may include time and level, preserving one volume
threshold for all of them. Pointwise convergence alone does not meet its
uniform exponential-bound hypothesis.

Use `localized_joint_second_moment` on the branch event $B$. It bounds the
restricted second moment by $a\mu(B)+4\varepsilon$, without dividing by
$\mu(B)$. Allocate the finite error budget before `weighted_localization_sum`.
Derive the concrete Guerra differential inequality from this estimate and
`convex_remainder_bounds`; Gronwall does not supply that identity.

Apply `eventually_uniform_small_of_differential_inequality` with a coefficient
independent of the auxiliary accuracy. Prove the terminal derivative bound and
continuity, invoke `endpoint_lower_of_derivative_bound`, then use
`eventual_lower_of_cutoff_estimates`. Identify the actual terminal free energy
and MIN functional and use the infimum's lower comparison. This supplies the
assembly pattern for the existing nondegenerate capstone once all bridges hold.

## Validation

The leaf must be checked explicitly because it is outside the convenience
import chain:

```text
lake build SpinGlass.Parisi.ARISTOTLE
rg -n '\b(sorry|admit|axiom)\b' SpinGlass/Parisi/ARISTOTLE.lean
git diff --check
```

Checks completed on 2026-09-28 with the repository's Lean 4.34.0-rc2 toolchain:

| Check | Result |
| --- | --- |
| `lake build SpinGlass.Parisi.ARISTOTLE` | Passed, 3175 jobs; linter warnings remain |
| `#print axioms` for every one of the 199 lemmas/theorems, via a temporary importing Lean file | Passed; only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` |
| Proof-hole and project-axiom source scan of ARISTOTLE | No matches |
| Scan of all Parisi Lean sources | One existing `sorry`, in `ParisiLowerBound.lean` |
| Documentation links and declaration owners | Checked |
| `git diff --check` | Passed |

This refinement preserves the declaration statements. It updates conversion
tactics for the current elaborator, makes the exponential-integrability set
explicit, adapts Gaussian integration by parts to the support-qualified Mathlib
interface, and adds the missing constant subtraction in the short-time Taylor
derivative argument. The module header now describes proved tools and includes
a heat-calculus search tag. No concrete Parisi bridge was added in this edit;
the next task is still the closed-competitor global comparison.
