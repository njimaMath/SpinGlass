# Lower-bound execution plan

## Goal and current frontier

Fill the existing nondegenerate eventual lower-bound theorem in
[ParisiLowerBound.lean](../ParisiLowerBound.lean), preserving every claim there.
Follow Talagrand, Vol. II, Sections 14.5-14.10. Source status is recorded in
[Architecture](ARCHITECTURE.md); declaration owners are in [INDEX.md](../INDEX.md).

Verified on 2026-10-11 with Lean 4.34.0-rc2: the actual root and nonroot inner-mass
U/f bridges, mass stationarity, f endpoints, uniform propagated mass remainders,
root/nonroot inner-mass square-root estimates, and variance calculus compile.
Zero root mass and one-sided endpoints are included. The capstone still has its
original `sorry`; uniform spatial/overlap estimates and the later probabilistic
stages remain open.

The standalone [ARISTOTLE analytic library](../ARISTOTLE.lean) now has checked
proofs for the generic analytic inputs. Its [guide](ARISTOTLE.md) records what
they establish, their validation, and how to apply them at each phase below.
The concrete mass modules now consume its mass-transform bounds and
field-integral differentiation theorem. Variance response calculus now also
has concrete operator specializations. The split-array and stationary-moment
bridges for the inner-mass variation are now proved; the mirror outer-mass
variation and later quantitative/probabilistic applications still need work.

## Next task

Continue the sharp spatial recursion estimates (14.271)-(14.274), then uniform
first-overlap separation and overlap curvature. The smallest next lemma is
preservation of $0\le A''\le1-(A')^2$ by a Cole-Hopf layer with mass in [0,1].
Use its actual first/second derivative formulas, Jensen and the variance term;
the log-cosh terminal satisfies this invariant with equality. Iterate it to
obtain $0\le A_p''\le1$ uniformly in all levels, also at zero mass/variance.
This supplies the upper-curvature input to `Aristotle.gaussian_mass_curvature_lower`.

The quantitative inner-mass estimate (14.264) is now proved in
[ParisiQuantitativeMass.lean](../Variational/ParisiQuantitativeMass.lean):
`exists_uniform_parisiRootf_lower_bound` and
`exists_uniform_parisiRightf_lower_bound` give $f\ge-4\sqrt{M\varepsilon}$.
Each f is twice the actual inserted-mass derivative. M depends only on ξ and
is selected before k, parameters, field law and tolerance. Root upper mass B
may be arbitrarily small and includes k=0, B=1. The nonroot upper endpoint
includes mass 1 and compares the old closed functional at `qUpdate qs p.succ u`.
Global infimum comparison supplies near-minimality across the split dimensions;
fixed-level minimality is used only for those endpoint comparisons.

[ParisiMassPropagation.lean](../Variational/ParisiMassPropagation.lean) proves
the full ordered-prefix Taylor estimate. The logarithmic cascade-density
perturbation telescopes to twice the input perturbation, independent of prefix
length. This controls changes of the transported mass derivative together with
the centered single-layer second-mass bound. Field/root averaging requires only
an integrable spatial shift. The earlier conditional-variance route was not
needed. The mirror free outer mass still needs its own U/f bridge, including
the terminal old interval of mass 1.

The proved U/f bridge is
[ParisiSplitResponse.lean](../Variational/ParisiSplitResponse.lean): root uses the
full post-root iterate; nonroot inner mass uses `splitParisiMassRight`, prefix
length p.val and suffix `parisiQSuffix ... p.castSucc`. Both U'(0) identities
are derived from the actual old q-moments, with the field/root product law and
Fubini proved. The nonroot f left endpoint is
`parisiRightf_left_endpoint_eq_zero_of_isMinOn`; its mass stationarity is in
[ParisiMassRecursion.lean](../Variational/ParisiMassRecursion.lean).

Read [ParisiSpatialRegularity.lean](../Variational/ParisiSpatialRegularity.lean),
the [ARISTOTLE curvature propagation section](../ARISTOTLE.lean), and book
pp. 411-414. Quantitative q₁ separation and overlap curvature still need
constants uniform in the chosen MIN; the current C4 suffix bound may depend on
its levels and is not such a uniform constant.

Completed declarations and checks on 2026-10-11:

| Owner | Verified additions |
| --- | --- |
| [Minimizer/Full.lean](../Minimizer/Full.lean) | `randomFieldParisiInf_le_closedRandomFieldParisiFunctional`, `randomFieldParisiFunctional_sub_lt_closed_of_near_inf` |
| [ParisiMVariation.lean](../Variational/ParisiMVariation.lean) | `splitParisiMassRight_mem_domain`, `splitParisiRight_mem_parameterDomain`, `randomFieldParisiInf_le_split_left`, `randomFieldParisiInf_le_split_right`, `randomFieldParisiFunctional_sub_lt_split_left_of_near_inf`, `randomFieldParisiFunctional_sub_lt_split_right_of_near_inf` |
| [ParisiMassDerivative.lean](../Variational/ParisiMassDerivative.lean) | `hasDerivAt_coleHopf_exponent_zero`, `hasDerivAt_coleHopf_mass`, `exists_uniform_coleHopf_mass_second_derivative_bound`, `hasDerivAt_coleHopfIterate_mass_layer`, `exists_uniform_coleHopfIterate_mass_derivative_bound`, `hasDerivWithinAt_integral_integral_coleHopfIterate_mass_layer`, `exists_uniform_parisiQSuffix_mass_second_derivative_bound` |
| [ParisiMassRecursion.lean](../Variational/ParisiMassRecursion.lean) | `closedParisiX₀_mass_update_eq`, `randomFieldParisiMassMoment`, `hasDerivWithinAt_randomFieldParisiX₀_mass_update`, `parisiMassPenalty_mass_update_eq`, `hasDerivWithinAt_closedRandomFieldParisiFunctional_mass_update` |
| [ParisiMassRecursion.lean](../Variational/ParisiMassRecursion.lean) | `ParisiMAdmissible.eventually_mass_update`, `isLocalMin_closedRandomFieldParisiFunctional_mass_update_of_isMinOn`, `randomFieldParisiMassMoment_sub_theta_eq_zero_of_isMinOn` |
| [ParisiMVariation.lean](../Variational/ParisiMVariation.lean) | `splitParisiLeftMassDeriv`, `splitParisiRightMassDeriv`, `hasDerivWithinAt_closedRandomFieldParisiFunctional_split_left_mass`, `hasDerivWithinAt_closedRandomFieldParisiFunctional_split_right_mass`, `splitParisiLeftMassDeriv_left_endpoint`, `splitParisiRightMassDeriv_right_endpoint` |
| [ParisiRootMVariation.lean](../Variational/ParisiRootMVariation.lean) | Root constructors, closed-domain membership, zero-mass/empty-interval identities, global comparison, root mass derivative |
| [ParisiRootMVariation.lean](../Variational/ParisiRootMVariation.lean) | `closedRandomFieldParisiFunctional_split_root_upper_mass`, `closedRandomFieldParisiFunctional_split_root_zero_le_upper_of_isMin` |
| [ParisiMassPropagation.lean](../Variational/ParisiMassPropagation.lean) | Actual cascade density logarithm, uniform perturbation bound, `exists_uniform_coleHopfIterateMassDeriv_lipschitz_bound`, `exists_uniform_integral_coleHopfIterate_mass_taylor_bound` |
| [ParisiQuantitativeMass.lean](../Variational/ParisiQuantitativeMass.lean) | Actual mass-coordinate Taylor estimate, root/nonroot upper endpoint comparisons and `exists_uniform_parisiRootf_lower_bound`, `exists_uniform_parisiRightf_lower_bound` |
| [ParisiSpatialRegularity.lean](../Variational/ParisiSpatialRegularity.lean) | `parisiQSuffix_spatial_regular_four`, `iteratedDeriv_coleHopf_one_two_bounds` |
| [ParisiVarianceResponse.lean](../Variational/ParisiVarianceResponse.lean) | Concrete response/moment definitions, zero-mass response, matching-mass baseline, `hasDerivAt_coleHopfIterate_split_mass_of_pos` |
| [ParisiVarianceAveraging.lean](../Variational/ParisiVarianceAveraging.lean) | Actual suffix variance derivatives and concavity under any fixed probability law; uniform-in-variance spatial moment bounds |
| [ParisiVariancePropagation.lean](../Variational/ParisiVariancePropagation.lean) | Actual suffix derivatives, dissipation and concavity after fixed-prefix and probability-law averages; prefix/field-independent response envelope |
| [ParisiSplitResponse.lean](../Variational/ParisiSplitResponse.lean) | Actual root/nonroot inner-mass recursion identities, U/f normalization, variance derivatives, concavity, U'(0)=q_r, f(q_r)=f'(q_r)=0, and nonroot f(q_{r-1})=0 from fixed-level mass minimality |
| [MeasurableParamDeriv.lean](../../../Common/Mathlib/Analysis/Calculus/MeasurableParamDeriv.lean) | Within derivative measurability from admissible difference quotients, including both endpoints |

This command passed with 3542 jobs:

```text
lake build Common.Mathlib.Analysis.Calculus.MeasurableParamDeriv SpinGlass.Parisi.Minimizer.QVariation.RandomField SpinGlass.Parisi.Minimizer.Full SpinGlass.Parisi.Variational.ParisiRootMVariation SpinGlass.Parisi.Variational.ParisiVariancePropagation SpinGlass.Parisi.Variational.ParisiQuantitativeMass SpinGlass.Parisi.ParisiLowerBound
```

`git diff --check` passed. A proof-hole scan of SpinGlass/Parisi and Common
found only `ParisiLowerBound.lean:44`. A temporary `lake env lean` audit of
213 public theorems in the thirteen changed proof owners passed: all have only
`propext`, `Classical.choice`, and `Quot.sound`. The separate capstone audit
still reports `sorryAx`. No build blocker remains. The mathematical obligations
are the mirror outer-mass bridge, uniform spatial/overlap curvature estimates, main estimate,
random-field concentration transfer, localization, and interpolation comparison.

## Source lookup

The source PDF is [Notes/Talagrand-spin-glass-II.pdf](../../../Notes/Talagrand-spin-glass-II.pdf).
Use the existing [text extract](talagrand-reference.txt) for search, not as the
authority for formulas. Do not read the whole extract into context.

The following page ranges use printed book pages; viewer page numbers are
one-based. In this PDF the viewer page is the printed page plus 5 in Chapter 14.

| Material | Printed pages | PDF viewer pages | Read for |
| --- | --- | --- | --- |
| Section 14.4 | 362-371 | 367-376 | Interpolation definitions, endpoints, upper bound |
| Section 14.5 | 371-381 | 376-386 | MIN, target estimates, concentration, proof assembly |
| Section 14.6 | 381-395 | 386-400 | Coupled bounds and Taylor calculus |
| Section 14.7 | 395-414 | 400-419 | Operators, stationarity, mass variations |
| Section 14.8 | 415-419 | 420-424 | Seven cases and compactness assembly |
| Section 14.9 | 419-428 | 424-433 | Critical case proofs |
| Section 14.10 | 428-439 | 433-444 | Outside-interval and zero-time cases |

Useful anchors: (14.101) and Theorem 14.5.1 on p. 373; MIN and Theorem 14.5.4
on pp. 373-374; (14.109) on p. 375; Theorem 14.5.7 on p. 376;
Proposition 14.5.8 on pp. 377-381; random-field caveat after (14.123) on p. 381;
(14.239) on p. 404; (14.283) on p. 414.

For field conditions, read (14.65) on p. 363 together with the nonzero-field
definition on p. 373 and the random-field qualification on p. 381. The Gaussian
Hamiltonian assumption does not make the external field Gaussian. The current
Lean contract explicitly assumes finite second moment; do not infer stronger
field assumptions from a concentration lemma's inputs.

From the repository root:

```text
rg -n '14\.239|14\.250|14\.283' SpinGlass/Parisi/Docs/talagrand-reference.txt
pdftotext -f 378 -l 386 -layout Notes/Talagrand-spin-glass-II.pdf -
```

Inspect the relevant PDF page when extracted subscripts, derivatives, or signs
are ambiguous. Equation numbers are more stable references than extract lines.

## Execution rules

Build the current leaf before a proof edit to distinguish existing failures
from new ones. Finish one consumer-ready result at a time; do not create a chain
of placeholder modules. Read the next consumer's signature before fixing the
helper's quantifiers. Proposed files below should be created only when they have
actual definitions and proofs. Adapt names to the repository structure.

The main estimate and concentration are independent inputs to localization.
The sequence below is a practical single-agent order, not a requirement that
concentration import the main estimate.

## Mass calculus: Section 14.7

Continue from the split comparison above and the existing q-stationarity.
Represent Talagrand's $\Phi$, $U$, and $f$ through the concrete recursion; document
their correspondence to (14.238)-(14.239). Define the inserted-mass derivative
with its actual domain, including one-sided endpoints.

Required outputs:

- The concrete mass derivative identity (14.239), with integrability and
  differentiation under the field expectation proved.
- The formulas and sign control for $U'$ and $U''$, including $U'(0)=q_r$ from
  existing stationarity. State concavity on precisely the book's domain.
- $f(q_r)=f'(q_r)=0$ and the appropriate left-endpoint identity for $r\ge2$.
  Use fixed-level mass minimality for that endpoint identity.
- The needed bounds for mass Taylor remainders and the third overlap derivative.
  Check the current profile assumptions before claiming a global smoothness bound.
- The quantitative $f(u)\ge-M\sqrt{\varepsilon}$ consequence of split
  near-minimality, with constants uniform over the parameters required by the
  book. A bound on the first derivative alone does not control a Taylor remainder.
- Lemma 14.7.15's $q_1\ge1/M$ under nondegeneracy, uniform in the eligible MIN
  approximation; endpoint strictness alone is insufficient.
- The curvature bound (14.283), of order $\varepsilon^{1/6}$. Retain the book's
  split according to whether $q_r-\varepsilon^{1/6}\ge q_{r-1}$; use the
  near-minimality bound or the endpoint identity accordingly.

Exit condition: the case proofs can import these estimates without reopening
the recursion. Check both split orientations and terminal intervals. Bounds
used to select the MIN tolerance must not depend on the MIN chosen afterwards.

## Coupled adapters: Section 14.6

Reuse CoupledProp, CoupledLambdaZero, Coupled/Derivative/First and Zero, and
CoupledSecondDeriv via the exact owners in INDEX.md. Existing averaged zero
coupling and derivative lemmas should be applied before new adapters are added.

Expose the constrained two-copy pressure in the normalization of (14.100).
For realized fields, use `sharedReplicaSiteField` and prove the integrability
needed to average over externalFieldVecLaw. Track the sign parameter for
negative overlaps. Separate witness construction from coupled-bound algebra
and scalar analysis.

Exit condition: a case proof can choose admissible parameters, invoke the
coupled bound, rewrite its zero-coupling value, apply `pairSiteY₀_le_taylor`,
and finish a scalar inequality. It should not manipulate cascade internals.

## Main estimate: Theorem 14.5.7

Suggested new owner: SpinGlass/Parisi/ParisiMainEstimate.lean (not yet present).

First fix the profile, nondegenerate law, and $0\le t_0<1$. Choose a positive
MIN tolerance depending only on those data. For every MIN satisfying that
tolerance, obtain $K>0$ such that, for all relevant volumes, levels, realizable
overlaps, and $0\le t\le t_0$,
$\Psi_r(t,u)\le2\psi(t)-(u-q_r)^2/K$.

Do not omit the smallness choice for the MIN tolerance. Near-case hypotheses
include bounds of the form $M\varepsilon^{1/6}\le1-t_0$; far cases additionally
use the positive convexity gap in (14.302)-(14.306). These choices must precede
MIN selection.

| Book proposition | Range and task |
| --- | --- |
| 14.8.1 | Near left, $q_{r-1}\le u\le q_r$; Taylor in coupling and curvature give quadratic gain |
| 14.8.2 | Far left with $r\ge2$; split variation and convexity give strict gain |
| 14.8.3 | First level with $|u|\le q_1$; preserve the negative-overlap argument |
| 14.8.4 | Near right, $q_r\le u\le q_{r+1}$; mirror critical calculation |
| 14.8.5 | Far right; mirror strict-gain argument |
| 14.8.6 | Positive time outside neighboring overlap interval |
| 14.8.7 | Zero time and $u\ne q_r$ |

For the far region, prove a uniform positive gap on a compact set. A direct
witness approach can replace the abstract infimum $\Psi^*$, but must still
supply the local continuity/upper semicontinuity or finite-cover argument
needed for uniformity. Handle empty far regions separately. Convert a gap
$\delta>0$ into a quadratic penalty using $(u-q_r)^2\le4$, then take finite
maxima over levels/cases.

Exit condition: one theorem matching (14.112), with all choices and constants
in the correct order and an independent leaf build.

## Concentration: Proposition 14.5.8

Suggested new owner: SpinGlass/Parisi/ParisiConcentration.lean (not yet present).

Build the constrained/unconstrained recursion, multiplicative weights, and
bounded terminal factor of (14.116)-(14.120). Derive the negative mean of the
logarithmic weighted product from a positive pressure gap, as in (14.121).

For a deterministic realized field, prove the Gaussian log-product map has a
Lipschitz constant of order $\sqrt N$, uniform in that field, and apply the
existing concentration infrastructure. Account for both interaction disorder
and root marks. Handle zero variance without dividing by its square root.

Resolve the random-field transfer explicitly. Talagrand's text after (14.123)
does not supply the full non-Gaussian proof. If $L$ is the logarithmic product,
conditioning controls $L-\mathbb E[L\mid h]$; the averaged gap controls
$\mathbb E L$. The remaining term $\mathbb E[L\mid h]-\mathbb E L$ needs proof.

Possible routes to investigate, not established facts:

- Prove appropriate martingale/field-fluctuation control from the actual law
  assumptions, keeping its rate uniform enough for localization.
- Prove the argument first for bounded field approximations, then establish
  uniform free-energy and variational-value continuity under truncation to
  recover the original finite-second-moment target.

For the second route, current FieldContinuity lemmas concern constant-field
changes; do not assume arbitrary-law truncation continuity is already available.
Prove nondegeneracy of suitable approximations and justify every limit exchange.
If a weaker decay bound replaces (14.114), label it accurately and prove it
suffices after summing over at most $2N+1$ overlap values. Mere convergence to
zero for each overlap is insufficient.

Exit condition: an averaged constrained-mass estimate actually applicable to
the final field law, or a complete approximation bridge with a rate sufficient
for localization. The gap-dependent constant must be independent of volume,
time, and overlap. Do not mark this phase done after only a conditional theorem.

## Localization: Proposition 14.5.6

Suggested new owner: SpinGlass/Parisi/ParisiLocalization.lean (not yet present).

Combine the main estimate with the pressure-gap estimate on the event
$(R_{1,2}-q_r)^2\ge K(\psi(t)-\varphi_N(t)+\varepsilon_1)$.
Sum over realizable overlaps, using the safe bound of $2N+1$ values and handling
empty constraints explicitly.

Choose localization $K$ before $\varepsilon_1$. The volume threshold may depend
on $\varepsilon_1$, but must be uniform over $t\in[0,t_0]$ and the finitely many
levels. The main estimate's $K$ and concentration's gap-dependent constant are
different roles; do not let the latter change the former's quantifier order.

Exit condition: the expectation of the bad-overlap event intersected with the
branch-meeting event is eventually at most $\varepsilon_1$, as in (14.110).
The book uses this joint mass, not a normalized conditional probability requiring
division by the branch-meeting probability.

## Interpolation: Theorem 14.5.4

Suggested new owner: SpinGlass/Parisi/ParisiInterpolationLower.lean (not yet present).

Identify the concrete interpolation and its Parisi-side comparison. Obtain the
exact Guerra derivative remainder, with the repository's normalization; an
already integrated upper bound alone cannot give the lower comparison.
Bound the profile remainder by a constant times $(R_{1,2}-q_r)^2$, proving the
needed regularity from TalagrandXiCondition.

Insert localization and sum over levels to get, eventually and uniformly in
time, $(\psi-\varphi_N)'\le K(\psi-\varphi_N+\varepsilon_1)$, with zero initial
difference and $K$ independent of $\varepsilon_1$. Apply the differential
inequality argument (Lemma A.11.1 in the book), then let $\varepsilon_1$ tend
to zero in an eventual accuracy statement.

Exit condition: (14.107) for eligible MIN at each fixed cutoff below 1, in a
form directly usable by the endpoint proof.

## Endpoint and capstone: Theorems 14.5.2 and 14.5.1

Prove the coarse volume-uniform derivative comparison (14.109). Use endpoint
continuity if derivatives are available only at interior times. Combine the
comparison with interpolation convergence to get an eventual inequality of
the form $\varphi_N(1)\ge\psi(1)-M(1-t_0)-\delta$.

For a requested lower-bound accuracy, choose $t_0$ near 1 first, then a tolerance
allowed by the main/interpolation theorem, then MIN, and finally large volume.
Use $\varphi_N(1)=p_N$, $\psi(1)=P_k$, and $\mathcal P\le P_k$.
The MIN tolerance enables the variational estimates; its near-infimum upper
inequality is not the lower inequality needed in the last comparison.

Replace the capstone hole with a short assembly proof. Preserve the existing
zero-second-moment reduction, convergence squeeze, liminf result, and all their
hypotheses.

Exit condition: all existing claims compile from completed dependencies with
no new project axioms or proof holes.

## Final integration and handoff

Add the completed capstone to the import chain through SpinGlass/Parisi.lean
(or directly through SpinGlass.lean). Build every new leaf when introduced,
then the capstone and full project. Follow [AGENTS.md](../AGENTS.md#validation)
for proof-hole and axiom checks. Update the status table and this plan.

At the end of each proof session, replace the next-task description with a short
record containing: completed declaration and owner; exact commands/results;
remaining mathematical or build blocker; next consumer-ready lemma. Do not
duplicate a full historical log in every document.
