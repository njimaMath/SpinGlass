import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Standalone analytic lemmas for the Parisi lower bound

This file imports only Mathlib and contains proof bodies for all its declarations,
with no proof placeholders. Namespace `SpinGlass.Aristotle` avoids collisions when
these lemmas are imported into the project. Heat-semigroup helpers live in the
subnamespace `SpinGlass.Aristotle.Heat`.

The status, hypotheses, validation evidence, and application guide are maintained
in `Docs/ARISTOTLE.md`. Import this leaf with `import SpinGlass.Parisi.ARISTOTLE`;
the convenience module `SpinGlass.Parisi` does not currently import it.

Application map: `Docs/EDITING_PLAN.md` and its current declaration owners.
Already implemented MIN existence, q-stationarity, split identities, Gaussian
concentration, and coupled Taylor bounds are not duplicated here.

The sections collect general mathematical ingredients for the remaining stages:
closed-competitor comparison; mass differentiation and quantitative variation;
profile remainders; compactness assembly; bounded-field concentration and field
truncation; overlap localization; differential inequalities and endpoint limits.
Each section records its intended consumer. Statements with analytic hypotheses
are general tools: applying them still requires proving those hypotheses for the
actual Parisi recursion. In particular this file does not assert the main estimate,
the concrete U identities, or the lower bound by assuming their conclusions.

For random fields the proposed route is bounded truncation, followed by uniform
L1 continuity. Exponential concentration is required only for bounded fields.
These are proved general tools with explicit hypotheses. The project-specific
bridges and the seven main-estimate cases still require proofs in their owners.

## Search guide

Search for a `PARISI_LB_` tag to jump to its section, or use the exact declaration
names below with the editor's symbol search. Tags are stable when line numbers
change. Book references identify intended applications, not completed bridges.
The task-level declarations below belong to `SpinGlass.Aristotle`; the heat
helpers listed under `PARISI_LB_HEAT` belong to `SpinGlass.Aristotle.Heat`.

| Search tag | Purpose |
| --- | --- |
| `PARISI_LB_INFIMUM` | Closed competitors, MIN tolerance, infimum continuity |
| `PARISI_LB_MASS` | Mass derivatives, zero mass, domination, Taylor constants |
| `PARISI_LB_HEAT` | Gaussian smoothing, variance endpoints, jets |
| `PARISI_LB_SPLIT` | Gaussian split, U derivatives, concavity |
| `PARISI_LB_VARIATION` | Square-root slope, sixth-root curvature, coupling gain |
| `PARISI_LB_PROFILE` | Covariance remainder, first-overlap positivity |
| `PARISI_LB_COMPACTNESS` | Uniform gap from pointwise witnesses |
| `PARISI_LB_TRUNCATION` | Bounded fields, L1/L2 approximation, law continuity |
| `PARISI_LB_CONCENTRATION` | Bounded differences, conditional mean, pressure gap |
| `PARISI_LB_LOCALIZATION` | Overlap sum, joint branch mass, error budget |
| `PARISI_LB_ENDPOINT` | Gronwall, time cutoff, approximation transfer |

Each section below records its book references and intended consumers.

## Declaration lookup by task

- Closed competitor: `sInf_le_of_reduced_minimum`; alternative density route:
  `lower_bound_on_closure`; split comparison: `near_minimum_competitor`.
- Infimum stability under field approximation: `abs_sInf_range_sub_le`.
- First mass derivative: `hasDerivAt_massTransform`; zero mass:
  `hasDerivAt_massTransform_zero`; second derivative:
  `hasDerivAt_massTransform_deriv`; uniform bound:
  `uniform_mass_second_derivative_bound`.
- Differentiate a field average, including endpoints:
  `hasDerivWithinAt_integral_Icc`.
- Heat calculus: `Heat.heat_heat`, `Heat.hasDerivAt_heat`,
  `Heat.hasDerivWithinAt_heat_time`, `Heat.hasDerivWithinAt_heat_backward`;
  smooth-family inputs: `Heat.Jet`, `Heat.jet_iteratedDeriv`, `Heat.Jet.exp`.
- U calculus before recursion propagation: `hasDerivWithinAt_splitMassResponse`,
  `hasDerivWithinAt_splitSpatialMoment`, `concaveOn_splitMassResponse`,
  `concaveOn_integral_weighted`.
- Quantitative MIN estimates: `split_slope_ge_neg_sqrt`,
  `curvature_ge_of_cubic_remainder`; Taylor inputs: `abs_taylor_one_le`,
  `abs_taylor_two_le`.
- Coupling improvement: `exists_quadratic_gain`,
  `exists_strict_gain_of_deriv_ne_zero`.
- Guerra error bound: `lipschitz_deriv_of_monotone_second`,
  `lipschitz_deriv_even_extension`, `convex_remainder_bounds`.
- First overlap bounded away from zero: `gaussian_mass_curvature_lower`,
  `abs_deriv_ge_mul_tanh`, `integral_tanh_sq_pos`, `integral_sq_ge_tanh_sq`.
- Uniform main-estimate coefficient: `finite_witnesses_uniform_gap`,
  `uniform_gap_to_quadratic`, `finite_uniform_positive_coefficient`.
- Truncate an i.i.d. field: `clip`, `clipped_law_nondegenerate`, `map_pi_clip`,
  `tendsto_integral_clip_error`, `tendsto_integral_sq_clip_error`.
- Uniform free-energy approximation: `abs_normalized_log_partition_field_sub_le`,
  `integral_average_clip_error`; functional approximation:
  `abs_massTransform_sub_le`, `abs_integral_lipschitz_coupling`.
- Average conditional concentration: `bounded_differences_mgf`,
  `mgf_prod_of_section_and_mean_bounds`, `integral_capped_exp_le_of_mgf`.
- Localize overlaps: `pressure_gap_of_overlap_distance`,
  `eventually_uniform_finite_overlap_sum`, `localized_joint_second_moment`,
  `weighted_localization_sum`.
- Close the interpolation argument: `gronwall_zero_initial`,
  `eventually_uniform_small_of_differential_inequality`.
- Finish the lower bound: `endpoint_lower_of_derivative_bound`,
  `eventual_lower_of_cutoff_estimates`, `eventual_lower_of_uniform_approximation`.

Suggested search from the repository root:
`rg -n 'PARISI_LB_|14\.264|14\.283|zero|truncation' SpinGlass/Parisi/ARISTOTLE.lean`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

/-! ## Closed competitors and global near-minimality

Search tag: `PARISI_LB_INFIMUM`. Keywords: global infimum, closed domain,
MIN epsilon, split competitor, density, perturbation of the variational value.

Consumer: `Minimizer/Full.lean` and `Variational/ParisiMVariation.lean`.
The set S below is the set of ordinary admissible functional values. Reduction
of a closed minimum supplies its membership in S; no comparison across different
level counts is inferred from fixed-level minimality.
-/

/-- Transfer a lower bound through a value-preserving reduction of an attained minimum. -/
theorem sInf_le_of_reduced_minimum {X : Type*} {D : Set X} {F : X → ℝ}
    {S : Set ℝ} (hS : BddBelow S) {x y : X}
    (hy : IsMinOn F D y) (hvalue : F y ∈ S) (hx : x ∈ D) :
    sInf S ≤ F x := by
  exact (csInf_le hS hvalue).trans (hy hx)

/-- Alternative route when ordinary competitors are dense among closed competitors. -/
theorem lower_bound_on_closure {X : Type*} [TopologicalSpace X]
    {D : Set X} {F : X → ℝ} {b : ℝ}
    (hF : ContinuousOn F (closure D)) (hD : ∀ x ∈ D, b ≤ F x) :
    ∀ x ∈ closure D, b ≤ F x := by
  intro x hx
  exact ContinuousWithinAt.closure_le hx continuousWithinAt_const
    ((hF x hx).mono subset_closure) hD

/-- Global near-minimality applies to a split even though the level count changes. -/
theorem near_minimum_competitor {P I ε Φ : ℝ}
    (hnear : P < I + ε) (hcompetitor : I ≤ Φ) : P - ε < Φ := by
  linarith

/-- Uniform perturbations of a nonempty family perturb its infimum by the same amount. -/
theorem abs_sInf_range_sub_le {ι : Type*} [Nonempty ι]
    {F G : ι → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hF : BddBelow (range F)) (hG : BddBelow (range G))
    (h : ∀ i, |F i - G i| ≤ δ) :
    |sInf (range F) - sInf (range G)| ≤ δ := by
  have h₁ : iInf F - δ ≤ iInf G :=
    le_ciInf fun i => by linarith [ciInf_le hF i, (abs_le.1 (h i)).2]
  have h₂ : iInf G - δ ≤ iInf F :=
    le_ciInf fun i => by linarith [ciInf_le hG i, (abs_le.1 (h i)).1]
  rw [← iInf, ← iInf, abs_sub_le_iff]
  constructor <;> linarith

/-! ## Mass calculus for a single logarithmic Laplace transform

Search tag: `PARISI_LB_MASS`. Keywords: entropy, tilted covariance, mass zero,
variance, differentiation under the integral, uniform second derivative.

Consumer: the missing mass derivative and mass Taylor estimates in Section 14.7.
These are actual integral formulas, including the removable singularity at mass
zero. Exponential integrability here is for the variable integrated by one
recursion layer, usually a Gaussian increment; it is not a field-law assumption.
-/

/-- Logarithm of the exponential moment; the unnormalized input to `massTransform`. -/
def logLaplace {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (m : ℝ) : ℝ :=
  Real.log (∫ ω, Real.exp (m * X ω) ∂μ)

/-- Single recursion layer with its zero-mass value defined by ordinary expectation.
Search with `gaussianLayer` for its Gaussian specialization. -/
def massTransform {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (m : ℝ) : ℝ :=
  if m = 0 then ∫ ω, X ω ∂μ else logLaplace μ X m / m

/-- Expectation of Y under the normalized exponential tilt generated by X.
Used in the mass derivative, covariance, and split spatial-moment formulas. -/
def tiltedMean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (m : ℝ) : ℝ :=
  (∫ ω, Y ω * Real.exp (m * X ω) ∂μ) /
    (∫ ω, Real.exp (m * X ω) ∂μ)

/-- Polynomial weights are dominated by exponential ones: `|x| ^ j ≤ j! / c ^ j * exp (c |x|)`. -/
theorem abs_pow_le_mul_exp {c : ℝ} (hc : 0 < c) (x : ℝ) (j : ℕ) :
    |x| ^ j ≤ j.factorial / c ^ j * Real.exp (c * |x|) := by
  have h := Real.pow_div_factorial_le_exp (c * |x|) (by positivity) j
  rw [div_le_iff₀ (by positivity), mul_pow] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- Any strictly smaller exponential rate absorbs a polynomial weight. -/
theorem integrable_abs_mul_pow_mul_exp_abs {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) {a b : ℝ}
    (hb : b < a) (hint : Integrable (fun ω => |Y ω| * Real.exp (a * |X ω|)) μ) (j : ℕ) :
    Integrable (fun ω => |Y ω| * |X ω| ^ j * Real.exp (b * |X ω|)) μ := by
  refine (hint.const_mul (j.factorial / (a - b) ^ j)).mono' (by fun_prop)
    (.of_forall fun ω => ?_)
  have h := abs_pow_le_mul_exp (sub_pos.2 hb) (X ω) j
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc |Y ω| * |X ω| ^ j * Real.exp (b * |X ω|)
      ≤ |Y ω| * (j.factorial / (a - b) ^ j * Real.exp ((a - b) * |X ω|)) *
          Real.exp (b * |X ω|) := by gcongr
    _ = j.factorial / (a - b) ^ j * (|Y ω| * Real.exp (a * |X ω|)) := by
        rw [mul_assoc, mul_assoc, ← Real.exp_add]; ring_nf

theorem mul_le_abs_mul_abs_of_le {m b x : ℝ} (h : |m| ≤ b) : m * x ≤ b * |x| :=
  (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right h (abs_nonneg x))

/-- Weighted polynomial moments under an exponential tilt of rate below the envelope rate. -/
theorem integrable_mul_pow_mul_exp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) {a m : ℝ}
    (hm : |m| < a) (hint : Integrable (fun ω => |Y ω| * Real.exp (a * |X ω|)) μ) (j : ℕ) :
    Integrable (fun ω => Y ω * X ω ^ j * Real.exp (m * X ω)) μ := by
  refine (integrable_abs_mul_pow_mul_exp_abs hX hY hm hint j).mono' (by fun_prop)
    (.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_abs_mul_abs_of_le le_rfl))
    (by positivity)

/-- Differentiation of a weighted exponential moment under the integral sign. -/
theorem hasDerivAt_integral_mul_exp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) {a m : ℝ}
    (hm : |m| < a) (hint : Integrable (fun ω => |Y ω| * Real.exp (a * |X ω|)) μ) :
    HasDerivAt (fun m => ∫ ω, Y ω * Real.exp (m * X ω) ∂μ)
      (∫ ω, Y ω * X ω * Real.exp (m * X ω) ∂μ) m := by
  set ε := (a - |m|) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  have hb : |m| + ε < a := by simp only [ε]; linarith
  have hball : ∀ x ∈ Metric.ball m ε, |x| ≤ |m| + ε := fun x hx => by
    rw [Metric.mem_ball, Real.dist_eq] at hx
    linarith [abs_sub_abs_le_abs_sub x m]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds m hε)
    (F := fun x ω => Y ω * Real.exp (x * X ω))
    (F' := fun x ω => Y ω * X ω * Real.exp (x * X ω))
    (.of_forall fun x => by fun_prop)
    (by simpa using integrable_mul_pow_mul_exp hX hY hm hint 0) (by fun_prop)
    (bound := fun ω => |Y ω| * |X ω| ^ 1 * Real.exp ((|m| + ε) * |X ω|))
    (.of_forall fun ω x hx => ?_) (integrable_abs_mul_pow_mul_exp_abs hX hY hb hint 1)
    (.of_forall fun ω x _ => ?_)).2
  · simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), pow_one]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_abs_mul_abs_of_le
      (hball x hx))) (by positivity)
  · have := (((hasDerivAt_id x).mul_const (X ω)).exp).const_mul (Y ω)
    convert! this using 1
    simp; ring

/-- Local exponential domination supplies every polynomially weighted moment needed below. -/
theorem integrable_pow_mul_exp_of_exp_abs {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : Measurable X)
    {a m : ℝ} (hm : |m| < a)
    (hint : Integrable (fun ω => Real.exp (a * |X ω|)) μ) (j : ℕ) :
    Integrable (fun ω => X ω ^ j * Real.exp (m * X ω)) μ := by
  simpa using integrable_mul_pow_mul_exp (Y := fun _ => (1 : ℝ)) hX.aestronglyMeasurable
    aestronglyMeasurable_const hm (by simpa using hint) j

/-- The exponential moment and its derivative, from the exponential envelope. -/
theorem hasDerivAt_integral_exp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : Measurable X) {a m : ℝ} (hm : |m| < a)
    (hint : Integrable (fun ω => Real.exp (a * |X ω|)) μ) :
    HasDerivAt (fun m => ∫ ω, Real.exp (m * X ω) ∂μ) (∫ ω, X ω * Real.exp (m * X ω) ∂μ) m := by
  simpa using hasDerivAt_integral_mul_exp (Y := fun _ => (1 : ℝ)) hX.aestronglyMeasurable
    aestronglyMeasurable_const hm (by simpa using hint)

theorem integral_exp_mul_pos {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) {a m : ℝ} (hm : |m| < a)
    (hint : Integrable (fun ω => Real.exp (a * |X ω|)) μ) :
    0 < ∫ ω, Real.exp (m * X ω) ∂μ :=
  integral_exp_pos (by simpa using integrable_pow_mul_exp_of_exp_abs hX hm hint 0)

/-- The derivative of the log exponential moment is the tilted mean of X.
Analytic input for `hasDerivAt_massTransform`. -/
theorem hasDerivAt_logLaplace {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) {a m : ℝ} (hm : |m| < a)
    (hint : Integrable (fun ω => Real.exp (a * |X ω|)) μ) :
    HasDerivAt (logLaplace μ X) (tiltedMean μ X X m) m := by
  exact (hasDerivAt_integral_exp hX hm hint).log (integral_exp_mul_pos hX hm hint).ne'

/-- Differentiating a tilted expectation gives a covariance. -/
theorem hasDerivAt_tiltedMean {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) {a m : ℝ} (hm : |m| < a)
    (hXint : Integrable (fun ω => Real.exp (a * |X ω|)) μ)
    (hYint : Integrable (fun ω => |Y ω| * Real.exp (a * |X ω|)) μ) :
    HasDerivAt (tiltedMean μ X Y)
      (tiltedMean μ X (fun ω => Y ω * X ω) m -
        tiltedMean μ X Y m * tiltedMean μ X X m) m := by
  have hZ := integral_exp_mul_pos hX hm hXint
  have h := (hasDerivAt_integral_mul_exp hX.aestronglyMeasurable hY.aestronglyMeasurable hm
    hYint).div (hasDerivAt_integral_exp hX hm hXint) hZ.ne'
  convert! h using 1
  simp only [tiltedMean]
  generalize (∫ ω, Real.exp (m * X ω) ∂μ) = Z at hZ ⊢
  generalize (∫ ω, Y ω * X ω * Real.exp (m * X ω) ∂μ) = A
  generalize (∫ ω, Y ω * Real.exp (m * X ω) ∂μ) = B
  generalize (∫ ω, X ω * Real.exp (m * X ω) ∂μ) = C
  field_simp

/-- The mass derivative away from zero, in entropy form. -/
theorem hasDerivAt_massTransform {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) {a m : ℝ} (hm : |m| < a) (hm0 : m ≠ 0)
    (hint : Integrable (fun ω => Real.exp (a * |X ω|)) μ) :
    HasDerivAt (massTransform μ X)
      ((m * tiltedMean μ X X m - logLaplace μ X m) / m ^ 2) m := by
  have h := (hasDerivAt_logLaplace hX hm hint).div (hasDerivAt_id m) hm0
  refine (h.congr_of_eventuallyEq ?_).congr_deriv (by simp only [id]; ring)
  filter_upwards [eventually_ne_nhds hm0] with x hx
  simp [massTransform, hx]

/-- The tilted mean of `X` has derivative the tilted variance. -/
theorem hasDerivAt_tiltedMean_self {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) {a m : ℝ} (hm : |m| < a)
    (hint : Integrable (fun ω => Real.exp (a * |X ω|)) μ) :
    HasDerivAt (tiltedMean μ X X)
      (tiltedMean μ X (fun ω => X ω ^ 2) m - tiltedMean μ X X m ^ 2) m := by
  set b := (|m| + a) / 2
  have hmb : |m| < b := by simp only [b]; linarith
  have hba : b < a := by simp only [b]; linarith
  have h1 := integrable_abs_mul_pow_mul_exp_abs (Y := fun _ => (1 : ℝ)) hX.aestronglyMeasurable
    aestronglyMeasurable_const hba (by simpa using hint)
  have := hasDerivAt_tiltedMean hX hX hmb (by simpa using h1 0) (by simpa using h1 1)
  convert! this using 2
  · simp only [pow_two]
  · ring

/-- At zero mass the derivative is half the variance, with no division by zero. -/
theorem hasDerivAt_massTransform_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) {a : ℝ} (ha : 0 < a)
    (hint : Integrable (fun ω => Real.exp (a * |X ω|)) μ) :
    HasDerivAt (massTransform μ X)
      (((∫ ω, X ω ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2) / 2) 0 := by
  have h0 : |(0 : ℝ)| < a := by simpa using ha
  have hT0 : tiltedMean μ X X 0 = ∫ ω, X ω ∂μ := by simp [tiltedMean]
  have hT20 : tiltedMean μ X (fun ω => X ω ^ 2) 0 = ∫ ω, X ω ^ 2 ∂μ := by simp [tiltedMean]
  have hL0 : logLaplace μ X 0 = 0 := by simp [logLaplace]
  have hT := hasDerivAt_tiltedMean_self hX h0 hint
  rw [hT0, hT20] at hT
  set V := (∫ ω, X ω ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2
  set E := ∫ ω, X ω ∂μ
  have hnear : ∀ᶠ x in 𝓝 (0 : ℝ), |x| < a :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds h0
  have hf : ∀ᶠ x in 𝓝[≠] (0 : ℝ), HasDerivAt (fun x => logLaplace μ X x - E * x)
      (tiltedMean μ X X x - E) x := by
    filter_upwards [nhdsWithin_le_nhds hnear] with x hx
    convert! (hasDerivAt_logLaplace hX hx hint).sub
      ((hasDerivAt_id x).const_mul E) using 1 <;> simp
  have hg : ∀ᶠ x in 𝓝[≠] (0 : ℝ), HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x :=
    .of_forall fun x => by simpa using hasDerivAt_pow 2 x
  have hg' : ∀ᶠ x in 𝓝[≠] (0 : ℝ), 2 * x ≠ 0 :=
    eventually_mem_nhdsWithin.mono fun x hx => mul_ne_zero two_ne_zero hx
  have hfc : Tendsto (fun x => logLaplace μ X x - E * x) (𝓝[≠] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun x => logLaplace μ X x - E * x) 0 :=
      (hasDerivAt_logLaplace hX h0 hint).continuousAt.sub (continuousAt_const.mul continuousAt_id)
    have := hc.tendsto
    simp only [hL0, mul_zero, sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hgc : Tendsto (fun x : ℝ => x ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => x ^ 2) (𝓝 0) (𝓝 0) := by
      simpa using ((continuous_pow 2).tendsto (0 : ℝ))
    exact this.mono_left nhdsWithin_le_nhds
  have hdiv : Tendsto (fun x => (tiltedMean μ X X x - E) / (2 * x)) (𝓝[≠] 0) (𝓝 (V / 2)) := by
    have := (hasDerivAt_iff_tendsto_slope.1 hT).div_const 2
    refine this.congr' (eventually_mem_nhdsWithin.mono fun x hx => ?_)
    rw [slope_def_field, hT0, sub_zero]
    field_simp
  have hlim := HasDerivAt.lhopital_zero_nhdsNE hf hg hg' hfc hgc hdiv
  rw [hasDerivAt_iff_tendsto_slope]
  refine hlim.congr' (eventually_mem_nhdsWithin.mono fun x hx => ?_)
  have hx' : x ≠ 0 := hx
  rw [slope_def_field]
  simp only [massTransform, hx', if_false, if_true, sub_zero]
  field_simp
  rw [mul_comm]

/-- Explicit second mass derivative for quantitative Taylor control. -/
theorem hasDerivAt_massTransform_deriv {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) {a m : ℝ} (hm : |m| < a) (hm0 : m ≠ 0)
    (hint : Integrable (fun ω => Real.exp (a * |X ω|)) μ) :
    HasDerivAt (deriv (massTransform μ X))
      ((tiltedMean μ X (fun ω => X ω ^ 2) m - (tiltedMean μ X X m) ^ 2) / m -
        2 * tiltedMean μ X X m / m ^ 2 + 2 * logLaplace μ X m / m ^ 3) m := by
  have hev : deriv (massTransform μ X) =ᶠ[𝓝 m]
      fun x => (x * tiltedMean μ X X x - logLaplace μ X x) / x ^ 2 := by
    have hopen : IsOpen {x : ℝ | |x| < a ∧ x ≠ 0} :=
      (isOpen_lt continuous_abs continuous_const).inter isOpen_ne
    filter_upwards [hopen.mem_nhds ⟨hm, hm0⟩] with x hx
    exact (hasDerivAt_massTransform hX hx.1 hx.2 hint).deriv
  have hT := hasDerivAt_tiltedMean_self hX hm hint
  have hL := hasDerivAt_logLaplace hX hm hint
  have h := (((hasDerivAt_id m).mul hT).sub hL).div ((hasDerivAt_id m).pow 2)
    (pow_ne_zero 2 hm0)
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [id, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply]
  field_simp
  ring

/-- Centering removes a possibly unbounded additive external field from mass derivatives. -/
theorem massTransform_add_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) (hXi : Integrable X μ) {m : ℝ}
    (hint : Integrable (fun ω => Real.exp (m * X ω)) μ) (c : ℝ) :
    massTransform μ (fun ω => X ω + c) m = massTransform μ X m + c := by
  unfold massTransform
  split_ifs with hm
  · rw [integral_add hXi (integrable_const c)]; simp
  · have hpos : 0 < ∫ ω, Real.exp (m * X ω) ∂μ := integral_exp_pos hint
    unfold logLaplace
    have : (fun ω => Real.exp (m * (X ω + c))) =
        fun ω => Real.exp (m * c) * Real.exp (m * X ω) := by
      ext ω; rw [← Real.exp_add]; ring_nf
    rw [this, integral_const_mul, Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp]
    field_simp
    ring

/-- Removable singularities: the difference quotient of an analytic function is analytic. -/
theorem analyticAt_dslope {f : ℝ → ℝ} {a x : ℝ} (hf : AnalyticAt ℝ f x)
    (ha : AnalyticAt ℝ f a) : AnalyticAt ℝ (dslope f a) x := by
  rcases eq_or_ne x a with rfl | hx
  · obtain ⟨p, hp⟩ := ha
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  · have h : AnalyticAt ℝ (fun y => (y - a)⁻¹ * (f y - f a)) x :=
      ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 hx)).mul
        (hf.sub analyticAt_const)
    refine h.congr ?_
    filter_upwards [eventually_ne_nhds hx] with y hy
    rw [dslope_of_ne _ hy, slope_def_field, div_eq_inv_mul]

/-- A layer is the difference quotient at zero of the cumulant generating function. -/
theorem massTransform_eq_dslope_cgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (h0 : 0 ∈ interior (integrableExpSet X μ)) :
    massTransform μ X = dslope (cgf X μ) 0 := by
  ext m
  rcases eq_or_ne m 0 with rfl | hm
  · rw [dslope_same, deriv_cgf_zero h0]; simp [massTransform]
  · rw [dslope_of_ne _ hm, slope_def_field]
    simp [massTransform, hm, logLaplace, cgf, mgf]

/-- Exponential envelopes make a layer real analytic in the mass, including at zero. -/
theorem analyticOnNhd_massTransform {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) {a : ℝ}
    (hint : Integrable (fun ω => Real.exp (a * |X ω|)) μ) :
    AnalyticOnNhd ℝ (massTransform μ X) (Ioo (-a) a) := by
  have hsub : Ioo (-a) a ⊆ interior (integrableExpSet X μ) :=
    interior_maximal (fun t ht => by
      simpa [integrableExpSet, mgf] using
        integrable_pow_mul_exp_of_exp_abs hX (abs_lt.2 ht) hint 0) isOpen_Ioo
  intro m hm
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet X μ) := hsub ⟨by linarith [hm.1, hm.2],
    by linarith [hm.1, hm.2]⟩
  rw [massTransform_eq_dslope_cgf h0]
  exact analyticAt_dslope (analyticAt_cgf (hsub hm)) (analyticAt_cgf h0)

/-- The tilted variance has derivative the tilted third cumulant. -/
theorem hasDerivAt_tiltedVariance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) {a m : ℝ} (hm : |m| < a)
    (hint : Integrable (fun ω => Real.exp (a * |X ω|)) μ) :
    HasDerivAt (fun t => tiltedMean μ X (fun ω => X ω ^ 2) t - tiltedMean μ X X t ^ 2)
      (tiltedMean μ X (fun ω => X ω ^ 3) m -
        3 * tiltedMean μ X (fun ω => X ω ^ 2) m * tiltedMean μ X X m +
        2 * tiltedMean μ X X m ^ 3) m := by
  set b := (|m| + a) / 2
  have hmb : |m| < b := by simp only [b]; linarith
  have hba : b < a := by simp only [b]; linarith
  have h1 := integrable_abs_mul_pow_mul_exp_abs (Y := fun _ => (1 : ℝ)) hX.aestronglyMeasurable
    aestronglyMeasurable_const hba (by simpa using hint)
  have h2 := hasDerivAt_tiltedMean hX (hX.pow_const 2) hmb (by simpa using h1 0)
    (by simpa using h1 2)
  have h3 := hasDerivAt_tiltedMean_self hX hm hint
  have e : (fun ω => X ω ^ 2 * X ω) = fun ω => X ω ^ 3 := by ext ω; ring
  rw [e] at h2
  convert! h2.sub (h3.pow 2) using 1
  simp only [Nat.cast_ofNat]; ring

/-- Tilted polynomial moments are controlled by a nonnegative envelope, uniformly for
masses in `[0, 1]`. -/
theorem abs_tiltedMean_pow_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : ∀ᵐ ω ∂μ, |X ω| ≤ Y ω)
    (hint : Integrable (fun ω => Real.exp (2 * Y ω)) μ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (k : ℕ) :
    |tiltedMean μ X (fun ω => X ω ^ k) m| ≤
      (∫ ω, Y ω ^ k * Real.exp (Y ω) ∂μ) / ∫ ω, Real.exp (-Y ω) ∂μ := by
  obtain ⟨hm0, hm1⟩ := hm
  have hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω := hXY.mono fun ω h => (abs_nonneg _).trans h
  have iY : ∀ j : ℕ, Integrable (fun ω => Y ω ^ j * Real.exp (Y ω)) μ := fun j => by
    refine (hint.const_mul (j.factorial : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [hY0] with ω hω
    have h := Real.pow_div_factorial_le_exp (Y ω) hω j
    rw [div_le_iff₀ (by positivity)] at h
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      show 2 * Y ω = Y ω + Y ω by ring, Real.exp_add]
    calc Y ω ^ j * Real.exp (Y ω) ≤ Real.exp (Y ω) * j.factorial * Real.exp (Y ω) := by gcongr
      _ = _ := by ring
  have ieY : Integrable (fun ω => Real.exp (-Y ω)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [hY0] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hle : ∀ᵐ ω ∂μ, m * X ω ≤ Y ω ∧ -Y ω ≤ m * X ω := by
    filter_upwards [hXY, hY0] with ω h h0
    have h1 : |m * X ω| ≤ Y ω := by
      rw [abs_mul, abs_of_nonneg hm0]
      nlinarith [abs_nonneg (X ω)]
    exact ⟨(le_abs_self _).trans h1, by linarith [neg_abs_le (m * X ω)]⟩
  have hbound : ∀ᵐ ω ∂μ, ‖X ω ^ k * Real.exp (m * X ω)‖ ≤ Y ω ^ k * Real.exp (Y ω) := by
    filter_upwards [hXY, hle] with ω h h'
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h k) (Real.exp_le_exp.2 h'.1)
      (Real.exp_pos _).le (pow_nonneg ((abs_nonneg _).trans h) k)
  have iN : Integrable (fun ω => X ω ^ k * Real.exp (m * X ω)) μ :=
    (iY k).mono' (by fun_prop) hbound
  have iZ : Integrable (fun ω => Real.exp (m * X ω)) μ := by
    refine (iY 0).mono' (by fun_prop) ?_
    filter_upwards [hle] with ω h
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_zero, one_mul]
    exact Real.exp_le_exp.2 h.1
  have hZ : ∫ ω, Real.exp (-Y ω) ∂μ ≤ ∫ ω, Real.exp (m * X ω) ∂μ :=
    integral_mono_ae ieY iZ (hle.mono fun ω h => Real.exp_le_exp.2 h.2)
  have hZ0 : 0 < ∫ ω, Real.exp (-Y ω) ∂μ := integral_exp_pos ieY
  have hN : |∫ ω, X ω ^ k * Real.exp (m * X ω) ∂μ| ≤ ∫ ω, Y ω ^ k * Real.exp (Y ω) ∂μ :=
    abs_integral_le_integral_abs.trans (integral_mono_ae iN.abs (iY k) (hbound.mono
      fun ω h => by simpa [Real.norm_eq_abs] using h))
  rw [tiltedMean, abs_div, abs_of_pos (hZ0.trans_le hZ)]
  exact div_le_div₀ ((abs_nonneg _).trans hN) hN hZ0 hZ

/-- The second mass derivative of a layer is bounded by any bound on the tilted third cumulant
over `[0, 1]`, including at zero mass. -/
theorem abs_deriv_deriv_massTransform_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hXY : ∀ᵐ ω ∂μ, |X ω| ≤ Y ω)
    (hint : Integrable (fun ω => Real.exp (2 * Y ω)) μ) {K : ℝ}
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, |tiltedMean μ X (fun ω => X ω ^ 3) t -
        3 * tiltedMean μ X (fun ω => X ω ^ 2) t * tiltedMean μ X X t +
        2 * tiltedMean μ X X t ^ 3| ≤ K)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    |deriv (deriv (massTransform μ X)) m| ≤ K := by
  have hint2 : Integrable (fun ω => Real.exp (2 * |X ω|)) μ := by
    refine hint.mono' (by fun_prop) ?_
    filter_upwards [hXY] with ω h
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ⟨le_rfl, zero_le_one⟩)
  have hana := analyticOnNhd_massTransform hX hint2
  have hgc : ContinuousOn (deriv (deriv (massTransform μ X))) (Ioo (-2) 2) :=
    hana.deriv.deriv.continuousOn
  have hpos : ∀ m ∈ Ioc (0 : ℝ) 1, |deriv (deriv (massTransform μ X)) m| ≤ K := by
    rintro m ⟨hm0, hm1⟩
    have hm2 : |m| < 2 := by rw [abs_of_pos hm0]; linarith
    rw [(hasDerivAt_massTransform_deriv hX hm2 hm0.ne' hint2).deriv]
    set φ : ℝ → ℝ := fun t => t ^ 2 * (tiltedMean μ X (fun ω => X ω ^ 2) t -
      tiltedMean μ X X t ^ 2) - 2 * t * tiltedMean μ X X t + 2 * logLaplace μ X t
    have hφ : ∀ t, |t| < 2 → HasDerivAt φ (t ^ 2 * (tiltedMean μ X (fun ω => X ω ^ 3) t -
        3 * tiltedMean μ X (fun ω => X ω ^ 2) t * tiltedMean μ X X t +
        2 * tiltedMean μ X X t ^ 3)) t := by
      intro t ht
      have h1 := hasDerivAt_tiltedVariance hX ht hint2
      have h2 := hasDerivAt_tiltedMean_self hX ht hint2
      have h3 := hasDerivAt_logLaplace hX ht hint2
      convert! (((hasDerivAt_pow 2 t).mul h1).sub (((hasDerivAt_id t).const_mul 2).mul h2)).add
        (h3.const_mul 2) using 1
      simp only [id, Nat.cast_ofNat]; ring
    have hφ0 : φ 0 = 0 := by simp [φ, logLaplace]
    have hmvt := (convex_Icc 0 m).norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ)
      (C := K * m ^ 2) (fun t ht => (hφ t (by
        rw [abs_of_nonneg ht.1]; linarith [ht.2])).hasDerivWithinAt) (fun t ht => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t), mul_comm]
        exact mul_le_mul (hK t ⟨ht.1, ht.2.trans hm1⟩) (pow_le_pow_left₀ ht.1 ht.2 2)
          (sq_nonneg _) hK0) ⟨le_rfl, hm0.le⟩ ⟨hm0.le, le_rfl⟩
    rw [hφ0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hm0] at hmvt
    have e : (tiltedMean μ X (fun ω => X ω ^ 2) m - tiltedMean μ X X m ^ 2) / m -
        2 * tiltedMean μ X X m / m ^ 2 + 2 * logLaplace μ X m / m ^ 3 = φ m / m ^ 3 := by
      simp only [φ]; field_simp
    rw [e, abs_div, abs_of_pos (pow_pos hm0 3), div_le_iff₀ (pow_pos hm0 3)]
    linarith
  rcases eq_or_lt_of_le hm.1 with rfl | hm0
  · have hc : ContinuousAt (deriv (deriv (massTransform μ X))) 0 :=
      hgc.continuousAt (Ioo_mem_nhds (by norm_num) (by norm_num))
    have ht : Tendsto (fun t => |deriv (deriv (massTransform μ X)) t|) (𝓝[>] (0 : ℝ))
        (𝓝 |deriv (deriv (massTransform μ X)) 0|) :=
      hc.tendsto.abs.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    exact hpos t ⟨ht.1, ht.2.le⟩
  · exact hpos m ⟨hm0, hm.2⟩

/-- Uniform mass Taylor constants from a common centered envelope, including mass
zero. The constant is independent of X and its additive center c. This is the
single-layer analytic input for the uniform bounds around (14.265). -/
theorem uniform_mass_second_derivative_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : Measurable Y) (hYnonneg : ∀ᵐ ω ∂μ, 0 ≤ Y ω)
    (hint : Integrable (fun ω => Real.exp (2 * Y ω)) μ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (X : Ω → ℝ) (c : ℝ), Measurable X →
      (∀ᵐ ω ∂μ, |X ω - c| ≤ Y ω) →
      ContDiffOn ℝ 2 (massTransform μ X) (Icc (0 : ℝ) 1) ∧
        ∀ m ∈ Icc (0 : ℝ) 1, |deriv (deriv (massTransform μ X)) m| ≤ M := by
  set B : ℕ → ℝ := fun k => (∫ ω, Y ω ^ k * Real.exp (Y ω) ∂μ) / ∫ ω, Real.exp (-Y ω) ∂μ
  have hB0 : ∀ k, 0 ≤ B k := fun k => div_nonneg
    (integral_nonneg_of_ae (hYnonneg.mono fun ω h => by positivity))
    (integral_nonneg fun ω => (Real.exp_pos _).le)
  set K := B 3 + 3 * B 2 * B 1 + 2 * B 1 ^ 3
  have hK0 : 0 ≤ K := by have := hB0 1; have := hB0 2; have := hB0 3; positivity
  refine ⟨K + 1, by linarith, fun X c hX hXc => ?_⟩
  set X' : Ω → ℝ := fun ω => X ω - c
  have hX' : Measurable X' := hX.sub_const c
  have hint2 : Integrable (fun ω => Real.exp (2 * |X' ω|)) μ := by
    refine hint.mono' (by fun_prop) ?_
    filter_upwards [hXc] with ω h
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith)
  have hX'i : Integrable X' μ := by
    simpa using integrable_pow_mul_exp_of_exp_abs hX' (m := 0) (by norm_num) hint2 1
  have heq : EqOn (massTransform μ X) (fun m => massTransform μ X' m + c) (Ioo (-2) 2) := by
    intro m hm
    have := massTransform_add_const hX' hX'i
      (by simpa using integrable_pow_mul_exp_of_exp_abs hX' (abs_lt.2 hm) hint2 0) c
    simpa [X'] using this
  have hana := analyticOnNhd_massTransform hX' hint2
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-2) 2 := fun m hm => ⟨by linarith [hm.1], by linarith [hm.2]⟩
  refine ⟨((hana.contDiffOn_of_completeSpace.add contDiffOn_const).mono hsub).congr
    fun m hm => heq (hsub hm), fun m hm => ?_⟩
  have hev : massTransform μ X =ᶠ[𝓝 m] fun y => massTransform μ X' y + c :=
    heq.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds (hsub hm))
  have hd : deriv (massTransform μ X) =ᶠ[𝓝 m] deriv (massTransform μ X') := by
    filter_upwards [hev.eventuallyEq_nhds] with y hy
    rw [hy.deriv_eq, deriv_add_const]
  rw [hd.deriv_eq]
  refine (abs_deriv_deriv_massTransform_le (K := K) hX' hXc hint
    (fun t ht => ?_) hm).trans (by linarith)
  have hb := abs_tiltedMean_pow_le hX' hY hXc hint ht
  have h1 : |tiltedMean μ X' X' t| ≤ B 1 := by
    have := hb 1
    rwa [show (fun ω => X' ω ^ 1) = X' from funext fun ω => pow_one _] at this
  have h2 : |tiltedMean μ X' (fun ω => X' ω ^ 2) t| ≤ B 2 := hb 2
  have h3 : |tiltedMean μ X' (fun ω => X' ω ^ 3) t| ≤ B 3 := hb 3
  calc _ ≤ |tiltedMean μ X' (fun ω => X' ω ^ 3) t| +
        3 * |tiltedMean μ X' (fun ω => X' ω ^ 2) t| * |tiltedMean μ X' X' t| +
        2 * |tiltedMean μ X' X' t| ^ 3 := by
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ((abs_sub _ _).trans ?_) ?_
        · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
        · rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ K := by
        have := abs_nonneg (tiltedMean μ X' X' t)
        have := abs_nonneg (tiltedMean μ X' (fun ω => X' ω ^ 2) t)
        simp only [K]
        gcongr

/-- Gaussian increments supply centered envelopes without any assumption on the
additive external field. The variance may be zero. -/
theorem integrable_gaussian_exp_abs (a : ℝ) (v : ℝ≥0) :
    Integrable (fun z : ℝ => Real.exp (a * |z|)) (gaussianReal 0 v) := by
  refine ((integrable_exp_mul_gaussianReal a).add (integrable_exp_mul_gaussianReal (-a))).mono'
    (by fun_prop) (.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]; simp only [Pi.add_apply]; linarith [Real.exp_pos (-a * z)]
  · rw [abs_of_nonpos hz]; simp only [Pi.add_apply]
    have : a * -z = -a * z := by ring
    rw [this]; linarith [Real.exp_pos (a * z)]

/-- A layer is nonexpansive for uniformly close inputs, including zero mass. -/
theorem abs_massTransform_sub_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X μ) (hYi : Integrable Y μ) {m c : ℝ}
    (hm : 0 ≤ m) (hc : 0 ≤ c)
    (hXe : Integrable (fun ω => Real.exp (m * X ω)) μ)
    (hYe : Integrable (fun ω => Real.exp (m * Y ω)) μ)
    (hclose : ∀ᵐ ω ∂μ, |X ω - Y ω| ≤ c) :
    |massTransform μ X m - massTransform μ Y m| ≤ c := by
  unfold massTransform
  split_ifs with hm0
  · rw [← integral_sub hXi hYi]
    refine abs_integral_le_integral_abs.trans ?_
    calc (∫ ω, |X ω - Y ω| ∂μ) ≤ ∫ _, c ∂μ :=
          integral_mono_ae (hXi.sub hYi).abs (integrable_const c) hclose
      _ = c := by simp
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  have key : ∀ X Y : Ω → ℝ, Integrable (fun ω => Real.exp (m * X ω)) μ →
      Integrable (fun ω => Real.exp (m * Y ω)) μ → (∀ᵐ ω ∂μ, X ω - Y ω ≤ c) →
      logLaplace μ X m / m - logLaplace μ Y m / m ≤ c := by
    intro X Y hXe hYe h
    have hXp := integral_exp_pos hXe
    have hYp := integral_exp_pos hYe
    rw [← sub_div, div_le_iff₀ hmpos, logLaplace, logLaplace, sub_le_iff_le_add,
      ← Real.log_exp (c * m), ← Real.log_mul (Real.exp_pos _).ne' hYp.ne']
    refine Real.log_le_log hXp ?_
    rw [← integral_const_mul]
    refine integral_mono_ae hXe (hYe.const_mul _) (h.mono fun ω hω => ?_)
    dsimp only
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  rw [abs_sub_le_iff]
  exact ⟨key X Y hXe hYe (hclose.mono fun ω h => (abs_le.1 h).2),
    key Y X hYe hXe (hclose.mono fun ω h => by linarith [(abs_le.1 h).1])⟩

/-- Differentiate under the external-field integral on an admissible closed interval.
Only domination of the derivative and integrability at one base point are needed. -/
theorem hasDerivWithinAt_integral_Icc {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F D : ℝ → Ω → ℝ} {a b t : ℝ} {g : Ω → ℝ}
    (hab : a < b) (ht : t ∈ Icc a b)
    (hF : ∀ s ∈ Icc a b, AEStronglyMeasurable (F s) μ)
    (hD : AEStronglyMeasurable (D t) μ)
    (hbase : Integrable (F a) μ) (hg : Integrable g μ)
    (hderiv : ∀ᵐ ω ∂μ, ∀ s ∈ Icc a b,
      HasDerivWithinAt (fun u => F u ω) (D s ω) (Icc a b) s)
    (hbound : ∀ᵐ ω ∂μ, ∀ s ∈ Icc a b, |D s ω| ≤ g ω) :
    HasDerivWithinAt (fun s => ∫ ω, F s ω ∂μ) (∫ ω, D t ω ∂μ) (Icc a b) t := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hlip : ∀ᵐ ω ∂μ, ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |F u ω - F v ω| ≤ g ω * |u - v| := by
    filter_upwards [hderiv, hbound] with ω h1 h2 u hu v hv
    simpa [Real.norm_eq_abs] using (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u => F u ω) (C := g ω) h1 (fun s hs => by simpa using h2 s hs) hv hu
  have hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω := hbound.mono fun ω h => (abs_nonneg _).trans (h a ha)
  have hint : ∀ u ∈ Icc a b, Integrable (F u) μ := by
    intro u hu
    refine (hbase.abs.add (hg.mul_const (b - a))).mono' (hF u hu) ?_
    filter_upwards [hlip, hg0] with ω hω hg0
    have h1 := hω u hu a ha
    have hua : |u - a| ≤ b - a := by rw [abs_of_nonneg (by linarith [hu.1])]; linarith [hu.2]
    rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (F u ω) (F a ω)
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left hua hg0]
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hslope : ∀ u ∈ Icc a b, slope (fun s => ∫ ω, F s ω ∂μ) t u =
      ∫ ω, (u - t)⁻¹ * (F u ω - F t ω) ∂μ := by
    intro u hu
    rw [slope_def_field, integral_const_mul, integral_sub (hint u hu) (hint t ht), div_eq_inv_mul]
  have hev : ∀ᶠ u in 𝓝[Icc a b \ {t}] t, u ∈ Icc a b :=
    eventually_nhdsWithin_of_forall fun u hu => hu.1
  refine Tendsto.congr' (hev.mono fun u hu => (hslope u hu).symm) ?_
  refine tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hg ?_
  · filter_upwards [hev] with u hu
    exact ((hF u hu).sub (hF t ht)).const_mul _
  · filter_upwards [hev, self_mem_nhdsWithin] with u hu hut
    filter_upwards [hlip] with ω hω
    have hne : u - t ≠ 0 := sub_ne_zero.2 hut.2
    rw [Real.norm_eq_abs, abs_mul, abs_inv, inv_mul_le_iff₀ (abs_pos.2 hne), mul_comm]
    exact hω u hu t ht
  · filter_upwards [hderiv] with ω hω
    have := (hasDerivWithinAt_iff_tendsto_slope.1 (hω t ht))
    refine this.congr fun u => ?_
    rw [slope_def_field, div_eq_inv_mul]

namespace Heat

section HeatSemigroup

/-!
# Gaussian heat semigroup calculus

Search tag: `PARISI_LB_HEAT`. Namespace: `SpinGlass.Aristotle.Heat`.
Consumer: the concrete single-layer split formulas in `PARISI_LB_SPLIT`.

General tools about the Gaussian smoothing operator
`heat t f x = ∫ f (x + z) d𝒩(0, t)` acting on continuous functions of exponential type:
integrability, continuity in `(t, x)`, differentiation in `x`, the semigroup law,
a short-time expansion, and a backward differentiation formula in the variance for
time-dependent integrands.
-/

/-- Gaussian smoothing with variance `t` (negative variances are clamped to zero). -/
noncomputable def heat (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, f (x + z) ∂(gaussianReal 0 t.toNNReal)

/-- Uniform exponential-type bound for a family of functions on a parameter set. -/
def UExp (S : Set ℝ) (h : ℝ → ℝ → ℝ) : Prop :=
  ∃ C K : ℝ, ∀ v ∈ S, ∀ y, |h v y| ≤ C * Real.exp (K * |y|)

section UExp

variable {S : Set ℝ} {h g : ℝ → ℝ → ℝ}

theorem UExp.nonneg (hh : UExp S h) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ v ∈ S, ∀ y, |h v y| ≤ C * Real.exp (K * |y|) := by
  obtain ⟨C, K, hb⟩ := hh
  refine ⟨max C 0, max K 0, le_max_right _ _, le_max_right _ _, fun v hv y => ?_⟩
  refine (hb v hv y).trans ?_
  rcases le_total 0 C with hC | hC
  · rw [max_eq_left hC]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))) hC
  · exact (mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le).trans (by positivity)

theorem UExp.mono (hh : UExp S h) {T : Set ℝ} (hT : T ⊆ S) : UExp T h := by
  obtain ⟨C, K, hb⟩ := hh
  exact ⟨C, K, fun v hv => hb v (hT hv)⟩

theorem UExp.of_le (hh : UExp S h) (hle : ∀ v ∈ S, ∀ y, |g v y| ≤ |h v y|) : UExp S g := by
  obtain ⟨C, K, hb⟩ := hh
  exact ⟨C, K, fun v hv y => (hle v hv y).trans (hb v hv y)⟩

theorem UExp.const (c : ℝ) : UExp S (fun _ _ => c) :=
  ⟨|c|, 0, fun _ _ _ => by simp⟩

theorem UExp.add (hh : UExp S h) (hg : UExp S g) : UExp S (fun v y => h v y + g v y) := by
  obtain ⟨C₁, K₁, hC₁, hK₁, h₁⟩ := hh.nonneg
  obtain ⟨C₂, K₂, hC₂, hK₂, h₂⟩ := hg.nonneg
  refine ⟨C₁ + C₂, K₁ + K₂, fun v hv y => ?_⟩
  have e₁ : Real.exp (K₁ * |y|) ≤ Real.exp ((K₁ + K₂) * |y|) :=
    Real.exp_le_exp.2 (by nlinarith [abs_nonneg y])
  have e₂ : Real.exp (K₂ * |y|) ≤ Real.exp ((K₁ + K₂) * |y|) :=
    Real.exp_le_exp.2 (by nlinarith [abs_nonneg y])
  calc |h v y + g v y| ≤ |h v y| + |g v y| := abs_add_le _ _
    _ ≤ C₁ * Real.exp (K₁ * |y|) + C₂ * Real.exp (K₂ * |y|) := add_le_add (h₁ v hv y) (h₂ v hv y)
    _ ≤ C₁ * Real.exp ((K₁ + K₂) * |y|) + C₂ * Real.exp ((K₁ + K₂) * |y|) := by gcongr
    _ = (C₁ + C₂) * Real.exp ((K₁ + K₂) * |y|) := by ring

theorem UExp.neg (hh : UExp S h) : UExp S (fun v y => -h v y) :=
  hh.of_le fun _ _ _ => by rw [abs_neg]

theorem UExp.sub (hh : UExp S h) (hg : UExp S g) : UExp S (fun v y => h v y - g v y) := by
  simpa [sub_eq_add_neg] using hh.add hg.neg

theorem UExp.mul (hh : UExp S h) (hg : UExp S g) : UExp S (fun v y => h v y * g v y) := by
  obtain ⟨C₁, K₁, hC₁, hK₁, h₁⟩ := hh.nonneg
  obtain ⟨C₂, K₂, hC₂, hK₂, h₂⟩ := hg.nonneg
  refine ⟨C₁ * C₂, K₁ + K₂, fun v hv y => ?_⟩
  rw [abs_mul]
  calc |h v y| * |g v y| ≤ (C₁ * Real.exp (K₁ * |y|)) * (C₂ * Real.exp (K₂ * |y|)) :=
        mul_le_mul (h₁ v hv y) (h₂ v hv y) (abs_nonneg _) (by positivity)
    _ = C₁ * C₂ * Real.exp ((K₁ + K₂) * |y|) := by
        rw [add_mul, Real.exp_add]; ring

theorem UExp.const_mul (hh : UExp S h) (c : ℝ) : UExp S (fun v y => c * h v y) :=
  (UExp.const c).mul hh

theorem UExp.mul_const (hh : UExp S h) (c : ℝ) : UExp S (fun v y => h v y * c) :=
  hh.mul (UExp.const c)

theorem UExp.div_const (hh : UExp S h) (c : ℝ) : UExp S (fun v y => h v y / c) := by
  simpa [div_eq_mul_inv] using hh.mul_const c⁻¹

theorem UExp.pow (hh : UExp S h) (n : ℕ) : UExp S (fun v y => h v y ^ n) := by
  induction n with
  | zero => simpa using UExp.const (S := S) 1
  | succ n ih => simpa [pow_succ] using ih.mul hh

end UExp

/-! ## Gaussian integrability and the standard-normal representation -/

theorem integrable_exp_abs_gaussian (c : ℝ) (v : ℝ≥0) :
    Integrable (fun z : ℝ => Real.exp (c * |z|)) (gaussianReal 0 v) := by
  refine ((integrable_exp_mul_gaussianReal c).add (integrable_exp_mul_gaussianReal (-c))).mono'
    (by fun_prop) (.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]; simp only [Pi.add_apply]; linarith [Real.exp_pos (-c * z)]
  · rw [abs_of_nonpos hz]; simp only [Pi.add_apply]
    have : c * -z = -c * z := by ring
    rw [this]; linarith [Real.exp_pos (c * z)]

theorem exp_abs_affine_le {K : ℝ} (hK : 0 ≤ K) (x s z : ℝ) :
    Real.exp (K * |x + s * z|) ≤ Real.exp (K * |x|) * Real.exp (K * |s| * |z|) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : |x + s * z| ≤ |x| + |s| * |z| := (abs_add_le _ _).trans (by rw [abs_mul])
  nlinarith

/-- A continuous function of exponential type composed with an affine map is integrable
against any centered Gaussian. -/
theorem integrable_affine {f : ℝ → ℝ} (hf : Continuous f) {C K : ℝ}
    (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|)) (x s : ℝ) (v : ℝ≥0) :
    Integrable (fun z => f (x + s * z)) (gaussianReal 0 v) := by
  obtain ⟨C', K', hC', hK', hb'⟩ := UExp.nonneg (S := univ) (h := fun _ => f) ⟨C, K, fun _ _ => hb⟩
  refine ((integrable_exp_abs_gaussian (K' * |s|) v).const_mul (C' * Real.exp (K' * |x|))).mono'
    (by fun_prop) (.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  calc |f (x + s * z)| ≤ C' * Real.exp (K' * |x + s * z|) := hb' 0 trivial _
    _ ≤ C' * (Real.exp (K' * |x|) * Real.exp (K' * |s| * |z|)) := by
        gcongr; exact exp_abs_affine_le hK' x s z
    _ = C' * Real.exp (K' * |x|) * Real.exp (K' * |s| * |z|) := by ring

theorem integrable_shift {f : ℝ → ℝ} (hf : Continuous f) {C K : ℝ}
    (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|)) (x : ℝ) (v : ℝ≥0) :
    Integrable (fun z => f (x + z)) (gaussianReal 0 v) := by
  simpa using integrable_affine hf hb x 1 v

theorem gaussianReal_map_sqrt (t : ℝ) :
    (gaussianReal 0 1).map (fun z => Real.sqrt t * z) = gaussianReal 0 t.toNNReal := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp only [NNReal.coe_mk, mul_one, Real.coe_toNNReal']
    rcases le_total 0 t with ht | ht
    · rw [Real.sq_sqrt ht, max_eq_left ht]
    · rw [Real.sqrt_eq_zero'.2 ht, max_eq_right ht]; simp

/-- Representation of `heat` through a standard Gaussian. Valid for every real `t`. -/
theorem heat_eq_std (t : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    heat t f x = ∫ z, f (x + Real.sqrt t * z) ∂(gaussianReal 0 1) := by
  rw [heat, ← gaussianReal_map_sqrt t, integral_map (by fun_prop)
    (by fun_prop : Continuous fun z => f (x + z)).aestronglyMeasurable]

theorem heat_zero {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) : heat 0 f x = f x := by
  rw [heat_eq_std 0 hf]; simp

/-- Dominated convergence for standard-Gaussian integrals of affinely moving integrands. -/
theorem tendsto_integral_std {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {q : ι → ℝ → ℝ} {k : ℝ → ℝ} {x s : ι → ℝ} {x₀ s₀ : ℝ}
    (hx : Tendsto x l (𝓝 x₀)) (hs : Tendsto s l (𝓝 s₀))
    (hmeas : ∀ᶠ i in l, AEStronglyMeasurable (fun z => q i (x i + s i * z)) (gaussianReal 0 1))
    (hbd : ∃ C K : ℝ, ∀ᶠ i in l, ∀ y, |q i y| ≤ C * Real.exp (K * |y|))
    (hlim : ∀ z, Tendsto (fun i => q i (x i + s i * z)) l (𝓝 (k (x₀ + s₀ * z)))) :
    Tendsto (fun i => ∫ z, q i (x i + s i * z) ∂(gaussianReal 0 1)) l
      (𝓝 (∫ z, k (x₀ + s₀ * z) ∂(gaussianReal 0 1))) := by
  obtain ⟨C, K, hbd⟩ := hbd
  set K' := max K 0
  have hK' : 0 ≤ K' := le_max_right _ _
  set C' := max C 0
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => C' * Real.exp (K' * (|x₀| + 1)) * Real.exp (K' * (|s₀| + 1) * |z|)) hmeas ?_
    ((integrable_exp_abs_gaussian _ 1).const_mul _) (.of_forall hlim)
  have hx1 : ∀ᶠ i in l, |x i| ≤ |x₀| + 1 := by
    filter_upwards [(Metric.tendsto_nhds.1 hx) 1 one_pos] with i hi
    rw [Real.dist_eq] at hi
    linarith [abs_sub_abs_le_abs_sub (x i) x₀]
  have hs1 : ∀ᶠ i in l, |s i| ≤ |s₀| + 1 := by
    filter_upwards [(Metric.tendsto_nhds.1 hs) 1 one_pos] with i hi
    rw [Real.dist_eq] at hi
    linarith [abs_sub_abs_le_abs_sub (s i) s₀]
  filter_upwards [hbd, hx1, hs1] with i hi hxi hsi
  refine .of_forall fun z => ?_
  rw [Real.norm_eq_abs]
  have h1 : |q i (x i + s i * z)| ≤ C' * Real.exp (K' * |x i + s i * z|) := by
    refine (hi _).trans ?_
    rcases le_total 0 C with hC | hC
    · exact mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))) (by positivity)
        (le_max_right _ _)
    · exact (mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le).trans (by positivity)
  refine h1.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : |x i + s i * z| ≤ |x i| + |s i| * |z| := (abs_add_le _ _).trans (by rw [abs_mul])
  have : |s i| * |z| ≤ (|s₀| + 1) * |z| := mul_le_mul_of_nonneg_right hsi (abs_nonneg _)
  nlinarith

/-- Joint continuity of the heat operator in the variance and the base point. -/
theorem continuous_heat {f : ℝ → ℝ} (hf : Continuous f) {C K : ℝ}
    (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|)) :
    Continuous (fun p : ℝ × ℝ => heat p.1 f p.2) := by
  have : (fun p : ℝ × ℝ => heat p.1 f p.2) =
      fun p => ∫ z, f (p.2 + Real.sqrt p.1 * z) ∂(gaussianReal 0 1) := by
    funext p; exact heat_eq_std _ hf _
  rw [this, continuous_iff_continuousAt]
  intro p
  refine tendsto_integral_std (q := fun _ => f) (x := fun p : ℝ × ℝ => p.2)
    (s := fun p : ℝ × ℝ => Real.sqrt p.1) continuous_snd.continuousAt
    (Real.continuous_sqrt.comp continuous_fst).continuousAt
    (.of_forall fun _ => (by fun_prop : Continuous _).aestronglyMeasurable)
    ⟨C, K, .of_forall fun _ => hb⟩ fun z => ?_
  exact (hf.comp (continuous_snd.add
    ((Real.continuous_sqrt.comp continuous_fst).mul continuous_const))).continuousAt

/-- Differentiation of the heat operator in the base point. -/
theorem hasDerivAt_heat (t : ℝ) {f f₁ : ℝ → ℝ} (hd : ∀ y, HasDerivAt f (f₁ y) y)
    (hf₁ : Continuous f₁) {C K : ℝ} (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|))
    (hb₁ : ∀ y, |f₁ y| ≤ C * Real.exp (K * |y|)) (x : ℝ) :
    HasDerivAt (heat t f) (heat t f₁ x) x := by
  have hf : Continuous f := continuous_iff_continuousAt.2 fun y => (hd y).continuousAt
  have e1 : heat t f = fun x => ∫ z, f (x + Real.sqrt t * z) ∂(gaussianReal 0 1) := by
    funext x; exact heat_eq_std t hf x
  rw [e1, heat_eq_std t hf₁]
  obtain ⟨C', K', hC', hK', hb'⟩ :=
    UExp.nonneg (S := univ) (h := fun _ => f₁) ⟨C, K, fun _ _ => hb₁⟩
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds x one_pos)
    (F := fun x z => f (x + Real.sqrt t * z)) (F' := fun x z => f₁ (x + Real.sqrt t * z))
    (bound := fun z => C' * Real.exp (K' * (|x| + 1)) * Real.exp (K' * |Real.sqrt t| * |z|))
    (.of_forall fun _ => (by fun_prop : Continuous _).aestronglyMeasurable)
    (integrable_affine hf hb x _ 1) (by fun_prop : Continuous _).aestronglyMeasurable
    (.of_forall fun z y hy => ?_) ((integrable_exp_abs_gaussian _ 1).const_mul _)
    (.of_forall fun z y _ => ?_)).2
  · rw [Real.norm_eq_abs]
    refine (hb' 0 trivial _).trans ?_
    have hy' : |y| ≤ |x| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hy; linarith [abs_sub_abs_le_abs_sub y x]
    calc C' * Real.exp (K' * |y + Real.sqrt t * z|)
        ≤ C' * (Real.exp (K' * |y|) * Real.exp (K' * |Real.sqrt t| * |z|)) := by
          gcongr; exact exp_abs_affine_le hK' _ _ _
      _ ≤ C' * (Real.exp (K' * (|x| + 1)) * Real.exp (K' * |Real.sqrt t| * |z|)) := by
          gcongr
      _ = _ := by ring
  · convert! (hd (y + Real.sqrt t * z)).comp y
      ((hasDerivAt_id y).add_const _) using 1 <;> simp

/-- The semigroup law of Gaussian smoothing. -/
theorem heat_heat {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {f : ℝ → ℝ} (hf : Continuous f)
    {C K : ℝ} (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|)) (x : ℝ) :
    heat s (heat t f) x = heat (s + t) f x := by
  have hconv : gaussianReal 0 (s + t).toNNReal =
      gaussianReal 0 s.toNNReal ∗ gaussianReal 0 t.toNNReal := by
    rw [gaussianReal_conv_gaussianReal, Real.toNNReal_add hs ht, add_zero]
  have hint : Integrable (fun z => f (x + z))
      (gaussianReal 0 s.toNNReal ∗ gaussianReal 0 t.toNNReal) := by
    rw [← hconv]; exact integrable_shift hf hb x _
  rw [heat, heat, hconv, integral_conv hint]
  simp only [heat, add_assoc]

theorem nonneg_of_exp_bound {f : ℝ → ℝ} {C K : ℝ} (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|)) :
    0 ≤ C := by
  have := (abs_nonneg _).trans (hb 0)
  simpa using this

/-- Exponential-type bounds are preserved by the heat operator, uniformly in bounded time. -/
theorem abs_heat_le {f : ℝ → ℝ} (hf : Continuous f) {C K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|)) {t a : ℝ} (hta : t ≤ a) (x : ℝ) :
    |heat t f x| ≤ C * (∫ z, Real.exp (K * Real.sqrt a * |z|) ∂(gaussianReal 0 1)) *
      Real.exp (K * |x|) := by
  have hC := nonneg_of_exp_bound hb
  rw [heat_eq_std t hf]
  refine (abs_integral_le_integral_abs).trans ?_
  calc (∫ z, |f (x + Real.sqrt t * z)| ∂(gaussianReal 0 1))
      ≤ ∫ z, C * Real.exp (K * |x|) * Real.exp (K * Real.sqrt a * |z|) ∂(gaussianReal 0 1) := by
        refine integral_mono (integrable_affine hf hb x _ 1).abs
          ((integrable_exp_abs_gaussian _ 1).const_mul _) fun z => ?_
        refine (hb _).trans ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hC
        refine (exp_abs_affine_le hK x _ z).trans ?_
        gcongr
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt hta
    _ = _ := by rw [integral_const_mul]; ring

theorem uexp_heat {f : ℝ → ℝ} (hf : Continuous f) {C K : ℝ}
    (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|)) (a : ℝ) :
    UExp (Iic a) (fun t y => heat t f y) := by
  obtain ⟨C', K', _, hK', hb'⟩ := UExp.nonneg (S := univ) (h := fun _ => f) ⟨C, K, fun _ _ => hb⟩
  exact ⟨_, _, fun t ht y => abs_heat_le hf hK' (hb' 0 trivial) ht y⟩

/-- A positive lower envelope survives Gaussian smoothing, uniformly in bounded time. -/
theorem heat_lower {g : ℝ → ℝ} (hg : Continuous g) {C K : ℝ}
    (hb : ∀ y, |g y| ≤ C * Real.exp (K * |y|)) {c L : ℝ} (hc : 0 < c) (hL : 0 ≤ L)
    (hlow : ∀ y, c * Real.exp (-(L * |y|)) ≤ g y) (a : ℝ) :
    ∃ c' > 0, ∀ t ≤ a, ∀ y, c' * Real.exp (-(L * |y|)) ≤ heat t g y := by
  set I := ∫ z, Real.exp (-(L * Real.sqrt a) * |z|) ∂(gaussianReal 0 1)
  have hI : 0 < I := integral_exp_pos (integrable_exp_abs_gaussian _ 1)
  refine ⟨c * I, mul_pos hc hI, fun t ht y => ?_⟩
  rw [heat_eq_std t hg]
  calc c * I * Real.exp (-(L * |y|))
      = ∫ z, c * Real.exp (-(L * |y|)) * Real.exp (-(L * Real.sqrt a) * |z|)
          ∂(gaussianReal 0 1) := by rw [integral_const_mul]; ring
    _ ≤ ∫ z, g (y + Real.sqrt t * z) ∂(gaussianReal 0 1) := by
        refine integral_mono ((integrable_exp_abs_gaussian _ 1).const_mul _)
          (integrable_affine hg hb y _ 1) fun z => ?_
        refine le_trans ?_ (hlow _)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hc.le
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have h1 : |y + Real.sqrt t * z| ≤ |y| + Real.sqrt a * |z| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          gcongr
        nlinarith

/-! ## Taylor remainders and the short-time expansion -/

theorem abs_le_of_hasDerivAt_abs_le_aux {G g : ℝ → ℝ} {M : ℝ} {n : ℕ}
    (hG0 : G 0 = 0) (hd : ∀ u, HasDerivAt G (g u) u) {w : ℝ} (hw : 0 ≤ w)
    (hb : ∀ u ∈ Icc 0 w, |g u| ≤ M * |u| ^ n) :
    |G w| ≤ M * |w| ^ (n + 1) / (n + 1) := by
  have key : ∀ σ : ℝ, |σ| ≤ 1 → σ * G w ≤ M * w ^ (n + 1) / (n + 1) := by
    intro σ hσ
    set φ : ℝ → ℝ := fun u => σ * G u - M * u ^ (n + 1) / (n + 1)
    have hφd : ∀ u, HasDerivAt φ (σ * g u - M * u ^ n) u := by
      intro u
      have := ((hd u).const_mul σ).sub (((hasDerivAt_pow (n + 1) u).const_mul M).div_const
        ((n : ℝ) + 1))
      convert! this using 1
      push_cast
      field_simp
    have hφc : Continuous φ := continuous_iff_continuousAt.2 fun u => (hφd u).continuousAt
    have := antitoneOn_of_deriv_nonpos (convex_Icc 0 w) hφc.continuousOn
      (fun u _ => (hφd u).differentiableAt.differentiableWithinAt)
      (by
        rw [interior_Icc]
        intro u hu
        rw [(hφd u).deriv]
        have h1 := hb u (Ioo_subset_Icc_self hu)
        rw [abs_of_pos hu.1] at h1
        have h2 : σ * g u ≤ |g u| := by
          calc σ * g u ≤ |σ * g u| := le_abs_self _
            _ = |σ| * |g u| := abs_mul _ _
            _ ≤ 1 * |g u| := mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
            _ = |g u| := one_mul _
        linarith)
      ⟨le_rfl, hw⟩ ⟨hw, le_rfl⟩ hw
    simp only [φ, hG0, mul_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, not_false_eq_true, zero_pow, zero_div, sub_zero] at this
    linarith
  rw [abs_of_nonneg hw, abs_le]
  constructor
  · have := key (-1) (by norm_num); linarith
  · have := key 1 (by norm_num); linarith

/-- Integrating a derivative bound `|g u| ≤ M |u|^n` from `0`. -/
theorem abs_le_of_hasDerivAt_abs_le {G g : ℝ → ℝ} {M : ℝ} {n : ℕ}
    (hG0 : G 0 = 0) (hd : ∀ u, HasDerivAt G (g u) u) {w : ℝ}
    (hb : ∀ u ∈ uIcc 0 w, |g u| ≤ M * |u| ^ n) :
    |G w| ≤ M * |w| ^ (n + 1) / (n + 1) := by
  rcases le_total 0 w with hw | hw
  · exact abs_le_of_hasDerivAt_abs_le_aux hG0 hd hw fun u hu => hb u (by
      rw [uIcc_of_le hw]; exact hu)
  · have := abs_le_of_hasDerivAt_abs_le_aux (G := fun u => G (-u)) (g := fun u => -g (-u))
      (n := n) (by simpa using hG0)
      (fun u => by convert! (hd (-u)).comp u (hasDerivAt_neg u) using 1 <;> simp)
      (w := -w) (by linarith) (fun u hu => by
        rw [abs_neg, ← abs_neg u]
        exact hb (-u) (by rw [uIcc_of_ge hw]; constructor <;> linarith [hu.1, hu.2]))
    simpa using this

/-- Second-order Taylor remainder controlled by an exponential-type third derivative. -/
theorem abs_taylor3_le {f f₁ f₂ f₃ : ℝ → ℝ} (h₁ : ∀ y, HasDerivAt f (f₁ y) y)
    (h₂ : ∀ y, HasDerivAt f₁ (f₂ y) y) (h₃ : ∀ y, HasDerivAt f₂ (f₃ y) y) {C K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ y, |f₃ y| ≤ C * Real.exp (K * |y|)) (y w : ℝ) :
    |f (y + w) - f y - w * f₁ y - w ^ 2 / 2 * f₂ y| ≤
      C * Real.exp (K * (|y| + |w|)) * |w| ^ 3 / 6 := by
  have hC := nonneg_of_exp_bound hb
  set M := C * Real.exp (K * (|y| + |w|))
  have hM : 0 ≤ M := by positivity
  have hsub : ∀ u ∈ uIcc 0 w, uIcc 0 u ⊆ uIcc 0 w := fun u hu =>
    uIcc_subset_uIcc left_mem_uIcc hu
  have habs : ∀ u ∈ uIcc 0 w, |u| ≤ |w| := fun u hu => by
    simpa using abs_sub_left_of_mem_uIcc hu
  have hb3 : ∀ u ∈ uIcc 0 w, |f₃ (y + u)| ≤ M * |u| ^ 0 := by
    intro u hu
    rw [pow_zero, mul_one]
    refine (hb _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC)
    have := abs_add_le y u
    have := habs u hu
    nlinarith
  have s2 : ∀ u ∈ uIcc 0 w, |f₂ (y + u) - f₂ y| ≤ M * |u| ^ 1 := by
    intro u hu
    have := abs_le_of_hasDerivAt_abs_le (G := fun u => f₂ (y + u) - f₂ y)
      (g := fun u => f₃ (y + u)) (n := 0) (by simp)
      (fun u => by
        convert! ((h₃ (y + u)).comp u
          ((hasDerivAt_id u).const_add y)).sub_const (f₂ y) using 1 <;> simp)
      (fun u' hu' => hb3 u' (hsub u hu hu'))
    simpa using this
  have s1 : ∀ u ∈ uIcc 0 w, |f₁ (y + u) - f₁ y - u * f₂ y| ≤ (M / 2) * |u| ^ 2 := by
    intro u hu
    have := abs_le_of_hasDerivAt_abs_le (G := fun u => f₁ (y + u) - f₁ y - u * f₂ y)
      (g := fun u => f₂ (y + u) - f₂ y) (n := 1) (by simp)
      (fun u => by
        have := (((h₂ (y + u)).comp u ((hasDerivAt_id u).const_add y)).sub_const (f₁ y)).sub
          ((hasDerivAt_id u).mul_const (f₂ y))
        convert! this using 1 <;> simp) (fun u' hu' => s2 u' (hsub u hu hu'))
    refine this.trans_eq ?_
    push_cast; ring
  have := abs_le_of_hasDerivAt_abs_le
    (G := fun u => f (y + u) - f y - u * f₁ y - u ^ 2 / 2 * f₂ y)
    (g := fun u => f₁ (y + u) - f₁ y - u * f₂ y) (n := 2) (by simp)
    (fun u => by
      have := ((((h₁ (y + u)).comp u ((hasDerivAt_id u).const_add y)).sub_const (f y)).sub
        ((hasDerivAt_id u).mul_const (f₁ y))).sub (((hasDerivAt_pow 2 u).div_const 2).mul_const
          (f₂ y))
      convert! this using 1; simp) s1 (w := w)
  convert! this using 1; push_cast; ring

theorem integral_sq_std : ∫ z, z ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have := variance_of_integral_eq_zero (X := id) (μ := gaussianReal 0 1) aemeasurable_id
    (by simp [integral_id_gaussianReal (μ := (0 : ℝ)) (v := 1)])
  rw [variance_id_gaussianReal] at this
  simpa using this.symm

theorem integral_id_std : ∫ z, z ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal

theorem integrable_pow_abs_mul_exp_std (n : ℕ) (c : ℝ) :
    Integrable (fun z : ℝ => |z| ^ n * Real.exp (c * |z|)) (gaussianReal 0 1) := by
  refine ((integrable_exp_abs_gaussian (c + 1) 1).const_mul (n.factorial : ℝ)).mono'
    (by fun_prop) (.of_forall fun z => ?_)
  have h := Real.pow_div_factorial_le_exp |z| (abs_nonneg z) n
  rw [div_le_iff₀ (by positivity)] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), add_mul, one_mul, Real.exp_add]
  calc |z| ^ n * Real.exp (c * |z|) ≤ Real.exp |z| * n.factorial * Real.exp (c * |z|) := by gcongr
    _ = _ := by ring

/-- The constant in the short-time expansion. -/
noncomputable def taylorConst (K a : ℝ) : ℝ :=
  (∫ z, |z| ^ 3 * Real.exp (K * Real.sqrt a * |z|) ∂(gaussianReal 0 1)) / 6

theorem taylorConst_nonneg (K a : ℝ) : 0 ≤ taylorConst K a :=
  div_nonneg (integral_nonneg fun _ => by positivity) (by norm_num)

/-- Short-time expansion of the heat operator: `heat δ f = f + δ f'' / 2 + O(δ^{3/2})`. -/
theorem heat_short_time {f f₁ f₂ f₃ : ℝ → ℝ} (h₁ : ∀ y, HasDerivAt f (f₁ y) y)
    (h₂ : ∀ y, HasDerivAt f₁ (f₂ y) y) (h₃ : ∀ y, HasDerivAt f₂ (f₃ y) y) {C K : ℝ}
    (hK : 0 ≤ K) (hb₀ : ∀ y, |f y| ≤ C * Real.exp (K * |y|))
    (hb₃ : ∀ y, |f₃ y| ≤ C * Real.exp (K * |y|)) {δ a : ℝ} (hδ : 0 ≤ δ) (hδa : δ ≤ a)
    (y : ℝ) :
    |heat δ f y - f y - δ / 2 * f₂ y| ≤
      C * taylorConst K a * (δ * Real.sqrt δ) * Real.exp (K * |y|) := by
  have hf : Continuous f := continuous_iff_continuousAt.2 fun y => (h₁ y).continuousAt
  have hC := nonneg_of_exp_bound hb₀
  set s := Real.sqrt δ
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = δ := Real.sq_sqrt hδ
  have hsa : s ≤ Real.sqrt a := Real.sqrt_le_sqrt hδa
  set γ := gaussianReal (0 : ℝ) 1
  have hiz : Integrable (fun z : ℝ => z) γ := (memLp_id_gaussianReal 1).integrable le_rfl
  have hiz2 : Integrable (fun z : ℝ => z ^ 2) γ :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hF := integrable_affine hf hb₀ y s 1
  have hL : Integrable (fun z : ℝ => (s * z) * f₁ y) γ := (hiz.const_mul s).mul_const _
  have hQ : Integrable (fun z : ℝ => (s * z) ^ 2 / 2 * f₂ y) γ :=
    ((hiz2.const_mul (s ^ 2 / 2 * f₂ y))).congr (.of_forall fun z => by simp only; ring)
  have i1 : ∫ z, (s * z) * f₁ y ∂γ = 0 := by
    have : (fun z : ℝ => (s * z) * f₁ y) = fun z => (s * f₁ y) * z := by funext z; ring
    rw [this, integral_const_mul, integral_id_std, mul_zero]
  have i2 : ∫ z, (s * z) ^ 2 / 2 * f₂ y ∂γ = δ / 2 * f₂ y := by
    have : (fun z : ℝ => (s * z) ^ 2 / 2 * f₂ y) = fun z => (s ^ 2 / 2 * f₂ y) * z ^ 2 := by
      funext z; ring
    rw [this, integral_const_mul, integral_sq_std, hs2, mul_one]
  have hmain : heat δ f y - f y - δ / 2 * f₂ y =
      ∫ z, (f (y + s * z) - f y - (s * z) * f₁ y - (s * z) ^ 2 / 2 * f₂ y) ∂γ := by
    have hA : Integrable (fun z => f (y + s * z) - f y) γ := hF.sub (integrable_const _)
    have hB : Integrable (fun z => f (y + s * z) - f y - (s * z) * f₁ y) γ := hA.sub hL
    rw [heat_eq_std δ hf, integral_sub hB hQ, integral_sub hA hL,
      integral_sub hF (integrable_const _),
      integral_const, i1, i2]
    simp [s]
  rw [hmain]
  refine (abs_integral_le_integral_abs).trans ?_
  calc (∫ z, |f (y + s * z) - f y - (s * z) * f₁ y - (s * z) ^ 2 / 2 * f₂ y| ∂γ)
      ≤ ∫ z, C * Real.exp (K * |y|) * (δ * s) / 6 *
          (|z| ^ 3 * Real.exp (K * Real.sqrt a * |z|)) ∂γ := by
        refine integral_mono_of_nonneg (.of_forall fun _ => abs_nonneg _)
          ((integrable_pow_abs_mul_exp_std 3 _).const_mul _) (.of_forall fun z => ?_)
        refine (abs_taylor3_le h₁ h₂ h₃ hK hb₃ y (s * z)).trans ?_
        rw [abs_mul, abs_of_nonneg hs, mul_pow, mul_add, Real.exp_add]
        have e1 : Real.exp (K * (s * |z|)) ≤ Real.exp (K * Real.sqrt a * |z|) := by
          refine Real.exp_le_exp.2 ?_
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsa hK) (abs_nonneg _)
        have e2 : s ^ 3 = δ * s := by rw [pow_succ, hs2]
        rw [e2]
        have : 0 ≤ δ * s := by positivity
        calc C * (Real.exp (K * |y|) * Real.exp (K * (s * |z|))) * (δ * s * |z| ^ 3) / 6
            ≤ C * (Real.exp (K * |y|) * Real.exp (K * Real.sqrt a * |z|)) *
                (δ * s * |z| ^ 3) / 6 := by gcongr
          _ = _ := by ring
    _ = C * taylorConst K a * (δ * s) * Real.exp (K * |y|) := by
        rw [integral_const_mul, taylorConst]; ring

/-! ## Backward differentiation in the variance -/

theorem UExp.abs {S : Set ℝ} {h : ℝ → ℝ → ℝ} (hh : UExp S h) : UExp S (fun v y => |h v y|) :=
  hh.of_le fun _ _ _ => by rw [abs_abs]

theorem heat_sub_div {t : ℝ} {f g : ℝ → ℝ} (x c : ℝ)
    (hf : Integrable (fun z => f (x + z)) (gaussianReal 0 t.toNNReal))
    (hg : Integrable (fun z => g (x + z)) (gaussianReal 0 t.toNNReal)) :
    (heat t f x - heat t g x) / c = heat t (fun y => (f y - g y) / c) x := by
  simp only [heat]; rw [← integral_sub hf hg, integral_div]

/-- Mean-value bound in the time variable. -/
theorem abs_sub_le_of_time {h g : ℝ → ℝ → ℝ} {a C K : ℝ}
    (htime : ∀ y, ∀ w ∈ Icc 0 a, HasDerivWithinAt (fun u => h u y) (g w y) (Icc 0 a) w)
    (hbv : ∀ w ∈ Icc 0 a, ∀ y, |g w y| ≤ C * Real.exp (K * |y|)) {v w : ℝ}
    (hv : v ∈ Icc 0 a) (hw : w ∈ Icc 0 a) (y : ℝ) :
    |h w y - h v y| ≤ C * Real.exp (K * |y|) * |w - v| := by
  have := (convex_Icc 0 a).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u => h u y) (f' := fun u => g u y) (fun u hu => htime y u hu)
    (fun u hu => by rw [Real.norm_eq_abs]; exact hbv u hu y) hv hw
  simpa [Real.norm_eq_abs] using this

/-- Difference quotients in time converge along moving base points when the time derivative
is jointly continuous. -/
theorem tendsto_slope_joint {h g : ℝ → ℝ → ℝ} {a v y₀ : ℝ}
    (htime : ∀ y, ∀ w ∈ Icc 0 a, HasDerivWithinAt (fun u => h u y) (g w y) (Icc 0 a) w)
    (hcont : ContinuousWithinAt (fun p : ℝ × ℝ => g p.1 p.2) (Icc 0 a ×ˢ univ) (v, y₀))
    (hv : v ∈ Icc 0 a) {ι : Type*} {l : Filter ι} {w y : ι → ℝ}
    (hw : Tendsto w l (𝓝[Icc 0 a \ {v}] v)) (hy : Tendsto y l (𝓝 y₀)) :
    Tendsto (fun i => (h (w i) (y i) - h v (y i)) / (w i - v)) l (𝓝 (g v y₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.1 hcont (ε / 2) (half_pos hε)
  have hw1 : ∀ᶠ i in l, w i ∈ Icc 0 a \ {v} := hw (self_mem_nhdsWithin)
  have hw2 : ∀ᶠ i in l, dist (w i) v < δ :=
    (tendsto_nhdsWithin_iff.1 hw).1 (Metric.ball_mem_nhds v hδ)
  have hy2 : ∀ᶠ i in l, dist (y i) y₀ < δ := (Metric.tendsto_nhds.1 hy) δ hδ
  filter_upwards [hw1, hw2, hy2] with i hi1 hi2 hi3
  set c := g v y₀
  have hne : w i - v ≠ 0 := sub_ne_zero.2 hi1.2
  have hsub : uIcc v (w i) ⊆ Icc 0 a := uIcc_subset_Icc hv hi1.1
  have key := (convex_uIcc v (w i)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u => h u (y i) - u * c) (f' := fun u => g u (y i) - c) (C := ε / 2)
    (fun u hu => ((htime (y i) u (hsub hu)).mono hsub).sub
      ((hasDerivWithinAt_id u _).mul_const c) |>.congr_deriv (by simp))
    (fun u hu => by
      have hu' : (u, y i) ∈ Icc 0 a ×ˢ (univ : Set ℝ) := ⟨hsub hu, trivial⟩
      have hd : dist (u, y i) (v, y₀) < δ := by
        rw [Prod.dist_eq, max_lt_iff]
        refine ⟨?_, hi3⟩
        rw [Real.dist_eq] at hi2 ⊢
        exact lt_of_le_of_lt (by simpa using abs_sub_left_of_mem_uIcc hu) hi2
      have := hδε hu' hd
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]; exact this.le) left_mem_uIcc right_mem_uIcc
  rw [Real.dist_eq]
  simp only [Real.norm_eq_abs] at key
  have e : (h (w i) (y i) - h v (y i)) / (w i - v) - c =
      ((h (w i) (y i) - w i * c) - (h v (y i) - v * c)) / (w i - v) := by
    field_simp; ring
  rw [e, abs_div]
  rw [div_lt_iff₀ (abs_pos.2 hne)]
  calc _ ≤ ε / 2 * |w i - v| := key
    _ < ε * |w i - v| := by
        have := abs_pos.2 hne
        nlinarith

/-- The heat difference quotient `(heat δ f - f) / δ` converges to half of the second
derivative, uniformly along families. -/
theorem tendsto_heat_quotient {a : ℝ} {h h₁ h₂ h₃ : ℝ → ℝ → ℝ}
    (hd₁ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h w) (h₁ w y) y)
    (hd₂ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h₁ w) (h₂ w y) y)
    (hd₃ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h₂ w) (h₃ w y) y) {C K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ w ∈ Icc 0 a, ∀ y, |h w y| ≤ C * Real.exp (K * |y|))
    (hb₃ : ∀ w ∈ Icc 0 a, ∀ y, |h₃ w y| ≤ C * Real.exp (K * |y|))
    {ι : Type*} {l : Filter ι} {w δ y : ι → ℝ} {y₀ L : ℝ}
    (hw : ∀ᶠ i in l, w i ∈ Icc 0 a) (hδ : Tendsto δ l (𝓝[>] 0)) (hδa : ∀ᶠ i in l, δ i ≤ a)
    (hy : Tendsto y l (𝓝 y₀)) (h2lim : Tendsto (fun i => h₂ (w i) (y i)) l (𝓝 L)) :
    Tendsto (fun i => (heat (δ i) (h (w i)) (y i) - h (w i) (y i)) / δ i) l (𝓝 (L / 2)) := by
  have hδpos : ∀ᶠ i in l, 0 < δ i := hδ self_mem_nhdsWithin
  have hδ0 : Tendsto δ l (𝓝 0) := tendsto_nhdsWithin_iff.1 hδ |>.1
  set E := fun i => (heat (δ i) (h (w i)) (y i) - h (w i) (y i)) / δ i - h₂ (w i) (y i) / 2
  have hE : Tendsto E l (𝓝 0) := by
    have hbound : Tendsto (fun i => C * taylorConst K a * Real.sqrt (δ i) *
        Real.exp (K * |y i|)) l (𝓝 0) := by
      have : Tendsto (fun i => C * taylorConst K a * Real.sqrt (δ i) *
          Real.exp (K * |y i|)) l
          (𝓝 (C * taylorConst K a * Real.sqrt 0 * Real.exp (K * |y₀|))) :=
        ((tendsto_const_nhds.mul ((Real.continuous_sqrt.tendsto 0).comp hδ0)).mul
          ((Real.continuous_exp.tendsto _).comp
            ((continuous_abs.tendsto _).comp hy |>.const_mul K)))
      simpa using this
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hw, hδpos, hδa] with i hwi hδi hδai
    have := heat_short_time (hd₁ (w i) hwi) (hd₂ (w i) hwi) (hd₃ (w i) hwi) hK (hb (w i) hwi)
      (hb₃ (w i) hwi) hδi.le hδai (y i)
    rw [Real.norm_eq_abs]
    have e : E i = (heat (δ i) (h (w i)) (y i) - h (w i) (y i) - δ i / 2 * h₂ (w i) (y i)) /
        δ i := by simp only [E]; field_simp
    rw [e, abs_div, abs_of_pos hδi, div_le_iff₀ hδi]
    have hs : δ i * Real.sqrt (δ i) = Real.sqrt (δ i) * δ i := mul_comm _ _
    rw [hs] at this
    linarith
  have := hE.add (h2lim.div_const 2)
  simp only [zero_add] at this
  refine this.congr fun i => ?_
  simp only [E]; ring

/-- **Backward differentiation formula.** For a time-dependent integrand `h w` with
three space derivatives and a jointly continuous time derivative `hv'`,
`d/dw heat (a - w) (h w) x = heat (a - w) (∂_w h - h'' / 2) x` on `[0, a]`, including
both endpoints. -/
theorem hasDerivWithinAt_heat_backward {a x v : ℝ} (hv : v ∈ Icc 0 a)
    {h h₁ h₂ h₃ hv' : ℝ → ℝ → ℝ}
    (hd₁ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h w) (h₁ w y) y)
    (hd₂ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h₁ w) (h₂ w y) y)
    (hd₃ : ∀ w ∈ Icc 0 a, ∀ y, HasDerivAt (h₂ w) (h₃ w y) y)
    (hb : UExp (Icc 0 a) h) (hb₂ : UExp (Icc 0 a) h₂) (hb₃ : UExp (Icc 0 a) h₃)
    (hbv : UExp (Icc 0 a) hv')
    (htime : ∀ y, ∀ w ∈ Icc 0 a, HasDerivWithinAt (fun u => h u y) (hv' w y) (Icc 0 a) w)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => hv' p.1 p.2) (Icc 0 a ×ˢ univ))
    (hcont₂ : ∀ y, ContinuousWithinAt (fun w => h₂ w y) (Icc 0 a) v) :
    HasDerivWithinAt (fun w => heat (a - w) (h w) x)
      (heat (a - v) (fun y => hv' v y - h₂ v y / 2) x) (Icc 0 a) v := by
  obtain ⟨C, K, hC, hK, hB⟩ := (((hb.abs.add hb₂.abs).add hb₃.abs).add hbv.abs).nonneg
  have b0 : ∀ w ∈ Icc 0 a, ∀ y, |h w y| ≤ C * Real.exp (K * |y|) := fun w hw y => by
    have := hB w hw y; rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (h₂ w y), abs_nonneg (h₃ w y), abs_nonneg (hv' w y)]
  have b2 : ∀ w ∈ Icc 0 a, ∀ y, |h₂ w y| ≤ C * Real.exp (K * |y|) := fun w hw y => by
    have := hB w hw y; rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (h w y), abs_nonneg (h₃ w y), abs_nonneg (hv' w y)]
  have b3 : ∀ w ∈ Icc 0 a, ∀ y, |h₃ w y| ≤ C * Real.exp (K * |y|) := fun w hw y => by
    have := hB w hw y; rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (h w y), abs_nonneg (h₂ w y), abs_nonneg (hv' w y)]
  have bv : ∀ w ∈ Icc 0 a, ∀ y, |hv' w y| ≤ C * Real.exp (K * |y|) := fun w hw y => by
    have := hB w hw y; rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (h w y), abs_nonneg (h₂ w y), abs_nonneg (h₃ w y)]
  have hcf : ∀ w ∈ Icc 0 a, Continuous (h w) := fun w hw =>
    continuous_iff_continuousAt.2 fun y => (hd₁ w hw y).continuousAt
  have hc2 : ∀ w ∈ Icc 0 a, Continuous (h₂ w) := fun w hw =>
    continuous_iff_continuousAt.2 fun y => (hd₃ w hw y).continuousAt
  have hcv : Continuous (hv' v) := by
    exact hcont.comp_continuous (by fun_prop : Continuous fun y : ℝ => (v, y))
      fun y => ⟨hv, trivial⟩
  set k : ℝ → ℝ := fun y => hv' v y - h₂ v y / 2
  have hk : Continuous k := hcv.sub ((hc2 v hv).div_const 2)
  have hkb : ∀ y, |k y| ≤ (3 / 2 * C) * Real.exp (K * |y|) := fun y => by
    have := abs_sub (hv' v y) (h₂ v y / 2)
    rw [abs_div, abs_two] at this
    have := bv v hv y; have := b2 v hv y
    simp only [k]; nlinarith
  set T := taylorConst K a
  have hT := taylorConst_nonneg K a
  -- bound on the Taylor quotient
  have tq_bound : ∀ w ∈ Icc 0 a, ∀ δ, 0 < δ → δ ≤ a → ∀ y,
      |(heat δ (h w) y - h w y) / δ| ≤ (C / 2 + C * T * Real.sqrt a) * Real.exp (K * |y|) := by
    intro w hw δ hδ hδa y
    have := heat_short_time (hd₁ w hw) (hd₂ w hw) (hd₃ w hw) hK (b0 w hw) (b3 w hw) hδ.le hδa y
    have h2 := b2 w hw y
    have e : (heat δ (h w) y - h w y) / δ =
        (heat δ (h w) y - h w y - δ / 2 * h₂ w y) / δ + h₂ w y / 2 := by field_simp; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_of_pos hδ, abs_div, abs_two]
    have hsq : Real.sqrt δ ≤ Real.sqrt a := Real.sqrt_le_sqrt hδa
    have hE := Real.exp_pos (K * |y|)
    have h1 : |heat δ (h w) y - h w y - δ / 2 * h₂ w y| / δ ≤
        C * T * Real.sqrt a * Real.exp (K * |y|) := by
      rw [div_le_iff₀ hδ]
      refine this.trans ?_
      have := mul_le_mul_of_nonneg_left hsq
        (by positivity : 0 ≤ C * T * Real.exp (K * |y|) * δ)
      calc C * T * (δ * Real.sqrt δ) * Real.exp (K * |y|)
          = C * T * Real.exp (K * |y|) * δ * Real.sqrt δ := by ring
        _ ≤ C * T * Real.exp (K * |y|) * δ * Real.sqrt a := this
        _ = _ := by ring
    have : (C / 2 + C * T * Real.sqrt a) * Real.exp (K * |y|) =
        C / 2 * Real.exp (K * |y|) + C * T * Real.sqrt a * Real.exp (K * |y|) := by ring
    rw [this]
    linarith
  -- bound on the slope quotient
  have sl_bound : ∀ w ∈ Icc 0 a, w ≠ v → ∀ y,
      |(h w y - h v y) / (w - v)| ≤ C * Real.exp (K * |y|) := by
    intro w hw hne y
    have := abs_sub_le_of_time htime bv hv hw y
    rw [abs_div, div_le_iff₀ (abs_pos.2 (sub_ne_zero.2 hne))]
    exact this
  have hsplit : Icc 0 a = Icc 0 v ∪ Icc v a := (Icc_union_Icc_eq_Icc hv.1 hv.2).symm
  rw [hsplit]
  refine HasDerivWithinAt.union ?_ ?_
  · -- left branch
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hsub : Icc 0 v \ {v} ⊆ Icc 0 a \ {v} := diff_subset_diff_left (Icc_subset_Icc le_rfl hv.2)
    have hl : ∀ w ∈ Icc 0 v \ {v}, slope (fun w => heat (a - w) (h w) x) v w =
        ∫ z, (fun y => (h w y - h v y) / (w - v) - (heat (v - w) (h w) y - h w y) / (v - w))
          (x + Real.sqrt (a - v) * z) ∂(gaussianReal 0 1) := by
      intro w hw
      have hw' : w ∈ Icc 0 a := ⟨hw.1.1, hw.1.2.trans hv.2⟩
      have hwv : w < v := lt_of_le_of_ne hw.1.2 hw.2
      have hH := heat_heat (s := a - v) (t := v - w) (by linarith [hv.2]) (by linarith)
        (hcf w hw') (b0 w hw') x
      rw [show a - v + (v - w) = a - w by ring] at hH
      have hcg : Continuous (heat (v - w) (h w)) :=
        (continuous_heat (hcf w hw') (b0 w hw')).comp (Continuous.prodMk_right _)
      rw [slope_def_field, ← hH, heat_sub_div]
      · rw [heat_eq_std _ (by
          refine (hcg.sub (hcf v hv)).div_const _)]
        congr 1; funext z
        have : w - v ≠ 0 := sub_ne_zero.2 hwv.ne
        have : v - w ≠ 0 := sub_ne_zero.2 hwv.ne'
        field_simp; ring
      · exact integrable_shift hcg (fun y => abs_heat_le (hcf w hw') hK (b0 w hw') le_rfl y) x _
      · exact integrable_shift (hcf v hv) (b0 v hv) x _
    refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun w hw => (hl w hw).symm) ?_
    rw [heat_eq_std _ hk]
    have hmem : ∀ᶠ w in 𝓝[Icc 0 v \ {v}] v, w ∈ Icc 0 v \ {v} := self_mem_nhdsWithin
    refine tendsto_integral_std (x := fun _ => x) (s := fun _ => Real.sqrt (a - v))
      (q := fun w y => (h w y - h v y) / (w - v) - (heat (v - w) (h w) y - h w y) / (v - w))
      (k := k) tendsto_const_nhds tendsto_const_nhds ?_ ?_ fun z => ?_
    · filter_upwards [hmem] with w hw
      have hw' : w ∈ Icc 0 a := ⟨hw.1.1, hw.1.2.trans hv.2⟩
      exact (((hcf w hw').sub (hcf v hv)).div_const _ |>.sub
        ((((continuous_heat (hcf w hw') (b0 w hw')).comp (Continuous.prodMk_right _)).sub
          (hcf w hw')).div_const _)).comp (by fun_prop) |>.aestronglyMeasurable
    · refine ⟨C + (C / 2 + C * T * Real.sqrt a), K, ?_⟩
      filter_upwards [hmem] with w hw y
      have hw' : w ∈ Icc 0 a := ⟨hw.1.1, hw.1.2.trans hv.2⟩
      have hwv : w < v := lt_of_le_of_ne hw.1.2 hw.2
      refine (abs_sub _ _).trans ?_
      have := sl_bound w hw' hw.2 y
      have := tq_bound w hw' (v - w) (by linarith) (by linarith [hw.1.1, hv.2]) y
      linarith
    · have hA := tendsto_slope_joint (y := fun _ => x + Real.sqrt (a - v) * z) htime
        (hcont (v, _) ⟨hv, trivial⟩) hv (tendsto_nhdsWithin_mono_right hsub
          (tendsto_id (x := 𝓝[Icc 0 v \ {v}] v))) tendsto_const_nhds
      have hδ : Tendsto (fun w => v - w) (𝓝[Icc 0 v \ {v}] v) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have : Tendsto (fun w => v - w) (𝓝 v) (𝓝 (v - v)) :=
            tendsto_const_nhds.sub tendsto_id
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [hmem] with w hw
          exact sub_pos.2 (lt_of_le_of_ne hw.1.2 hw.2)
      have hB := tendsto_heat_quotient (w := fun w => w) (y := fun _ => x + Real.sqrt (a - v) * z)
        hd₁ hd₂ hd₃ hK b0 b3 (hmem.mono fun w hw => ⟨hw.1.1, hw.1.2.trans hv.2⟩) hδ
        (hmem.mono fun w hw => by linarith [hw.1.1, hv.2]) tendsto_const_nhds
        ((hcont₂ _).mono_left (nhdsWithin_mono _ (hsub.trans diff_subset)))
      exact hA.sub hB
  · -- right branch
    rw [hasDerivWithinAt_iff_tendsto_slope]
    have hsub : Icc v a \ {v} ⊆ Icc 0 a \ {v} := diff_subset_diff_left (Icc_subset_Icc hv.1 le_rfl)
    have hr : ∀ w ∈ Icc v a \ {v}, slope (fun w => heat (a - w) (h w) x) v w =
        ∫ z, (fun y => (h w y - h v y) / (w - v) - (heat (w - v) (h v) y - h v y) / (w - v))
          (x + Real.sqrt (a - w) * z) ∂(gaussianReal 0 1) := by
      intro w hw
      have hw' : w ∈ Icc 0 a := ⟨hv.1.trans hw.1.1, hw.1.2⟩
      have hwv : v < w := lt_of_le_of_ne hw.1.1 (Ne.symm hw.2)
      have hH := heat_heat (s := a - w) (t := w - v) (by linarith [hw.1.2]) (by linarith)
        (hcf v hv) (b0 v hv) x
      rw [show a - w + (w - v) = a - v by ring] at hH
      have hcg : Continuous (heat (w - v) (h v)) :=
        (continuous_heat (hcf v hv) (b0 v hv)).comp (Continuous.prodMk_right _)
      rw [slope_def_field, ← hH, heat_sub_div]
      · rw [heat_eq_std _ (by
          refine ((hcf w hw').sub hcg).div_const _)]
        congr 1; funext z
        have : w - v ≠ 0 := sub_ne_zero.2 hwv.ne'
        field_simp; ring
      · exact integrable_shift (hcf w hw') (b0 w hw') x _
      · exact integrable_shift hcg (fun y => abs_heat_le (hcf v hv) hK (b0 v hv) le_rfl y) x _
    refine Tendsto.congr' (eventually_nhdsWithin_of_forall fun w hw => (hr w hw).symm) ?_
    rw [heat_eq_std _ hk]
    have hmem : ∀ᶠ w in 𝓝[Icc v a \ {v}] v, w ∈ Icc v a \ {v} := self_mem_nhdsWithin
    have hsq : Tendsto (fun w => Real.sqrt (a - w)) (𝓝[Icc v a \ {v}] v)
        (𝓝 (Real.sqrt (a - v))) :=
      ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).tendsto v).mono_left
        nhdsWithin_le_nhds
    refine tendsto_integral_std (x := fun _ => x) (s := fun w => Real.sqrt (a - w))
      (q := fun w y => (h w y - h v y) / (w - v) - (heat (w - v) (h v) y - h v y) / (w - v))
      (k := k) tendsto_const_nhds hsq ?_ ?_ fun z => ?_
    · filter_upwards [hmem] with w hw
      have hw' : w ∈ Icc 0 a := ⟨hv.1.trans hw.1.1, hw.1.2⟩
      exact (((hcf w hw').sub (hcf v hv)).div_const _ |>.sub
        ((((continuous_heat (hcf v hv) (b0 v hv)).comp (Continuous.prodMk_right _)).sub
          (hcf v hv)).div_const _)).comp (by fun_prop) |>.aestronglyMeasurable
    · refine ⟨C + (C / 2 + C * T * Real.sqrt a), K, ?_⟩
      filter_upwards [hmem] with w hw y
      have hw' : w ∈ Icc 0 a := ⟨hv.1.trans hw.1.1, hw.1.2⟩
      have hwv : v < w := lt_of_le_of_ne hw.1.1 (Ne.symm hw.2)
      refine (abs_sub _ _).trans ?_
      have := sl_bound w hw' hw.2 y
      have := tq_bound v hv (w - v) (by linarith) (by linarith [hw.1.2, hv.1]) y
      linarith
    · have hy : Tendsto (fun w => x + Real.sqrt (a - w) * z) (𝓝[Icc v a \ {v}] v)
          (𝓝 (x + Real.sqrt (a - v) * z)) := tendsto_const_nhds.add (hsq.mul_const z)
      have hA := tendsto_slope_joint htime (hcont (v, _) ⟨hv, trivial⟩) hv
        (tendsto_nhdsWithin_mono_right hsub (tendsto_id (x := 𝓝[Icc v a \ {v}] v))) hy
      have hδ : Tendsto (fun w => w - v) (𝓝[Icc v a \ {v}] v) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have : Tendsto (fun w => w - v) (𝓝 v) (𝓝 (v - v)) :=
            tendsto_id.sub tendsto_const_nhds
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [hmem] with w hw
          exact sub_pos.2 (lt_of_le_of_ne hw.1.1 (Ne.symm hw.2))
      have hB := tendsto_heat_quotient (w := fun _ => v) (y := fun w => x + Real.sqrt (a - w) * z)
        hd₁ hd₂ hd₃ hK b0 b3 (.of_forall fun _ => hv) hδ
        (hmem.mono fun w hw => by linarith [hw.1.2, hv.1]) hy
        (((hc2 v hv).tendsto _).comp hy)
      exact hA.sub hB

end HeatSemigroup

section SplitJets

/-!
# Heat-semigroup identities behind the Gaussian split

Four-jets of functions of exponential type, the forward heat equation for their Gaussian
smoothings, and the backward variance derivatives of the specific integrands that appear in
the split mass response and the squared-gradient moment.
-/

/-- Exponential type of a single function. -/
abbrev ExpT (f : ℝ → ℝ) : Prop := UExp univ (fun _ => f)

theorem ExpT.bound {f : ℝ → ℝ} (hf : ExpT f) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ y, |f y| ≤ C * Real.exp (K * |y|) := by
  obtain ⟨C, K, hC, hK, h⟩ := UExp.nonneg hf
  exact ⟨C, K, hC, hK, fun y => h 0 trivial y⟩

/-- A four-jet: `d 0` with four successive derivatives, all of exponential type. -/
structure Jet (d : ℕ → ℝ → ℝ) : Prop where
  hasDeriv : ∀ j < 4, ∀ y, HasDerivAt (d j) (d (j + 1) y) y
  cont : Continuous (d 4)
  expT : ∀ j ≤ 4, ExpT (d j)

namespace Jet

variable {d : ℕ → ℝ → ℝ}

theorem continuous (hd : Jet d) {j : ℕ} (hj : j ≤ 4) : Continuous (d j) := by
  rcases lt_or_eq_of_le hj with h | rfl
  · exact continuous_iff_continuousAt.2 fun y => (hd.hasDeriv j h y).continuousAt
  · exact hd.cont

theorem heat_hasDerivAt (hd : Jet d) {j : ℕ} (hj : j < 4) (t y : ℝ) :
    HasDerivAt (heat t (d j)) (heat t (d (j + 1)) y) y := by
  obtain ⟨C₁, K₁, -, -, h₁⟩ := (hd.expT j hj.le).bound
  obtain ⟨C₂, K₂, -, -, h₂⟩ := (hd.expT (j + 1) hj).bound
  obtain ⟨C, K, -, -, h⟩ := ((hd.expT j hj.le).abs.add (hd.expT (j + 1) hj).abs).nonneg
  refine hasDerivAt_heat t (hd.hasDeriv j hj) (hd.continuous hj) (C := C) (K := K)
    (fun y => ?_) (fun y => ?_) y
  · have := h 0 trivial y
    rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (d (j + 1) y)]
  · have := h 0 trivial y
    rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (d j y)]

theorem continuous_heat (hd : Jet d) {j : ℕ} (hj : j ≤ 4) :
    Continuous (fun p : ℝ × ℝ => heat p.1 (d j) p.2) := by
  obtain ⟨C, K, -, -, h⟩ := (hd.expT j hj).bound
  exact Heat.continuous_heat (hd.continuous hj) h

theorem uexp_heat (hd : Jet d) {j : ℕ} (hj : j ≤ 4) (a : ℝ) :
    UExp (Icc 0 a) (fun t y => heat t (d j) y) := by
  obtain ⟨C, K, -, -, h⟩ := (hd.expT j hj).bound
  exact (Heat.uexp_heat (hd.continuous hj) h a).mono fun _ ht => ht.2

end Jet

theorem heat_neg (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : heat t (fun y => -f y) x = -heat t f x := by
  simp [heat, integral_neg]

theorem heat_const_mul (t c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    heat t (fun y => c * f y) x = c * heat t f x := by
  simp [heat, integral_const_mul]

theorem heat_div_const (t c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    heat t (fun y => f y / c) x = heat t f x / c := by
  simp [heat, integral_div]

theorem heat_congr {t : ℝ} {f g : ℝ → ℝ} (h : ∀ y, f y = g y) (x : ℝ) :
    heat t f x = heat t g x := by
  rw [show f = g from funext h]

/-- The forward heat equation in the variance, including the endpoint `t = 0`. -/
theorem hasDerivWithinAt_heat_time {f f₁ f₂ f₃ : ℝ → ℝ} (h₁ : ∀ y, HasDerivAt f (f₁ y) y)
    (h₂ : ∀ y, HasDerivAt f₁ (f₂ y) y) (h₃ : ∀ y, HasDerivAt f₂ (f₃ y) y)
    (hb : ExpT f) (hb₂ : ExpT f₂) (hb₃ : ExpT f₃) {a t : ℝ} (ht : t ∈ Icc 0 a) (y : ℝ) :
    HasDerivWithinAt (fun s => heat s f y) (heat t f₂ y / 2) (Icc 0 a) t := by
  have hv : a - t ∈ Icc 0 a := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have key := hasDerivWithinAt_heat_backward (a := a) (x := y) hv
    (h := fun _ => f) (h₁ := fun _ => f₁) (h₂ := fun _ => f₂) (h₃ := fun _ => f₃)
    (hv' := fun _ _ => 0) (fun _ _ => h₁) (fun _ _ => h₂) (fun _ _ => h₃)
    (hb.mono (subset_univ _)) (hb₂.mono (subset_univ _)) (hb₃.mono (subset_univ _))
    (UExp.const 0) (fun _ _ _ => hasDerivWithinAt_const _ _ _) continuousOn_const
    (fun _ => continuousWithinAt_const)
  have hmap : MapsTo (fun s => a - s) (Icc 0 a) (Icc 0 a) := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hφ : HasDerivWithinAt (fun s => a - s) (-1) (Icc 0 a) t :=
    ((hasDerivAt_id t).const_sub a).hasDerivWithinAt
  have := key.comp t hφ hmap
  simp only [Function.comp_def, sub_sub_cancel, zero_sub] at this
  convert! this using 1
  rw [heat_neg, heat_div_const]; ring

namespace Jet

variable {d : ℕ → ℝ → ℝ}

theorem heat_time (hd : Jet d) {j : ℕ} (hj : j ≤ 1) {a t : ℝ} (ht : t ∈ Icc 0 a) (y : ℝ) :
    HasDerivWithinAt (fun s => heat s (d j) y) (heat t (d (j + 2)) y / 2) (Icc 0 a) t :=
  hasDerivWithinAt_heat_time (hd.hasDeriv j (by omega)) (hd.hasDeriv (j + 1) (by omega))
    (hd.hasDeriv (j + 2) (by omega)) (hd.expT j (by omega)) (hd.expT (j + 2) (by omega))
    (hd.expT (j + 3) (by omega)) ht y

end Jet

/-- Leibniz products of four-jets. -/
def jetMul (d e : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun y => d 0 y * e 0 y
  | 1 => fun y => d 1 y * e 0 y + d 0 y * e 1 y
  | 2 => fun y => d 2 y * e 0 y + 2 * (d 1 y * e 1 y) + d 0 y * e 2 y
  | 3 => fun y => d 3 y * e 0 y + 3 * (d 2 y * e 1 y) + 3 * (d 1 y * e 2 y) + d 0 y * e 3 y
  | _ => fun y => d 4 y * e 0 y + 4 * (d 3 y * e 1 y) + 6 * (d 2 y * e 2 y) +
      4 * (d 1 y * e 3 y) + d 0 y * e 4 y

theorem ExpT.mul {f g : ℝ → ℝ} (hf : ExpT f) (hg : ExpT g) : ExpT (fun y => f y * g y) :=
  UExp.mul hf hg

theorem ExpT.add {f g : ℝ → ℝ} (hf : ExpT f) (hg : ExpT g) : ExpT (fun y => f y + g y) :=
  UExp.add hf hg

theorem ExpT.const_mul {f : ℝ → ℝ} (hf : ExpT f) (c : ℝ) : ExpT (fun y => c * f y) :=
  UExp.const_mul hf c

theorem Jet.mul {d e : ℕ → ℝ → ℝ} (hd : Jet d) (he : Jet e) : Jet (jetMul d e) := by
  have D := hd.hasDeriv
  have E := he.hasDeriv
  refine ⟨fun j hj y => ?_, ?_, fun j hj => ?_⟩
  · interval_cases j
    · convert! (D 0 (by norm_num) y).mul (E 0 (by norm_num) y) using 1
    · convert! ((D 1 (by norm_num) y).mul (E 0 (by norm_num) y)).add
        ((D 0 (by norm_num) y).mul (E 1 (by norm_num) y)) using 1
      simp only [jetMul]; ring
    · convert! (((D 2 (by norm_num) y).mul (E 0 (by norm_num) y)).add
        (((D 1 (by norm_num) y).mul (E 1 (by norm_num) y)).const_mul 2)).add
        ((D 0 (by norm_num) y).mul (E 2 (by norm_num) y)) using 1
      simp only [jetMul]; ring
    · convert! ((((D 3 (by norm_num) y).mul (E 0 (by norm_num) y)).add
        (((D 2 (by norm_num) y).mul (E 1 (by norm_num) y)).const_mul 3)).add
        (((D 1 (by norm_num) y).mul (E 2 (by norm_num) y)).const_mul 3)).add
        ((D 0 (by norm_num) y).mul (E 3 (by norm_num) y)) using 1
      simp only [jetMul]; ring
  · have c := fun j (hj : j ≤ 4) => hd.continuous hj
    have c' := fun j (hj : j ≤ 4) => he.continuous hj
    simp only [jetMul]
    have := c 0 (by norm_num); have := c 1 (by norm_num); have := c 2 (by norm_num)
    have := c 3 (by norm_num); have := c 4 le_rfl
    have := c' 0 (by norm_num); have := c' 1 (by norm_num); have := c' 2 (by norm_num)
    have := c' 3 (by norm_num); have := c' 4 le_rfl
    fun_prop
  · have b := fun j (hj : j ≤ 4) => hd.expT j hj
    have b' := fun j (hj : j ≤ 4) => he.expT j hj
    interval_cases j <;> simp only [jetMul]
    · exact (b 0 (by norm_num)).mul (b' 0 (by norm_num))
    · exact ((b 1 (by norm_num)).mul (b' 0 (by norm_num))).add
        ((b 0 (by norm_num)).mul (b' 1 (by norm_num)))
    · exact (((b 2 (by norm_num)).mul (b' 0 (by norm_num))).add
        (((b 1 (by norm_num)).mul (b' 1 (by norm_num))).const_mul 2)).add
        ((b 0 (by norm_num)).mul (b' 2 (by norm_num)))
    · exact ((((b 3 (by norm_num)).mul (b' 0 (by norm_num))).add
        (((b 2 (by norm_num)).mul (b' 1 (by norm_num))).const_mul 3)).add
        (((b 1 (by norm_num)).mul (b' 2 (by norm_num))).const_mul 3)).add
        ((b 0 (by norm_num)).mul (b' 3 (by norm_num)))
    · exact (((((b 4 le_rfl).mul (b' 0 (by norm_num))).add
        (((b 3 (by norm_num)).mul (b' 1 (by norm_num))).const_mul 4)).add
        (((b 2 (by norm_num)).mul (b' 2 (by norm_num))).const_mul 6)).add
        (((b 1 (by norm_num)).mul (b' 3 (by norm_num))).const_mul 4)).add
        ((b 0 (by norm_num)).mul (b' 4 le_rfl))

/-! ## Smoothed families -/

/-- The smoothed family `(w, y) ↦ heat w (g j) y` of the `j`-th jet component. -/
noncomputable def hfam (g : ℕ → ℝ → ℝ) (j : ℕ) (w y : ℝ) : ℝ := heat w (g j) y

/-- A positive lower envelope of exponential type. -/
def PosLow (f : ℝ → ℝ) : Prop :=
  ∃ c L : ℝ, 0 < c ∧ 0 ≤ L ∧ ∀ y, c * Real.exp (-(L * |y|)) ≤ f y

macro "uexp_tac" : tactic => `(tactic| repeat (first
  | assumption
  | apply UExp.add
  | apply UExp.sub
  | apply UExp.neg
  | apply UExp.mul
  | apply UExp.pow
  | apply UExp.div_const
  | apply UExp.const))

macro "pi_norm" : tactic => `(tactic| (try simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply,
  Pi.sub_apply, Pi.inv_apply, Pi.neg_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul]))

section Fam

variable {g : ℕ → ℝ → ℝ}

theorem hfam_deriv (hg : Jet g) {j : ℕ} (hj : j < 4) (w y : ℝ) :
    HasDerivAt (hfam g j w) (hfam g (j + 1) w y) y := hg.heat_hasDerivAt hj w y

theorem hfam_time (hg : Jet g) {j : ℕ} (hj : j ≤ 1) {a w : ℝ} (hw : w ∈ Icc 0 a) (y : ℝ) :
    HasDerivWithinAt (fun u => hfam g j u y) (hfam g (j + 2) w y / 2) (Icc 0 a) w :=
  hg.heat_time hj hw y

theorem hfam_cont (hg : Jet g) {j : ℕ} (hj : j ≤ 4) :
    Continuous (fun p : ℝ × ℝ => hfam g j p.1 p.2) := hg.continuous_heat hj

theorem hfam_uexp (hg : Jet g) {j : ℕ} (hj : j ≤ 4) (a : ℝ) : UExp (Icc 0 a) (hfam g j) :=
  hg.uexp_heat hj a

theorem hfam_lower (hg : Jet g) (hlow : PosLow (g 0)) (a : ℝ) :
    ∃ c L : ℝ, 0 < c ∧ 0 ≤ L ∧ ∀ w ≤ a, ∀ y, c * Real.exp (-(L * |y|)) ≤ hfam g 0 w y := by
  obtain ⟨c, L, hc, hL, hl⟩ := hlow
  obtain ⟨C, K, -, -, hb⟩ := (hg.expT 0 (by norm_num)).bound
  obtain ⟨c', hc', h⟩ := heat_lower (hg.continuous (by norm_num)) hb hc hL hl a
  exact ⟨c', L, hc', hL, h⟩

theorem hfam_pos (hg : Jet g) (hlow : PosLow (g 0)) (w y : ℝ) : 0 < hfam g 0 w y := by
  obtain ⟨c, L, hc, -, h⟩ := hfam_lower hg hlow w
  exact lt_of_lt_of_le (by positivity) (h w le_rfl y)

theorem hfam_inv_uexp (hg : Jet g) (hlow : PosLow (g 0)) (a : ℝ) :
    UExp (Icc 0 a) (fun w y => (hfam g 0 w y)⁻¹) := by
  obtain ⟨c, L, hc, hL, h⟩ := hfam_lower hg hlow a
  refine ⟨c⁻¹, L, fun w hw y => ?_⟩
  have hp := hfam_pos hg hlow w y
  rw [abs_of_pos (inv_pos.2 hp)]
  calc (hfam g 0 w y)⁻¹ ≤ (c * Real.exp (-(L * |y|)))⁻¹ := inv_anti₀ (by positivity) (h w hw.2 y)
    _ = c⁻¹ * Real.exp (L * |y|) := by rw [mul_inv, ← Real.exp_neg, neg_neg]

theorem hfam_inv_cont (hg : Jet g) (hlow : PosLow (g 0)) :
    Continuous (fun p : ℝ × ℝ => (hfam g 0 p.1 p.2)⁻¹) :=
  (hfam_cont hg (by norm_num)).inv₀ fun p => (hfam_pos hg hlow p.1 p.2).ne'

theorem hfam_inv_deriv (hg : Jet g) (hlow : PosLow (g 0)) (w y : ℝ) :
    HasDerivAt (fun y => (hfam g 0 w y)⁻¹) (-(hfam g 1 w y) * (hfam g 0 w y)⁻¹ ^ 2) y := by
  have := (hfam_deriv hg (j := 0) (by norm_num) w y).inv (hfam_pos hg hlow w y).ne'
  convert! this using 1
  field_simp

theorem continuousWithinAt_of_joint {F : ℝ → ℝ → ℝ} (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (y : ℝ) (s : Set ℝ) (v : ℝ) : ContinuousWithinAt (fun w => F w y) s v :=
  (hF.comp (Continuous.prodMk_left y)).continuousWithinAt

/-- Backward derivative of the squared-gradient integrand `e₁² / e`. -/
theorem backward_gradSq (hg : Jet g) (hlow : PosLow (g 0)) {a x v : ℝ} (hv : v ∈ Icc 0 a) :
    HasDerivWithinAt (fun w => heat (a - w) (fun y => hfam g 1 w y ^ 2 * (hfam g 0 w y)⁻¹) x)
      (heat (a - v) (fun y => -((hfam g 2 v y * hfam g 0 v y - hfam g 1 v y ^ 2) ^ 2 *
        (hfam g 0 v y)⁻¹ ^ 3)) x) (Icc 0 a) v := by
  have d0 : ∀ w y, HasDerivAt (hfam g 0 w) (hfam g 1 w y) y := fun w y =>
    hfam_deriv hg (by norm_num) w y
  have d1 : ∀ w y, HasDerivAt (hfam g 1 w) (hfam g 2 w y) y := fun w y =>
    hfam_deriv hg (by norm_num) w y
  have d2 : ∀ w y, HasDerivAt (hfam g 2 w) (hfam g 3 w y) y := fun w y =>
    hfam_deriv hg (by norm_num) w y
  have d3 : ∀ w y, HasDerivAt (hfam g 3 w) (hfam g 4 w y) y := fun w y =>
    hfam_deriv hg (by norm_num) w y
  have dE := hfam_inv_deriv hg hlow
  have hp := hfam_pos hg hlow
  have U0 := hfam_uexp hg (j := 0) (by norm_num) a
  have U1 := hfam_uexp hg (j := 1) (by norm_num) a
  have U2 := hfam_uexp hg (j := 2) (by norm_num) a
  have U3 := hfam_uexp hg (j := 3) (by norm_num) a
  have U4 := hfam_uexp hg (j := 4) (by norm_num) a
  have UE := hfam_inv_uexp hg hlow a
  have C0 := hfam_cont hg (j := 0) (by norm_num)
  have C1 := hfam_cont hg (j := 1) (by norm_num)
  have C2 := hfam_cont hg (j := 2) (by norm_num)
  have C3 := hfam_cont hg (j := 3) (by norm_num)
  have CE := hfam_inv_cont hg hlow
  have t0 : ∀ w ∈ Icc 0 a, ∀ y, HasDerivWithinAt (fun u => hfam g 0 u y)
      (hfam g 2 w y / 2) (Icc 0 a) w := fun w hw y => hfam_time hg (j := 0) (by norm_num) hw y
  have t1 : ∀ w ∈ Icc 0 a, ∀ y, HasDerivWithinAt (fun u => hfam g 1 u y)
      (hfam g 3 w y / 2) (Icc 0 a) w := fun w hw y => hfam_time hg (j := 1) (by norm_num) hw y
  have h2c : Continuous (fun p : ℝ × ℝ =>
      2 * hfam g 2 p.1 p.2 ^ 2 * (hfam g 0 p.1 p.2)⁻¹ +
      2 * hfam g 1 p.1 p.2 * hfam g 3 p.1 p.2 * (hfam g 0 p.1 p.2)⁻¹ -
      5 * hfam g 1 p.1 p.2 ^ 2 * hfam g 2 p.1 p.2 * (hfam g 0 p.1 p.2)⁻¹ ^ 2 +
      2 * hfam g 1 p.1 p.2 ^ 4 * (hfam g 0 p.1 p.2)⁻¹ ^ 3) := by fun_prop
  refine (hasDerivWithinAt_heat_backward hv
    (h := fun w y => hfam g 1 w y ^ 2 * (hfam g 0 w y)⁻¹)
    (h₁ := fun w y => 2 * hfam g 1 w y * hfam g 2 w y * (hfam g 0 w y)⁻¹ -
      hfam g 1 w y ^ 3 * (hfam g 0 w y)⁻¹ ^ 2)
    (h₂ := fun w y => 2 * hfam g 2 w y ^ 2 * (hfam g 0 w y)⁻¹ +
      2 * hfam g 1 w y * hfam g 3 w y * (hfam g 0 w y)⁻¹ -
      5 * hfam g 1 w y ^ 2 * hfam g 2 w y * (hfam g 0 w y)⁻¹ ^ 2 +
      2 * hfam g 1 w y ^ 4 * (hfam g 0 w y)⁻¹ ^ 3)
    (h₃ := fun w y => 6 * hfam g 2 w y * hfam g 3 w y * (hfam g 0 w y)⁻¹ +
      2 * hfam g 1 w y * hfam g 4 w y * (hfam g 0 w y)⁻¹ -
      12 * hfam g 1 w y * hfam g 2 w y ^ 2 * (hfam g 0 w y)⁻¹ ^ 2 -
      7 * hfam g 1 w y ^ 2 * hfam g 3 w y * (hfam g 0 w y)⁻¹ ^ 2 +
      18 * hfam g 1 w y ^ 3 * hfam g 2 w y * (hfam g 0 w y)⁻¹ ^ 3 -
      6 * hfam g 1 w y ^ 5 * (hfam g 0 w y)⁻¹ ^ 4)
    (hv' := fun w y => hfam g 1 w y * hfam g 3 w y * (hfam g 0 w y)⁻¹ -
      hfam g 1 w y ^ 2 * hfam g 2 w y * (hfam g 0 w y)⁻¹ ^ 2 / 2)
    (fun w _ y => ?_) (fun w _ y => ?_) (fun w _ y => ?_) (by uexp_tac) (by uexp_tac)
    (by uexp_tac) (by uexp_tac) (fun y w hw => ?_) (Continuous.continuousOn (by fun_prop))
    (fun y => (h2c.comp (Continuous.prodMk_left y)).continuousWithinAt)).congr_deriv ?_
  · convert! ((d1 w y).pow 2).mul (dE w y) using 1; pi_norm; ring
  · convert! ((((d1 w y).const_mul 2).mul (d2 w y)).mul (dE w y)).sub
      (((d1 w y).pow 3).mul ((dE w y).pow 2)) using 1; pi_norm; ring
  · convert! (((((d2 w y).pow 2).const_mul 2).mul (dE w y)).add
      ((((d1 w y).const_mul 2).mul (d3 w y)).mul (dE w y))).sub
      ((((d1 w y).pow 2).const_mul 5).mul (d2 w y) |>.mul ((dE w y).pow 2)) |>.add
      ((((d1 w y).pow 4).const_mul 2).mul ((dE w y).pow 3)) using 1; pi_norm; ring
  · have := ((t1 w hw y).pow 2).mul ((t0 w hw y).inv (hp w y).ne')
    convert! this using 1
    pi_norm
    field_simp
    ring
  · exact heat_congr (fun y => by field_simp; ring) x

theorem abs_log_le_add_inv {x : ℝ} (hx : 0 < x) : |Real.log x| ≤ x + x⁻¹ := by
  have h1 := Real.log_le_sub_one_of_pos hx
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 hx)
  rw [Real.log_inv] at h2
  have := inv_pos.2 hx
  rw [abs_le]; constructor <;> linarith

/-- Backward derivative of the entropy-form integrand `m r - e log e`, where `r` is the
smoothing of an arbitrary jet `G`. -/
theorem backward_entropy {G : ℕ → ℝ → ℝ} (hg : Jet g) (hlow : PosLow (g 0)) (hG : Jet G)
    (m : ℝ) {a x v : ℝ} (hv : v ∈ Icc 0 a) :
    HasDerivWithinAt (fun w => heat (a - w)
        (fun y => m * hfam G 0 w y - hfam g 0 w y * Real.log (hfam g 0 w y)) x)
      (heat (a - v) (fun y => hfam g 1 v y ^ 2 * (hfam g 0 v y)⁻¹ / 2) x) (Icc 0 a) v := by
  have d0 : ∀ w y, HasDerivAt (hfam g 0 w) (hfam g 1 w y) y := fun w y =>
    hfam_deriv hg (by norm_num) w y
  have d1 : ∀ w y, HasDerivAt (hfam g 1 w) (hfam g 2 w y) y := fun w y =>
    hfam_deriv hg (by norm_num) w y
  have d2 : ∀ w y, HasDerivAt (hfam g 2 w) (hfam g 3 w y) y := fun w y =>
    hfam_deriv hg (by norm_num) w y
  have r0 : ∀ w y, HasDerivAt (hfam G 0 w) (hfam G 1 w y) y := fun w y =>
    hfam_deriv hG (by norm_num) w y
  have r1 : ∀ w y, HasDerivAt (hfam G 1 w) (hfam G 2 w y) y := fun w y =>
    hfam_deriv hG (by norm_num) w y
  have r2 : ∀ w y, HasDerivAt (hfam G 2 w) (hfam G 3 w y) y := fun w y =>
    hfam_deriv hG (by norm_num) w y
  have dE := hfam_inv_deriv hg hlow
  have hp := hfam_pos hg hlow
  have dL : ∀ w y, HasDerivAt (fun y => Real.log (hfam g 0 w y))
      (hfam g 1 w y * (hfam g 0 w y)⁻¹) y := fun w y => by
    simpa [div_eq_mul_inv] using (d0 w y).log (hp w y).ne'
  have U0 := hfam_uexp hg (j := 0) (by norm_num) a
  have U1 := hfam_uexp hg (j := 1) (by norm_num) a
  have U2 := hfam_uexp hg (j := 2) (by norm_num) a
  have U3 := hfam_uexp hg (j := 3) (by norm_num) a
  have V0 := hfam_uexp hG (j := 0) (by norm_num) a
  have V2 := hfam_uexp hG (j := 2) (by norm_num) a
  have V3 := hfam_uexp hG (j := 3) (by norm_num) a
  have UE := hfam_inv_uexp hg hlow a
  have UL : UExp (Icc 0 a) (fun w y => Real.log (hfam g 0 w y)) :=
    (U0.add UE).of_le fun w _ y => (abs_log_le_add_inv (hp w y)).trans (le_abs_self _)
  have C0 := hfam_cont hg (j := 0) (by norm_num)
  have C1 := hfam_cont hg (j := 1) (by norm_num)
  have C2 := hfam_cont hg (j := 2) (by norm_num)
  have D2 := hfam_cont hG (j := 2) (by norm_num)
  have CE := hfam_inv_cont hg hlow
  have CL : Continuous (fun p : ℝ × ℝ => Real.log (hfam g 0 p.1 p.2)) :=
    C0.log fun p => (hp p.1 p.2).ne'
  have t0 : ∀ w ∈ Icc 0 a, ∀ y, HasDerivWithinAt (fun u => hfam g 0 u y)
      (hfam g 2 w y / 2) (Icc 0 a) w := fun w hw y => hfam_time hg (j := 0) (by norm_num) hw y
  have s0 : ∀ w ∈ Icc 0 a, ∀ y, HasDerivWithinAt (fun u => hfam G 0 u y)
      (hfam G 2 w y / 2) (Icc 0 a) w := fun w hw y => hfam_time hG (j := 0) (by norm_num) hw y
  have h2c : Continuous (fun p : ℝ × ℝ =>
      m * hfam G 2 p.1 p.2 - hfam g 2 p.1 p.2 * Real.log (hfam g 0 p.1 p.2) -
      hfam g 1 p.1 p.2 ^ 2 * (hfam g 0 p.1 p.2)⁻¹ - hfam g 2 p.1 p.2) := by fun_prop
  refine (hasDerivWithinAt_heat_backward hv
    (h := fun w y => m * hfam G 0 w y - hfam g 0 w y * Real.log (hfam g 0 w y))
    (h₁ := fun w y => m * hfam G 1 w y - hfam g 1 w y * Real.log (hfam g 0 w y) -
      hfam g 1 w y)
    (h₂ := fun w y => m * hfam G 2 w y - hfam g 2 w y * Real.log (hfam g 0 w y) -
      hfam g 1 w y ^ 2 * (hfam g 0 w y)⁻¹ - hfam g 2 w y)
    (h₃ := fun w y => m * hfam G 3 w y - hfam g 3 w y * Real.log (hfam g 0 w y) -
      3 * hfam g 1 w y * hfam g 2 w y * (hfam g 0 w y)⁻¹ +
      hfam g 1 w y ^ 3 * (hfam g 0 w y)⁻¹ ^ 2 - hfam g 3 w y)
    (hv' := fun w y => m * hfam G 2 w y / 2 - hfam g 2 w y / 2 * Real.log (hfam g 0 w y) -
      hfam g 2 w y / 2)
    (fun w _ y => ?_) (fun w _ y => ?_) (fun w _ y => ?_) (by uexp_tac) (by uexp_tac)
    (by uexp_tac) (by uexp_tac) (fun y w hw => ?_) (Continuous.continuousOn (by fun_prop))
    (fun y => (h2c.comp (Continuous.prodMk_left y)).continuousWithinAt)).congr_deriv ?_
  · convert! ((r0 w y).const_mul m).sub ((d0 w y).mul (dL w y)) using 1
    have := (hp w y).ne'
    pi_norm; field_simp; ring
  · convert! (((r1 w y).const_mul m).sub ((d1 w y).mul (dL w y))).sub (d1 w y) using 1
    pi_norm; ring
  · convert! (((((r2 w y).const_mul m).sub ((d2 w y).mul (dL w y))).sub
      (((d1 w y).pow 2).mul (dE w y))).sub (d2 w y)) using 1
    pi_norm; ring
  · have := ((s0 w hw y).const_mul m).sub ((t0 w hw y).mul ((t0 w hw y).log (hp w y).ne'))
    convert! this using 1
    have := (hp w y).ne'
    pi_norm
    field_simp
    ring
  · exact heat_congr (fun y => by ring) x

/-- Backward derivative of `u₁²` for the smoothing `u` of an arbitrary jet. -/
theorem backward_gradSq_linear {f : ℕ → ℝ → ℝ} (hf : Jet f) {a x v : ℝ} (hv : v ∈ Icc 0 a) :
    HasDerivWithinAt (fun w => heat (a - w) (fun y => hfam f 1 w y ^ 2) x)
      (heat (a - v) (fun y => -(hfam f 2 v y ^ 2)) x) (Icc 0 a) v := by
  have d1 : ∀ w y, HasDerivAt (hfam f 1 w) (hfam f 2 w y) y := fun w y =>
    hfam_deriv hf (by norm_num) w y
  have d2 : ∀ w y, HasDerivAt (hfam f 2 w) (hfam f 3 w y) y := fun w y =>
    hfam_deriv hf (by norm_num) w y
  have d3 : ∀ w y, HasDerivAt (hfam f 3 w) (hfam f 4 w y) y := fun w y =>
    hfam_deriv hf (by norm_num) w y
  have U1 := hfam_uexp hf (j := 1) (by norm_num) a
  have U2 := hfam_uexp hf (j := 2) (by norm_num) a
  have U3 := hfam_uexp hf (j := 3) (by norm_num) a
  have U4 := hfam_uexp hf (j := 4) (by norm_num) a
  have C1 := hfam_cont hf (j := 1) (by norm_num)
  have C2 := hfam_cont hf (j := 2) (by norm_num)
  have C3 := hfam_cont hf (j := 3) (by norm_num)
  have t1 : ∀ w ∈ Icc 0 a, ∀ y, HasDerivWithinAt (fun u => hfam f 1 u y)
      (hfam f 3 w y / 2) (Icc 0 a) w := fun w hw y => hfam_time hf (j := 1) (by norm_num) hw y
  have h2c : Continuous (fun p : ℝ × ℝ =>
      2 * hfam f 2 p.1 p.2 ^ 2 + 2 * hfam f 1 p.1 p.2 * hfam f 3 p.1 p.2) := by fun_prop
  refine (hasDerivWithinAt_heat_backward hv
    (h := fun w y => hfam f 1 w y ^ 2)
    (h₁ := fun w y => 2 * hfam f 1 w y * hfam f 2 w y)
    (h₂ := fun w y => 2 * hfam f 2 w y ^ 2 + 2 * hfam f 1 w y * hfam f 3 w y)
    (h₃ := fun w y => 6 * hfam f 2 w y * hfam f 3 w y + 2 * hfam f 1 w y * hfam f 4 w y)
    (hv' := fun w y => hfam f 1 w y * hfam f 3 w y)
    (fun w _ y => ?_) (fun w _ y => ?_) (fun w _ y => ?_) (by uexp_tac) (by uexp_tac)
    (by uexp_tac) (by uexp_tac) (fun y w hw => ?_) (Continuous.continuousOn (by fun_prop))
    (fun y => (h2c.comp (Continuous.prodMk_left y)).continuousWithinAt)).congr_deriv ?_
  · convert! (d1 w y).pow 2 using 1; pi_norm; ring
  · convert! ((d1 w y).const_mul 2).mul (d2 w y) using 1; pi_norm; ring
  · convert! (((d2 w y).pow 2).const_mul 2).add (((d1 w y).const_mul 2).mul (d3 w y)) using 1
    pi_norm; ring
  · convert! (t1 w hw y).pow 2 using 1; pi_norm; ring
  · exact heat_congr (fun y => by ring) x

/-- Backward derivative of `w - u²` (half a variance), for arbitrary jets `f` and `F`. -/
theorem backward_variance {f F : ℕ → ℝ → ℝ} (hf : Jet f) (hF : Jet F) {a x v : ℝ}
    (hv : v ∈ Icc 0 a) :
    HasDerivWithinAt (fun w => heat (a - w) (fun y => hfam F 0 w y - hfam f 0 w y ^ 2) x)
      (heat (a - v) (fun y => hfam f 1 v y ^ 2) x) (Icc 0 a) v := by
  have d0 : ∀ w y, HasDerivAt (hfam f 0 w) (hfam f 1 w y) y := fun w y =>
    hfam_deriv hf (by norm_num) w y
  have d1 : ∀ w y, HasDerivAt (hfam f 1 w) (hfam f 2 w y) y := fun w y =>
    hfam_deriv hf (by norm_num) w y
  have d2 : ∀ w y, HasDerivAt (hfam f 2 w) (hfam f 3 w y) y := fun w y =>
    hfam_deriv hf (by norm_num) w y
  have e0 : ∀ w y, HasDerivAt (hfam F 0 w) (hfam F 1 w y) y := fun w y =>
    hfam_deriv hF (by norm_num) w y
  have e1 : ∀ w y, HasDerivAt (hfam F 1 w) (hfam F 2 w y) y := fun w y =>
    hfam_deriv hF (by norm_num) w y
  have e2 : ∀ w y, HasDerivAt (hfam F 2 w) (hfam F 3 w y) y := fun w y =>
    hfam_deriv hF (by norm_num) w y
  have U0 := hfam_uexp hf (j := 0) (by norm_num) a
  have U1 := hfam_uexp hf (j := 1) (by norm_num) a
  have U2 := hfam_uexp hf (j := 2) (by norm_num) a
  have U3 := hfam_uexp hf (j := 3) (by norm_num) a
  have V0 := hfam_uexp hF (j := 0) (by norm_num) a
  have V2 := hfam_uexp hF (j := 2) (by norm_num) a
  have V3 := hfam_uexp hF (j := 3) (by norm_num) a
  have C0 := hfam_cont hf (j := 0) (by norm_num)
  have C1 := hfam_cont hf (j := 1) (by norm_num)
  have C2 := hfam_cont hf (j := 2) (by norm_num)
  have D2 := hfam_cont hF (j := 2) (by norm_num)
  have t0 : ∀ w ∈ Icc 0 a, ∀ y, HasDerivWithinAt (fun u => hfam f 0 u y)
      (hfam f 2 w y / 2) (Icc 0 a) w := fun w hw y => hfam_time hf (j := 0) (by norm_num) hw y
  have s0 : ∀ w ∈ Icc 0 a, ∀ y, HasDerivWithinAt (fun u => hfam F 0 u y)
      (hfam F 2 w y / 2) (Icc 0 a) w := fun w hw y => hfam_time hF (j := 0) (by norm_num) hw y
  have h2c : Continuous (fun p : ℝ × ℝ => hfam F 2 p.1 p.2 - 2 * hfam f 1 p.1 p.2 ^ 2 -
      2 * hfam f 0 p.1 p.2 * hfam f 2 p.1 p.2) := by fun_prop
  refine (hasDerivWithinAt_heat_backward hv
    (h := fun w y => hfam F 0 w y - hfam f 0 w y ^ 2)
    (h₁ := fun w y => hfam F 1 w y - 2 * hfam f 0 w y * hfam f 1 w y)
    (h₂ := fun w y => hfam F 2 w y - 2 * hfam f 1 w y ^ 2 - 2 * hfam f 0 w y * hfam f 2 w y)
    (h₃ := fun w y => hfam F 3 w y - 6 * hfam f 1 w y * hfam f 2 w y -
      2 * hfam f 0 w y * hfam f 3 w y)
    (hv' := fun w y => hfam F 2 w y / 2 - hfam f 0 w y * hfam f 2 w y)
    (fun w _ y => ?_) (fun w _ y => ?_) (fun w _ y => ?_) (by uexp_tac) (by uexp_tac)
    (by uexp_tac) (by uexp_tac) (fun y w hw => ?_) (Continuous.continuousOn (by fun_prop))
    (fun y => (h2c.comp (Continuous.prodMk_left y)).continuousWithinAt)).congr_deriv ?_
  · convert! (e0 w y).sub ((d0 w y).pow 2) using 1; pi_norm; ring
  · convert! (e1 w y).sub (((d0 w y).const_mul 2).mul (d1 w y)) using 1; pi_norm; ring
  · convert! ((e2 w y).sub (((d1 w y).pow 2).const_mul 2)).sub
      (((d0 w y).const_mul 2).mul (d2 w y)) using 1
    pi_norm; ring
  · convert! (s0 w hw y).sub ((t0 w hw y).pow 2) using 1; pi_norm; ring
  · exact heat_congr (fun y => by ring) x

end Fam

/-! ## Concrete jets -/

/-- The derivatives of a `C⁴` function with bounded derivatives of orders one to four form a
four-jet; the function itself has linear growth. -/
theorem jet_iteratedDeriv {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C) :
    Jet (fun j => iteratedDeriv j A) := by
  have hd : ∀ j < 4, ∀ y, HasDerivAt (iteratedDeriv j A) (iteratedDeriv (j + 1) A y) y := by
    intro j hj y
    rw [iteratedDeriv_succ]
    exact ((hA.differentiable_iteratedDeriv j (by exact_mod_cast hj)) y).hasDerivAt
  refine ⟨hd, hA.continuous_iteratedDeriv 4 le_rfl, fun j hj => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · refine ⟨|A 0| + |C|, 1, fun _ _ y => ?_⟩
    have hmv := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := A) (f' := iteratedDeriv 1 A) (C := C)
      (fun u _ => by
        have := (hd 0 (by norm_num) u).hasDerivWithinAt (s := univ)
        simpa only [iteratedDeriv_zero, zero_add] using this)
      (fun u _ => by rw [Real.norm_eq_abs]; exact hb 1 (by simp) u) (mem_univ 0) (mem_univ y)
    simp only [iteratedDeriv_zero, Real.norm_eq_abs, sub_zero] at hmv ⊢
    have h1 : |y| + 1 ≤ Real.exp |y| := Real.add_one_le_exp _
    have h2 : 1 ≤ Real.exp |y| := Real.one_le_exp (abs_nonneg _)
    have := abs_sub_abs_le_abs_sub (A y) (A 0)
    have hC : C ≤ |C| := le_abs_self C
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb 1 (by simp) 0)
    rw [one_mul]
    nlinarith [abs_nonneg (A 0), abs_nonneg y, abs_nonneg C]
  · exact ⟨C, 0, fun _ _ y => by
      simpa using hb j (Finset.mem_Icc.2 ⟨hj0, hj⟩) y⟩

/-- The four-jet of `exp (m * f)`. -/
noncomputable def expJet (m : ℝ) (d : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun y => Real.exp (m * d 0 y)
  | 1 => fun y => m * d 1 y * Real.exp (m * d 0 y)
  | 2 => fun y => (m * d 2 y + m ^ 2 * d 1 y ^ 2) * Real.exp (m * d 0 y)
  | 3 => fun y => (m * d 3 y + 3 * m ^ 2 * d 1 y * d 2 y + m ^ 3 * d 1 y ^ 3) *
      Real.exp (m * d 0 y)
  | _ => fun y => (m * d 4 y + 4 * m ^ 2 * d 1 y * d 3 y + 3 * m ^ 2 * d 2 y ^ 2 +
      6 * m ^ 3 * d 1 y ^ 2 * d 2 y + m ^ 4 * d 1 y ^ 4) * Real.exp (m * d 0 y)

theorem expT_exp_of_linear {f : ℝ → ℝ} {α β : ℝ} (hlin : ∀ y, |f y| ≤ α + β * |y|)
    (m : ℝ) : ExpT (fun y => Real.exp (m * f y)) := by
  refine ⟨Real.exp (|m| * α), |m| * β, fun _ _ y => ?_⟩
  rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_left (hlin y) (abs_nonneg m)
  have := neg_abs_le (m * f y)
  have := le_abs_self (m * f y)
  rw [abs_mul] at *
  nlinarith

theorem posLow_exp_of_linear {f : ℝ → ℝ} {α β : ℝ} (hβ : 0 ≤ β)
    (hlin : ∀ y, |f y| ≤ α + β * |y|) (m : ℝ) : PosLow (fun y => Real.exp (m * f y)) := by
  refine ⟨Real.exp (-(|m| * α)), |m| * β, Real.exp_pos _, mul_nonneg (abs_nonneg _) hβ,
    fun y => ?_⟩
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_left (hlin y) (abs_nonneg m)
  have := neg_abs_le (m * f y)
  rw [abs_mul] at *
  nlinarith

theorem Jet.exp {d : ℕ → ℝ → ℝ} (hd : Jet d) {α β : ℝ}
    (hlin : ∀ y, |d 0 y| ≤ α + β * |y|) (m : ℝ) : Jet (expJet m d) := by
  have D := hd.hasDeriv
  have hE : ∀ y, HasDerivAt (fun y => Real.exp (m * d 0 y)) (m * d 1 y * Real.exp (m * d 0 y)) y :=
    fun y => by
      convert! ((D 0 (by norm_num) y).const_mul m).exp using 1; ring
  have UE := expT_exp_of_linear hlin m
  have b := fun j (hj : j ≤ 4) => hd.expT j hj
  have b1 := b 1 (by norm_num); have b2 := b 2 (by norm_num); have b3 := b 3 (by norm_num)
  have b4 := b 4 le_rfl
  refine ⟨fun j hj y => ?_, ?_, fun j hj => ?_⟩
  · interval_cases j
    · exact hE y
    · convert! ((D 1 (by norm_num) y).const_mul m).mul (hE y) using 1
      simp only [expJet]; ring
    · convert! (((D 2 (by norm_num) y).const_mul m).add
        (((D 1 (by norm_num) y).pow 2).const_mul (m ^ 2))).mul (hE y) using 1
      simp only [expJet]; pi_norm; ring
    · convert! ((((D 3 (by norm_num) y).const_mul m).add
        ((((D 1 (by norm_num) y).const_mul (3 * m ^ 2)).mul (D 2 (by norm_num) y)))).add
        (((D 1 (by norm_num) y).pow 3).const_mul (m ^ 3))).mul (hE y) using 1
      simp only [expJet]; pi_norm; ring
  · have c := fun j (hj : j ≤ 4) => hd.continuous hj
    have := c 0 (by norm_num); have := c 1 (by norm_num); have := c 2 (by norm_num)
    have := c 3 (by norm_num); have := c 4 le_rfl
    simp only [expJet]
    fun_prop
  · interval_cases j <;> simp only [expJet] <;> uexp_tac

theorem linear_bound_of_iteratedDeriv {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C) :
    0 ≤ C ∧ ∀ y, |A y| ≤ |A 0| + C * |y| := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb 1 (by simp) 0)
  refine ⟨hC0, fun y => ?_⟩
  have hd : ∀ u, HasDerivAt A (iteratedDeriv 1 A u) u := fun u => by
    rw [iteratedDeriv_one]
    exact ((hA.differentiable (by norm_num)) u).hasDerivAt
  have hmv := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := A) (f' := iteratedDeriv 1 A) (C := C) (fun u _ => (hd u).hasDerivWithinAt)
    (fun u _ => by rw [Real.norm_eq_abs]; exact hb 1 (by simp) u) (mem_univ 0) (mem_univ y)
  simp only [Real.norm_eq_abs, sub_zero] at hmv
  have := abs_sub_abs_le_abs_sub (A y) (A 0)
  linarith

end SplitJets

end Heat

/-! ## Gaussian split identities behind U

Search tag: `PARISI_LB_SPLIT`. Keywords: Cole-Hopf, inserted mass, mixed derivative,
variance split, squared gradient, dissipation, U concavity, one-sided endpoints.

Consumers: (14.208)-(14.211), followed by (14.240)-(14.248). These local definitions
spell out the Gaussian integrals so the claims do not depend on the project's
Cole-Hopf API. The variance interval is closed and derivatives at its endpoints
are taken within that interval. Later bridges must identify these expressions
with the concrete recursion and propagate them through its earlier layers.
-/

/-- Gaussian specialization of `massTransform`. `Real.toNNReal` clamps variance;
the split lemmas therefore use derivatives within the admissible variance interval. -/
def gaussianLayer (m v : ℝ) (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  massTransform (gaussianReal 0 (Real.toNNReal v)) (fun z => A (x + z)) m

/-- Local inserted-mass response, corresponding to Delta in (14.208).
The inner mass varies while the outer mass and total variance remain fixed. -/
def splitMassResponse (m a : ℝ) (A : ℝ → ℝ) (x v : ℝ) : ℝ :=
  deriv (fun b => gaussianLayer m (a - v) (gaussianLayer b v A) x) m

/-- Tilted square of the j-th spatial derivative after Gaussian smoothing.
Use j=1 for the response derivative and j=2 for its negative curvature. -/
def splitSpatialMoment (j : ℕ) (m a : ℝ) (A : ℝ → ℝ) (x v : ℝ) : ℝ :=
  tiltedMean (gaussianReal 0 (Real.toNNReal (a - v)))
    (fun z => gaussianLayer m v A (x + z))
    (fun z => (iteratedDeriv j (gaussianLayer m v A) (x + z)) ^ 2) m

/-- A layer against a point mass is evaluation, at every mass. -/
theorem massTransform_dirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : α → ℝ) (a : α) (m : ℝ) : massTransform (Measure.dirac a) X m = X a := by
  unfold massTransform logLaplace
  split_ifs with hm
  · simp
  · rw [integral_dirac, Real.log_exp]; field_simp

/-- A Gaussian layer with zero variance is the identity. -/
theorem gaussianLayer_zero_var (m : ℝ) (A : ℝ → ℝ) : gaussianLayer m 0 A = A := by
  ext x
  simp [gaussianLayer, gaussianReal_zero_var, massTransform_dirac]

/-- Differentiating the inserted mass at a zero-length interval gives zero. -/
theorem splitMassResponse_zero (m a : ℝ) (A : ℝ → ℝ) (x : ℝ) :
    splitMassResponse m a A x 0 = 0 := by
  simp [splitMassResponse, gaussianLayer_zero_var]


/-! ### Heat-semigroup form of the split quantities -/

section SplitGlue

open Heat

theorem gaussianLayer_eq_log {m : ℝ} (hm : m ≠ 0) (v : ℝ) (A : ℝ → ℝ) :
    gaussianLayer m v A = fun y => Real.log (heat v (fun u => Real.exp (m * A u)) y) / m := by
  funext y; simp [gaussianLayer, massTransform, hm, logLaplace, heat]

theorem gaussianLayer_zero_mass (v : ℝ) (A : ℝ → ℝ) : gaussianLayer 0 v A = heat v A := by
  funext y; simp [gaussianLayer, massTransform, heat]

theorem hfam_expJet_zero (m v : ℝ) (A : ℝ → ℝ) :
    hfam (expJet m (fun j => iteratedDeriv j A)) 0 v = heat v (fun u => Real.exp (m * A u)) := by
  funext y; simp [hfam, expJet]

theorem hfam_iteratedDeriv_zero (v : ℝ) (A : ℝ → ℝ) :
    hfam (fun j => iteratedDeriv j A) 0 v = heat v A := by
  funext y; simp [hfam]

theorem deriv_log_hfam {g : ℕ → ℝ → ℝ} (hg : Jet g) (hlow : PosLow (g 0)) (m v : ℝ) :
    deriv (fun y => Real.log (hfam g 0 v y) / m) =
      fun y => hfam g 1 v y / hfam g 0 v y / m := by
  funext y
  exact (((hfam_deriv hg (j := 0) (by norm_num) v y).log
    (hfam_pos hg hlow v y).ne').div_const m).deriv

theorem deriv_ratio_hfam {g : ℕ → ℝ → ℝ} (hg : Jet g) (hlow : PosLow (g 0)) (m v : ℝ) :
    deriv (fun y => hfam g 1 v y / hfam g 0 v y / m) =
      fun y => (hfam g 2 v y * hfam g 0 v y - hfam g 1 v y * hfam g 1 v y) /
        hfam g 0 v y ^ 2 / m := by
  funext y
  exact (((hfam_deriv hg (j := 1) (by norm_num) v y).div
    (hfam_deriv hg (j := 0) (by norm_num) v y) (hfam_pos hg hlow v y).ne').div_const m).deriv

theorem deriv_hfam {g : ℕ → ℝ → ℝ} (hg : Jet g) {j : ℕ} (hj : j < 4) (v : ℝ) :
    deriv (hfam g j v) = hfam g (j + 1) v := by
  funext y; exact (hfam_deriv hg hj v y).deriv

theorem heat_hfam_zero {g : ℕ → ℝ → ℝ} (hg : Jet g) {a v : ℝ} (hv : v ∈ Icc 0 a) (x : ℝ) :
    heat (a - v) (hfam g 0 v) x = heat a (g 0) x := by
  obtain ⟨C, K, -, -, hb⟩ := (hg.expT 0 (by norm_num)).bound
  have := heat_heat (s := a - v) (t := v) (by linarith [hv.2]) hv.1
    (hg.continuous (by norm_num)) hb x
  rw [sub_add_cancel] at this
  exact this

theorem heat_pos_of_posLow {g : ℕ → ℝ → ℝ} (hg : Jet g) (hlow : PosLow (g 0)) (a x : ℝ) :
    0 < heat a (g 0) x := hfam_pos hg hlow a x

/-- Heat form of the squared-gradient moment at positive mass. -/
theorem splitSpatialMoment_one_eq {m a : ℝ} (hm : m ≠ 0) {A : ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    (hg : Jet g) (hlow : PosLow (g 0))
    (hlay : ∀ v, gaussianLayer m v A = fun y => Real.log (hfam g 0 v y) / m)
    {v : ℝ} (hv : v ∈ Icc 0 a) (x : ℝ) :
    splitSpatialMoment 1 m a A x v = 1 / m ^ 2 *
      heat (a - v) (fun y => hfam g 1 v y ^ 2 * (hfam g 0 v y)⁻¹) x / heat a (g 0) x := by
  have hp := hfam_pos hg hlow v
  have hE : ∀ y, Real.exp (m * (Real.log (hfam g 0 v y) / m)) = hfam g 0 v y := fun y => by
    rw [show m * (Real.log (hfam g 0 v y) / m) = Real.log (hfam g 0 v y) by field_simp,
      Real.exp_log (hp y)]
  unfold splitSpatialMoment tiltedMean
  rw [hlay v, iteratedDeriv_one, deriv_log_hfam hg hlow]
  have num : heat (a - v) (fun y => (hfam g 1 v y / hfam g 0 v y / m) ^ 2 *
      Real.exp (m * (Real.log (hfam g 0 v y) / m))) x = 1 / m ^ 2 *
      heat (a - v) (fun y => hfam g 1 v y ^ 2 * (hfam g 0 v y)⁻¹) x := by
    rw [← heat_const_mul]
    refine heat_congr (fun y => ?_) x
    rw [hE]; have := (hp y).ne'; field_simp
  have den : heat (a - v) (fun y => Real.exp (m * (Real.log (hfam g 0 v y) / m))) x =
      heat a (g 0) x := by
    rw [heat_congr hE]; exact heat_hfam_zero hg hv x
  exact congrArg₂ (· / ·) num den

/-- Heat form of the squared-curvature moment at positive mass. -/
theorem splitSpatialMoment_two_eq {m a : ℝ} (hm : m ≠ 0) {A : ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    (hg : Jet g) (hlow : PosLow (g 0))
    (hlay : ∀ v, gaussianLayer m v A = fun y => Real.log (hfam g 0 v y) / m)
    {v : ℝ} (hv : v ∈ Icc 0 a) (x : ℝ) :
    splitSpatialMoment 2 m a A x v = 1 / m ^ 2 *
      heat (a - v) (fun y => (hfam g 2 v y * hfam g 0 v y - hfam g 1 v y ^ 2) ^ 2 *
        (hfam g 0 v y)⁻¹ ^ 3) x / heat a (g 0) x := by
  have hp := hfam_pos hg hlow v
  have hE : ∀ y, Real.exp (m * (Real.log (hfam g 0 v y) / m)) = hfam g 0 v y := fun y => by
    rw [show m * (Real.log (hfam g 0 v y) / m) = Real.log (hfam g 0 v y) by field_simp,
      Real.exp_log (hp y)]
  unfold splitSpatialMoment tiltedMean
  rw [hlay v, iteratedDeriv_succ, iteratedDeriv_one, deriv_log_hfam hg hlow,
    deriv_ratio_hfam hg hlow]
  have num : heat (a - v) (fun y => ((hfam g 2 v y * hfam g 0 v y - hfam g 1 v y *
      hfam g 1 v y) / hfam g 0 v y ^ 2 / m) ^ 2 *
      Real.exp (m * (Real.log (hfam g 0 v y) / m))) x = 1 / m ^ 2 *
      heat (a - v) (fun y => (hfam g 2 v y * hfam g 0 v y - hfam g 1 v y ^ 2) ^ 2 *
        (hfam g 0 v y)⁻¹ ^ 3) x := by
    rw [← heat_const_mul]
    refine heat_congr (fun y => ?_) x
    rw [hE]; have := (hp y).ne'; field_simp
  have den : heat (a - v) (fun y => Real.exp (m * (Real.log (hfam g 0 v y) / m))) x =
      heat a (g 0) x := by
    rw [heat_congr hE]; exact heat_hfam_zero hg hv x
  exact congrArg₂ (· / ·) num den

/-- Heat form of the spatial moments at zero mass. -/
theorem splitSpatialMoment_zero_mass_eq {a : ℝ} {A : ℝ → ℝ} (hJ : Jet (fun j => iteratedDeriv j A))
    {j : ℕ} (hj : j = 1 ∨ j = 2) (x v : ℝ) :
    splitSpatialMoment j 0 a A x v =
      heat (a - v) (fun y => hfam (fun j => iteratedDeriv j A) j v y ^ 2) x := by
  have hlay : gaussianLayer 0 v A = hfam (fun j => iteratedDeriv j A) 0 v := by
    rw [gaussianLayer_zero_mass, hfam_iteratedDeriv_zero]
  have hder : iteratedDeriv j (gaussianLayer 0 v A) = hfam (fun j => iteratedDeriv j A) j v := by
    rw [hlay]
    rcases hj with rfl | rfl
    · rw [iteratedDeriv_one, deriv_hfam hJ (by norm_num)]
    · rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_hfam hJ (by norm_num),
        deriv_hfam hJ (by norm_num)]
  unfold splitSpatialMoment tiltedMean
  rw [hder]
  simp only [zero_mul, Real.exp_zero, mul_one, integral_const, probReal_univ, smul_eq_mul,
    div_one]
  rfl

theorem massTransform_scale_two {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (b : ℝ) : massTransform μ X b = massTransform μ (fun ω => 2 * X ω) (b / 2) / 2 := by
  unfold massTransform logLaplace
  by_cases hb : b = 0
  · subst hb; simp [integral_const_mul]
  · have hb2 : b / 2 ≠ 0 := div_ne_zero hb two_ne_zero
    rw [if_neg hb, if_neg hb2]
    have : (fun ω => Real.exp (b / 2 * (2 * X ω))) = fun ω => Real.exp (b * X ω) := by
      funext ω; ring_nf
    rw [this]; field_simp

theorem massTransform_neg_mass {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (s : ℝ) : massTransform μ X s = -massTransform μ (fun ω => -X ω) (-s) := by
  unfold massTransform logLaplace
  by_cases hs : s = 0
  · subst hs; simp [integral_neg]
  · rw [if_neg hs, if_neg (neg_ne_zero.2 hs)]
    have : (fun ω => Real.exp (-s * -X ω)) = fun ω => Real.exp (s * X ω) := by
      funext ω; ring_nf
    rw [this, div_neg, neg_neg]

/-- Uniform bounds on the first mass derivative and on the centred layer, for all inputs with
a common centred envelope, and masses in `[-2, 2]`. -/
theorem massTransform_deriv_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hint : ∀ k : ℝ, Integrable (fun ω => Real.exp (k * Y ω)) μ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (X : Ω → ℝ) (c : ℝ), Measurable X → (∀ ω, |X ω - c| ≤ Y ω) →
      (∀ b ∈ Ioo (-3 : ℝ) 3, DifferentiableAt ℝ (massTransform μ X) b) ∧
      (∀ b ∈ Icc (-2 : ℝ) 2, |deriv (massTransform μ X) b| ≤ M) ∧
      (∀ b ∈ Icc (-2 : ℝ) 2, |massTransform μ X b - c| ≤ M) := by
  have hYi1 : Integrable Y μ := (hint 1).mono' hY.aestronglyMeasurable (.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hY0 ω), one_mul]; linarith [Real.add_one_le_exp (Y ω)])
  have hYi2 : Integrable (fun ω => Y ω ^ 2) μ :=
    ((hint 1).const_mul 2).mono' (hY.pow_const 2).aestronglyMeasurable (.of_forall fun ω => by
      have := Real.pow_div_factorial_le_exp (Y ω) (hY0 ω) 2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul]
      norm_num [Nat.factorial] at this; linarith)
  have hexp : ∀ (X : Ω → ℝ) (c k : ℝ), Measurable X → (∀ ω, |X ω - c| ≤ 2 * Y ω) → 0 ≤ k →
      Integrable (fun ω => Real.exp (k * |X ω|)) μ := by
    intro X c k hX hXc hk
    refine ((hint (2 * k)).const_mul (Real.exp (k * |c|))).mono' (by fun_prop)
      (.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : |X ω| ≤ |c| + 2 * Y ω := by
      have := abs_sub_abs_le_abs_sub (X ω) c; linarith [hXc ω]
    nlinarith
  obtain ⟨M₁, hM₁, hunif⟩ := uniform_mass_second_derivative_bound (μ := μ)
    (Y := fun ω => 2 * Y ω) (hY.const_mul 2) (.of_forall fun ω => by linarith [hY0 ω])
    (by refine (hint 4).congr (.of_forall fun ω => ?_); simp only; ring_nf)
  set B₀ := ((∫ ω, (2 * Y ω) ^ 2 ∂μ) + (∫ ω, 2 * Y ω ∂μ) ^ 2) / 2
  have hB₀ : 0 ≤ B₀ := by
    have : 0 ≤ ∫ ω, (2 * Y ω) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    positivity
  have stepB : ∀ (X : Ω → ℝ) (c : ℝ), Measurable X → (∀ ω, |X ω - c| ≤ 2 * Y ω) →
      ∀ s ∈ Icc (0 : ℝ) 1, |deriv (massTransform μ X) s| ≤ B₀ + M₁ := by
    intro X c hX hXc s hs
    have hana := analyticOnNhd_massTransform hX (hexp X c 3 hX hXc (by norm_num))
    have h0 := hasDerivAt_massTransform_zero hX one_pos
      (by simpa using hexp X c 1 hX hXc (by norm_num))
    have hXi : ∀ j : ℕ, Integrable (fun ω => X ω ^ j) μ := fun j => by
      simpa using integrable_pow_mul_exp_of_exp_abs hX (m := 0) (a := 1) (by simp)
        (by simpa using hexp X c 1 hX hXc (by norm_num)) j
    have hX1 : Integrable X μ := by simpa using hXi 1
    have hb0 : |deriv (massTransform μ X) 0| ≤ B₀ := by
      rw [h0.deriv]
      have hsq : (fun ω => (X ω - c) ^ 2) = fun ω => X ω ^ 2 - 2 * c * X ω + c ^ 2 := by
        funext ω; ring
      have i1 : Integrable (fun ω => X ω ^ 2 - 2 * c * X ω) μ := (hXi 2).sub (hX1.const_mul _)
      have iZ2 : Integrable (fun ω => (X ω - c) ^ 2) μ := by
        rw [hsq]; exact i1.add (integrable_const _)
      have hZ2 : ∫ ω, (X ω - c) ^ 2 ∂μ = (∫ ω, X ω ^ 2 ∂μ) - 2 * c * (∫ ω, X ω ∂μ) + c ^ 2 := by
        rw [hsq, integral_add i1 (integrable_const _),
          integral_sub (hXi 2) (hX1.const_mul _), integral_const_mul, integral_const]
        simp
      have hZ1 : ∫ ω, (X ω - c) ∂μ = (∫ ω, X ω ∂μ) - c := by
        rw [integral_sub hX1 (integrable_const _), integral_const]; simp
      have hup : ∫ ω, (X ω - c) ^ 2 ∂μ ≤ ∫ ω, (2 * Y ω) ^ 2 ∂μ := by
        refine integral_mono iZ2
          ((hYi2.const_mul 4).congr (.of_forall fun ω => by simp only; ring)) fun ω => ?_
        have := hXc ω
        have h0 : 0 ≤ |X ω - c| := abs_nonneg _
        calc (X ω - c) ^ 2 = |X ω - c| ^ 2 := (sq_abs _).symm
          _ ≤ (2 * Y ω) ^ 2 := pow_le_pow_left₀ h0 this 2
      have hlow : 0 ≤ ∫ ω, (X ω - c) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
      have hZabs : |∫ ω, (X ω - c) ∂μ| ≤ ∫ ω, 2 * Y ω ∂μ :=
        (abs_integral_le_integral_abs).trans (integral_mono (hX1.sub (integrable_const c)).abs
          (hYi1.const_mul 2) fun ω => hXc ω)
      have hZsq : (∫ ω, (X ω - c) ∂μ) ^ 2 ≤ (∫ ω, 2 * Y ω ∂μ) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hZabs 2
      have hsq0 : 0 ≤ (∫ ω, (X ω - c) ∂μ) ^ 2 := sq_nonneg _
      have key : (∫ ω, X ω ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2 =
          (∫ ω, (X ω - c) ^ 2 ∂μ) - (∫ ω, (X ω - c) ∂μ) ^ 2 := by rw [hZ2, hZ1]; ring
      rw [key, abs_le]
      simp only [B₀]
      constructor <;> nlinarith
    have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (f := deriv (massTransform μ X)) (C := M₁)
      (fun u hu => (hana u ⟨by linarith [hu.1], by linarith [hu.2]⟩).deriv.differentiableAt)
      (fun u hu => by rw [Real.norm_eq_abs]; exact (hunif X c hX (.of_forall hXc)).2 u hu)
      ⟨le_rfl, zero_le_one⟩ hs
    simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1] at hmvt
    have := abs_sub_abs_le_abs_sub (deriv (massTransform μ X) s) (deriv (massTransform μ X) 0)
    nlinarith [hs.2]
  have stepC : ∀ (X : Ω → ℝ) (c : ℝ), Measurable X → (∀ ω, |X ω - c| ≤ 2 * Y ω) →
      ∀ s ∈ Icc (-1 : ℝ) 1, |deriv (massTransform μ X) s| ≤ B₀ + M₁ := by
    intro X c hX hXc s hs
    rcases le_total 0 s with h | h
    · exact stepB X c hX hXc s ⟨h, hs.2⟩
    · have hX' : Measurable (fun ω => -X ω) := hX.neg
      have hXc' : ∀ ω, |-X ω - -c| ≤ 2 * Y ω := fun ω => by
        rw [show -X ω - -c = -(X ω - c) by ring, abs_neg]; exact hXc ω
      have hana := analyticOnNhd_massTransform hX' (hexp _ _ 3 hX' hXc' (by norm_num))
      have hd : HasDerivAt (fun s => -massTransform μ (fun ω => -X ω) (-s))
          (deriv (massTransform μ (fun ω => -X ω)) (-s)) s := by
        have := (((hana (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩).differentiableAt
          |>.hasDerivAt).comp s (hasDerivAt_neg s)).neg
        convert! this using 1 <;> simp
      have hfun : massTransform μ X = fun s => -massTransform μ (fun ω => -X ω) (-s) :=
        funext (massTransform_neg_mass μ X)
      rw [hfun, hd.deriv]
      exact stepB _ _ hX' hXc' (-s) ⟨by linarith, by linarith [hs.1]⟩
  set M := (B₀ + M₁) / 4 + (B₀ + M₁) / 2 + ∫ ω, Y ω ∂μ
  have hYint0 : 0 ≤ ∫ ω, Y ω ∂μ := integral_nonneg hY0
  refine ⟨M, by positivity, fun X c hX hXc => ?_⟩
  have hXc2 : ∀ ω, |X ω - c| ≤ 2 * Y ω := fun ω => by linarith [hXc ω, hY0 ω]
  have hana := analyticOnNhd_massTransform hX (hexp X c 3 hX hXc2 (by norm_num))
  have hdiff : ∀ b ∈ Ioo (-3 : ℝ) 3, DifferentiableAt ℝ (massTransform μ X) b :=
    fun b hb => (hana b hb).differentiableAt
  have hderiv : ∀ b ∈ Icc (-2 : ℝ) 2, |deriv (massTransform μ X) b| ≤ (B₀ + M₁) / 4 := by
    intro b hb
    have h2X : Measurable (fun ω => 2 * X ω) := hX.const_mul 2
    have h2Xc : ∀ ω, |2 * X ω - 2 * c| ≤ 2 * Y ω := fun ω => by
      rw [show 2 * X ω - 2 * c = 2 * (X ω - c) by ring, abs_mul, abs_two]
      linarith [hXc ω]
    have hana2 := analyticOnNhd_massTransform h2X (hexp _ _ 3 h2X h2Xc (by norm_num))
    have hd : HasDerivAt (fun b => massTransform μ (fun ω => 2 * X ω) (b / 2) / 2)
        (deriv (massTransform μ (fun ω => 2 * X ω)) (b / 2) / 4) b := by
      have := ((((hana2 (b / 2) ⟨by linarith [hb.1], by linarith [hb.2]⟩).differentiableAt
        |>.hasDerivAt).comp b ((hasDerivAt_id b).div_const 2)).div_const 2)
      convert! this using 1; simp; ring
    have hfun : massTransform μ X = fun b => massTransform μ (fun ω => 2 * X ω) (b / 2) / 2 :=
      funext (massTransform_scale_two μ X)
    rw [hfun, hd.deriv, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact div_le_div_of_nonneg_right (stepC _ _ h2X h2Xc (b / 2)
      ⟨by linarith [hb.1], by linarith [hb.2]⟩) (by norm_num)
  have hB : 0 ≤ (B₀ + M₁) / 4 := by positivity
  refine ⟨hdiff, fun b hb => (hderiv b hb).trans (by simp only [M]; linarith), fun b hb => ?_⟩
  have hmvt := (convex_Icc (-2 : ℝ) 2).norm_image_sub_le_of_norm_deriv_le
    (f := massTransform μ X) (C := (B₀ + M₁) / 4) (x := 0)
    (fun u hu => hdiff u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (fun u hu => by rw [Real.norm_eq_abs]; exact hderiv u hu) ⟨by norm_num, by norm_num⟩ hb
  simp only [Real.norm_eq_abs, sub_zero] at hmvt
  have h0 : massTransform μ X 0 = ∫ ω, X ω ∂μ := by simp [massTransform]
  have hX1 : Integrable X μ := by
    simpa using integrable_pow_mul_exp_of_exp_abs hX (m := 0) (a := 1) (by simp)
      (by simpa using hexp X c 1 hX hXc2 (by norm_num)) 1
  have hc : |massTransform μ X 0 - c| ≤ ∫ ω, Y ω ∂μ := by
    rw [h0, show (∫ ω, X ω ∂μ) - c = ∫ ω, (X ω - c) ∂μ by
      rw [integral_sub hX1 (integrable_const c), integral_const]; simp]
    exact (abs_integral_le_integral_abs).trans (integral_mono (hX1.sub (integrable_const c)).abs
      hYi1 fun ω => hXc ω)
  have hbabs : |b| ≤ 2 := abs_le.2 ⟨hb.1, hb.2⟩
  calc |massTransform μ X b - c|
      ≤ |massTransform μ X b - massTransform μ X 0| + |massTransform μ X 0 - c| := by
        have := abs_sub_le (massTransform μ X b) (massTransform μ X 0) c; linarith
    _ ≤ (B₀ + M₁) / 4 * |b| + ∫ ω, Y ω ∂μ := add_le_add hmvt hc
    _ ≤ M := by simp only [M]; nlinarith

theorem lipschitz_of_iteratedDeriv {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C) (y z : ℝ) :
    |A (y + z) - A y| ≤ C * |z| := by
  have hd : ∀ u, HasDerivAt A (iteratedDeriv 1 A u) u := fun u => by
    rw [iteratedDeriv_one]
    exact ((hA.differentiable (by norm_num)) u).hasDerivAt
  have hmv := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := A) (f' := iteratedDeriv 1 A) (C := C) (fun u _ => (hd u).hasDerivWithinAt)
    (fun u _ => by rw [Real.norm_eq_abs]; exact hb 1 (by simp) u) (mem_univ y) (mem_univ (y + z))
  simpa [Real.norm_eq_abs] using hmv

/-- Uniform mass bounds for the inner Gaussian layer. -/
theorem gaussianLayer_mass_bounds {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C) (v : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y,
      (∀ b ∈ Ioo (-3 : ℝ) 3, DifferentiableAt ℝ (fun b => gaussianLayer b v A y) b) ∧
      (∀ b ∈ Icc (-2 : ℝ) 2, |deriv (fun b => gaussianLayer b v A y) b| ≤ M) ∧
      (∀ b ∈ Icc (-2 : ℝ) 2, |gaussianLayer b v A y - A y| ≤ M) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb 1 (by simp) 0)
  obtain ⟨M, hM, h⟩ := massTransform_deriv_bound (μ := gaussianReal 0 v.toNNReal)
    (Y := fun z => C * |z|) (by fun_prop) (fun z => by positivity)
    (fun k => by simpa [mul_assoc] using integrable_gaussian_exp_abs (k * C) v.toNNReal)
  refine ⟨M, hM, fun y => ?_⟩
  exact h (fun z => A (y + z)) (A y) (hA.continuous.comp (continuous_add_left y)).measurable
    (fun z => lipschitz_of_iteratedDeriv hA hb y z)

theorem continuous_gaussianLayer {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C) (b v : ℝ) :
    Continuous (gaussianLayer b v A) := by
  have hJ := Heat.jet_iteratedDeriv hA hb
  obtain ⟨hC0, hlin⟩ := Heat.linear_bound_of_iteratedDeriv hA hb
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [gaussianLayer_zero_mass, ← hfam_iteratedDeriv_zero]
    exact (Heat.hfam_cont hJ (j := 0) (by norm_num)).comp (Continuous.prodMk_right v)
  · have hlin' : ∀ y, |(fun j => iteratedDeriv j A) 0 y| ≤ |A 0| + C * |y| := by simpa using hlin
    have hg := hJ.exp hlin' b
    have hlow := Heat.posLow_exp_of_linear hC0 hlin' b
    rw [gaussianLayer_eq_log hb0, ← hfam_expJet_zero]
    exact (((Heat.hfam_cont hg (j := 0) (by norm_num)).comp (Continuous.prodMk_right v)).log
      fun y => (Heat.hfam_pos hg hlow v y).ne').div_const b

/-- Heat form of the split mass response at zero mass: half a smoothed variance. -/
theorem splitMassResponse_zero_mass_eq {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C) (a x v : ℝ) :
    splitMassResponse 0 a A x v = heat (a - v) (fun y => 1 / 2 *
      (hfam (jetMul (fun j => iteratedDeriv j A) (fun j => iteratedDeriv j A)) 0 v y -
        hfam (fun j => iteratedDeriv j A) 0 v y ^ 2)) x := by
  have hJ := jet_iteratedDeriv hA hb
  obtain ⟨hC0, hlin⟩ := linear_bound_of_iteratedDeriv hA hb
  obtain ⟨M, hM, hB⟩ := gaussianLayer_mass_bounds hA hb v
  set F := jetMul (fun j => iteratedDeriv j A) (fun j => iteratedDeriv j A)
  have hF := hJ.mul hJ
  set ψ : ℝ → ℝ := fun y => 1 / 2 *
    (hfam F 0 v y - hfam (fun j => iteratedDeriv j A) 0 v y ^ 2)
  have hψc : Continuous ψ := by
    have h1 := (hfam_cont hF (j := 0) (by norm_num)).comp (Continuous.prodMk_right v)
    have h2 := (hfam_cont hJ (j := 0) (by norm_num)).comp (Continuous.prodMk_right v)
    exact continuous_const.mul (h1.sub (h2.pow 2))
  have hψ : ∀ y, deriv (fun b => gaussianLayer b v A y) 0 = ψ y := by
    intro y
    have hint : Integrable (fun z => Real.exp (1 * |A (y + z)|)) (gaussianReal 0 v.toNNReal) := by
      refine ((integrable_gaussian_exp_abs C v.toNNReal).const_mul (Real.exp |A y|)).mono'
        ((continuous_const.mul (hA.continuous.comp (continuous_add_left y)).abs).rexp
          |>.aestronglyMeasurable) (.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add, one_mul]
      refine Real.exp_le_exp.2 ?_
      have := lipschitz_of_iteratedDeriv hA hb y z
      have := abs_sub_abs_le_abs_sub (A (y + z)) (A y)
      linarith
    have := hasDerivAt_massTransform_zero (μ := gaussianReal 0 v.toNNReal)
      (X := fun z => A (y + z)) (hA.continuous.comp (continuous_add_left y)).measurable
      one_pos hint
    rw [show (fun b => gaussianLayer b v A y) = massTransform (gaussianReal 0 v.toNNReal)
      (fun z => A (y + z)) from rfl, this.deriv]
    simp only [ψ, F, hfam, jetMul, heat, iteratedDeriv_zero]
    ring_nf
  unfold splitMassResponse
  simp only [gaussianLayer_zero_mass]
  have key : HasDerivAt (fun b => ∫ z, gaussianLayer b v A (x + z) ∂gaussianReal 0 (a - v).toNNReal)
      (∫ z, deriv (fun b => gaussianLayer b v A (x + z)) 0 ∂gaussianReal 0 (a - v).toNNReal) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds (0 : ℝ) one_pos)
      (F' := fun b z => deriv (fun b => gaussianLayer b v A (x + z)) b) (bound := fun _ => M)
      (.of_forall fun b => ((continuous_gaussianLayer hA hb b v).comp
        (continuous_add_left x)).aestronglyMeasurable) ?_ ?_
      (.of_forall fun z b hb' => ?_) (integrable_const M) (.of_forall fun z b hb' => ?_)).2
    · refine ((integrable_gaussian_exp_abs 1 _).const_mul (|A 0| + C * |x| + M + C)).mono'
        ((continuous_gaussianLayer hA hb 0 v).comp (continuous_add_left x)).aestronglyMeasurable
        (.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, Function.comp_apply]
      have h1 := (hB (x + z)).2.2 0 ⟨by norm_num, by norm_num⟩
      have h2 := hlin (x + z)
      have h3 : |x + z| ≤ |x| + |z| := abs_add_le x z
      have h4 : |z| + 1 ≤ Real.exp (1 * |z|) := by rw [one_mul]; exact Real.add_one_le_exp _
      have h5 := abs_sub_abs_le_abs_sub (gaussianLayer 0 v A (x + z)) (A (x + z))
      have h6 : 1 ≤ Real.exp (1 * |z|) := by linarith [abs_nonneg z]
      have h7 : 0 ≤ |A 0| + C * |x| + M := by positivity
      have h8 : (|A 0| + C * |x| + M) * 1 ≤ (|A 0| + C * |x| + M) * Real.exp (1 * |z|) :=
        mul_le_mul_of_nonneg_left h6 h7
      have h9 : C * |z| ≤ C * Real.exp (1 * |z|) := mul_le_mul_of_nonneg_left (by linarith) hC0
      have h10 : C * |x + z| ≤ C * (|x| + |z|) := mul_le_mul_of_nonneg_left h3 hC0
      nlinarith [abs_nonneg z, abs_nonneg x]
    · exact (hψc.comp (continuous_add_left x)).aestronglyMeasurable.congr
        (.of_forall fun z => (hψ (x + z)).symm)
    · rw [Real.norm_eq_abs]
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hb'
      exact (hB (x + z)).2.1 b ⟨by linarith [(abs_lt.1 hb').1], by linarith [(abs_lt.1 hb').2]⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hb'
      exact ((hB (x + z)).1 b ⟨by linarith [(abs_lt.1 hb').1], by
        linarith [(abs_lt.1 hb').2]⟩).hasDerivAt
  rw [show (fun b => heat (a - v) (gaussianLayer b v A) x) =
    fun b => ∫ z, gaussianLayer b v A (x + z) ∂gaussianReal 0 (a - v).toNNReal from rfl, key.deriv]
  exact congrArg _ (funext fun z => hψ (x + z))

/-- Heat form of the split mass response at positive mass. -/
theorem splitMassResponse_pos_mass_eq {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C) {m a v : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) (hm0 : m ≠ 0) (hv : v ∈ Icc 0 a) (x : ℝ) :
    splitMassResponse m a A x v = 1 / m ^ 2 *
      heat (a - v) (fun y => m * hfam (jetMul (fun j => iteratedDeriv j A)
        (expJet m (fun j => iteratedDeriv j A))) 0 v y -
        hfam (expJet m (fun j => iteratedDeriv j A)) 0 v y *
          Real.log (hfam (expJet m (fun j => iteratedDeriv j A)) 0 v y)) x /
      heat a (expJet m (fun j => iteratedDeriv j A) 0) x := by
  have hJ := jet_iteratedDeriv hA hb
  obtain ⟨hC0, hlin⟩ := linear_bound_of_iteratedDeriv hA hb
  have hlin' : ∀ y, |(fun j => iteratedDeriv j A) 0 y| ≤ |A 0| + C * |y| := by simpa using hlin
  have hg : Jet (expJet m (fun j => iteratedDeriv j A)) := hJ.exp hlin' m
  have hlow : PosLow (expJet m (fun j => iteratedDeriv j A) 0) := posLow_exp_of_linear hC0 hlin' m
  have hG : Jet (jetMul (fun j => iteratedDeriv j A) (expJet m (fun j => iteratedDeriv j A))) :=
    hJ.mul hg
  obtain ⟨M, hM, hB⟩ := gaussianLayer_mass_bounds hA hb v
  set g := expJet m (fun j => iteratedDeriv j A) with hgdef
  set e := hfam g 0 v with hedef
  set G := hfam (jetMul (fun j => iteratedDeriv j A) g) 0 v with hGdef
  have he : ∀ y, 0 < e y := hfam_pos hg hlow v
  have hec : Continuous e := (hfam_cont hg (j := 0) (by norm_num)).comp (Continuous.prodMk_right v)
  have hGc : Continuous G :=
    (hfam_cont hG (j := 0) (by norm_num)).comp (Continuous.prodMk_right v)
  have hlay : gaussianLayer m v A = fun y => Real.log (e y) / m := by
    rw [gaussianLayer_eq_log hm0, ← hfam_expJet_zero]
  have hE : ∀ y, Real.exp (m * gaussianLayer m v A y) = e y := by
    intro y; rw [hlay]; simp only; rw [mul_div_cancel₀ _ hm0, Real.exp_log (he y)]
  set ψ : ℝ → ℝ := fun y => (m * (G y / e y) - Real.log (e y)) / m ^ 2 with hψdef
  have hψc : Continuous ψ :=
    (((continuous_const.mul (hGc.div hec fun y => (he y).ne')).sub
      (hec.log fun y => (he y).ne')).div_const _)
  have hψ : ∀ y, HasDerivAt (fun b => gaussianLayer b v A y) (ψ y) m := by
    intro y
    have hint : Integrable (fun z => Real.exp (2 * |A (y + z)|)) (gaussianReal 0 v.toNNReal) := by
      refine ((integrable_gaussian_exp_abs (2 * C) v.toNNReal).const_mul
        (Real.exp (2 * |A y|))).mono'
        ((continuous_const.mul (hA.continuous.comp (continuous_add_left y)).abs).rexp
          |>.aestronglyMeasurable) (.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := lipschitz_of_iteratedDeriv hA hb y z
      have := abs_sub_abs_le_abs_sub (A (y + z)) (A y)
      nlinarith
    have h := hasDerivAt_massTransform (μ := gaussianReal 0 v.toNNReal)
      (X := fun z => A (y + z)) (hA.continuous.comp (continuous_add_left y)).measurable
      (a := 2) (by rw [abs_of_nonneg hm.1]; linarith [hm.2]) hm0 hint
    convert! h using 1
  have hK : ∀ b ∈ Icc (-2 : ℝ) 2, ∀ z, Real.exp (m * gaussianLayer b v A (x + z)) ≤
      Real.exp (|A 0| + C * |x| + M) * Real.exp (C * |z|) := by
    intro b hb' z
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 := (hB (x + z)).2.2 b hb'
    have h2 := hlin (x + z)
    have h3 : C * |x + z| ≤ C * (|x| + |z|) := mul_le_mul_of_nonneg_left (abs_add_le x z) hC0
    have h5 := abs_sub_abs_le_abs_sub (gaussianLayer b v A (x + z)) (A (x + z))
    have h6 : m * gaussianLayer b v A (x + z) ≤ |gaussianLayer b v A (x + z)| := by
      have := le_abs_self (gaussianLayer b v A (x + z))
      have := abs_nonneg (gaussianLayer b v A (x + z))
      have := neg_abs_le (gaussianLayer b v A (x + z))
      nlinarith [hm.1, hm.2]
    linarith
  have hball : ∀ b ∈ Metric.ball m 1, b ∈ Icc (-2 : ℝ) 2 ∧ b ∈ Ioo (-3 : ℝ) 3 := by
    intro b hb'
    rw [Metric.mem_ball, Real.dist_eq] at hb'
    have := abs_lt.1 hb'
    exact ⟨⟨by linarith [hm.1], by linarith [hm.2]⟩, ⟨by linarith [hm.1], by linarith [hm.2]⟩⟩
  have key : HasDerivAt (fun b => ∫ z, Real.exp (m * gaussianLayer b v A (x + z))
        ∂gaussianReal 0 (a - v).toNNReal)
      (∫ z, m * deriv (fun b => gaussianLayer b v A (x + z)) m *
        Real.exp (m * gaussianLayer m v A (x + z)) ∂gaussianReal 0 (a - v).toNNReal) m := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds m one_pos)
      (F' := fun b z => m * deriv (fun b => gaussianLayer b v A (x + z)) b *
        Real.exp (m * gaussianLayer b v A (x + z)))
      (bound := fun z => M * (Real.exp (|A 0| + C * |x| + M) * Real.exp (C * |z|)))
      (.of_forall fun b => (continuous_const.mul ((continuous_gaussianLayer hA hb b v).comp
        (continuous_add_left x))).rexp.aestronglyMeasurable) ?_ ?_
      (.of_forall fun z b hb' => ?_) ?_ (.of_forall fun z b hb' => ?_)).2
    · refine ((integrable_gaussian_exp_abs C _).const_mul
        (Real.exp (|A 0| + C * |x| + M))).mono'
        (continuous_const.mul ((continuous_gaussianLayer hA hb m v).comp
          (continuous_add_left x))).rexp.aestronglyMeasurable (.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hK m ⟨by linarith [hm.1], by linarith [hm.2]⟩ z
    · refine ((by fun_prop : Continuous fun z => m * ψ (x + z) * e (x + z))
        |>.aestronglyMeasurable).congr (.of_forall fun z => ?_)
      simp only
      rw [(hψ (x + z)).deriv, hE]
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hm.1, abs_of_pos (Real.exp_pos _)]
      have h1 := (hB (x + z)).2.1 b (hball b hb').1
      have h2 := hK b (hball b hb').1 z
      have h3 : m * |deriv (fun b => gaussianLayer b v A (x + z)) b| ≤ M := by
        nlinarith [abs_nonneg (deriv (fun b => gaussianLayer b v A (x + z)) b), hm.1, hm.2]
      calc m * |deriv (fun b => gaussianLayer b v A (x + z)) b| *
            Real.exp (m * gaussianLayer b v A (x + z))
          ≤ M * Real.exp (m * gaussianLayer b v A (x + z)) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 hM
    · exact ((integrable_gaussian_exp_abs C _).const_mul _).const_mul _
    · have := (((hB (x + z)).1 b (hball b hb').2).hasDerivAt.const_mul m).exp
      convert! this using 1; ring
  have hI : (∫ z, Real.exp (m * gaussianLayer m v A (x + z)) ∂gaussianReal 0 (a - v).toNNReal) =
      heat a (g 0) x := by
    rw [← heat_hfam_zero hg hv x]
    exact integral_congr_ae (.of_forall fun z => hE (x + z))
  have hIpos : 0 < heat a (g 0) x := heat_pos_of_posLow hg hlow a x
  have hfun : (fun b => gaussianLayer m (a - v) (gaussianLayer b v A) x) =
      fun b => Real.log (∫ z, Real.exp (m * gaussianLayer b v A (x + z))
        ∂gaussianReal 0 (a - v).toNNReal) / m := by
    funext b; rw [gaussianLayer_eq_log hm0]; rfl
  unfold splitMassResponse
  rw [hfun, ((key.log (by rw [hI]; exact hIpos.ne')).div_const m).deriv, hI]
  have hnum : (∫ z, m * deriv (fun b => gaussianLayer b v A (x + z)) m *
        Real.exp (m * gaussianLayer m v A (x + z)) ∂gaussianReal 0 (a - v).toNNReal) =
      1 / m * heat (a - v) (fun y => m * G y - e y * Real.log (e y)) x := by
    rw [← heat_const_mul]
    refine integral_congr_ae (.of_forall fun z => ?_)
    simp only
    rw [(hψ (x + z)).deriv, hE, hψdef]
    have := (he (x + z)).ne'
    field_simp
  rw [hnum]
  field_simp

end SplitGlue

/-- Concrete mixed mass/variance formula (14.209); includes m=0 and both endpoints. -/
theorem hasDerivWithinAt_splitMassResponse {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hbound : ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C)
    {m a v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivWithinAt (splitMassResponse m a A x)
      (splitSpatialMoment 1 m a A x v / 2) (Icc (0 : ℝ) a) v := by
  open Heat in
  · obtain ⟨C, hb⟩ := hbound
    have hJ := jet_iteratedDeriv hA hb
    obtain ⟨hC0, hlin⟩ := linear_bound_of_iteratedDeriv hA hb
    rcases eq_or_ne m 0 with rfl | hm0
    · have h := (backward_variance (x := x) hJ (hJ.mul hJ) hv).const_mul (1 / 2)
      refine (h.congr_of_mem (fun w _ => ?_) hv).congr_deriv ?_
      · rw [splitMassResponse_zero_mass_eq hA hb, heat_const_mul]
      · rw [splitSpatialMoment_zero_mass_eq hJ (Or.inl rfl)]; ring
    · have hlin' : ∀ y, |(fun j => iteratedDeriv j A) 0 y| ≤ |A 0| + C * |y| := by simpa using hlin
      have hg : Jet (expJet m (fun j => iteratedDeriv j A)) := hJ.exp hlin' m
      have hlow : PosLow (expJet m (fun j => iteratedDeriv j A) 0) :=
        posLow_exp_of_linear hC0 hlin' m
      have h := ((backward_entropy (x := x) hg hlow (hJ.mul hg) m hv).const_mul
        (1 / m ^ 2)).div_const (heat a (expJet m (fun j => iteratedDeriv j A) 0) x)
      refine (h.congr_of_mem (fun w hw => ?_) hv).congr_deriv ?_
      · rw [splitMassResponse_pos_mass_eq hA hb hm hm0 hw]
      · have hlay : ∀ v, gaussianLayer m v A =
            fun y => Real.log (hfam (expJet m (fun j => iteratedDeriv j A)) 0 v y) / m := by
          intro v; rw [gaussianLayer_eq_log hm0, ← hfam_expJet_zero]
        rw [splitSpatialMoment_one_eq hm0 hg hlow hlay hv,
          show (fun y => hfam (expJet m (fun j => iteratedDeriv j A)) 1 v y ^ 2 *
            (hfam (expJet m (fun j => iteratedDeriv j A)) 0 v y)⁻¹ / 2) = fun y => 1 / 2 *
            (hfam (expJet m (fun j => iteratedDeriv j A)) 1 v y ^ 2 *
            (hfam (expJet m (fun j => iteratedDeriv j A)) 0 v y)⁻¹) from funext fun y => by ring,
          heat_const_mul]
        ring

/-- Dissipation of the concrete squared-gradient moment, yielding (14.211). -/
theorem hasDerivWithinAt_splitSpatialMoment {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hbound : ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C)
    {m a v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivWithinAt (splitSpatialMoment 1 m a A x)
      (-splitSpatialMoment 2 m a A x v) (Icc (0 : ℝ) a) v := by
  obtain ⟨C, hC⟩ := hbound
  have hJ := Heat.jet_iteratedDeriv hA hC
  obtain ⟨hC0, hlin⟩ := Heat.linear_bound_of_iteratedDeriv hA hC
  rcases eq_or_ne m 0 with rfl | hm0
  · have key := Heat.backward_gradSq_linear hJ (x := x) hv
    refine (key.congr_of_mem (fun w _ => splitSpatialMoment_zero_mass_eq hJ (Or.inl rfl) x w)
      hv).congr_deriv ?_
    rw [splitSpatialMoment_zero_mass_eq hJ (Or.inr rfl), Heat.heat_neg]
  · have hlin' : ∀ y, |(fun j => iteratedDeriv j A) 0 y| ≤ |A 0| + C * |y| := by simpa using hlin
    have hg := hJ.exp hlin' m
    have hlow : Heat.PosLow (Heat.expJet m (fun j => iteratedDeriv j A) 0) :=
      Heat.posLow_exp_of_linear hC0 hlin' m
    have hlay : ∀ v, gaussianLayer m v A = fun y =>
        Real.log (Heat.hfam (Heat.expJet m (fun j => iteratedDeriv j A)) 0 v y) / m := fun v => by
      rw [gaussianLayer_eq_log hm0, hfam_expJet_zero]
    have key := ((Heat.backward_gradSq hg hlow (x := x) hv).const_mul (1 / m ^ 2)).div_const
      (Heat.heat a (Heat.expJet m (fun j => iteratedDeriv j A) 0) x)
    refine (key.congr_of_mem (fun w hw => splitSpatialMoment_one_eq hm0 hg hlow hlay hw x)
      hv).congr_deriv ?_
    rw [splitSpatialMoment_two_eq hm0 hg hlow hlay hv x, Heat.heat_neg]
    ring

/-- Concavity needed for U, before averaging against the earlier recursion weights. -/
theorem concaveOn_splitMassResponse {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hbound : ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C)
    {m a : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a) (x : ℝ) :
    ConcaveOn ℝ (Icc (0 : ℝ) a) (splitMassResponse m a A x) := by
  have h1 := fun v (hv : v ∈ Icc (0 : ℝ) a) =>
    hasDerivWithinAt_splitMassResponse hA hbound hm ha hv x
  have h2 := fun v (hv : v ∈ Icc (0 : ℝ) a) =>
    hasDerivWithinAt_splitSpatialMoment hA hbound hm ha hv x
  have hint : interior (Icc (0 : ℝ) a) = Ioo 0 a := interior_Icc
  have hS2 : ∀ v, 0 ≤ splitSpatialMoment 2 m a A x v := fun v =>
    div_nonneg (integral_nonneg fun z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (integral_nonneg fun z => (Real.exp_pos _).le)
  have hanti : AntitoneOn (splitSpatialMoment 1 m a A x) (Icc (0 : ℝ) a) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 a)
      (fun v hv => (h2 v hv).continuousWithinAt) ?_ ?_
    · rw [hint]
      exact fun v hv => ((h2 v (Ioo_subset_Icc_self hv)).hasDerivAt
        (Icc_mem_nhds hv.1 hv.2)).differentiableAt.differentiableWithinAt
    · rw [hint]
      intro v hv
      rw [((h2 v (Ioo_subset_Icc_self hv)).hasDerivAt (Icc_mem_nhds hv.1 hv.2)).deriv]
      linarith [hS2 v]
  refine AntitoneOn.concaveOn_of_deriv (convex_Icc 0 a)
    (fun v hv => (h1 v hv).continuousWithinAt) ?_ ?_
  · rw [hint]
    exact fun v hv => ((h1 v (Ioo_subset_Icc_self hv)).hasDerivAt
      (Icc_mem_nhds hv.1 hv.2)).differentiableAt.differentiableWithinAt
  · rw [hint]
    intro u hu w hw huw
    rw [((h1 u (Ioo_subset_Icc_self hu)).hasDerivAt (Icc_mem_nhds hu.1 hu.2)).deriv,
      ((h1 w (Ioo_subset_Icc_self hw)).hasDerivAt (Icc_mem_nhds hw.1 hw.2)).deriv]
    have := hanti (Ioo_subset_Icc_self hu) (Ioo_subset_Icc_self hw) huw
    linarith

/-- A fixed nonnegative weighted average preserves the split concavity. -/
theorem concaveOn_integral_weighted {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F : Ω → ℝ → ℝ} {W : Ω → ℝ} {a b : ℝ}
    (hW : ∀ᵐ ω ∂μ, 0 ≤ W ω)
    (hF : ∀ᵐ ω ∂μ, ConcaveOn ℝ (Icc a b) (F ω))
    (hint : ∀ v ∈ Icc a b, Integrable (fun ω => W ω * F ω v) μ) :
    ConcaveOn ℝ (Icc a b) (fun v => ∫ ω, W ω * F ω v ∂μ) := by
  refine ⟨convex_Icc a b, fun x hx y hy s t hs ht hst => ?_⟩
  have hxy : s • x + t • y ∈ Icc a b := convex_Icc a b hx hy hs ht hst
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((hint x hx).const_mul s) ((hint y hy).const_mul t)]
  refine integral_mono_ae (((hint x hx).const_mul s).add ((hint y hy).const_mul t))
    (hint _ hxy) ?_
  filter_upwards [hW, hF] with ω hWω hFω
  have := hFω.2 hx hy hs ht hst
  simp only [smul_eq_mul] at this ⊢
  nlinarith [mul_le_mul_of_nonneg_left this hWω]

/-! ## Quantitative one-sided variation

Search tag: `PARISI_LB_VARIATION`. Keywords: Taylor remainder, near minimum,
square-root epsilon, sixth-root epsilon, short mass interval, coupling lambda.

Consumers: (14.264), (14.283), and coupling optimization in Sections 14.8-14.10.
The endpoint comparison in the square-root estimate is essential when the
available mass interval is short. It comes from fixed-level minimality.
-/

/-- Second-order Taylor control from a Lipschitz derivative, including endpoints. -/
theorem abs_taylor_one_le {F D : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b)
    (hL : 0 ≤ L) (hF : ContinuousOn F (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F (D x) x)
    (hD : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |D x - D y| ≤ L * |x - y|)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |F y - F x - D x * (y - x)| ≤ L / 2 * (y - x) ^ 2 := by
  set φ : ℝ → ℝ → ℝ := fun s t => s * (F t - F x - D x * (t - x)) - L / 2 * (t - x) ^ 2
  have hφd : ∀ s, ∀ t ∈ Ioo a b, HasDerivAt (φ s) (s * (D t - D x) - L * (t - x)) t := by
    intro s t ht
    have h1 := (((hd t ht).sub_const (F x)).sub
      (((hasDerivAt_id t).sub_const x).const_mul (D x))).const_mul s
    have h2 := (((hasDerivAt_id t).sub_const x).pow 2).const_mul (L / 2)
    convert! h1.sub h2 using 1
    simp; ring
  have hφc : ∀ s, ContinuousOn (φ s) (Icc a b) := fun s =>
    ((hF.sub continuousOn_const).sub (by fun_prop)).const_smul s |>.sub (by fun_prop)
  have hbound : ∀ s, |s| ≤ 1 → ∀ t ∈ Icc a b, |s * (D t - D x)| ≤ L * |t - x| := by
    intro s hs t ht
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) hs).trans (hD t ht x hx)
  have key : ∀ s, |s| ≤ 1 → φ s y ≤ φ s x := by
    intro s hs
    rcases le_total x y with hxy | hxy
    · have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
      have hsub' : Ioo x y ⊆ Ioo a b := Ioo_subset_Ioo hx.1 hy.2
      refine antitoneOn_of_deriv_nonpos (convex_Icc x y) ((hφc s).mono hsub) ?_ ?_
        ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
      · rw [interior_Icc]
        exact fun t ht => (hφd s t (hsub' ht)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        rw [(hφd s t (hsub' ht)).deriv]
        have := hbound s hs t (Ioo_subset_Icc_self (hsub' ht))
        rw [abs_of_nonneg (by linarith [ht.1] : 0 ≤ t - x)] at this
        linarith [le_abs_self (s * (D t - D x))]
    · have hsub : Icc y x ⊆ Icc a b := Icc_subset_Icc hy.1 hx.2
      have hsub' : Ioo y x ⊆ Ioo a b := Ioo_subset_Ioo hy.1 hx.2
      refine monotoneOn_of_deriv_nonneg (convex_Icc y x) ((hφc s).mono hsub) ?_ ?_
        ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
      · rw [interior_Icc]
        exact fun t ht => (hφd s t (hsub' ht)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro t ht
        rw [(hφd s t (hsub' ht)).deriv]
        have := hbound s hs t (Ioo_subset_Icc_self (hsub' ht))
        rw [abs_of_nonpos (by linarith [ht.2] : t - x ≤ 0)] at this
        linarith [neg_abs_le (s * (D t - D x))]
  have h1 := key 1 (by norm_num)
  have h2 := key (-1) (by norm_num)
  simp only [φ, sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- Third-order remainder with a Lipschitz second derivative; no fourth derivative. -/
theorem abs_taylor_two_le {F D E : ℝ → ℝ} {a b L : ℝ}
    (hab : a < b) (hL : 0 ≤ L)
    (hF : ContinuousOn F (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F (D x) x)
    (he : ∀ x ∈ Ioo a b, HasDerivAt D (E x) x)
    (hE : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |E x - E y| ≤ L * |x - y|)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |F y - F x - D x * (y - x) - E x / 2 * (y - x) ^ 2| ≤
      L / 6 * |y - x| ^ 3 := by
  set g : ℝ → ℝ := fun t => F t - F x - D x * (t - x) - E x / 2 * (t - x) ^ 2
  have hgd : ∀ t ∈ Ioo a b, HasDerivAt g (D t - D x - E x * (t - x)) t := by
    intro t ht
    have h1 := (((hd t ht).sub_const (F x)).sub
      (((hasDerivAt_id t).sub_const x).const_mul (D x)))
    have h2 := (((hasDerivAt_id t).sub_const x).pow 2).const_mul (E x / 2)
    convert! h1.sub h2 using 1
    simp; ring
  have hgc : ContinuousOn g (Icc a b) :=
    ((hF.sub continuousOn_const).sub (by fun_prop)).sub (by fun_prop)
  have hg' : ∀ t ∈ Icc a b, |D t - D x - E x * (t - x)| ≤ L / 2 * (t - x) ^ 2 :=
    fun t ht => abs_taylor_one_le hab.le hL hD he hE hx ht
  have hb : ∀ s, |s| ≤ 1 → ∀ t ∈ Icc a b,
      |s * (D t - D x - E x * (t - x))| ≤ L / 2 * (t - x) ^ 2 := fun s hs t ht => by
    rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) hs).trans (hg' t ht)
  have key : ∀ s, |s| ≤ 1 → s * g y ≤ L / 6 * |y - x| ^ 3 := by
    intro s hs
    rcases le_total x y with hxy | hxy
    · have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
      have hsub' : Ioo x y ⊆ Ioo a b := Ioo_subset_Ioo hx.1 hy.2
      set φ : ℝ → ℝ := fun t => s * g t - L / 6 * (t - x) ^ 3
      have hφd : ∀ t ∈ Ioo x y, HasDerivAt φ
          (s * (D t - D x - E x * (t - x)) - L / 2 * (t - x) ^ 2) t := fun t ht => by
        convert! ((hgd t (hsub' ht)).const_mul s).sub
          ((((hasDerivAt_id t).sub_const x).pow 3).const_mul (L / 6)) using 1
        simp; ring
      have hφc : ContinuousOn φ (Icc x y) :=
        (continuousOn_const.mul (hgc.mono hsub)).sub (by fun_prop)
      have := antitoneOn_of_deriv_nonpos (convex_Icc x y) hφc
        (by
          rw [interior_Icc]
          exact fun t ht => (hφd t ht).differentiableAt.differentiableWithinAt)
        (by
          rw [interior_Icc]; intro t ht
          rw [(hφd t ht).deriv]
          linarith [le_abs_self (s * (D t - D x - E x * (t - x))),
            hb s hs t (hsub (Ioo_subset_Icc_self ht))])
        ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
      simp only [φ, g, sub_self, mul_zero] at this
      rw [abs_of_nonneg (by linarith : 0 ≤ y - x)]
      simpa using this
    · have hsub : Icc y x ⊆ Icc a b := Icc_subset_Icc hy.1 hx.2
      have hsub' : Ioo y x ⊆ Ioo a b := Ioo_subset_Ioo hy.1 hx.2
      set φ : ℝ → ℝ := fun t => s * g t - L / 6 * (x - t) ^ 3
      have hφd : ∀ t ∈ Ioo y x, HasDerivAt φ
          (s * (D t - D x - E x * (t - x)) + L / 2 * (t - x) ^ 2) t := fun t ht => by
        convert! ((hgd t (hsub' ht)).const_mul s).sub
          ((((hasDerivAt_id t).const_sub x).pow 3).const_mul (L / 6)) using 1
        simp; ring
      have hφc : ContinuousOn φ (Icc y x) :=
        (continuousOn_const.mul (hgc.mono hsub)).sub (by fun_prop)
      have := monotoneOn_of_deriv_nonneg (convex_Icc y x) hφc
        (by
          rw [interior_Icc]
          exact fun t ht => (hφd t ht).differentiableAt.differentiableWithinAt)
        (by
          rw [interior_Icc]; intro t ht
          rw [(hφd t ht).deriv]
          linarith [neg_abs_le (s * (D t - D x - E x * (t - x))),
            hb s hs t (hsub (Ioo_subset_Icc_self ht))])
        ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
      simp only [φ, g, sub_self, mul_zero] at this
      rw [abs_of_nonpos (by linarith : y - x ≤ 0), neg_sub]
      simp at this
      exact this
  have h1 := key 1 (by norm_num)
  have h2 := key (-1) (by norm_num)
  rw [abs_le]
  constructor <;> simp only [g] at h1 h2 <;> linarith

/-- Algebraic core of (14.264), uniform even when d tends to zero. -/
theorem slope_ge_neg_sqrt_of_near_minimum {d M ε s : ℝ}
    (hd : 0 < d) (hM : 0 < M) (hε : 0 ≤ ε)
    (hend : 0 ≤ d * s + M * d ^ 2)
    (hnear : ∀ t ∈ Icc (0 : ℝ) d, -ε ≤ t * s + M * t ^ 2) :
    -(2 * Real.sqrt (M * ε)) ≤ s := by
  rcases le_or_gt 0 s with hs | hs
  · linarith [Real.sqrt_nonneg (M * ε)]
  have hsd : -s ≤ M * d := by nlinarith
  have ht := hnear (-s / (2 * M)) ⟨div_nonneg (by linarith) (by positivity), by
    rw [div_le_iff₀ (by positivity)]; nlinarith⟩
  have key : s ^ 2 ≤ (2 * Real.sqrt (M * ε)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp at ht
    nlinarith
  exact (abs_le_of_sq_le_sq' key (by positivity)).1

/-- Consumer form of the preceding estimate, with the split functional explicit. -/
theorem split_slope_ge_neg_sqrt {Φ : ℝ → ℝ} {a b M ε s : ℝ}
    (hab : a < b) (hM : 0 < M) (hε : 0 ≤ ε)
    (hend : Φ a ≤ Φ b)
    (hnear : ∀ m ∈ Icc a b, Φ a - ε ≤ Φ m)
    (htaylor : ∀ m ∈ Icc a b,
      Φ m ≤ Φ a + (m - a) * s + M * (m - a) ^ 2) :
    -(2 * Real.sqrt (M * ε)) ≤ s := by
  refine slope_ge_neg_sqrt_of_near_minimum (d := b - a) (by linarith) hM hε ?_ ?_
  · linarith [htaylor b ⟨hab.le, le_rfl⟩]
  · rintro t ⟨ht0, htd⟩
    have hm : a + t ∈ Icc a b := ⟨by linarith, by linarith⟩
    have h1 := hnear _ hm
    have h2 := htaylor _ hm
    simp only [add_sub_cancel_left] at h2
    linarith

/-- The two interval-length cases in (14.283), with ρ playing the role of ε^(1/6).
For the first level, provide ρ ≤ q-a; for other levels, provide f(a)=0. -/
theorem curvature_ge_of_cubic_remainder {f : ℝ → ℝ} {a q c M δ ρ : ℝ}
    (haq : a < q) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hρ : 0 < ρ)
    (hlower : ∀ u ∈ Icc a q, -δ ≤ f u)
    (htaylor : ∀ u ∈ Icc a q,
      f u ≤ c / 2 * (u - q) ^ 2 + M * |u - q| ^ 3)
    (hend : ρ ≤ q - a ∨ f a = 0) :
    -c ≤ 2 * δ / ρ ^ 2 + 2 * M * ρ := by
  have short : ρ ≤ q - a → -c ≤ 2 * δ / ρ ^ 2 + 2 * M * ρ := by
    intro h
    have hu : q - ρ ∈ Icc a q := ⟨by linarith, by linarith⟩
    have h1 := (hlower _ hu).trans (htaylor _ hu)
    rw [show q - ρ - q = -ρ by ring, abs_neg, abs_of_pos hρ] at h1
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith
  rcases hend with h | h
  · exact short h
  rcases le_or_gt ρ (q - a) with h' | h'
  · exact short h'
  have h1 := htaylor a ⟨le_rfl, haq.le⟩
  rw [h, abs_sub_comm, abs_of_pos (by linarith)] at h1
  have : -c ≤ 2 * M * (q - a) := by
    have hqa : 0 < q - a := by linarith
    have : 0 ≤ (q - a) ^ 2 * (c + 2 * M * (q - a)) := by rw [sub_sq'] at h1; nlinarith
    nlinarith [(mul_nonneg_iff_of_pos_left (by positivity : (0:ℝ) < (q - a) ^ 2)).1 this]
  have : 0 ≤ 2 * δ / ρ ^ 2 := by positivity
  nlinarith

/-- Choose a coupling of the correct sign to obtain a quadratic gain. -/
theorem exists_quadratic_gain {B : ℝ → ℝ} {A d L r : ℝ}
    (hL : 0 < L) (hr : 0 ≤ r) (hd : |d| ≤ L * r)
    (hB : ∀ lam ∈ Icc (-r) r, B lam ≤ A + d * lam + L / 2 * lam ^ 2) :
    ∃ lam ∈ Icc (-r) r, B lam ≤ A - d ^ 2 / (2 * L) := by
  have hmem : -d / L ∈ Icc (-r) r := by
    rw [mem_Icc, le_div_iff₀ hL, div_le_iff₀ hL]
    constructor <;> linarith [abs_le.1 hd]
  refine ⟨-d / L, hmem, (hB _ hmem).trans (le_of_eq ?_)⟩
  field_simp
  ring

/-- Strict improvement from a nonzero derivative, within the permitted coupling range. -/
theorem exists_strict_gain_of_deriv_ne_zero {B : ℝ → ℝ} {d r : ℝ}
    (hB : HasDerivAt B d 0) (hd : d ≠ 0) (hr : 0 < r) :
    ∃ lam ∈ Ioo (-r) r, B lam < B 0 := by
  by_contra! h
  refine hd (IsLocalMin.hasDerivAt_eq_zero ?_ hB)
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 hr) hr] with x hx using h x hx

/-! ## Covariance-profile remainders and a uniform first-overlap input

Search tag: `PARISI_LB_PROFILE`. Keywords: xi, convex remainder, negative overlap,
q1 lower bound, nondegenerate field, tanh moment, cosh curvature, Gaussian Jensen.

Consumer: exact Guerra remainder and Lemma 14.7.15. Derivative control is required
only on the overlap interval. In particular no positive second derivative at zero
or globally bounded third derivative is introduced.
-/

/-- A monotone second derivative on (0,1] bounds the first derivative up to zero. -/
theorem lipschitz_deriv_of_monotone_second {ξ : ℝ → ℝ}
    (hc : ContinuousOn (deriv ξ) (Icc (0 : ℝ) 1))
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (deriv ξ) x)
    (hmono : MonotoneOn (deriv (deriv ξ)) (Ioc (0 : ℝ) 1))
    (hnonneg : ∀ x ∈ Ioc (0 : ℝ) 1, 0 ≤ deriv (deriv ξ) x) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |deriv ξ x - deriv ξ y| ≤ deriv (deriv ξ) 1 * |x - y| := by
  have key : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, x < y →
      |deriv ξ x - deriv ξ y| ≤ deriv (deriv ξ) 1 * |x - y| := by
    intro x hx y hy hxy
    obtain ⟨c, hc', hceq⟩ := exists_deriv_eq_slope (deriv ξ) hxy
      (hc.mono (Icc_subset_Icc hx.1 hy.2))
      (fun t ht => (hd t ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩).differentiableWithinAt)
    have hc0 : c ∈ Ioc (0 : ℝ) 1 := ⟨hx.1.trans_lt hc'.1, (hc'.2.trans_le hy.2).le⟩
    have h1 := hnonneg c hc0
    have h2 := hmono hc0 ⟨zero_lt_one, le_rfl⟩ hc0.2
    rw [eq_div_iff (by linarith)] at hceq
    rw [abs_sub_comm, ← hceq, abs_mul, abs_of_nonneg h1, abs_sub_comm]
    exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  intro x hx y hy
  rcases lt_trichotomy x y with h | rfl | h
  · exact key x hx y hy h
  · simp
  · rw [abs_sub_comm, abs_sub_comm x]
    exact key y hy x hx h

/-- Evenness extends first-derivative control to negative overlaps. -/
theorem lipschitz_deriv_even_extension {ξ : ℝ → ℝ} {L : ℝ}
    (heven : Function.Even ξ) (hL : 0 ≤ L)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ ξ x)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |deriv ξ x - deriv ξ y| ≤ L * |x - y|) :
    ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |deriv ξ x - deriv ξ y| ≤ L * |x - y| := by
  have hodd : ∀ x, deriv ξ (-x) = -deriv ξ x := by
    intro x
    have : ξ = fun y => ξ (-y) := funext fun y => (heven y).symm
    conv_lhs => rw [this]
    rw [deriv_comp_neg, neg_neg]
  have h0 : deriv ξ 0 = 0 := by
    have := hodd 0; rw [neg_zero] at this; linarith
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have mixed : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |deriv ξ u + deriv ξ v| ≤ L * (u + v) := by
    intro u hu v hv
    have h1 := hpos u hu 0 h01
    have h2 := hpos v hv 0 h01
    rw [h0, sub_zero, sub_zero, abs_of_nonneg hu.1] at h1
    rw [h0, sub_zero, sub_zero, abs_of_nonneg hv.1] at h2
    linarith [abs_add_le (deriv ξ u) (deriv ξ v)]
  intro x hx y hy
  rcases le_total 0 x with hx0 | hx0 <;> rcases le_total 0 y with hy0 | hy0
  · exact hpos x ⟨hx0, hx.2⟩ y ⟨hy0, hy.2⟩
  · have := mixed x ⟨hx0, hx.2⟩ (-y) ⟨by linarith, by linarith [hy.1]⟩
    rw [hodd, ← sub_eq_add_neg] at this
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
    linarith
  · have := mixed (-x) ⟨by linarith, by linarith [hx.1]⟩ y ⟨hy0, hy.2⟩
    rw [hodd, neg_add_eq_sub, abs_sub_comm] at this
    rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith
  · have := hpos (-x) ⟨by linarith, by linarith [hx.1]⟩ (-y) ⟨by linarith, by linarith [hy.1]⟩
    rw [hodd, hodd, neg_sub_neg, neg_sub_neg, abs_sub_comm, abs_sub_comm y] at this
    exact this

/-- Nonnegative Guerra remainder with a quadratic upper bound. -/
theorem convex_remainder_bounds {ξ : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) ξ)
    (hd : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt ξ (deriv ξ x) x)
    (hLip : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |deriv ξ x - deriv ξ y| ≤ L * |x - y|)
    {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : q ∈ Icc (-1 : ℝ) 1) :
    0 ≤ ξ u - ξ q - deriv ξ q * (u - q) ∧
      ξ u - ξ q - deriv ξ q * (u - q) ≤ L / 2 * (u - q) ^ 2 := by
  constructor
  · rcases lt_trichotomy q u with h | rfl | h
    · have := hconv.le_slope_of_hasDerivAt hq hu h (hd q hq)
      rw [slope_def_field, le_div_iff₀ (by linarith)] at this
      linarith
    · simp
    · have := hconv.slope_le_of_hasDerivAt hu hq h (hd q hq)
      rw [slope_def_field, div_le_iff₀ (by linarith)] at this
      linarith
  · exact (le_abs_self _).trans (abs_taylor_one_le (by norm_num) hL
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx)) hLip hq hu)

/-- The derivative of the real hyperbolic tangent is `1 / cosh²`. -/
theorem hasDerivAt_real_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have e : Real.sinh / Real.cosh = Real.tanh :=
    funext fun y => (Real.tanh_eq_sinh_div_cosh y).symm
  rw [e] at h
  convert! h using 1
  rw [← Real.cosh_sq_sub_sinh_sq x]; ring

theorem real_tanh_nonneg_iff {x : ℝ} : 0 ≤ Real.tanh x ↔ 0 ≤ x := by
  rw [Real.tanh_eq_sinh_div_cosh, div_nonneg_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact Real.sinh_nonneg_iff.1 h
    · linarith [Real.cosh_pos x]
  · intro h; exact .inl ⟨Real.sinh_nonneg_iff.2 h, (Real.cosh_pos x).le⟩

@[fun_prop]
theorem continuous_real_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_real_tanh x).continuousAt

theorem integrable_tanh_sq (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun x : ℝ => Real.tanh x ^ 2) μ :=
  Integrable.of_bound (C := 1) (by fun_prop) (.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (Real.tanh_sq_lt_one x).le)

/-- Curvature bounded below by c / cosh² gives a uniform slope lower bound. -/
theorem abs_deriv_ge_mul_tanh {A : ℝ → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hzero : deriv A 0 = 0)
    (hd : Differentiable ℝ (deriv A))
    (hcurv : ∀ x, c / Real.cosh x ^ 2 ≤ deriv (deriv A) x) (x : ℝ) :
    c * |Real.tanh x| ≤ |deriv A x| := by
  set G : ℝ → ℝ := fun y => deriv A y - c * Real.tanh y
  have hG : ∀ y, HasDerivAt G (deriv (deriv A) y - c * (1 / Real.cosh y ^ 2)) y := fun y =>
    (hd y).hasDerivAt.sub ((hasDerivAt_real_tanh y).const_mul c)
  have hmono : Monotone G := monotone_of_deriv_nonneg (fun y => (hG y).differentiableAt)
    fun y => by rw [(hG y).deriv]; have := hcurv y; rw [mul_one_div]; linarith
  have hG0 : G 0 = 0 := by simp [G, hzero]
  rcases le_total 0 x with hx | hx
  · have h1 := hmono hx
    have ht := real_tanh_nonneg_iff.2 hx
    rw [hG0] at h1
    simp only [G] at h1
    rw [abs_of_nonneg ht, abs_of_nonneg (by nlinarith)]
    linarith
  · have h1 := hmono hx
    have ht : Real.tanh x ≤ 0 := by
      have := real_tanh_nonneg_iff.2 (neg_nonneg.2 hx)
      rw [Real.tanh_neg] at this; linarith
    rw [hG0] at h1
    simp only [G] at h1
    rw [abs_of_nonpos ht, abs_of_nonpos (by nlinarith)]
    linarith

/-- Nondegeneracy produces a positive bounded moment without any exponential field moment. -/
theorem integral_tanh_sq_pos {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsecond : Integrable (fun x : ℝ => x ^ 2) μ)
    (hpos : 0 < ∫ x : ℝ, x ^ 2 ∂μ) :
    0 < ∫ x : ℝ, Real.tanh x ^ 2 ∂μ := by
  refine lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg _) fun h => hpos.ne' ?_
  have h0 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
    (integrable_tanh_sq μ)).1 h.symm
  refine integral_eq_zero_of_ae (h0.mono fun x hx => ?_)
  simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero] at hx ⊢
  rw [Real.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at hx
  rcases hx with h | h
  · exact Real.sinh_injective (h.trans Real.sinh_zero.symm)
  · exact absurd h (Real.cosh_pos x).ne'

/-- Uniform lower bound after averaging a derivative comparison. -/
theorem integral_sq_ge_tanh_sq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {D : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hD : Integrable (fun x => D x ^ 2) μ)
    (hbound : ∀ᵐ x ∂μ, c * |Real.tanh x| ≤ |D x|) :
    c ^ 2 * (∫ x, Real.tanh x ^ 2 ∂μ) ≤ ∫ x, D x ^ 2 ∂μ := by
  rw [← integral_const_mul]
  refine integral_mono_ae ((integrable_tanh_sq μ).const_mul _) hD (hbound.mono fun x hx => ?_)
  have := pow_le_pow_left₀ (by positivity) hx 2
  rwa [mul_pow, sq_abs, sq_abs] at this

/-- Hoeffding's lemma for a `±1` variable with mean `t`, in hyperbolic form. -/
theorem cosh_add_mul_sinh_le {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (y : ℝ) :
    Real.cosh y + t * Real.sinh y ≤ Real.exp (t * y + y ^ 2 / 2) := by
  obtain ⟨ht1, ht2⟩ := ht
  set p : ℝ := (1 + t) / 2
  set ν : Measure ℝ :=
    ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal (1 - p) • Measure.dirac (-1)
  have hp0 : 0 ≤ p := by simp only [p]; linarith
  have hp1 : 0 ≤ 1 - p := by simp only [p]; linarith
  haveI : IsProbabilityMeasure ν := by
    constructor
    simp only [ν, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp0 hp1]; simp
  have hint : ∀ f : ℝ → ℝ, ∫ z, f z ∂ν = p * f 1 + (1 - p) * f (-1) := by
    intro f
    have h1 : Integrable f (ENNReal.ofReal p • Measure.dirac (1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure (by simp)
    have h2 : Integrable f (ENNReal.ofReal (1 - p) • Measure.dirac (-1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure (by simp)
    rw [integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
      integral_dirac, integral_dirac, ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal hp1,
      smul_eq_mul, smul_eq_mul]
  set X : ℝ → ℝ := fun z => max (-1) (min 1 z)
  have hX1 : X 1 = 1 := by norm_num [X]
  have hX2 : X (-1) = -1 := by norm_num [X]
  have hmean : ν[X] = t := by
    rw [hint, hX1, hX2]; simp only [p]; ring
  have hH := hasSubgaussianMGF_of_mem_Icc (μ := ν) (X := X) (a := -1) (b := 1)
    (by fun_prop) (ae_of_all _ fun z => ⟨le_max_left _ _,
      max_le (by norm_num) (min_le_left _ _)⟩)
  have := hH.mgf_le y
  rw [mgf, hint, hmean, hX1, hX2] at this
  have hnorm : ((‖(1 : ℝ) - -1‖₊ / 2) ^ 2 : ℝ≥0) = 1 := by
    rw [show (1 : ℝ) - -1 = 2 by norm_num]
    ext; simp
  rw [hnorm, NNReal.coe_one, one_mul] at this
  have e : p * Real.exp (y * (1 - t)) + (1 - p) * Real.exp (y * (-1 - t)) =
      Real.exp (-(t * y)) * (Real.cosh y + t * Real.sinh y) := by
    rw [Real.cosh_eq, Real.sinh_eq]
    simp only [p]
    rw [show y * (1 - t) = -(t * y) + y by ring, show y * (-1 - t) = -(t * y) + -y by ring,
      Real.exp_add, Real.exp_add]
    ring
  rw [e] at this
  calc Real.cosh y + t * Real.sinh y
      = Real.exp (t * y) * (Real.exp (-(t * y)) * (Real.cosh y + t * Real.sinh y)) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (t * y) * Real.exp (y ^ 2 / 2) := by gcongr
    _ = Real.exp (t * y + y ^ 2 / 2) := (Real.exp_add _ _).symm

/-- Elementary estimate (14.281), used to propagate lower curvature bounds. -/
theorem inv_cosh_sq_add_lower (x y : ℝ) :
    Real.exp (-2 * y * Real.tanh x - y ^ 2) / Real.cosh x ^ 2 ≤
      1 / Real.cosh (x + y) ^ 2 := by
  set t := Real.tanh x
  have hcx := Real.cosh_pos x
  have hcxy := Real.cosh_pos (x + y)
  set K := Real.cosh y + t * Real.sinh y
  have hK : Real.cosh (x + y) = Real.cosh x * K := by
    simp only [K, t, Real.cosh_add, Real.tanh_eq_sinh_div_cosh]
    field_simp
  have hKpos : 0 < K := by
    rw [hK] at hcxy; exact pos_of_mul_pos_right hcxy hcx.le
  have hKle := cosh_add_mul_sinh_le ⟨(Real.neg_one_lt_tanh x).le, (Real.tanh_lt_one x).le⟩ y
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, hK, mul_pow]
  have : Real.exp (-2 * y * t - y ^ 2) * K ^ 2 ≤ 1 := by
    calc Real.exp (-2 * y * t - y ^ 2) * K ^ 2
        ≤ Real.exp (-2 * y * t - y ^ 2) * Real.exp (t * y + y ^ 2 / 2) ^ 2 := by gcongr
      _ = 1 := by rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf; simp
  nlinarith [pow_pos hcx 2]

/-- Jensen's Gaussian estimate in (14.282), including a zero increment variance. -/
theorem integral_gaussian_exp_linear_sub_sq_lower (c : ℝ) (v : ℝ≥0) :
    Real.exp (-(v : ℝ)) ≤
      ∫ z : ℝ, Real.exp (c * z - z ^ 2) ∂(gaussianReal 0 v) := by
  have hsq : ∫ z, z ^ 2 ∂(gaussianReal 0 v) = v := by
    have := variance_fun_id_gaussianReal (μ := 0) (v := v)
    rw [variance_eq_integral measurable_id'.aemeasurable] at this
    simpa [integral_id_gaussianReal] using this
  have hid : Integrable (fun z : ℝ => z) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hid2 : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hA : Integrable (fun z : ℝ => c * z - z ^ 2) (gaussianReal 0 v) :=
    (hid.const_mul c).sub hid2
  have hB : Integrable (fun z : ℝ => 1 + (c * z - z ^ 2)) (gaussianReal 0 v) :=
    (integrable_const 1).add hA
  have hexp : Integrable (fun z : ℝ => Real.exp (c * z - z ^ 2)) (gaussianReal 0 v) := by
    refine Integrable.of_bound (C := Real.exp (c ^ 2 / 4)) (by fun_prop)
      (.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (z - c / 2)])
  calc Real.exp (-(v : ℝ))
      = ∫ z, Real.exp (-(v : ℝ)) * (1 + (c * z - z ^ 2) + v) ∂(gaussianReal 0 v) := by
        rw [integral_const_mul, integral_add hB (integrable_const _),
          integral_add (integrable_const _) hA, integral_sub (hid.const_mul c) hid2,
          integral_const_mul]
        simp [integral_id_gaussianReal, hsq]
    _ ≤ _ := integral_mono ((hB.add (integrable_const _)).const_mul _) hexp fun z => by
        have := Real.add_one_le_exp (c * z - z ^ 2 + v)
        calc Real.exp (-(v : ℝ)) * (1 + (c * z - z ^ 2) + v)
            ≤ Real.exp (-(v : ℝ)) * Real.exp (c * z - z ^ 2 + v) := by
              gcongr; linarith
          _ = Real.exp (c * z - z ^ 2) := by rw [← Real.exp_add]; ring_nf

/-- The centered Gaussian density satisfies `φ' = -(z / v) φ`. -/
theorem hasDerivAt_gaussianPDFReal_zero (v : ℝ≥0) (z : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v) (-(z / v) * gaussianPDFReal 0 v z) z := by
  have h : HasDerivAt (fun z : ℝ => -(z - 0) ^ 2 / (2 * v)) (-(z / v)) z := by
    have := (((hasDerivAt_id z).sub_const 0).pow 2).neg.div_const (2 * (v : ℝ))
    convert! this using 1
    simp only [id]
    rcases eq_or_ne (v : ℝ) 0 with hv | hv
    · simp [hv]
    · field_simp; ring
  have := h.exp.const_mul (Real.sqrt (2 * Real.pi * v))⁻¹
  convert! this using 1
  simp only [gaussianPDFReal]; ring

/-- Gaussian integration by parts (Stein's identity). -/
theorem integral_mul_gaussianReal {v : ℝ≥0} {f f' : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f' z) z)
    (hf0 : Integrable f (gaussianReal 0 v))
    (hf1 : Integrable (fun z => z * f z) (gaussianReal 0 v))
    (hf2 : Integrable f' (gaussianReal 0 v)) :
    ∫ z, z * f z ∂gaussianReal 0 v = v * ∫ z, f' z ∂gaussianReal 0 v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianReal_zero_var]
  have hmeas : Measurable (gaussianPDF 0 v) := measurable_gaussianPDF 0 v
  have htr : ∀ g : ℝ → ℝ, Integrable g (gaussianReal 0 v) →
      Integrable (fun z => gaussianPDFReal 0 v z * g z) := by
    intro g hg
    rw [gaussianReal_of_var_ne_zero 0 hv, integrable_withDensity_iff_integrable_smul' hmeas
      (.of_forall fun _ => gaussianPDF_lt_top)] at hg
    simpa [toReal_gaussianPDF] using hg
  have e : ∀ g : ℝ → ℝ, ∫ z, g z ∂gaussianReal 0 v = ∫ z, gaussianPDFReal 0 v z * g z := by
    intro g; rw [integral_gaussianReal_eq_integral_smul hv]; rfl
  rw [e, e]
  have h1 := htr _ hf1
  have ibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := f) (v := gaussianPDFReal 0 v)
    (u' := f') (v' := fun z => -(z / v) * gaussianPDFReal 0 v z) (fun z _ => hf z)
    (fun z _ => hasDerivAt_gaussianPDFReal_zero v z)
    (by
      have := h1.const_mul (-(v : ℝ)⁻¹)
      refine this.congr (.of_forall fun z => ?_)
      simp only [Pi.mul_apply]; field_simp)
    (by convert! htr _ hf2 using 1; funext z; exact mul_comm _ _)
    (by convert! htr _ hf0 using 1; funext z; exact mul_comm _ _)
  have hvpos : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have : ∫ z, f z * (-(z / v) * gaussianPDFReal 0 v z) =
      -(v : ℝ)⁻¹ * ∫ z, gaussianPDFReal 0 v z * (z * f z) := by
    rw [← integral_const_mul]; congr 1; ext z; field_simp
  rw [this, show (∫ z, f' z * gaussianPDFReal 0 v z) = ∫ z, gaussianPDFReal 0 v z * f' z by
    congr 1; ext z; ring] at ibp
  rw [neg_mul, neg_inj] at ibp
  rw [← ibp]; field_simp

/-- Functions of at most exponential growth are Gaussian integrable. -/
theorem integrable_gaussianReal_of_abs_le_exp {v : ℝ≥0} {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (gaussianReal 0 v)) {C c : ℝ}
    (h : ∀ z, |g z| ≤ C * Real.exp (c * |z|)) : Integrable g (gaussianReal 0 v) :=
  ((integrable_gaussian_exp_abs c v).const_mul C).mono' hg (.of_forall fun z => by
    simpa [Real.norm_eq_abs] using h z)

theorem exp_mul_abs_add_le {c : ℝ} (hc : 0 ≤ c) (x z : ℝ) :
    Real.exp (c * |x + z|) ≤ Real.exp (c * |x|) * Real.exp (c * |z|) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 (by nlinarith [abs_add_le x z])

/-- Differentiation of a Gaussian smoothing under the integral sign. -/
theorem hasDerivAt_integral_gaussian_add {v : ℝ≥0} {g g' : ℝ → ℝ}
    (hg : ∀ y, HasDerivAt g (g' y) y) (hg' : Continuous g') {C c : ℝ} (hc : 0 ≤ c)
    (hbg : ∀ y, |g y| ≤ C * Real.exp (c * |y|))
    (hbg' : ∀ y, |g' y| ≤ C * Real.exp (c * |y|)) (x : ℝ) :
    HasDerivAt (fun y => ∫ z, g (y + z) ∂gaussianReal 0 v)
      (∫ z, g' (x + z) ∂gaussianReal 0 v) x := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun y => (hg y).continuousAt
  have hC : 0 ≤ C := by nlinarith [(abs_nonneg _).trans (hbg 0), Real.exp_pos (c * |0|)]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds x one_pos)
    (F := fun y z => g (y + z)) (F' := fun y z => g' (y + z))
    (bound := fun z => C * Real.exp (c * (|x| + 1)) * Real.exp (c * |z|))
    (.of_forall fun y => (hgc.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    (integrable_gaussianReal_of_abs_le_exp (C := C * Real.exp (c * |x|)) (c := c)
      (hgc.comp (continuous_const.add continuous_id)).aestronglyMeasurable fun z => ?_)
    (hg'.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    (.of_forall fun z y hy => ?_)
    ((integrable_gaussian_exp_abs c v).const_mul _)
    (.of_forall fun z y _ => hg (y + z) |>.comp y ((hasDerivAt_id y).add_const z) |>.congr_deriv
      (by simp))).2
  · calc |g (x + z)| ≤ C * Real.exp (c * |x + z|) := hbg _
      _ ≤ C * (Real.exp (c * |x|) * Real.exp (c * |z|)) := by
        gcongr; exact exp_mul_abs_add_le hc x z
      _ = _ := by ring
  · rw [Metric.mem_ball, Real.dist_eq] at hy
    have hy' : |y| ≤ |x| + 1 := by linarith [abs_sub_abs_le_abs_sub y x]
    simp only [Real.norm_eq_abs]; rw [mul_assoc]
    refine (hbg' _).trans (mul_le_mul_of_nonneg_left ?_ hC)
    refine (exp_mul_abs_add_le hc y z).trans ?_
    gcongr

/-- A derivative bounded by one gives a one-Lipschitz function. -/
theorem abs_sub_le_of_abs_deriv_le_one {A : ℝ → ℝ} (hA : Differentiable ℝ A)
    (h : ∀ x, |deriv A x| ≤ 1) (y w : ℝ) : |A y - A w| ≤ |y - w| := by
  have := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le (C := 1)
    (fun x _ => hA x) (fun x _ => by simpa [Real.norm_eq_abs] using h x) (mem_univ w) (mem_univ y)
  simpa [Real.norm_eq_abs] using this

/-- Exponential moment bound behind the denominator in (14.282): Gaussian integration by
parts along the scaling `s ↦ x + s z` with `|A'| ≤ 1` and `|A''| ≤ 1`. -/
theorem integral_exp_mul_comp_add_le {A : ℝ → ℝ} (hA : ContDiff ℝ 2 A)
    (hfirst : ∀ x, |deriv A x| ≤ 1) (hsecond : ∀ x, |deriv (deriv A) x| ≤ 1)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : ℝ≥0) (x : ℝ) :
    ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v ≤ Real.exp (m * A x + v) := by
  obtain ⟨hm0, hm1⟩ := hm
  have hA1 : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hA2 : ContDiff ℝ 1 (deriv A) := (contDiff_succ_iff_deriv.1 hA).2.2
  have hA2d : Differentiable ℝ (deriv A) := hA2.differentiable one_ne_zero
  have hA2c : Continuous (deriv (deriv A)) := hA2.continuous_deriv le_rfl
  have hA1c : Continuous (deriv A) := hA2d.continuous
  have hAc : Continuous A := hA1.continuous
  have hlip := abs_sub_le_of_abs_deriv_le_one hA1 hfirst
  have henv : ∀ s z : ℝ, Real.exp (m * A (x + s * z)) ≤
      Real.exp (|A x|) * Real.exp (|s| * |z|) := by
    intro s z
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 := hlip (x + s * z) x
    rw [add_sub_cancel_left, abs_mul] at h1
    have h2 : m * A (x + s * z) ≤ |A (x + s * z)| := by
      calc m * A (x + s * z) ≤ m * |A (x + s * z)| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hm0
        _ ≤ 1 * |A (x + s * z)| := mul_le_mul_of_nonneg_right hm1 (abs_nonneg _)
        _ = _ := one_mul _
    linarith [abs_sub_abs_le_abs_sub (A (x + s * z)) (A x)]
  set h : ℝ → ℝ := fun s => ∫ z, Real.exp (m * A (x + s * z)) ∂gaussianReal 0 v with hh
  set h' : ℝ → ℝ := fun s =>
    ∫ z, m * deriv A (x + s * z) * z * Real.exp (m * A (x + s * z)) ∂gaussianReal 0 v
  have hmeas : ∀ s, Continuous fun z => Real.exp (m * A (x + s * z)) := fun s => by fun_prop
  have hint : ∀ s, Integrable (fun z => Real.exp (m * A (x + s * z))) (gaussianReal 0 v) :=
    fun s => integrable_gaussianReal_of_abs_le_exp (hmeas s).aestronglyMeasurable fun z => by
      rw [abs_of_pos (Real.exp_pos _)]; exact henv s z
  have hpos : ∀ s, 0 < h s := fun s => integral_exp_pos (hint s)
  have hderiv : ∀ s, HasDerivAt h (h' s) s := by
    intro s
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s one_pos)
      (F := fun s z => Real.exp (m * A (x + s * z)))
      (F' := fun s z => m * deriv A (x + s * z) * z * Real.exp (m * A (x + s * z)))
      (bound := fun z => Real.exp (|A x|) * Real.exp ((|s| + 2) * |z|))
      (.of_forall fun s => (hmeas s).aestronglyMeasurable) (hint s)
      (by fun_prop : Continuous _).aestronglyMeasurable
      (.of_forall fun z t ht => ?_)
      ((integrable_gaussian_exp_abs _ v).const_mul _)
      (.of_forall fun z t _ => ?_)).2
    · rw [Metric.mem_ball, Real.dist_eq] at ht
      have ht' : |t| ≤ |s| + 1 := by linarith [abs_sub_abs_le_abs_sub t s]
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hm0]
      have hz : |z| ≤ Real.exp |z| := by linarith [Real.add_one_le_exp |z|, abs_nonneg z]
      calc m * |deriv A (x + t * z)| * |z| * Real.exp (m * A (x + t * z))
          ≤ 1 * 1 * Real.exp |z| * (Real.exp (|A x|) * Real.exp ((|s| + 1) * |z|)) := by
            gcongr
            · exact hfirst _
            · exact (henv t z).trans (by gcongr)
        _ = _ := by
          rw [one_mul, one_mul, mul_left_comm, ← Real.exp_add]; congr 2; ring
    · have hl := ((hasDerivAt_id t).mul_const z).const_add x
      have := (((hA1 _).hasDerivAt.comp t hl).const_mul m).exp
      convert! this using 1
      simp; ring
  set f' : ℝ → ℝ → ℝ := fun s z => (m * deriv (deriv A) (x + s * z) * s +
      m ^ 2 * deriv A (x + s * z) ^ 2 * s) * Real.exp (m * A (x + s * z))
  have hz : ∀ z : ℝ, |z| ≤ Real.exp |z| := fun z => by
    linarith [Real.add_one_le_exp |z|, abs_nonneg z]
  have hf'bd : ∀ s z, |m * deriv (deriv A) (x + s * z) * s +
      m ^ 2 * deriv A (x + s * z) ^ 2 * s| ≤ 2 * |s| := by
    intro s z
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul, abs_pow, abs_of_nonneg hm0]
    have a1 := hsecond (x + s * z)
    have a2 : |deriv A (x + s * z)| ^ 2 ≤ 1 := by
      nlinarith [hfirst (x + s * z), abs_nonneg (deriv A (x + s * z))]
    have hm2 : m ^ 2 ≤ 1 := by nlinarith
    have b1 : m * |deriv (deriv A) (x + s * z)| ≤ 1 := by
      nlinarith [abs_nonneg (deriv (deriv A) (x + s * z))]
    have b2 : m ^ 2 * |deriv A (x + s * z)| ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (deriv A (x + s * z))]
    nlinarith [abs_nonneg s]
  have hintf' : ∀ s, Integrable (f' s) (gaussianReal 0 v) := fun s =>
    integrable_gaussianReal_of_abs_le_exp (C := 2 * |s| * Real.exp |A x|) (c := |s|)
      (by fun_prop : Continuous _).aestronglyMeasurable fun z => by
        simp only [f']
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact (mul_le_mul (hf'bd s z) (henv s z) (Real.exp_pos _).le (by positivity)).trans_eq
          (by ring)
  have hstein : ∀ s, h' s = v * ∫ z, f' s z ∂gaussianReal 0 v := by
    intro s
    have hl : ∀ z, HasDerivAt (fun z => x + s * z) s z := fun z => by
      simpa using ((hasDerivAt_id z).const_mul s).const_add x
    have hf : ∀ z, HasDerivAt (fun z => m * deriv A (x + s * z) * Real.exp (m * A (x + s * z)))
        (f' s z) z := by
      intro z
      have h1 := ((hA2d _).hasDerivAt.comp z (hl z)).const_mul m
      have h2 := (((hA1 _).hasDerivAt.comp z (hl z)).const_mul m).exp
      convert! h1.mul h2 using 1
      simp only [f', Function.comp_def]; ring
    have hb := henv s
    rw [← integral_mul_gaussianReal hf _ _ (hintf' s)]
    · exact integral_congr_ae (.of_forall fun z => by simp only; ring)
    · refine integrable_gaussianReal_of_abs_le_exp (C := Real.exp |A x|) (c := |s|)
        (by fun_prop : Continuous _).aestronglyMeasurable fun z => ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hm0, abs_of_pos (Real.exp_pos _)]
      calc m * |deriv A (x + s * z)| * Real.exp (m * A (x + s * z))
          ≤ 1 * 1 * (Real.exp |A x| * Real.exp (|s| * |z|)) := by
            gcongr
            · exact hfirst _
            · exact hb z
        _ = _ := by ring
    · refine integrable_gaussianReal_of_abs_le_exp (C := Real.exp |A x|) (c := |s| + 1)
        (by fun_prop : Continuous _).aestronglyMeasurable fun z => ?_
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hm0, abs_of_pos (Real.exp_pos _)]
      calc |z| * (m * |deriv A (x + s * z)| * Real.exp (m * A (x + s * z)))
          ≤ Real.exp |z| * (1 * 1 * (Real.exp |A x| * Real.exp (|s| * |z|))) := by
            gcongr
            · exact hz z
            · exact hfirst _
            · exact hb z
        _ = _ := by
          rw [one_mul, one_mul, mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hle : ∀ s ∈ Icc (0 : ℝ) 1, h' s ≤ 2 * v * s * h s := by
    rintro s ⟨hs0, -⟩
    have hI : ∫ z, f' s z ∂gaussianReal 0 v ≤
        ∫ z, 2 * s * Real.exp (m * A (x + s * z)) ∂gaussianReal 0 v := by
      refine integral_mono (hintf' s) ((hint s).const_mul _) fun z => ?_
      have := hf'bd s z
      rw [abs_of_nonneg hs0] at this
      exact mul_le_mul_of_nonneg_right (le_abs_self _ |>.trans this) (Real.exp_pos _).le
    rw [integral_const_mul] at hI
    rw [hstein]
    calc (v : ℝ) * ∫ z, f' s z ∂gaussianReal 0 v ≤ v * (2 * s * h s) :=
          mul_le_mul_of_nonneg_left hI v.2
      _ = _ := by ring
  set k : ℝ → ℝ := fun s => Real.log (h s) - v * s ^ 2
  have hk : ∀ s, HasDerivAt k (h' s / h s - v * (2 * s)) s := fun s => by
    convert! ((hderiv s).log (hpos s).ne').sub
      ((hasDerivAt_pow 2 s).const_mul (v : ℝ)) using 1 <;> simp
  have hanti : AntitoneOn k (Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      (fun s _ => (hk s).continuousAt.continuousWithinAt)
      (fun s _ => (hk s).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [interior_Icc] at hs
    rw [(hk s).deriv, sub_nonpos, div_le_iff₀ (hpos s)]
    linarith [hle s (Ioo_subset_Icc_self hs)]
  have h10 := hanti (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one
  have h0 : h 0 = Real.exp (m * A x) := by simp [h]
  have h1 : h 1 = ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v := by simp [h]
  simp only [k, h0, Real.log_exp] at h10
  rw [← h1, ← Real.exp_log (hpos 1)]
  exact Real.exp_le_exp.2 (by linarith)

/-- Bounded continuous weights against the tilt `exp (m A (x + z))` are Gaussian integrable. -/
theorem integrable_mul_exp_comp_add {A w : ℝ → ℝ} (hA : Differentiable ℝ A)
    (hfirst : ∀ x, |deriv A x| ≤ 1) (hw : Continuous w) (hw1 : ∀ z, |w z| ≤ 1)
    {m : ℝ} (hm : 0 ≤ m) (v : ℝ≥0) (x : ℝ) :
    Integrable (fun z => w z * Real.exp (m * A (x + z))) (gaussianReal 0 v) := by
  have hAc := hA.continuous
  refine integrable_gaussianReal_of_abs_le_exp (C := Real.exp (m * |A x|)) (c := m)
    (by fun_prop : Continuous _).aestronglyMeasurable fun z => ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  have h1 := abs_sub_le_of_abs_deriv_le_one hA hfirst (x + z) x
  rw [add_sub_cancel_left] at h1
  have h2 : m * A (x + z) ≤ m * |A x| + m * |z| := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans
      (by linarith [abs_sub_abs_le_abs_sub (A (x + z)) (A x)])) hm
  calc |w z| * Real.exp (m * A (x + z)) ≤ 1 * Real.exp (m * |A x| + m * |z|) := by
        gcongr
        · exact hw1 z
    _ = _ := one_mul _

/-- Numerator estimate in (14.282): convexity of `A` and (14.281) under the Gaussian. -/
theorem integral_deriv_deriv_mul_exp_lower {A : ℝ → ℝ} (hA : ContDiff ℝ 2 A) {α m : ℝ}
    (hα : 0 ≤ α) (hm : 0 ≤ m)
    (hfirst : ∀ x, |deriv A x| ≤ 1) (hsecond : ∀ x, |deriv (deriv A) x| ≤ 1)
    (hlower : ∀ x, α / Real.cosh x ^ 2 ≤ deriv (deriv A) x) (v : ℝ≥0) (x : ℝ) :
    α * Real.exp (-(v : ℝ)) / Real.cosh x ^ 2 * Real.exp (m * A x) ≤
      ∫ z, deriv (deriv A) (x + z) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v := by
  have hA1 : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hA2 : ContDiff ℝ 1 (deriv A) := (contDiff_succ_iff_deriv.1 hA).2.2
  have hA2d : Differentiable ℝ (deriv A) := hA2.differentiable one_ne_zero
  have hA2c : Continuous (deriv (deriv A)) := hA2.continuous_deriv le_rfl
  have hmono : Monotone (deriv A) := monotone_of_deriv_nonneg hA2d fun y =>
    (div_nonneg hα (sq_nonneg _)).trans (hlower y)
  have htangent : ∀ z, A x + deriv A x * z ≤ A (x + z) := by
    intro z
    rcases le_total 0 z with hz | hz
    · have := (convex_Ici x).mul_sub_le_image_sub_of_le_deriv hA1.continuous.continuousOn
        hA1.differentiableOn (C := deriv A x) (fun y hy => by
          rw [interior_Ici] at hy; exact hmono (le_of_lt hy)) x self_mem_Ici (x + z)
        (by simpa using hz) (by linarith)
      rw [add_sub_cancel_left] at this; linarith
    · have := (convex_Iic x).image_sub_le_mul_sub_of_deriv_le hA1.continuous.continuousOn
        hA1.differentiableOn (C := deriv A x) (fun y hy => by
          rw [interior_Iic] at hy; exact hmono (le_of_lt hy)) (x + z) (by simpa using hz) x
        self_mem_Iic (by linarith)
      rw [sub_add_cancel_left] at this; linarith
  set t := Real.tanh x
  set c := m * deriv A x - 2 * t
  have hpt : ∀ z, α / Real.cosh x ^ 2 * Real.exp (m * A x) * Real.exp (c * z - z ^ 2) ≤
      deriv (deriv A) (x + z) * Real.exp (m * A (x + z)) := by
    intro z
    have h1 : α * (Real.exp (-2 * z * t - z ^ 2) / Real.cosh x ^ 2) ≤
        deriv (deriv A) (x + z) := by
      refine (mul_le_mul_of_nonneg_left (inv_cosh_sq_add_lower x z) hα).trans ?_
      rw [mul_one_div]; exact hlower _
    have h2 : Real.exp (m * (A x + deriv A x * z)) ≤ Real.exp (m * A (x + z)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (htangent z) hm)
    calc α / Real.cosh x ^ 2 * Real.exp (m * A x) * Real.exp (c * z - z ^ 2)
        = α / Real.cosh x ^ 2 * Real.exp (m * A x + (c * z - z ^ 2)) := by
          rw [Real.exp_add]; ring
      _ = α * (Real.exp (-2 * z * t - z ^ 2) / Real.cosh x ^ 2) *
            Real.exp (m * (A x + deriv A x * z)) := by
          have e : Real.exp (m * A x + (c * z - z ^ 2)) = Real.exp (-2 * z * t - z ^ 2) *
              Real.exp (m * (A x + deriv A x * z)) := by
            rw [← Real.exp_add]; congr 1; simp only [c]; ring
          rw [e]; ring
      _ ≤ _ := mul_le_mul h1 h2 (Real.exp_pos _).le (le_trans (by positivity) h1)
  have hint1 : Integrable (fun z => Real.exp (c * z - z ^ 2)) (gaussianReal 0 v) := by
    refine Integrable.of_bound (C := Real.exp (c ^ 2 / 4)) (by fun_prop)
      (.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (z - c / 2)])
  calc α * Real.exp (-(v : ℝ)) / Real.cosh x ^ 2 * Real.exp (m * A x)
      = α / Real.cosh x ^ 2 * Real.exp (m * A x) * Real.exp (-(v : ℝ)) := by ring
    _ ≤ α / Real.cosh x ^ 2 * Real.exp (m * A x) *
          ∫ z, Real.exp (c * z - z ^ 2) ∂gaussianReal 0 v := by
        gcongr
        exact integral_gaussian_exp_linear_sub_sq_lower c v
    _ = ∫ z, α / Real.cosh x ^ 2 * Real.exp (m * A x) * Real.exp (c * z - z ^ 2)
          ∂gaussianReal 0 v := (integral_const_mul _ _).symm
    _ ≤ _ := integral_mono (hint1.const_mul _)
        (integrable_mul_exp_comp_add hA1 hfirst (hA2c.comp (by fun_prop)) (fun z => hsecond _)
          hm v x) hpt

/-- Single-layer propagation behind (14.279). This uses concrete Gaussian
integration and the centered mass transform, rather than an assumed moment bound. -/
theorem gaussian_mass_curvature_lower {A : ℝ → ℝ} {α m : ℝ}
    (hA : ContDiff ℝ 2 A) (hα : 0 ≤ α) (hm : m ∈ Icc (0 : ℝ) 1)
    (hfirst : ∀ x, |deriv A x| ≤ 1)
    (hsecond : ∀ x, deriv (deriv A) x ≤ 1)
    (hlower : ∀ x, α / Real.cosh x ^ 2 ≤ deriv (deriv A) x)
    (v : ℝ≥0) (x : ℝ) :
    α * Real.exp (-2 * (v : ℝ)) / Real.cosh x ^ 2 ≤
      deriv (deriv (fun y => massTransform (gaussianReal 0 v) (fun z => A (y + z)) m)) x := by
  have hA1 : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hA2 : ContDiff ℝ 1 (deriv A) := (contDiff_succ_iff_deriv.1 hA).2.2
  have hA2d : Differentiable ℝ (deriv A) := hA2.differentiable one_ne_zero
  have hA2c : Continuous (deriv (deriv A)) := hA2.continuous_deriv le_rfl
  have hA1c : Continuous (deriv A) := hA2d.continuous
  have habs2 : ∀ x, |deriv (deriv A) x| ≤ 1 := fun x => abs_le.2
    ⟨by linarith [(div_nonneg hα (sq_nonneg (Real.cosh x))).trans (hlower x)], hsecond x⟩
  have hlip := abs_sub_le_of_abs_deriv_le_one hA1 hfirst
  have hAgrowth : ∀ y, |A y| ≤ |A 0| + |y| := fun y => by
    have := hlip y 0
    rw [sub_zero] at this
    linarith [abs_sub_abs_le_abs_sub (A y) (A 0)]
  have hexp1 : ∀ y : ℝ, 1 ≤ Real.exp (1 * |y|) := fun y =>
    Real.one_le_exp (by rw [one_mul]; exact abs_nonneg y)
  have hnum := integral_deriv_deriv_mul_exp_lower hA hα hm.1 hfirst habs2 hlower v x
  have hv : Real.exp (-2 * (v : ℝ)) ≤ Real.exp (-(v : ℝ)) :=
    Real.exp_le_exp.2 (by linarith [NNReal.coe_nonneg v])
  rcases eq_or_lt_of_le hm.1 with rfl | hmpos
  · have hU : (fun y => massTransform (gaussianReal 0 v) (fun z => A (y + z)) 0) =
        fun y => ∫ z, A (y + z) ∂gaussianReal 0 v := by
      ext y; simp [massTransform]
    have hd1 : ∀ y, HasDerivAt (fun y => ∫ z, A (y + z) ∂gaussianReal 0 v)
        (∫ z, deriv A (y + z) ∂gaussianReal 0 v) y := fun y =>
      hasDerivAt_integral_gaussian_add (C := |A 0| + 1) (c := 1) (fun y => (hA1 y).hasDerivAt)
        hA1c zero_le_one (fun y => by
          have h1 := Real.add_one_le_exp (1 * |y|)
          rw [one_mul] at h1 ⊢
          nlinarith [hAgrowth y, mul_le_mul_of_nonneg_left (Real.one_le_exp (abs_nonneg y))
            (abs_nonneg (A 0))])
        (fun y => by nlinarith [hfirst y, hexp1 y, abs_nonneg (A 0)]) y
    have hd2 := hasDerivAt_integral_gaussian_add (v := v) (C := 1) (c := 1)
      (fun y => (hA2d y).hasDerivAt) hA2c zero_le_one (fun y => by nlinarith [hfirst y, hexp1 y])
      (fun y => by nlinarith [habs2 y, hexp1 y]) x
    rw [hU, funext fun y => (hd1 y).deriv, hd2.deriv]
    simp only [zero_mul, Real.exp_zero, mul_one] at hnum
    calc α * Real.exp (-2 * (v : ℝ)) / Real.cosh x ^ 2
        ≤ α * Real.exp (-(v : ℝ)) / Real.cosh x ^ 2 := by gcongr
      _ ≤ _ := hnum
  have hm0 : m ≠ 0 := hmpos.ne'
  set E : ℝ → ℝ := fun y => Real.exp (m * A y) with hE
  set g1 : ℝ → ℝ := fun y => m * deriv A y * E y with hg1
  set g2 : ℝ → ℝ := fun y => (m * deriv (deriv A) y + m ^ 2 * deriv A y ^ 2) * E y with hg2
  have hEb : ∀ y, E y ≤ Real.exp |A 0| * Real.exp (1 * |y|) := fun y => by
    rw [one_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : m * A y ≤ |A y| := by
      calc m * A y ≤ m * |A y| := mul_le_mul_of_nonneg_left (le_abs_self _) hm.1
        _ ≤ 1 * |A y| := mul_le_mul_of_nonneg_right hm.2 (abs_nonneg _)
        _ = |A y| := one_mul _
    linarith [hAgrowth y]
  have hC : 0 ≤ Real.exp |A 0| * Real.exp (1 * |(0 : ℝ)|) := by positivity
  have hdE : ∀ y, HasDerivAt E (g1 y) y := fun y => by
    have := (((hA1 y).hasDerivAt.const_mul m).exp)
    convert! this using 1; simp only [hg1, hE]; ring
  have hdg1 : ∀ y, HasDerivAt g1 (g2 y) y := fun y => by
    have := ((hA2d y).hasDerivAt.const_mul m).mul (hdE y)
    convert! this using 1
    simp only [hg2, hg1]; ring
  have hm2 : m ^ 2 ≤ 1 := by nlinarith [hm.1, hm.2]
  have hEpos : ∀ y, 0 < E y := fun y => Real.exp_pos _
  have hef : ∀ y : ℝ, 0 < Real.exp |A 0| * Real.exp (1 * |y|) := fun y => by positivity
  have bE : ∀ y, |E y| ≤ 2 * Real.exp |A 0| * Real.exp (1 * |y|) := fun y => by
    rw [abs_of_pos (Real.exp_pos _)]; nlinarith [hEb y, Real.exp_pos |A 0|, hexp1 y]
  have bg1 : ∀ y, |g1 y| ≤ 2 * Real.exp |A 0| * Real.exp (1 * |y|) := fun y => by
    simp only [hg1, abs_mul, abs_of_pos hmpos, abs_of_pos (hEpos y)]
    have h1 : m * |deriv A y| ≤ 1 := by nlinarith [hfirst y, abs_nonneg (deriv A y), hm.2]
    calc m * |deriv A y| * E y ≤ 1 * E y :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ _ := by nlinarith [hEb y, hef y]
  have bg2 : ∀ y, |g2 y| ≤ 2 * Real.exp |A 0| * Real.exp (1 * |y|) := fun y => by
    simp only [hg2, abs_mul, abs_of_pos (hEpos y)]
    have h1 : |m * deriv (deriv A) y + m ^ 2 * deriv A y ^ 2| ≤ 2 := by
      refine (abs_add_le _ _).trans ?_
      simp only [abs_mul, abs_pow, abs_of_pos hmpos]
      have a2 : |deriv A y| ^ 2 ≤ 1 := by nlinarith [hfirst y, abs_nonneg (deriv A y)]
      have b1 : m * |deriv (deriv A) y| ≤ 1 * 1 :=
        mul_le_mul hm.2 (habs2 y) (abs_nonneg _) zero_le_one
      have b2 : m ^ 2 * |deriv A y| ^ 2 ≤ 1 * 1 := mul_le_mul hm2 a2 (sq_nonneg _) zero_le_one
      linarith
    calc |m * deriv (deriv A) y + m ^ 2 * deriv A y ^ 2| * E y ≤ 2 * E y :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ _ := by nlinarith [hEb y, hef y]
  have hAc := hA1.continuous
  have hcE : Continuous E := by fun_prop
  have hcg2 : Continuous g2 := by fun_prop
  set F : ℝ → ℝ := fun y => ∫ z, E (y + z) ∂gaussianReal 0 v with hF
  set F1 : ℝ → ℝ := fun y => ∫ z, g1 (y + z) ∂gaussianReal 0 v with hF1
  set F2 : ℝ → ℝ := fun y => ∫ z, g2 (y + z) ∂gaussianReal 0 v with hF2
  have hdF : ∀ y, HasDerivAt F (F1 y) y := fun y =>
    hasDerivAt_integral_gaussian_add hdE (by fun_prop) zero_le_one bE bg1 y
  have hdF1 : HasDerivAt F1 (F2 x) x :=
    hasDerivAt_integral_gaussian_add hdg1 hcg2 zero_le_one bg1 bg2 x
  have hiE : ∀ y, Integrable (fun z => E (y + z)) (gaussianReal 0 v) := fun y => by
    simpa using integrable_mul_exp_comp_add (w := fun _ => (1 : ℝ)) hA1 hfirst continuous_const
      (fun _ => by norm_num) hm.1 v y
  have hFpos : ∀ y, 0 < F y := fun y => integral_exp_pos (hiE y)
  have hU : (fun y => massTransform (gaussianReal 0 v) (fun z => A (y + z)) m) =
      fun y => Real.log (F y) / m := by
    ext y; simp [massTransform, hm0, logLaplace, hF, hE]
  have hdU : deriv (fun y => Real.log (F y) / m) = fun y => F1 y / F y / m :=
    funext fun y => (((hdF y).log (hFpos y).ne').div_const m).deriv
  have hd2 : HasDerivAt (fun y => F1 y / F y / m) ((F2 x * F x - F1 x * F1 x) / F x ^ 2 / m) x :=
    (hdF1.div (hdF x) (hFpos x).ne').div_const m
  rw [hU, hdU, hd2.deriv]
  set Z := F x
  set P := ∫ z, deriv A (x + z) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v
  set Q := ∫ z, deriv A (x + z) ^ 2 * Real.exp (m * A (x + z)) ∂gaussianReal 0 v
  set N := ∫ z, deriv (deriv A) (x + z) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v
  have iP := integrable_mul_exp_comp_add (w := fun z => deriv A (x + z)) hA1 hfirst
    (by fun_prop)
    (fun z => hfirst (x + z)) hm.1 v x
  have iQ := integrable_mul_exp_comp_add (w := fun z => deriv A (x + z) ^ 2) hA1 hfirst
    (by fun_prop) (fun z => by
      rw [abs_pow]; nlinarith [hfirst (x + z), abs_nonneg (deriv A (x + z))]) hm.1 v x
  have iN := integrable_mul_exp_comp_add (w := fun z => deriv (deriv A) (x + z)) hA1 hfirst
    (by fun_prop)
    (fun z => habs2 (x + z)) hm.1 v x
  have hF1x : F1 x = m * P := by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun z => by simp only [hg1, hE]; ring)
  have hF2x : F2 x = m * N + m ^ 2 * Q := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iN.const_mul _)
      (iQ.const_mul _)]
    exact integral_congr_ae (.of_forall fun z => by simp only [hg2, hE]; ring)
  have hZpos : 0 < Z := hFpos x
  have hCS : P ^ 2 ≤ Q * Z := by
    have h0 : 0 ≤ ∫ z, (deriv A (x + z) * Z - P) ^ 2 * Real.exp (m * A (x + z))
        ∂gaussianReal 0 v :=
      integral_nonneg fun z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    have hexp : ∫ z, (deriv A (x + z) * Z - P) ^ 2 * Real.exp (m * A (x + z))
        ∂gaussianReal 0 v = Z ^ 2 * Q - 2 * Z * P * P + P ^ 2 * Z := by
      have e : (fun z => (deriv A (x + z) * Z - P) ^ 2 * Real.exp (m * A (x + z))) =
          fun z => Z ^ 2 * (deriv A (x + z) ^ 2 * Real.exp (m * A (x + z))) -
            2 * Z * P * (deriv A (x + z) * Real.exp (m * A (x + z))) +
            P ^ 2 * E (x + z) := by
        ext z; simp only [hE]; ring
      rw [e, integral_add ?_ ((hiE x).const_mul _),
        integral_sub (iQ.const_mul _) (iP.const_mul _), integral_const_mul, integral_const_mul,
        integral_const_mul]
      exact (iQ.const_mul _).sub (iP.const_mul _)
    rw [hexp] at h0
    nlinarith
  have hden : Z ≤ Real.exp (m * A x + v) := integral_exp_mul_comp_add_le hA hfirst habs2 hm v x
  set K := α * Real.exp (-(v : ℝ)) / Real.cosh x ^ 2 * Real.exp (m * A x)
  have hK0 : 0 ≤ K := by positivity
  have hK : α * Real.exp (-2 * (v : ℝ)) / Real.cosh x ^ 2 = K / Real.exp (m * A x + v) := by
    simp only [K]
    rw [show -2 * (v : ℝ) = -(v : ℝ) - v by ring, Real.exp_sub, Real.exp_add]
    field_simp
  calc α * Real.exp (-2 * (v : ℝ)) / Real.cosh x ^ 2 = K / Real.exp (m * A x + v) := hK
    _ ≤ K / Z := div_le_div_of_nonneg_left hK0 hZpos hden
    _ ≤ N / Z := div_le_div_of_nonneg_right hnum hZpos.le
    _ ≤ N / Z + m * (Q * Z - P ^ 2) / Z ^ 2 :=
        le_add_of_nonneg_right (div_nonneg (mul_nonneg hm.1 (by linarith)) (sq_nonneg _))
    _ = _ := by
        rw [hF1x, hF2x]
        field_simp
        ring

/-! ## Uniform gains from local witnesses

Search tag: `PARISI_LB_COMPACTNESS`. Keywords: compact cover, far region,
strict improvement, uniform positive gap, finite witnesses, seven cases.

Consumer: Section 14.8, including the empty far-region case. The witness may
depend on the point, whereas the resulting positive gap is uniform.
-/

/-- A finite set of witnesses suffices, including when the compact set is empty. -/
theorem finite_witnesses_uniform_gap {X I : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {B : I → X → ℝ}
    (hcont : ∀ i, ContinuousOn (B i) K)
    (hneg : ∀ x ∈ K, ∃ i, B i x < 0) :
    ∃ (J : Finset I) (δ : ℝ), 0 < δ ∧
      ∀ x ∈ K, ∃ i ∈ J, B i x ≤ -δ := by
  classical
  choose w hw using fun x : K => hneg x x.2
  choose U hUo hUeq using fun x : K =>
    continuousOn_iff'.1 (hcont (w x)) _ (isOpen_Iio (a := B (w x) x / 2))
  have hxU : ∀ x : K, (x : X) ∈ U x := fun x =>
    ((Set.ext_iff.1 (hUeq x) x).1 ⟨by simp only [mem_preimage, mem_Iio]; linarith [hw x],
      x.2⟩).1
  obtain ⟨t, hcover⟩ := hK.elim_finite_subcover U hUo fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxU _⟩
  obtain ⟨δ, hδ, hδt⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ t, δ ≤ -(B (w x) x / 2) := by
    rcases t.eq_empty_or_nonempty with ht | ht
    · exact ⟨1, one_pos, by simp [ht]⟩
    refine ⟨t.inf' ht fun x => -(B (w x) x / 2), ?_, fun x hx => Finset.inf'_le _ hx⟩
    rw [Finset.lt_inf'_iff]
    intro x _
    linarith [hw x]
  refine ⟨t.image w, δ, hδ, fun y hy => ?_⟩
  obtain ⟨x, hxt, hyx⟩ := mem_iUnion₂.1 (hcover hy)
  have := ((Set.ext_iff.1 (hUeq x) y).2 ⟨hyx, hy⟩).1
  simp only [mem_preimage, mem_Iio] at this
  exact ⟨w x, Finset.mem_image_of_mem _ hxt, by linarith [hδt x hxt]⟩

/-- Upgrade pointwise strict improvement to a common positive gap on a compact set.
Use `finite_witnesses_uniform_gap` when the witness set must also be finite. -/
theorem uniform_gap_of_compact_witnesses {X I : Type*} [TopologicalSpace X]
    [Nonempty I] {K : Set X} (hK : IsCompact K) {B : I → X → ℝ}
    (hcont : ∀ i, ContinuousOn (B i) K)
    (hneg : ∀ x ∈ K, ∃ i, B i x < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∃ i, B i x ≤ -δ := by
  obtain ⟨J, δ, hδ, h⟩ := finite_witnesses_uniform_gap hK hcont hneg
  exact ⟨δ, hδ, fun x hx => (h x hx).imp fun i hi => hi.2⟩

/-- Convert a far-region gap into the same quadratic form as a local estimate. -/
theorem uniform_gap_to_quadratic {A B u q δ : ℝ}
    (hδ : 0 < δ) (hu : u ∈ Icc (-1 : ℝ) 1) (hq : q ∈ Icc (-1 : ℝ) 1)
    (hgap : B ≤ A - δ) : B ≤ A - δ / 4 * (u - q) ^ 2 := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hq1, hq2⟩ := hq
  have : (u - q) ^ 2 ≤ 4 := by nlinarith
  nlinarith

/-- Take one positive coefficient for finitely many levels or cases. -/
theorem finite_uniform_positive_coefficient {ι : Type*} [Fintype ι]
    {P : ι → ℝ → Prop}
    (hmono : ∀ i, ∀ c d : ℝ, 0 < d → d ≤ c → P i c → P i d)
    (hex : ∀ i, ∃ c : ℝ, 0 < c ∧ P i c) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, P i c := by
  choose c hc using hex
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := c)
  refine ⟨c j, (hc j).1, fun i => hmono i _ _ (hc j).1 ?_ (hc i).2⟩
  rw [hj]
  exact ciInf_le (Set.finite_range c).bddBelow i

/-! ## Field truncation and uniform continuity

Search tag: `PARISI_LB_TRUNCATION`. Keywords: clipping, bounded approximation,
finite second moment, L1, L2, product law, shared replica field, pressure continuity.

Consumers: bounded-field approximation for Proposition 14.5.8 and the final
finite-second-moment theorem. Truncation is performed coordinatewise under a
coupling. The same truncated coordinate is used for both replicas.
-/

/-- Symmetric field truncation to the interval with endpoints -R and R when R is
nonnegative. `map_pi_clip` applies this same map independently at every site. -/
def clip (R x : ℝ) : ℝ := max (-R) (min R x)

@[fun_prop]
theorem continuous_clip (R : ℝ) : Continuous (clip R) := by
  unfold clip; fun_prop

theorem clip_eq_self {R x : ℝ} (h : |x| ≤ R) : clip R x = x := by
  unfold clip
  rw [min_eq_right (abs_le.1 h).2, max_eq_right (abs_le.1 h).1]

/-- Pointwise domination for bounded support and dominated convergence of clip errors. -/
theorem clip_bounds {R : ℝ} (hR : 0 ≤ R) (x : ℝ) :
    |clip R x| ≤ R ∧ |clip R x| ≤ |x| ∧
      |x - clip R x| ≤ |x| := by
  have key : clip R x = x ∧ |x| ≤ R ∨ clip R x = R ∧ R ≤ x ∨ clip R x = -R ∧ x ≤ -R := by
    unfold clip
    rcases le_total x (-R) with h | h
    · exact .inr (.inr ⟨by rw [min_eq_right (by linarith), max_eq_left h], h⟩)
    rcases le_total x R with h' | h'
    · exact .inl ⟨by rw [min_eq_right h', max_eq_right h], abs_le.2 ⟨h, h'⟩⟩
    · exact .inr (.inl ⟨by rw [min_eq_left h', max_eq_right (by linarith)], h'⟩)
  rcases key with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> rw [h]
  · simp [h']
  · rw [abs_of_nonneg hR, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact ⟨le_rfl, h', by linarith⟩
  · rw [abs_neg, abs_of_nonneg hR, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    exact ⟨le_rfl, by linarith, by linarith⟩

/-- The L1 truncation cost is finite under a finite first absolute moment. -/
theorem integrable_clip_error {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable id μ) {R : ℝ} (hR : 0 ≤ R) :
    Integrable (fun x => |x - clip R x|) μ := by
  exact hint.abs.mono' (by fun_prop) (.of_forall fun x => by
    simpa using (clip_bounds hR x).2.2)

/-- L1 field approximation as the cutoff tends to infinity; supplies the vanishing
error in `eventual_lower_of_uniform_approximation`. -/
theorem tendsto_integral_clip_error {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable id μ) :
    Tendsto (fun R : ℝ => ∫ x, |x - clip R x| ∂μ) atTop (𝓝 0) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun R x => |x - clip R x|) (f := fun _ => 0) (fun x => |x|)
    (.of_forall fun R => by fun_prop)
    (eventually_ge_atTop 0 |>.mono fun R hR => .of_forall fun x => by
      simpa using (clip_bounds hR x).2.2)
    hint.abs
    (.of_forall fun x => tendsto_const_nhds.congr' <|
      (eventually_ge_atTop |x|).mono fun R hR => by simp [clip_eq_self hR])
  simpa using this

/-- L2 field approximation under the capstone's finite-second-moment assumption. -/
theorem tendsto_integral_sq_clip_error {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x ^ 2) μ) :
    Tendsto (fun R : ℝ => ∫ x, (x - clip R x) ^ 2 ∂μ) atTop (𝓝 0) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
    (F := fun R x => (x - clip R x) ^ 2) (f := fun _ => 0) (fun x => x ^ 2)
    (.of_forall fun R => by fun_prop)
    (eventually_ge_atTop 0 |>.mono fun R hR => .of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq.2 (by simpa using (clip_bounds hR x).2.2))
    hint
    (.of_forall fun x => tendsto_const_nhds.congr' <|
      (eventually_ge_atTop |x|).mono fun R hR => by simp [clip_eq_self hR])
  simpa using this

/-- Any positive truncation preserves nondegeneracy. -/
theorem clipped_law_nondegenerate {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x ^ 2) μ)
    (hpos : 0 < ∫ x : ℝ, x ^ 2 ∂μ) {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (Measure.map (clip R) μ) ∧
      Integrable (fun x : ℝ => x ^ 2) (Measure.map (clip R) μ) ∧
      0 < ∫ x : ℝ, x ^ 2 ∂(Measure.map (clip R) μ) := by
  have hm : AEMeasurable (clip R) μ := (continuous_clip R).aemeasurable
  have hsq : Integrable (fun x => clip R x ^ 2) μ := by
    refine Integrable.of_bound (C := R ^ 2) (by fun_prop) (.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (by linarith [(abs_le.1 (clip_bounds hR.le x).1).1])
      (abs_le.1 (clip_bounds hR.le x).1).2
  refine ⟨Measure.isProbabilityMeasure_map hm, ?_, ?_⟩
  · exact (integrable_map_measure (by fun_prop) hm).2 hsq
  rw [integral_map hm (by fun_prop)]
  refine lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg _) fun h => hpos.ne' ?_
  have h0 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hsq).1 h.symm
  refine integral_eq_zero_of_ae (h0.mono fun x hx => ?_)
  simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero] at hx ⊢
  unfold clip at hx
  rcases le_total x R with h1 | h1
  · rw [min_eq_right h1] at hx
    rcases le_total x (-R) with h2 | h2
    · rw [max_eq_left h2] at hx; linarith
    · rwa [max_eq_right h2] at hx
  · rw [min_eq_left h1, max_eq_right (by linarith)] at hx; linarith

/-- Coupled laws are close on every Lipschitz observable; the observable need not be bounded. -/
theorem abs_integral_lipschitz_coupling {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ} {f : ℝ → ℝ}
    {L : ℝ} (hL : 0 ≤ L) (hLip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hX : Integrable X μ) (hY : Integrable Y μ) :
    |(∫ ω, f (X ω) ∂μ) - (∫ ω, f (Y ω) ∂μ)| ≤
      L * ∫ ω, |X ω - Y ω| ∂μ := by
  have hf : Continuous f := by
    have : LipschitzWith (Real.toNNReal L) f := LipschitzWith.of_dist_le_mul fun x y => by
      simpa [Real.dist_eq, Real.coe_toNNReal _ hL] using hLip x y
    exact this.continuous
  have hint : ∀ Z : Ω → ℝ, Integrable Z μ → Integrable (fun ω => f (Z ω)) μ := fun Z hZ =>
    ((integrable_const (|f 0|)).add (hZ.abs.const_mul L)).mono'
      (hf.comp_aestronglyMeasurable hZ.1) (.of_forall fun ω => by
        have := hLip (Z ω) 0
        rw [sub_zero] at this
        simp only [Real.norm_eq_abs, Pi.add_apply]
        linarith [abs_sub_abs_le_abs_sub (f (Z ω)) (f 0)])
  rw [← integral_sub (hint X hX) (hint Y hY), ← integral_const_mul]
  exact abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
    (.of_forall fun _ => abs_nonneg _) ((hX.sub hY).abs.const_mul L)
    (.of_forall fun ω => hLip _ _))

/-- Finite log partition functions are stable under a uniform energy perturbation. -/
theorem abs_log_sum_exp_sub_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {H G : ι → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, |H i - G i| ≤ c) :
    |Real.log (∑ i, Real.exp (H i)) - Real.log (∑ i, Real.exp (G i))| ≤ c := by
  have key : ∀ H G : ι → ℝ, (∀ i, H i - G i ≤ c) →
      Real.log (∑ i, Real.exp (H i)) - Real.log (∑ i, Real.exp (G i)) ≤ c := by
    intro H G h
    have hG : 0 < ∑ i, Real.exp (G i) := Finset.sum_pos (fun i _ => Real.exp_pos _)
      Finset.univ_nonempty
    have hH : 0 < ∑ i, Real.exp (H i) := Finset.sum_pos (fun i _ => Real.exp_pos _)
      Finset.univ_nonempty
    rw [sub_le_iff_le_add, ← Real.log_exp c, ← Real.log_mul (Real.exp_pos c).ne' hG.ne']
    refine Real.log_le_log hH ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith [h i])
  rw [abs_sub_le_iff]
  exact ⟨key H G fun i => (abs_le.1 (h i)).2, key G H fun i => by linarith [(abs_le.1 (h i)).1]⟩

/-- Field continuity for an arbitrary finite spin system; replicas can be included
in the configuration type. The coefficient bound is one for a single replica. -/
theorem abs_normalized_log_partition_field_sub_le
    {Config : Type*} [Fintype Config] [Nonempty Config] {n : ℕ} (hn : 0 < n)
    (H : Config → ℝ) (σ : Config → Fin n → ℝ) (hσ : ∀ s i, |σ s i| ≤ 1)
    (h g : Fin n → ℝ) :
    |Real.log (∑ s, Real.exp (H s + ∑ i, h i * σ s i)) / n -
      Real.log (∑ s, Real.exp (H s + ∑ i, g i * σ s i)) / n| ≤
        (∑ i, |h i - g i|) / n := by
  rw [← sub_div, abs_div, Nat.abs_cast]
  gcongr
  refine abs_log_sum_exp_sub_le (Finset.sum_nonneg fun i _ => abs_nonneg _) fun s => ?_
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← sub_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hσ s i)

/-- The normalized product-coordinate truncation cost equals the one-site cost. -/
theorem integral_average_clip_error {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable id μ) {R : ℝ} (hR : 0 ≤ R) {n : ℕ} (hn : 0 < n) :
    (∫ x : Fin n → ℝ, (∑ i, |x i - clip R (x i)|) / n
      ∂(Measure.pi (fun _ : Fin n => μ))) = ∫ x, |x - clip R x| ∂μ := by
  have hi : ∀ i : Fin n, (∫ x : Fin n → ℝ, |x i - clip R (x i)| ∂(Measure.pi fun _ => μ)) =
      ∫ x, |x - clip R x| ∂μ := fun i => by
    conv_rhs => rw [← (measurePreserving_eval (fun _ : Fin n => μ) i).map_eq]
    rw [integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]
  have hint' : ∀ i : Fin n, Integrable (fun x : Fin n → ℝ => |x i - clip R (x i)|)
      (Measure.pi fun _ => μ) := fun i =>
    (measurePreserving_eval (fun _ : Fin n => μ) i).integrable_comp_of_integrable
      (integrable_clip_error hint hR)
  rw [integral_div, integral_finset_sum _ fun i _ => hint' i]
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Coordinatewise truncation has the i.i.d. product of the truncated site laws. -/
theorem map_pi_clip {μ : Measure ℝ} [IsProbabilityMeasure μ] (R : ℝ) (n : ℕ) :
    Measure.map (fun x : Fin n → ℝ => fun i => clip R (x i))
      (Measure.pi (fun _ : Fin n => μ)) =
        Measure.pi (fun _ : Fin n => Measure.map (clip R) μ) := by
  exact Measure.pi_map_pi fun _ => (continuous_clip R).aemeasurable

/-! ## Bounded-field fluctuations and pressure gaps

Search tag: `PARISI_LB_CONCENTRATION`. Keywords: McDiarmid, Hoeffding, MGF,
conditional Gaussian concentration, field fluctuations, capped exponential.

Consumer: the random-field transfer missing after (14.123). Gaussian fluctuation
around a conditional mean is already supported in the repository. The first
lemma supplies concentration of that mean for bounded independent coordinates.
The next lemma combines the two fluctuations without asserting a conditional
gap from a law-averaged gap. No independence of the two fluctuations is assumed.
-/

/-- Bounded coordinate oscillations bound the total oscillation. -/
theorem abs_sub_le_sum_of_bounded_differences {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : (ι → ℝ) → ℝ} {c : ι → ℝ}
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ c i) (x y : ι → ℝ) :
    |F y - F x| ≤ ∑ i, c i := by
  have key : ∀ s : Finset ι, |F (s.piecewise y x) - F x| ≤ ∑ i ∈ s, c i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.piecewise_insert, Finset.sum_insert ha]
      calc |F (Function.update (s.piecewise y x) a (y a)) - F x|
          ≤ |F (Function.update (s.piecewise y x) a (y a)) - F (s.piecewise y x)| +
            |F (s.piecewise y x) - F x| := abs_sub_le _ _ _
        _ ≤ c a + ∑ i ∈ s, c i := add_le_add (hosc _ _ _) ih
  simpa using key Finset.univ

theorem abs_le_of_bounded_differences {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : (ι → ℝ) → ℝ} {c : ι → ℝ}
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ c i) (x : ι → ℝ) :
    |F x| ≤ |F 0| + ∑ i, c i := by
  have := abs_sub_le_sum_of_bounded_differences hosc 0 x
  have := abs_sub_abs_le_abs_sub (F x) (F 0)
  linarith

theorem integrable_of_bounded_differences {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {κ : Measure Ω} [IsFiniteMeasure κ] {F : (ι → ℝ) → ℝ} {c : ι → ℝ}
    (hF : Measurable F) (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ c i)
    {φ : Ω → ι → ℝ} (hφ : Measurable φ) :
    Integrable (fun ω => F (φ ω)) κ :=
  Integrable.of_bound (C := |F 0| + ∑ i, c i) (hF.comp hφ).aestronglyMeasurable
    (.of_forall fun ω => abs_le_of_bounded_differences hosc (φ ω))

theorem integrable_exp_of_bounded_differences {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {κ : Measure Ω} [IsFiniteMeasure κ] {F : (ι → ℝ) → ℝ} {c : ι → ℝ}
    (hF : Measurable F) (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ c i)
    {φ : Ω → ι → ℝ} (hφ : Measurable φ) (t E : ℝ) :
    Integrable (fun ω => Real.exp (t * (F (φ ω) - E))) κ := by
  refine Integrable.of_bound (C := Real.exp (|t| * (|F 0| + ∑ i, c i + |E|)))
    (Real.continuous_exp.measurable.comp
      (((hF.comp hφ).sub_const E).const_mul t)).aestronglyMeasurable
    (.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]
  gcongr
  have := abs_le_of_bounded_differences hosc (φ ω)
  have := abs_sub (F (φ ω)) E
  linarith

/-- McDiarmid's exponential-moment bound, by induction on the number of coordinates. -/
theorem integral_exp_le_of_bounded_differences : ∀ {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {F : (Fin n → ℝ) → ℝ} (hF : Measurable F)
    (c : Fin n → ℝ) (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ c i) (t : ℝ),
    (∫ x, Real.exp (t * (F x - ∫ y, F y ∂(Measure.pi μ))) ∂(Measure.pi μ)) ≤
      Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8)
  | 0, μ, _, F, _, c, _, t => by
    have hconst : ∀ x, F x = F default := fun x => congrArg F (Subsingleton.elim x default)
    simp [hconst]
  | n + 1, μ, _, F, hF, c, hosc, t => by
    classical
    set ν := Measure.pi fun j : Fin n => μ j.succ
    set φ : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun p => Fin.cons p.1 p.2
    have hφ : MeasurePreserving φ ((μ 0).prod ν) (Measure.pi μ) := by
      have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
      convert! hmp using 1
      ext p : 1
      simp [φ, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero']
    have hφm : Measurable φ := hφ.measurable
    have htrans : ∀ f : (Fin (n + 1) → ℝ) → ℝ, Measurable f →
        ∫ x, f x ∂(Measure.pi μ) = ∫ p, f (φ p) ∂((μ 0).prod ν) := fun f hf => by
      rw [← hφ.map_eq, integral_map hφm.aemeasurable hf.aestronglyMeasurable]
    set G : ℝ → (Fin n → ℝ) → ℝ := fun x₀ x' => F (Fin.cons x₀ x')
    have hGm : ∀ x₀, Measurable (G x₀) := fun x₀ =>
      hF.comp (hφm.comp (measurable_prodMk_left (m := inferInstance)))
    have hGosc : ∀ x₀ x' j y, |G x₀ (Function.update x' j y) - G x₀ x'| ≤ c j.succ := by
      intro x₀ x' j y
      simp only [G]
      rw [Fin.cons_update]
      exact hosc _ _ _
    have hGint : ∀ x₀, Integrable (G x₀) ν := fun x₀ =>
      integrable_of_bounded_differences (hGm x₀) (hGosc x₀) measurable_id
    set g : ℝ → ℝ := fun x₀ => ∫ x', G x₀ x' ∂ν
    have hgm : Measurable g :=
      ((hF.comp hφm).stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
    have hgosc : ∀ x₀ y₀, g y₀ ≤ g x₀ + c 0 := by
      intro x₀ y₀
      have hpt : ∀ x', G y₀ x' ≤ G x₀ x' + c 0 := fun x' => by
        have := hosc (Fin.cons x₀ x') 0 y₀
        rw [Fin.update_cons_zero] at this
        linarith [le_abs_self (G y₀ x' - G x₀ x')]
      calc g y₀ ≤ ∫ x', (G x₀ x' + c 0) ∂ν :=
            integral_mono (hGint y₀) ((hGint x₀).add (integrable_const _)) hpt
        _ = g x₀ + c 0 := by rw [integral_add (hGint x₀) (integrable_const _)]; simp [g]
    have hbdd : BddBelow (range g) :=
      ⟨g 0 - c 0, by rintro _ ⟨y, rfl⟩; linarith [hgosc y 0]⟩
    set a := ⨅ x₀, g x₀
    have hga : ∀ x₀, g x₀ ∈ Icc a (a + c 0) := fun x₀ =>
      ⟨ciInf_le hbdd x₀, by
        have : g x₀ - c 0 ≤ a := le_ciInf fun y => by linarith [hgosc y x₀]
        linarith⟩
    have hE : ∫ y, F y ∂(Measure.pi μ) = ∫ x₀, g x₀ ∂(μ 0) := by
      rw [htrans F hF, integral_prod _ (integrable_of_bounded_differences hF hosc hφm)]
    set E := ∫ y, F y ∂(Measure.pi μ)
    set B' := Real.exp (t ^ 2 * (∑ j : Fin n, c j.succ ^ 2) / 8)
    have hIH : ∀ x₀, ∫ x', Real.exp (t * (G x₀ x' - g x₀)) ∂ν ≤ B' := fun x₀ =>
      integral_exp_le_of_bounded_differences (fun j => μ j.succ) (hGm x₀) (fun j => c j.succ)
        (hGosc x₀) t
    have hH := (hasSubgaussianMGF_of_mem_Icc (μ := μ 0) hgm.aemeasurable
      (ae_of_all _ hga)).mgf_le t
    rw [mgf, ← hE] at hH
    have hnorm : (((‖a + c 0 - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2 = t ^ 2 * c 0 ^ 2 / 8 := by
      rw [add_sub_cancel_left]
      push_cast
      rw [Real.norm_eq_abs, div_pow, sq_abs]
      ring
    rw [hnorm] at hH
    have hexpE : Measurable fun x : Fin (n + 1) → ℝ => Real.exp (t * (F x - E)) :=
      Real.continuous_exp.measurable.comp ((hF.sub_const E).const_mul t)
    have hjoint := integrable_exp_of_bounded_differences (κ := (μ 0).prod ν) hF hosc hφm t E
    rw [htrans _ hexpE, integral_prod _ hjoint]
    have hpt : ∀ x₀, ∫ x', Real.exp (t * (F (φ (x₀, x')) - E)) ∂ν ≤
        Real.exp (t * (g x₀ - E)) * B' := fun x₀ => by
      have : (fun x' => Real.exp (t * (F (φ (x₀, x')) - E))) =
          fun x' => Real.exp (t * (g x₀ - E)) * Real.exp (t * (G x₀ x' - g x₀)) := by
        ext x'; rw [← Real.exp_add]; congr 1; simp only [G, φ]; ring
      rw [this, integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hIH x₀) (Real.exp_nonneg _)
    have hgint : Integrable (fun x₀ => Real.exp (t * (g x₀ - E))) (μ 0) := by
      refine Integrable.of_bound (C := Real.exp (|t| * (|a| + |c 0| + |E|)))
        (Real.continuous_exp.measurable.comp ((hgm.sub_const E).const_mul t)).aestronglyMeasurable
        (.of_forall fun x₀ => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]
      gcongr
      obtain ⟨h1, h2⟩ := hga x₀
      rw [abs_le]
      constructor <;> cases abs_cases a <;> cases abs_cases (c 0) <;> cases abs_cases E <;>
        linarith
    calc ∫ x₀, ∫ x', Real.exp (t * (F (φ (x₀, x')) - E)) ∂ν ∂(μ 0)
        ≤ ∫ x₀, Real.exp (t * (g x₀ - E)) * B' ∂(μ 0) :=
          integral_mono hjoint.integral_prod_left (hgint.mul_const _) hpt
      _ = (∫ x₀, Real.exp (t * (g x₀ - E)) ∂(μ 0)) * B' := integral_mul_const _ _
      _ ≤ Real.exp (t ^ 2 * c 0 ^ 2 / 8) * B' :=
          mul_le_mul_of_nonneg_right hH (Real.exp_nonneg _)
      _ = Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
          rw [← Real.exp_add, Fin.sum_univ_succ]; ring_nf

/-- Product-measure bounded differences in exponential-moment form.
The coordinate oscillation can be obtained on clipped inputs, so the inequality
can be imposed globally even when the original site law has unbounded support. -/
theorem bounded_differences_mgf {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {F : (Fin n → ℝ) → ℝ}
    (hF : Measurable F) (hint : Integrable F (Measure.pi μ))
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hosc : ∀ x i y, |F (Function.update x i y) - F x| ≤ c i) (t : ℝ) :
    Integrable (fun x => Real.exp (t * (F x - ∫ y, F y ∂(Measure.pi μ))))
      (Measure.pi μ) ∧
    (∫ x, Real.exp (t * (F x - ∫ y, F y ∂(Measure.pi μ))) ∂(Measure.pi μ)) ≤
      Real.exp (t ^ 2 * (∑ i, c i ^ 2) / 8) := by
  exact ⟨integrable_exp_of_bounded_differences hF hosc measurable_id t _,
    integral_exp_le_of_bounded_differences μ hF c hosc t⟩

/-- Uniform conditional Gaussian bounds and bounded-field mean bounds combine additively. -/
theorem mgf_prod_of_section_and_mean_bounds
    {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    {μ : Measure Ω} {ν : Measure H} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {L : Ω → H → ℝ} {m : H → ℝ} {A B t : ℝ}
    (hm : Integrable m ν)
    (hjoint : Integrable (fun z : Ω × H =>
      Real.exp (t * (L z.1 z.2 - ∫ h, m h ∂ν))) (μ.prod ν))
    (hsection : ∀ᵐ h ∂ν,
      (∫ ω, Real.exp (t * (L ω h - m h)) ∂μ) ≤ Real.exp (A * t ^ 2 / 2))
    (hmean : Integrable (fun h => Real.exp (t * (m h - ∫ y, m y ∂ν))) ν)
    (hmean_bound : (∫ h, Real.exp (t * (m h - ∫ y, m y ∂ν)) ∂ν) ≤
      Real.exp (B * t ^ 2 / 2)) :
    (∫ z : Ω × H, Real.exp (t * (L z.1 z.2 - ∫ h, m h ∂ν)) ∂(μ.prod ν)) ≤
      Real.exp ((A + B) * t ^ 2 / 2) := by
  have hsplit : ∀ h, (∫ ω, Real.exp (t * (L ω h - ∫ y, m y ∂ν)) ∂μ) =
      Real.exp (t * (m h - ∫ y, m y ∂ν)) * ∫ ω, Real.exp (t * (L ω h - m h)) ∂μ := fun h => by
    rw [← integral_const_mul]
    congr 1 with ω
    rw [← Real.exp_add]; ring_nf
  have hint := Integrable.integral_prod_right hjoint
  simp only [hsplit] at hint
  rw [integral_prod_symm _ hjoint]
  simp only [hsplit]
  calc (∫ h, Real.exp (t * (m h - ∫ y, m y ∂ν)) * ∫ ω, Real.exp (t * (L ω h - m h)) ∂μ ∂ν)
      ≤ ∫ h, Real.exp (t * (m h - ∫ y, m y ∂ν)) * Real.exp (A * t ^ 2 / 2) ∂ν := by
        refine integral_mono_ae hint (hmean.mul_const _) ?_
        filter_upwards [hsection] with h hh
        exact mul_le_mul_of_nonneg_left hh (Real.exp_nonneg _)
    _ ≤ Real.exp (B * t ^ 2 / 2) * Real.exp (A * t ^ 2 / 2) := by
        rw [integral_mul_const]
        exact mul_le_mul_of_nonneg_right hmean_bound (Real.exp_nonneg _)
    _ = Real.exp ((A + B) * t ^ 2 / 2) := by rw [← Real.exp_add]; ring_nf

/-- A negative extensive mean and an MGF estimate make the capped exponential small.
This is an analytic reduction; the actual logarithmic cascade product must first
be shown to satisfy its mean and MGF hypotheses. -/
theorem integral_capped_exp_le_of_mgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L : Ω → ℝ}
    (hL : Measurable L) (hint : Integrable L μ)
    {n : ℕ} (hn : 0 < n) {a C : ℝ} (ha : 0 < a) (hC : 0 < C)
    (hmean : (∫ ω, L ω ∂μ) ≤ -a * n)
    (hmgf : ∀ t : ℝ,
      Integrable (fun ω => Real.exp (t * (L ω - ∫ z, L z ∂μ))) μ ∧
      (∫ ω, Real.exp (t * (L ω - ∫ z, L z ∂μ)) ∂μ) ≤
        Real.exp (C * n * t ^ 2 / 2)) :
    (∫ ω, min 1 (Real.exp (L ω)) ∂μ) ≤
      Real.exp (-a * n / 2) + Real.exp (-(a ^ 2 * n) / (8 * C)) := by
  set t := a / (2 * C)
  have ht : 0 ≤ t := by positivity
  obtain ⟨hI, hB⟩ := hmgf t
  set E := ∫ z, L z ∂μ
  have hpt : ∀ ω, min 1 (Real.exp (L ω)) ≤
      Real.exp (-a * n / 2) + Real.exp (-(t * a * n / 2)) * Real.exp (t * (L ω - E)) := by
    intro ω
    rcases lt_or_ge (L ω) (-a * n / 2) with h | h
    · exact (min_le_right _ _).trans ((Real.exp_le_exp.2 h.le).trans
        (le_add_of_nonneg_right (by positivity)))
    · refine (min_le_left _ _).trans (le_add_of_nonneg_of_le (Real.exp_nonneg _) ?_)
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
  calc (∫ ω, min 1 (Real.exp (L ω)) ∂μ)
      ≤ ∫ ω, (Real.exp (-a * n / 2) +
          Real.exp (-(t * a * n / 2)) * Real.exp (t * (L ω - E))) ∂μ :=
        integral_mono_of_nonneg (.of_forall fun ω => by positivity)
          ((integrable_const _).add (hI.const_mul _)) (.of_forall hpt)
    _ ≤ Real.exp (-a * n / 2) +
          Real.exp (-(t * a * n / 2)) * Real.exp (C * n * t ^ 2 / 2) := by
        rw [integral_add (integrable_const _) (hI.const_mul _), integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
        gcongr
    _ = Real.exp (-a * n / 2) + Real.exp (-(a ^ 2 * n) / (8 * C)) := by
        rw [← Real.exp_add]
        congr 2
        simp only [t]
        field_simp
        ring

/-- Cauchy–Schwarz for nonnegative square-integrable functions, in square-root form. -/
theorem integral_mul_le_sqrt_mul_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ ω, f ω * g ω ∂μ ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have h2 : ENNReal.ofReal 2 = 2 := by simp
  have := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hf0 hg0
    (h2 ▸ hf) (h2 ▸ hg)
  simpa only [Real.sqrt_eq_rpow, Real.rpow_two] using this

/-- Separate a bounded terminal factor from an unbounded positive weight. -/
theorem integral_weight_mul_le_of_small_event {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W B : Ω → ℝ} {s : Set Ω}
    (hs : MeasurableSet s) (hW : Integrable (fun ω => W ω ^ 2) μ)
    (hB : Measurable B) (hBbound : ∀ ω, B ω ∈ Icc (0 : ℝ) 1)
    {η : ℝ} (hη : 0 ≤ η) (hoff : ∀ ω ∉ s, B ω ≤ η) :
    (∫ ω, |W ω| * B ω ∂μ) ≤
      Real.sqrt (∫ ω, W ω ^ 2 ∂μ) * (η + Real.sqrt (μ.real s)) := by
  set I : Ω → ℝ := s.indicator fun _ => 1
  have hV : AEStronglyMeasurable (fun ω => |W ω|) μ := by
    have : (fun ω => |W ω|) = fun ω => Real.sqrt (W ω ^ 2) := by
      ext ω; rw [Real.sqrt_sq_eq_abs]
    rw [this]
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hW.1
  have hV2 : MemLp (fun ω => |W ω|) 2 μ :=
    (memLp_two_iff_integrable_sq hV).2 (by simpa only [sq_abs] using hW)
  have hVi : Integrable (fun ω => |W ω|) μ := hV2.integrable one_le_two
  have hind : MemLp I 2 μ := (memLp_const 1).indicator hs
  have hmul : Integrable (fun ω => |W ω| * I ω) μ := hV2.integrable_mul hind
  have hpt : ∀ ω, |W ω| * B ω ≤ η * |W ω| + |W ω| * I ω := by
    intro ω
    by_cases hω : ω ∈ s
    · simp only [I, indicator_of_mem hω, mul_one]
      nlinarith [abs_nonneg (W ω), (hBbound ω).2]
    · simp only [I, indicator_of_notMem hω, mul_zero, add_zero]
      nlinarith [abs_nonneg (W ω), hoff ω hω]
  have h1 := integral_mul_le_sqrt_mul_sqrt (.of_forall fun ω => abs_nonneg (W ω))
    (.of_forall fun _ => zero_le_one) hV2 (memLp_const (1 : ℝ))
  have h2 := integral_mul_le_sqrt_mul_sqrt (.of_forall fun ω => abs_nonneg (W ω))
    (.of_forall fun ω => indicator_nonneg (fun _ _ => zero_le_one) ω) hV2 hind
  simp only [mul_one, sq_abs, one_pow, integral_const, probReal_univ, one_smul,
    Real.sqrt_one] at h1 h2
  have hsq : ∀ ω, I ω ^ 2 = I ω := by
    intro ω; by_cases hω : ω ∈ s <;> simp [I, hω]
  simp only [hsq, I, integral_indicator_const _ hs, smul_eq_mul, mul_one] at h2
  have hS := Real.sqrt_nonneg (∫ ω, W ω ^ 2 ∂μ)
  calc (∫ ω, |W ω| * B ω ∂μ)
      ≤ ∫ ω, (η * |W ω| + |W ω| * I ω) ∂μ :=
        integral_mono_of_nonneg (.of_forall fun ω => mul_nonneg (abs_nonneg _) (hBbound ω).1)
          ((hVi.const_mul η).add hmul) (.of_forall hpt)
    _ = η * ∫ ω, |W ω| ∂μ + ∫ ω, |W ω| * I ω ∂μ := by
        rw [integral_add (hVi.const_mul η) hmul, integral_const_mul]
    _ ≤ _ := by nlinarith

/-! ## Localization with the required uniform quantifiers

Search tag: `PARISI_LB_LOCALIZATION`. Keywords: bad overlap event, finite overlap
count, exponential decay, uniform time threshold, joint branch probability.

Consumer: (14.110). The coefficient in the main estimate is fixed before the
auxiliary accuracy. Finite overlap sums retain their volume-dependent cardinality.
-/

/-- The quadratic main estimate supplies the gap needed by concentration. -/
theorem pressure_gap_of_overlap_distance {Ψ ψ φ u q K ε : ℝ}
    (hK : 0 < K) (hε : 0 < ε) (hgap : 0 ≤ ψ - φ)
    (hmain : Ψ ≤ 2 * ψ - (u - q) ^ 2 / K)
    (hfar : 2 * K * (ψ - φ + ε) ≤ (u - q) ^ 2) :
    Ψ ≤ 2 * φ - 2 * ε := by
  have : 2 * (ψ - φ + ε) ≤ (u - q) ^ 2 / K := by
    rw [le_div_iff₀ hK]; linarith
  linarith

/-- At most 2n+1 possible overlaps: a uniform exponential bound survives summation. -/
theorem finite_overlap_sum_le {ι : Type*} (s : Finset ι) {n : ℕ}
    (hcard : s.card ≤ 2 * n + 1) {p : ι → ℝ} {C c : ℝ} (hC : 0 ≤ C)
    (hp : ∀ i ∈ s, p i ≤ C * Real.exp (-c * n)) :
    ∑ i ∈ s, p i ≤ (2 * (n : ℝ) + 1) * C * Real.exp (-c * n) := by
  calc ∑ i ∈ s, p i ≤ s.card • (C * Real.exp (-c * n)) := Finset.sum_le_card_nsmul _ _ _ hp
    _ ≤ (2 * (n : ℝ) + 1) * C * Real.exp (-c * n) := by
      rw [nsmul_eq_mul, mul_assoc]
      gcongr
      exact_mod_cast hcard

/-- Exponential decay absorbs the linear number of possible overlaps.
Used by `eventually_uniform_finite_overlap_sum` to choose one volume threshold. -/
theorem eventually_overlap_exponential_small {C c ε : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (2 * (n : ℝ) + 1) * C * Real.exp (-c * n) ≤ ε := by
  have hlin : Tendsto (fun n : ℕ => c * n) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hlin
  have h0 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hlin
  have : Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) * C * Real.exp (-c * n)) atTop (𝓝 0) := by
    have := ((h1.const_mul (2 / c)).add h0).mul_const C
    simp only [Function.comp_def, pow_one, pow_zero, one_mul, mul_zero, zero_add,
      zero_mul] at this
    refine this.congr fun n => ?_
    rw [neg_mul]
    field_simp
  exact this.eventually (ge_mem_nhds hε)

/-- Uniformity in time and level is preserved when summing constrained masses. -/
theorem eventually_uniform_finite_overlap_sum
    {T I : Type*} {S : ℕ → Finset I} {p : ℕ → T → I → ℝ}
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hcard : ∀ n, (S n).card ≤ 2 * n + 1)
    (hbound : ∀ n t i, i ∈ S n → p n t i ≤ C * Real.exp (-c * n)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t, ∑ i ∈ S n, p n t i ≤ ε := by
  intro ε hε
  filter_upwards [eventually_overlap_exponential_small hC hc hε] with n hn t
  exact (finite_overlap_sum_le _ (hcard n) hC (hbound n t)).trans hn

/-- Joint branch mass is enough; no division by its probability is necessary. -/
theorem localized_joint_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {R : Ω → ℝ} {B : Set Ω}
    (hR : Measurable R) (hB : MeasurableSet B)
    (hRbound : ∀ᵐ ω ∂μ, R ω ∈ Icc (-1 : ℝ) 1)
    {q a ε : ℝ} (hq : q ∈ Icc (-1 : ℝ) 1) (ha : 0 ≤ a)
    (hbad : μ.real (B ∩ {ω | a ≤ (R ω - q) ^ 2}) ≤ ε) :
    (∫ ω in B, (R ω - q) ^ 2 ∂μ) ≤ a * μ.real B + 4 * ε := by
  set S := {ω | a ≤ (R ω - q) ^ 2}
  have hS : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hI : Integrable (fun ω => a + S.indicator (fun _ => (4 : ℝ)) ω) (μ.restrict B) :=
    (integrable_const _).add ((integrable_const _).indicator hS)
  calc (∫ ω in B, (R ω - q) ^ 2 ∂μ)
      ≤ ∫ ω in B, (a + S.indicator (fun _ => (4 : ℝ)) ω) ∂μ := by
        refine integral_mono_of_nonneg (.of_forall fun _ => sq_nonneg _) hI ?_
        refine ae_restrict_of_ae (hRbound.mono fun ω hω => ?_)
        dsimp only
        by_cases h : ω ∈ S
        · rw [indicator_of_mem h]
          obtain ⟨h1, h2⟩ := hω
          obtain ⟨h3, h4⟩ := hq
          nlinarith
        · rw [indicator_of_notMem h]
          simp only [S, mem_setOf_eq, not_le] at h
          linarith
    _ = a * μ.real B + 4 * μ.real (B ∩ S) := by
        rw [integral_add (integrable_const _) ((integrable_const _).indicator hS),
          integral_indicator_const _ hS, setIntegral_const]
        simp only [smul_eq_mul, measureReal_restrict_apply hS]
        rw [inter_comm]; ring
    _ ≤ a * μ.real B + 4 * ε := by linarith

/-- Sum joint localization bounds with an explicit total error budget. One may
allocate ε divided by the number of levels to each error; proportionality to a
branch probability is not assumed. -/
theorem weighted_localization_sum {ι : Type*} [Fintype ι]
    {w x e : ι → ℝ} {a ε : ℝ} (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i ≤ 1) (ha : 0 ≤ a) (herr : ∑ i, e i ≤ ε)
    (hx : ∀ i, x i ≤ a * w i + e i) :
    ∑ i, x i ≤ a + ε := by
  calc ∑ i, x i ≤ ∑ i, (a * w i + e i) := Finset.sum_le_sum fun i _ => hx i
    _ = a * ∑ i, w i + ∑ i, e i := by rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a + ε := by nlinarith

/-! ## Interpolation, endpoint passage, and approximation transfer

Search tag: `PARISI_LB_ENDPOINT`. Keywords: Gronwall, differential inequality,
time cutoff, terminal time, eventual epsilon lower bound, truncation transfer.

Consumers: Theorem 14.5.4, (14.109), and the eventual lower-bound capstone.
Differentiability is only required at interior times. Endpoint continuity is
explicit. In the eventual statements all time points use the same volume threshold.
-/

/-- Gronwall estimate for an interpolation gap starting at zero.
Analytic input for Theorem 14.5.4 and the eventual uniform estimate below. -/
theorem gronwall_zero_initial {f D : ℝ → ℝ} {T K ε : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hc : ContinuousOn f (Icc (0 : ℝ) T)) (hzero : f 0 = 0)
    (hd : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt f (D t) t)
    (hineq : ∀ t ∈ Ioo (0 : ℝ) T, D t ≤ K * (f t + ε)) :
    ∀ t ∈ Icc (0 : ℝ) T, f t ≤ ε * (Real.exp (K * t) - 1) := by
  set g : ℝ → ℝ := fun t => (f t + ε) * Real.exp (-(K * t))
  have hg : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt g ((D t - K * (f t + ε)) * Real.exp (-(K * t))) t := by
    intro t ht
    have h2 : HasDerivAt (fun s => -(K * s)) (-K) t := by
      convert! ((hasDerivAt_id t).const_mul K).neg using 1 <;> simp
    convert! ((hd t ht).add_const ε).mul h2.exp using 1
    ring
  have hanti : AntitoneOn g (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) ?_ ?_ ?_
    · exact (hc.add continuousOn_const).mul (by fun_prop)
    · rw [interior_Icc]
      exact fun t ht => (hg t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hg t ht).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hineq t ht]) (Real.exp_nonneg _)
  intro t ht
  have h := hanti ⟨le_rfl, hT⟩ ht ht.1
  simp only [g, hzero, zero_add, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
  have := (le_div_iff₀ (Real.exp_pos _)).2 h
  rw [Real.exp_neg, div_inv_eq_mul] at this
  linarith

/-- Constant K is chosen before ε; thresholds may depend on ε. -/
theorem eventually_uniform_small_of_differential_inequality
    {f D : ℕ → ℝ → ℝ} {T K : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K)
    (hc : ∀ n, ContinuousOn (f n) (Icc (0 : ℝ) T))
    (hzero : ∀ n, f n 0 = 0)
    (hd : ∀ n t, t ∈ Ioo (0 : ℝ) T → HasDerivAt (f n) (D n t) t)
    (hineq : ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Ioo (0 : ℝ) T,
      D n t ≤ K * (f n t + ε)) :
    ∀ δ > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, f n t ≤ δ := by
  intro δ hδ
  have hE := Real.exp_pos (K * T)
  filter_upwards [hineq (δ / Real.exp (K * T)) (by positivity)] with n hn t ht
  refine (gronwall_zero_initial hT hK (by positivity) (hc n) (hzero n) (hd n) hn t ht).trans ?_
  have : Real.exp (K * t) ≤ Real.exp (K * T) := Real.exp_le_exp.2 (by nlinarith [ht.2])
  calc δ / Real.exp (K * T) * (Real.exp (K * t) - 1)
      ≤ δ / Real.exp (K * T) * Real.exp (K * T) := by gcongr; linarith
    _ = δ := div_mul_cancel₀ _ hE.ne'

/-- Coarse comparison on the final time interval, including the endpoint t=1. -/
theorem endpoint_lower_of_derivative_bound {φ D : ℝ → ℝ} {t M : ℝ}
    (ht : t < 1) (hc : ContinuousOn φ (Icc t 1))
    (hd : ∀ s ∈ Ioo t 1, HasDerivAt φ (D s) s)
    (hbound : ∀ s ∈ Ioo t 1, -M ≤ D s) :
    φ t - M * (1 - t) ≤ φ 1 := by
  have hder : ∀ s ∈ Ioo t 1, HasDerivAt (fun s => φ s + M * s) (D s + M) s := fun s hs => by
    convert! (hd s hs).add ((hasDerivAt_id s).const_mul M) using 1 <;> simp
  have hmono : MonotoneOn (fun s => φ s + M * s) (Icc t 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc t 1) (hc.add (by fun_prop)) ?_ ?_
    · rw [interior_Icc]
      exact fun s hs => (hder s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hder s hs).deriv]
      linarith [hbound s hs]
  have := hmono ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht.le
  simp only at this
  linarith

/-- Choose the cutoff before the approximating parameters and the volume threshold. -/
theorem eventual_lower_of_cutoff_estimates {p : ℕ → ℝ} {P M : ℝ}
    (hM : 0 ≤ M)
    (hcut : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ δ > 0,
      ∀ᶠ n in atTop, P - M * (1 - t) - δ ≤ p n) :
    ∀ ε > 0, ∀ᶠ n in atTop, P - ε ≤ p n := by
  intro ε hε
  set r := min (1 / 2) (ε / (2 * (M + 1)))
  have hr : 0 < r := by positivity
  have hr1 : r ≤ 1 / 2 := min_le_left _ _
  have hMr : M * r ≤ ε / 2 := by
    calc M * r ≤ (M + 1) * (ε / (2 * (M + 1))) := by
          gcongr
          · linarith
          · exact min_le_right _ _
      _ = ε / 2 := by field_simp
  filter_upwards [hcut (1 - r) ⟨by linarith, by linarith⟩ (ε / 2) (by positivity)] with n hn
  rw [sub_sub_cancel] at hn
  linarith

/-- Transfer bounded-field lower bounds through uniform truncation errors.
The approximation index is fixed before taking volume large. -/
theorem eventual_lower_of_uniform_approximation
    {p : ℕ → ℝ} {P : ℝ} {pApprox : ℕ → ℕ → ℝ} {PApprox e : ℕ → ℝ}
    (he : ∀ j, 0 ≤ e j) (hlim : Tendsto e atTop (𝓝 0))
    (hp : ∀ j n, |p n - pApprox j n| ≤ e j)
    (hP : ∀ j, |P - PApprox j| ≤ e j)
    (happrox : ∀ j, ∀ ε > 0, ∀ᶠ n in atTop, PApprox j - ε ≤ pApprox j n) :
    ∀ ε > 0, ∀ᶠ n in atTop, P - ε ≤ p n := by
  intro ε hε
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds (by positivity : 0 < ε / 3))).exists
  filter_upwards [happrox j (ε / 3) (by positivity)] with n hn
  linarith [(abs_le.1 (hp j n)).1, (abs_le.1 (hP j)).2]

end

end SpinGlass.Aristotle
