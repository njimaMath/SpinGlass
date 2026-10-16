import SpinGlass.Parisi.Analytic.Mass.Basic
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Derivatives of the logarithmic Laplace layer

Exponential envelopes justify differentiation under the integral and control
polynomially weighted moments. The mass layer is analytic at zero, with first
derivative equal to half the variance.

Search tag: `PARISI_LB_MASS`. These are single-layer estimates for the variable
integrated by the recursion, rather than assumptions on the external field law.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

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
  simp only [massTransform, hx', ite_false, ite_true, sub_zero]
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


end

end SpinGlass.Aristotle
