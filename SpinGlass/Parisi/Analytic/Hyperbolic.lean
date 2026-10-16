import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Hyperbolic analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

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

end

end SpinGlass.Aristotle
