import SpinGlass.Parisi.Analytic.Heat.Basic

/-!
# Gaussian Calculus analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

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

theorem exp_mul_abs_add_le {c : ℝ} (hc : 0 ≤ c) (x z : ℝ) :
    Real.exp (c * |x + z|) ≤ Real.exp (c * |x|) * Real.exp (c * |z|) := by
  simpa using Heat.exp_abs_affine_le hc x 1 z

/-- Differentiation of a Gaussian smoothing under the integral sign. -/
theorem hasDerivAt_integral_gaussian_add {v : ℝ≥0} {g g' : ℝ → ℝ}
    (hg : ∀ y, HasDerivAt g (g' y) y) (hg' : Continuous g') {C c : ℝ} (hc : 0 ≤ c)
    (hbg : ∀ y, |g y| ≤ C * Real.exp (c * |y|))
    (hbg' : ∀ y, |g' y| ≤ C * Real.exp (c * |y|)) (x : ℝ) :
    HasDerivAt (fun y => ∫ z, g (y + z) ∂gaussianReal 0 v)
      (∫ z, g' (x + z) ∂gaussianReal 0 v) x := by
  have h := Heat.hasDerivAt_heat (v : ℝ) hg hg' hbg hbg' x
  unfold Heat.heat at h
  simpa only [Real.toNNReal_coe] using h


end

end SpinGlass.Aristotle
