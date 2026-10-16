import SpinGlass.Parisi.Analytic.BoundedDifferences
import SpinGlass.Parisi.Analytic.Concentration
import Mathlib.Probability.Moments.SubGaussian

/-!
# Combining conditional fluctuation bounds

Uniform section bounds and a bound for their means give an additive variance
proxy. Joint exponential integrability is proved from these same estimates.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace SpinGlass

/-- Combine centered section and mean bounds under a product probability law.
The exponential integrability required by Fubini follows from the bounds. -/
theorem hasSubgaussianMGF_prod_of_section_and_mean
    {Ω H : Type*} [MeasurableSpace Ω] [MeasurableSpace H]
    {μ : Measure Ω} {ν : Measure H} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F : Ω × H → ℝ} (hF : Measurable F) (hi : Integrable F (μ.prod ν))
    {A B : ℝ≥0}
    (hs : ∀ h, HasSubgaussianMGF (fun ω => F (ω, h) - ∫ w, F (w, h) ∂μ) A μ)
    (hm : HasSubgaussianMGF
      (fun h => (∫ ω, F (ω, h) ∂μ) - ∫ y, ∫ ω, F (ω, y) ∂μ ∂ν) B ν) :
    HasSubgaussianMGF (fun z => F z - ∫ w, F w ∂μ.prod ν) (A + B) (μ.prod ν) := by
  let m := fun h => ∫ ω, F (ω, h) ∂μ
  let E := ∫ h, m h ∂ν
  have hmean : (∫ z, F z ∂μ.prod ν) = E := integral_prod_symm F hi
  have hsplit (t : ℝ) (ω : Ω) (h : H) :
      Real.exp (t * (F (ω, h) - E)) =
        Real.exp (t * (m h - E)) * Real.exp (t * (F (ω, h) - m h)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsec (t : ℝ) (h : H) :
      Integrable (fun ω => Real.exp (t * (F (ω, h) - E))) μ := by
    simp_rw [hsplit]
    exact (hs h |>.integrable_exp_mul t).const_mul _
  have hbound (t : ℝ) (h : H) :
      (∫ ω, Real.exp (t * (F (ω, h) - E)) ∂μ) ≤
        Real.exp (t * (m h - E)) * Real.exp ((A : ℝ) * t ^ 2 / 2) := by
    simp_rw [hsplit]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hs h |>.mgf_le t) (Real.exp_nonneg _)
  have hjoint (t : ℝ) : Integrable (fun z => Real.exp (t * (F z - E))) (μ.prod ν) := by
    have hmeas : Measurable (fun z => Real.exp (t * (F z - E))) := by fun_prop
    apply (integrable_prod_iff' hmeas.aestronglyMeasurable).2
    refine ⟨.of_forall (hsec t), ?_⟩
    have hn : (fun h => ∫ ω, ‖Real.exp (t * (F (ω, h) - E))‖ ∂μ) =
        (fun h => ∫ ω, Real.exp (t * (F (ω, h) - E)) ∂μ) := by
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hn]
    refine ((hm.integrable_exp_mul t).mul_const (Real.exp ((A : ℝ) * t ^ 2 / 2))).mono'
      hmeas.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable ?_
    exact .of_forall fun h => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => Real.exp_nonneg _)]
      exact hbound t h
  constructor
  · intro t
    simpa only [hmean] using hjoint t
  · intro t
    simp only [mgf, hmean, NNReal.coe_add]
    exact Aristotle.mgf_prod_of_section_and_mean_bounds hi.integral_prod_right (hjoint t)
      (.of_forall fun h => hs h |>.mgf_le t) (hm.integrable_exp_mul t) (hm.mgf_le t)

/-- Uniform coordinate oscillations control the conditional mean, so the
section variance and the bounded-differences variance add. No moment
assumption is imposed on the coordinate laws. -/
theorem integrable_and_hasSubgaussianMGF_prod_of_section_and_bounded_differences
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (ν : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    {F : Ω × (Fin n → ℝ) → ℝ} (hF : Measurable F) {A : ℝ≥0}
    (hs : ∀ a, HasSubgaussianMGF (fun ω => F (ω, a) - ∫ w, F (w, a) ∂μ) A μ)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hosc : ∀ ω a i y, |F (ω, Function.update a i y) - F (ω, a)| ≤ c i) :
    Integrable F (μ.prod (Measure.pi ν)) ∧
      HasSubgaussianMGF (fun z => F z - ∫ w, F w ∂μ.prod (Measure.pi ν))
        (A + (∑ i, c i ^ 2 / 4).toNNReal) (μ.prod (Measure.pi ν)) := by
  classical
  have his (a : Fin n → ℝ) : Integrable (fun ω => F (ω, a)) μ := by
    apply ((hs a).integrable.add (integrable_const (∫ w, F (w, a) ∂μ))).congr
    exact .of_forall fun ω => sub_add_cancel _ _
  have hi : Integrable F (μ.prod (Measure.pi ν)) := by
    refine ((his 0).abs.comp_fst (Measure.pi ν) |>.add (integrable_const (∑ i, c i))).mono'
      hF.aestronglyMeasurable ?_
    exact .of_forall fun z => by
      change |F z| ≤ |F (z.1, 0)| + ∑ i, c i
      exact Aristotle.abs_le_of_bounded_differences
        (F := fun a => F (z.1, a)) (c := c) (hosc z.1) z.2
  let m := fun a => ∫ ω, F (ω, a) ∂μ
  have hm : Measurable m := hF.stronglyMeasurable.integral_prod_left'.measurable
  have hmosc (a : Fin n → ℝ) (i : Fin n) (y : ℝ) :
      |m (Function.update a i y) - m a| ≤ c i := by
    dsimp only [m]
    rw [← integral_sub (his _) (his _)]
    calc |∫ ω, (F (ω, Function.update a i y) - F (ω, a)) ∂μ|
        ≤ ∫ ω, |F (ω, Function.update a i y) - F (ω, a)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ _ω, c i ∂μ := integral_mono ((his _).sub (his _) |>.abs)
        (integrable_const _) (fun ω => hosc ω a i y)
      _ = c i := by simp
  have hmi : Integrable m (Measure.pi ν) := hi.integral_prod_right
  have hmgf : HasSubgaussianMGF (fun a => m a - ∫ b, m b ∂Measure.pi ν)
      (∑ i, c i ^ 2 / 4).toNNReal (Measure.pi ν) := by
    constructor
    · intro t
      exact (Aristotle.bounded_differences_mgf ν hm hmi c hc hmosc t).1
    · intro t
      have hb := (Aristotle.bounded_differences_mgf ν hm hmi c hc hmosc t).2
      have he : t ^ 2 * (∑ i, c i ^ 2) / 8 = (∑ i, c i ^ 2 / 4) * t ^ 2 / 2 := by
        rw [← Finset.sum_div]
        ring
      have hnonneg : 0 ≤ ∑ i, c i ^ 2 / 4 := Finset.sum_nonneg fun i _ => by positivity
      simpa only [mgf, Real.coe_toNNReal _ hnonneg, he] using hb
  exact ⟨hi, hasSubgaussianMGF_prod_of_section_and_mean hF hi hs hmgf⟩

end SpinGlass
