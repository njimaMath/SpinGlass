import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Concentration analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

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

end

end SpinGlass.Aristotle
