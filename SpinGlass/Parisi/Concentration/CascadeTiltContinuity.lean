import SpinGlass.Parisi.Concentration.CascadeTiltGap
import Common.Mathlib.Probability.PointProcess.CascadeGibbs
import Common.Mathlib.Probability.PointProcess.CascadeLinear

/-!
# Stability of the actual constrained tilted mass

The cascade Gibbs identity (14.54) writes a tilted partition ratio as
an average of ratios of positive cascade sums. Multiplicative changes
of the two branch partition functions therefore control its logarithm
without a factor depending on the number of cascade levels.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlass

/-- A common multiplicative perturbation of the constrained numerator
and unconstrained denominator passes through the actual tilted average.
No positivity assumption on either constrained numerator is needed. -/
theorem cascadeTilt_div_le_mul_of_partition_bounds {T : Type*} [MeasurableSpace T]
    [Nonempty T] {k : ℕ}
    (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
    {G₁ G₂ A₁ A₂ : (Fin k → T) → ℝ≥0∞}
    (hG₁ : Measurable G₁) (hG₂ : Measurable G₂)
    (hA₁ : Measurable A₁) (hA₂ : Measurable A₂)
    (hG₁pos : ∀ zs, 0 < G₁ zs) (hG₂pos : ∀ zs, 0 < G₂ zs)
    (hfin₁ : (∫⁻ zs, G₁ zs ∂Measure.pi μs) ≠ ∞)
    (hfin₂ : (∫⁻ zs, G₂ zs ∂Measure.pi μs) ≠ ∞)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hA : ∀ zs, A₁ zs ≤ c * A₂ zs) (hG : ∀ zs, G₂ zs ≤ c * G₁ zs) :
    cascadeTilt k ms μs G₁ (fun zs => A₁ zs / G₁ zs) ≤
      (c * c) * cascadeTilt k ms μs G₂ (fun zs => A₂ zs / G₂ zs) := by
  have hRat : Measurable (fun ω : CascadeSpace T k => cascadeSum k A₂ ω / cascadeSum k G₂ ω) :=
    (measurable_cascadeSum k hA₂).div (measurable_cascadeSum k hG₂)
  rw [← lintegral_cascadeSum_div_cascadeSum k ms μs hA₁ hG₁ hG₁pos hfin₁ hsm hpos hlt,
    ← lintegral_cascadeSum_div_cascadeSum k ms μs hA₂ hG₂ hG₂pos hfin₂ hsm hpos hlt,
    ← lintegral_const_mul _ hRat]
  apply lintegral_mono
  intro ω
  have hAs := cascadeSum_mono k hA ω
  have hGs := cascadeSum_mono k hG ω
  rw [cascadeSum_const_mul k c hA₂] at hAs
  rw [cascadeSum_const_mul k c hG₁] at hGs
  calc
    _ = (c * cascadeSum k A₁ ω) / (c * cascadeSum k G₁ ω) :=
      (ENNReal.mul_div_mul_left _ _ hc0 hctop).symm
    _ ≤ (c * (c * cascadeSum k A₂ ω)) / cascadeSum k G₂ ω :=
      ENNReal.div_le_div (mul_le_mul' le_rfl hAs) hGs
    _ = _ := by simp only [div_eq_mul_inv, mul_assoc]

/-- The logarithm of a nonempty constrained tilted mass changes by
at most twice the branch perturbation. This is the deterministic bound
used for both Gaussian disorder and bounded site-field concentration. -/
theorem log_cascadeTilt_div_sub_le_of_exp_mul_le {T : Type*} [MeasurableSpace T]
    [Nonempty T] {k : ℕ}
    (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
    {G₁ G₂ A₁ A₂ : (Fin k → T) → ℝ≥0∞}
    (hG₁ : Measurable G₁) (hG₂ : Measurable G₂)
    (hA₁ : Measurable A₁) (hA₂ : Measurable A₂)
    (hG₁pos : ∀ zs, 0 < G₁ zs) (hG₂pos : ∀ zs, 0 < G₂ zs)
    (hA₁pos : ∀ zs, 0 < A₁ zs) (hA₂pos : ∀ zs, 0 < A₂ zs)
    (hG₁finite : ∀ zs, G₁ zs ≠ ∞) (hG₂finite : ∀ zs, G₂ zs ≠ ∞)
    (hA₁G₁ : ∀ zs, A₁ zs ≤ G₁ zs) (hA₂G₂ : ∀ zs, A₂ zs ≤ G₂ zs)
    (hfin₁ : (∫⁻ zs, G₁ zs ∂Measure.pi μs) ≠ ∞)
    (hfin₂ : (∫⁻ zs, G₂ zs ∂Measure.pi μs) ≠ ∞)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (C : ℝ) (hA : ∀ zs, A₁ zs ≤ ENNReal.ofReal (Real.exp C) * A₂ zs)
    (hG : ∀ zs, G₂ zs ≤ ENNReal.ofReal (Real.exp C) * G₁ zs) :
    Real.log (cascadeTilt k ms μs G₁ (fun zs => A₁ zs / G₁ zs)).toReal -
      Real.log (cascadeTilt k ms μs G₂ (fun zs => A₂ zs / G₂ zs)).toReal ≤ 2 * C := by
  have hle : ∀ i, ms i ≤ 1 := fun i => (hlt i).le
  have htop₁ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (cascadeTilt_div_le_one ms μs hG₁ hG₁pos hG₁finite hA₁G₁ hpos hle hfin₁)
  have htop₂ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (cascadeTilt_div_le_one ms μs hG₂ hG₂pos hG₂finite hA₂G₂ hpos hle hfin₂)
  have hpos₁ := cascadeTilt_pos_of_pos ms μs hG₁ (hA₁.div hG₁) hG₁pos
    (fun zs => ENNReal.div_pos (hA₁pos zs).ne' (hG₁finite zs)) hpos hle hfin₁
  have hpos₂ := cascadeTilt_pos_of_pos ms μs hG₂ (hA₂.div hG₂) hG₂pos
    (fun zs => ENNReal.div_pos (hA₂pos zs).ne' (hG₂finite zs)) hpos hle hfin₂
  have hb := cascadeTilt_div_le_mul_of_partition_bounds ms μs hG₁ hG₂ hA₁ hA₂
    hG₁pos hG₂pos hfin₁ hfin₂ hsm hpos hlt
    (ENNReal.ofReal_pos.2 (Real.exp_pos C)).ne' ENNReal.ofReal_ne_top hA hG
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      htop₂) hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos C).le] at hr
  have hl := Real.log_le_log (ENNReal.toReal_pos hpos₁.ne' htop₁) hr
  have hR : 0 < (cascadeTilt k ms μs G₂ (fun zs => A₂ zs / G₂ zs)).toReal :=
    ENNReal.toReal_pos hpos₂.ne' htop₂
  rw [Real.log_mul (mul_pos (Real.exp_pos C) (Real.exp_pos C)).ne' hR.ne',
    Real.log_mul (Real.exp_pos C).ne' (Real.exp_pos C).ne', Real.log_exp] at hl
  change Real.log (cascadeTilt k ms μs G₁ (fun zs => A₁ zs / G₁ zs)).toReal ≤
    C + C + Real.log (cascadeTilt k ms μs G₂ (fun zs => A₂ zs / G₂ zs)).toReal at hl
  linarith only [hl]

end SpinGlass
