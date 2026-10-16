import Common.Mathlib.Probability.PointProcess.CascadePair

/-!
# Bounds for constrained cascade pair averages

A nonnegative branch numerator bounded by the product partition gives
a normalized prefix average between zero and one on every tree sample.
This supplies the finiteness needed to subtract successive averages.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

universe u

variable {T : Type u} [MeasurableSpace T]

theorem cascadePairSum_mono (k : ℕ) :
    ∀ {U V : (Fin k → T × T) → ℝ≥0∞}, (∀ x, U x ≤ V x) →
      ∀ ω₁ ω₂, cascadePairSum k U ω₁ ω₂ ≤ cascadePairSum k V ω₁ ω₂ := by
  induction k with
  | zero => intro U V hUV ω₁ ω₂; exact hUV _
  | succ k ih =>
    intro U V hUV ω₁ ω₂
    simp only [cascadePairSum_succ]
    apply lintegral_mono
    intro p
    apply lintegral_mono
    intro q
    exact mul_le_mul' le_rfl (ih (fun x => hUV _) _ _)

theorem cascadeSqPair_mono (k : ℕ) :
    ∀ r : ℕ, ∀ {U V : (Fin k → T × T) → ℝ≥0∞}, (∀ x, U x ≤ V x) →
      ∀ ω, cascadeSqPair k r U ω ≤ cascadeSqPair k r V ω := by
  induction k with
  | zero =>
    intro r U V hUV ω
    cases r with
    | zero => exact hUV _
    | succ r => exact le_rfl
  | succ k ih =>
    intro r U V hUV ω
    cases r with
    | zero => exact cascadePairSum_mono _ hUV ω ω
    | succ r =>
      simp only [cascadeSqPair_succ]
      exact lintegral_mono fun p => mul_le_mul' le_rfl (ih r (fun x => hUV _) _)

theorem measurable_cascadeSqPair (k r : ℕ)
    {U : (Fin k → T × T) → ℝ≥0∞} (hU : Measurable U) :
    Measurable (cascadeSqPair k r U) := by
  have hh := measurable_cascadeSqPair_prod k r (α := PUnit.{u + 1})
    (U := fun _ => U) (hU.comp measurable_snd)
  exact hh.comp (measurable_const.prodMk measurable_id :
    Measurable fun ω : CascadeSpace T k => (PUnit.unit, ω))

/-- The constrained normalized prefix average is bounded without any
exception for zero or infinite partition values. -/
theorem cascadeSqPair_mul_inv_sq_le_one (k r : ℕ)
    {G : (Fin k → T) → ℝ≥0∞} {U : (Fin k → T × T) → ℝ≥0∞}
    (hG : Measurable G)
    (hUG : ∀ x, U x ≤ G (fun p => (x p).1) * G (fun p => (x p).2))
    (ω : CascadeSpace T k) :
    cascadeSqPair k r U ω * (cascadeSum k G ω)⁻¹ ^ 2 ≤ 1 := by
  calc
    _ ≤ cascadeSqPair k r
        (fun x => G (fun p => (x p).1) * G (fun p => (x p).2)) ω *
        (cascadeSum k G ω)⁻¹ ^ 2 := mul_le_mul' (cascadeSqPair_mono k r hUG ω) le_rfl
    _ = cascadeSq k r G ω * (cascadeSum k G ω)⁻¹ ^ 2 := by
      rw [cascadeSqPair_prod k r hG]
    _ ≤ 1 := cascadeSq_mul_inv_sq_le_one k r hG ω

end ProbabilityTheory
