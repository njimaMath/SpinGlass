import SpinGlass.Parisi.Interpolation.IntegralIdentity

/-!
# Continuity and endpoint control of the physical pressure gap
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace SpinGlass

variable {N k : ℕ}

theorem continuousOn_parisiInterpolationGap
    (hN : 0 < N) {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) :
    ContinuousOn (fun t => parisiInterpolationBracket μh ξ ms qs t -
      parisiInterpolationPressure N μh ξ ms qs t) (Icc (0 : ℝ) 1) := by
  have hi := intervalIntegrable_parisiGuerraRemainder N k μh ξ ms qs hm hS
    (a := 0) (b := 1) le_rfl zero_le_one le_rfl
  have hc := intervalIntegral.continuousOn_primitive_interval' hi (a := 0) left_mem_uIcc
  rw [uIcc_of_le zero_le_one] at hc
  apply hc.congr
  intro t ht
  exact parisiInterpolationBracket_sub_pressure_eq_integral N k hN hμ hξ hS ms hm qs hq ht

theorem parisiInterpolationGap_sub_eq_integral
    (hN : 0 < N) {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (parisiInterpolationBracket μh ξ ms qs b - parisiInterpolationPressure N μh ξ ms qs b) -
      (parisiInterpolationBracket μh ξ ms qs a - parisiInterpolationPressure N μh ξ ms qs a) =
        ∫ t in a..b, parisiGuerraRemainder N μh ξ ms qs t := by
  have hp := parisiInterpolationPressure_sub_eq_integral_remainder N k hN hμ hξ hS ms hm
    qs hq ha hab hb
  have ha' := parisiInterpolationBracket_sub_zero μh ξ ms qs hm (hab.trans hb)
  have hb' := parisiInterpolationBracket_sub_zero μh ξ ms qs hm hb
  nlinarith only [hp, ha', hb']

/-- Uniform control of the last part of the interpolation, independent
of the selected MIN parameters and the external-field law. -/
theorem parisiInterpolationGap_sub_le_curvature
    (hN : 0 < N) {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (parisiInterpolationBracket μh ξ ms qs b - parisiInterpolationPressure N μh ξ ms qs b) -
      (parisiInterpolationBracket μh ξ ms qs a - parisiInterpolationPressure N μh ξ ms qs a) ≤
        deriv (deriv ξ) 1 * (b - a) := by
  rw [parisiInterpolationGap_sub_eq_integral hN hμ hξ hS ms hm qs hq ha hab hb]
  have hh := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_parisiGuerraRemainder N k μh ξ ms qs hm hS ha hab hb)
    (intervalIntegrable_const (c := deriv (deriv ξ) 1))
    (fun t _ => parisiGuerraRemainder_le_curvature μh hξ ms qs hm hq t)
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hh

end SpinGlass
