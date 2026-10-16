import SpinGlass.Parisi.Interpolation.PressureDifference
import SpinGlass.Parisi.Interpolation.BoundAverage
import SpinGlass.Parisi.Interpolation.RemainderTimeAverage
import SpinGlass.Parisi.Interpolation.InitialEndpoint

/-!
# The exact physical interpolation remainder identity

The finite-tree Gaussian formula passes to the full cascade, then to
the weight and i.i.d. field averages. The original pressure gap is the
integral of the concrete remainder controlled by localization.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

variable (N k : ℕ)

/-- Exact averaged interpolation on every closed subinterval, under
only a first moment of the original external-field probability law. -/
theorem parisiInterpolationPressure_sub_eq_integral_remainder
    (hN : 0 < N) {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    parisiInterpolationPressure N μh ξ ms qs b - parisiInterpolationPressure N μh ξ ms qs a =
      (b - a) * (((parisiVar ξ qs (k + 1) : ℝ) - parisiCorrection ξ ms qs) / 2) -
        ∫ t in a..b, parisiGuerraRemainder N μh ξ ms qs t := by
  let P := (externalFieldVecLaw N μh).prod (cascadeWeightsLaw k ms)
  have hiB : Integrable (fun q : (Fin N → ℝ) × CascadeWeights k =>
      ∫ t in a..b, guerraBound N k ξ qs q.1 q.2 t) P := by
    simpa only [intervalIntegral.integral_of_le hab] using
      (integrable_guerraBound_prod_time N k μh ξ ms qs a b).integral_prod_left
  have hiR : Integrable (fun q : (Fin N → ℝ) × CascadeWeights k =>
      ∫ t in a..b, parisiFixedWeightRemainder N k ξ qs q.1 q.2 t) P := by
    simpa only [intervalIntegral.integral_of_le hab] using
      (integrable_parisiFixedWeightRemainder_prod_time N k μh ξ ms qs a b).integral_prod_left
  rw [parisiInterpolationPressure_sub_eq_average N k hN hμ hξ hS ms hm qs hq ha hab hb]
  have he : (∫ q : (Fin N → ℝ) × CascadeWeights k,
      parisiFixedWeightPressure N k ξ qs q.1 q.2 b - parisiFixedWeightPressure N k ξ qs q.1 q.2 a
      ∂P) = ∫ q, (∫ t in a..b, guerraBound N k ξ qs q.1 q.2 t) -
        (∫ t in a..b, parisiFixedWeightRemainder N k ξ qs q.1 q.2 t) ∂P := by
    apply integral_congr_ae
    have hw := (measurePreserving_snd (μ := externalFieldVecLaw N μh) (ν := cascadeWeightsLaw k ms))
      |>.quasiMeasurePreserving.ae (ae_weightSum_ne_zero_ne_top k ms hm.1 hm.2.1 hm.2.2)
    filter_upwards [hw] with q hw'
    rw [parisiFixedWeightPressure_sub_eq_integral N k hN hξ hS qs hq q.1 q.2
      hw'.1 hw'.2 ha hab hb]
    exact intervalIntegral.integral_sub (intervalIntegrable_guerraBound N k ξ qs q.1 q.2 a b)
      (intervalIntegrable_parisiFixedWeightRemainder N k hξ qs hq q.1 q.2 hw'.1 hw'.2 a b)
  rw [he, integral_sub hiB hiR, integral_intervalIntegral_guerraBound_prod_eq N k μh ξ ms hm qs hab,
    integral_intervalIntegral_parisiFixedWeightRemainder_eq N k μh ξ ms qs hm hS ha hab hb,
    averagedGuerraBound_eq_bracket_slope k hξ ms qs hq, mul_comm]

/-- The actual pressure gap in Talagrand's interpolation is the
integral of the physical overlap/meeting remainder, including `t = 1`. -/
theorem parisiInterpolationBracket_sub_pressure_eq_integral
    (hN : 0 < N) {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiInterpolationBracket μh ξ ms qs t - parisiInterpolationPressure N μh ξ ms qs t =
      ∫ s in (0 : ℝ)..t, parisiGuerraRemainder N μh ξ ms qs s := by
  have hp := parisiInterpolationPressure_sub_eq_integral_remainder N k hN hμ hξ hS ms hm
    qs hq (a := 0) le_rfl ht.1 ht.2
  rw [parisiInterpolationPressure_zero hN hμ ξ ms qs hm hS] at hp
  have hb := parisiInterpolationBracket_sub_zero μh ξ ms qs hm ht.2
  simp only [sub_zero] at hp
  linarith only [hp, hb]

/-- Nonnegativity of the concrete remainder proves the sign of the
pressure gap, so its positive part in localization can be removed. -/
theorem parisiInterpolationPressure_le_bracket
    (hN : 0 < N) {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiInterpolationPressure N μh ξ ms qs t ≤ parisiInterpolationBracket μh ξ ms qs t := by
  apply sub_nonneg.1
  rw [parisiInterpolationBracket_sub_pressure_eq_integral N k hN hμ hξ hS ms hm qs hq ht]
  exact intervalIntegral.integral_nonneg ht.1 (fun s _ =>
    parisiGuerraRemainder_nonneg μh hξ ms qs hm hq s)

end

end SpinGlass
