import SpinGlass.Parisi.Interpolation.GapBounds
import SpinGlass.Parisi.Interpolation.IntegralGronwall

/-!
# Gronwall comparison for the physical interpolation

The exact remainder identity turns localization into a continuous
integral inequality for the original pressure gap.
-/

open MeasureTheory ProbabilityTheory Set

namespace SpinGlass

variable {N k : ℕ}

theorem parisiInterpolationGap_le_exp
    (hN : 0 < N) {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    {T C ε : ℝ} (hT : T ∈ Icc (0 : ℝ) 1) (hC : 0 < C) (hε : 0 ≤ ε)
    (hloc : ∀ t ∈ Icc (0 : ℝ) T, parisiGuerraRemainder N μh ξ ms qs t ≤
      C * (parisiInterpolationBracket μh ξ ms qs t -
        parisiInterpolationPressure N μh ξ ms qs t + ε)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      parisiInterpolationBracket μh ξ ms qs t - parisiInterpolationPressure N μh ξ ms qs t ≤
        ε * Real.exp (C * t) := by
  let g := fun t => parisiInterpolationBracket μh ξ ms qs t -
    parisiInterpolationPressure N μh ξ ms qs t
  have hg : ContinuousOn g (Icc (0 : ℝ) T) :=
    (continuousOn_parisiInterpolationGap hN hμ hξ hS ms hm qs hq).mono
      (fun t ht => ⟨ht.1, ht.2.trans hT.2⟩)
  have hg0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ g t :=
    sub_nonneg.2 (parisiInterpolationPressure_le_bracket N k hN hμ hξ hS ms hm qs hq
      ⟨ht.1, ht.2.trans hT.2⟩)
  apply le_exp_mul_of_integral_le hT.1 hC hε hg hg0
  intro t ht
  have hgt : ContinuousOn (fun s => C * (g s + ε)) (Icc (0 : ℝ) t) :=
    (hg.add continuousOn_const).const_mul C |>.mono (fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)
  have hi := intervalIntegral.integral_mono_on ht.1
    (intervalIntegrable_parisiGuerraRemainder N k μh ξ ms qs hm hS le_rfl ht.1 (ht.2.trans hT.2))
    (hgt.intervalIntegrable_of_Icc ht.1) (fun s hs => hloc s ⟨hs.1, hs.2.trans ht.2⟩)
  rw [intervalIntegral.integral_const_mul] at hi
  exact (parisiInterpolationBracket_sub_pressure_eq_integral N k hN hμ hξ hS ms hm qs hq
    ⟨ht.1, ht.2.trans hT.2⟩).le.trans hi

end SpinGlass
