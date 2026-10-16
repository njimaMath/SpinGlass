import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A continuous integral form of the scalar Gronwall estimate

The input is an integral inequality. Differentiability is proved only
for its continuous majorant, so the original remainder need not be
continuous or have a pointwise derivative.
-/

open MeasureTheory Set
open scoped Topology

namespace SpinGlass

theorem le_exp_mul_of_integral_le
    {g : ℝ → ℝ} {T C ε : ℝ} (hT : 0 ≤ T) (hC : 0 < C) (hε : 0 ≤ ε)
    (hg : ContinuousOn g (Icc 0 T)) (hg0 : ∀ t ∈ Icc 0 T, 0 ≤ g t)
    (hbound : ∀ t ∈ Icc 0 T, g t ≤ C * ∫ s in (0 : ℝ)..t, g s + ε) :
    ∀ t ∈ Icc 0 T, g t ≤ ε * Real.exp (C * t) := by
  let e := fun t => g (max 0 (min T t)) + ε
  have he : Continuous e := by
    apply Continuous.add_const
    apply hg.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
    intro t
    exact ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩
  have heq (t : ℝ) (ht : t ∈ Icc 0 T) : e t = g t + ε := by
    dsimp only [e]
    rw [min_eq_right ht.2, max_eq_right ht.1]
  let H := fun t => C * ∫ s in (0 : ℝ)..t, e s
  have hH (t : ℝ) : HasDerivAt H (C * e t) t :=
    (intervalIntegral.integral_hasDerivAt_right (he.intervalIntegrable 0 t)
      he.stronglyMeasurable.stronglyMeasurableAtFilter he.continuousAt).const_mul C
  have hmajor (t : ℝ) (ht : t ∈ Icc 0 T) : g t ≤ H t := by
    have hi : (∫ s in (0 : ℝ)..t, e s) = ∫ s in (0 : ℝ)..t, g s + ε := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      exact heq s ⟨hs.1, hs.2.trans ht.2⟩
    dsimp only [H]
    rw [hi]
    exact hbound t ht
  have hcont : ContinuousOn H (Icc (0 : ℝ) T) :=
    (continuous_iff_continuousAt.2 fun t => (hH t).continuousAt).continuousOn
  have hder : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt H (C * e t) (Ici t) t :=
    fun t _ => (hH t).hasDerivWithinAt
  have hz : ‖H 0‖ ≤ 0 := by simp [H]
  have hb : ∀ t ∈ Ico (0 : ℝ) T, ‖C * e t‖ ≤ C * ‖H t‖ + C * ε := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    rw [heq t ht', Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC.le (add_nonneg (hg0 t ht') hε))]
    have hh := mul_le_mul_of_nonneg_left ((hmajor t ht').trans (le_abs_self _)) hC.le
    change C * (g t + ε) ≤ C * |H t| + C * ε
    linarith only [hh]
  intro t ht
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hcont hder hz hb t ht
  rw [sub_zero, gronwallBound_of_K_ne_0 hC.ne'] at hh
  simp only [zero_mul, zero_add, mul_div_cancel_left₀ ε hC.ne'] at hh
  exact (hmajor t ht).trans ((le_abs_self _).trans (hh.trans (by nlinarith only [hε])))

end SpinGlass
