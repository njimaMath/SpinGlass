import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# IntegralDifferentiation analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open MeasureTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

/-- Differentiate under the external-field integral on an admissible closed interval.
Only domination of the derivative and integrability at one base point are needed. -/
theorem hasDerivWithinAt_integral_Icc {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F D : ℝ → Ω → ℝ} {a b t : ℝ} {g : Ω → ℝ}
    (hab : a < b) (ht : t ∈ Icc a b)
    (hF : ∀ s ∈ Icc a b, AEStronglyMeasurable (F s) μ)
    (hD : AEStronglyMeasurable (D t) μ)
    (hbase : Integrable (F a) μ) (hg : Integrable g μ)
    (hderiv : ∀ᵐ ω ∂μ, ∀ s ∈ Icc a b,
      HasDerivWithinAt (fun u => F u ω) (D s ω) (Icc a b) s)
    (hbound : ∀ᵐ ω ∂μ, ∀ s ∈ Icc a b, |D s ω| ≤ g ω) :
    HasDerivWithinAt (fun s => ∫ ω, F s ω ∂μ) (∫ ω, D t ω ∂μ) (Icc a b) t := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hlip : ∀ᵐ ω ∂μ, ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, |F u ω - F v ω| ≤ g ω * |u - v| := by
    filter_upwards [hderiv, hbound] with ω h1 h2 u hu v hv
    simpa [Real.norm_eq_abs] using (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u => F u ω) (C := g ω) h1 (fun s hs => by simpa using h2 s hs) hv hu
  have hg0 : ∀ᵐ ω ∂μ, 0 ≤ g ω := hbound.mono fun ω h => (abs_nonneg _).trans (h a ha)
  have hint : ∀ u ∈ Icc a b, Integrable (F u) μ := by
    intro u hu
    refine (hbase.abs.add (hg.mul_const (b - a))).mono' (hF u hu) ?_
    filter_upwards [hlip, hg0] with ω hω hg0
    have h1 := hω u hu a ha
    have hua : |u - a| ≤ b - a := by rw [abs_of_nonneg (by linarith [hu.1])]; linarith [hu.2]
    rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (F u ω) (F a ω)
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left hua hg0]
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hslope : ∀ u ∈ Icc a b, slope (fun s => ∫ ω, F s ω ∂μ) t u =
      ∫ ω, (u - t)⁻¹ * (F u ω - F t ω) ∂μ := by
    intro u hu
    rw [slope_def_field, integral_const_mul, integral_sub (hint u hu) (hint t ht), div_eq_inv_mul]
  have hev : ∀ᶠ u in 𝓝[Icc a b \ {t}] t, u ∈ Icc a b :=
    eventually_nhdsWithin_of_forall fun u hu => hu.1
  refine Tendsto.congr' (hev.mono fun u hu => (hslope u hu).symm) ?_
  refine tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hg ?_
  · filter_upwards [hev] with u hu
    exact ((hF u hu).sub (hF t ht)).const_mul _
  · filter_upwards [hev, self_mem_nhdsWithin] with u hu hut
    filter_upwards [hlip] with ω hω
    have hne : u - t ≠ 0 := sub_ne_zero.2 hut.2
    rw [Real.norm_eq_abs, abs_mul, abs_inv, inv_mul_le_iff₀ (abs_pos.2 hne), mul_comm]
    exact hω u hu t ht
  · filter_upwards [hderiv] with ω hω
    have := (hasDerivWithinAt_iff_tendsto_slope.1 (hω t ht))
    refine this.congr fun u => ?_
    rw [slope_def_field, div_eq_inv_mul]

end

end SpinGlass.Aristotle
