import SpinGlass.Parisi.RandomExternalField

/-!
# Reduction of a zero-second-moment site law

This local lemma supplies the measure identification in the zero-field branch
of the Chapter 14 lower bound. Integrability is necessary: the Bochner integral
alone can vanish for a nonintegrable function.
-/

open MeasureTheory

namespace SpinGlass

/-- A probability law with finite, zero second moment is the constant zero law. -/
theorem externalFieldLaw_eq_dirac_zero_of_second_moment_eq_zero
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h ^ 2) μh)
    (hzero : ∫ h, h ^ 2 ∂μh = 0) : μh = Measure.dirac 0 := by
  have hsq : (fun h : ℝ => h ^ 2) =ᵐ[μh] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun h => sq_nonneg h) hμh).1 hzero
  have hid : (fun h : ℝ => h) =ᵐ[μh] (fun _ => (0 : ℝ)) := by
    filter_upwards [hsq] with h hh
    exact (sq_eq_zero_iff).1 hh
  calc
    μh = μh.map (fun h : ℝ => h) := Measure.map_id'.symm
    _ = μh.map (fun _ => (0 : ℝ)) := Measure.map_congr hid
    _ = Measure.dirac 0 := by simp [Measure.map_const]

end SpinGlass
