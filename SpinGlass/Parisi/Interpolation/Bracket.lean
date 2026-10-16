import SpinGlass.Parisi.Coupled.CoupledOriginalPressure

/-!
# The affine interpolation bracket

The absorbed terminal Gaussian variance and the Parisi correction give
the exact slope of the original bracket on the interpolation interval.
-/

open MeasureTheory Set Filter Topology

namespace SpinGlass

variable {k : ℕ}

/-- The bracket is affine throughout the admissible time interval. -/
theorem parisiInterpolationBracket_eq_affine
    (μh : Measure ℝ) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) {t : ℝ} (ht : t ≤ 1) :
    parisiInterpolationBracket μh ξ ms qs t = randomFieldParisiFunctional μh ξ ms qs +
      (1 - t) * (parisiCorrection ξ ms qs - (parisiVar ξ qs (k + 1) : ℝ)) / 2 := by
  rw [parisiInterpolationBracket,
    parisiSplitBracket_eq_functional_add_correction μh ξ ms qs hm]
  simp only [parisiAuxTerminalVar, NNReal.coe_mul,
    Real.coe_toNNReal _ (sub_nonneg.2 ht)]
  ring

theorem parisiInterpolationBracket_sub_zero
    (μh : Measure ℝ) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) {t : ℝ} (ht : t ≤ 1) :
    parisiInterpolationBracket μh ξ ms qs t - parisiInterpolationBracket μh ξ ms qs 0 =
      t * ((parisiVar ξ qs (k + 1) : ℝ) - parisiCorrection ξ ms qs) / 2 := by
  rw [parisiInterpolationBracket_eq_affine μh ξ ms qs hm ht,
    parisiInterpolationBracket_eq_affine μh ξ ms qs hm zero_le_one]
  ring

theorem continuousOn_parisiInterpolationBracket
    (μh : Measure ℝ) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) :
    ContinuousOn (parisiInterpolationBracket μh ξ ms qs) (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.congr (f := fun t => randomFieldParisiFunctional μh ξ ms qs +
    (1 - t) * (parisiCorrection ξ ms qs - (parisiVar ξ qs (k + 1) : ℝ)) / 2)
    (by fun_prop)
  intro t ht
  exact parisiInterpolationBracket_eq_affine μh ξ ms qs hm ht.2

theorem hasDerivAt_parisiInterpolationBracket
    (μh : Measure ℝ) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (parisiInterpolationBracket μh ξ ms qs)
      (((parisiVar ξ qs (k + 1) : ℝ) - parisiCorrection ξ ms qs) / 2) t := by
  have hd := ((((hasDerivAt_id t).const_sub 1).mul_const
    (parisiCorrection ξ ms qs - (parisiVar ξ qs (k + 1) : ℝ))).div_const 2).const_add
      (randomFieldParisiFunctional μh ξ ms qs)
  have he : parisiInterpolationBracket μh ξ ms qs =ᶠ[𝓝 t]
      (fun s => randomFieldParisiFunctional μh ξ ms qs +
        (1 - s) * (parisiCorrection ξ ms qs - (parisiVar ξ qs (k + 1) : ℝ)) / 2) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact parisiInterpolationBracket_eq_affine μh ξ ms qs hm hs.2.le
  convert hd.congr_of_eventuallyEq he using 1 <;> first | rfl | ring

end SpinGlass
