import SpinGlass.Parisi.Field.FieldContinuity
import SpinGlass.Parisi.Analytic.FieldTruncation

/-!
# Stability of the Parisi value under coupled site laws

A measurable field perturbation changes every admissible functional by
at most its first absolute moment cost, uniformly in the number of
levels. The variational infimum retains that same bound. This is the
law-level continuity needed for bounded-field approximation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace SpinGlass

/-- A coupled change of the site law has the same Lipschitz constant
as the deterministic field functional, before optimizing its parameters. -/
theorem abs_randomFieldParisiFunctional_sub_map_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {T : ℝ → ℝ} (hT : Measurable T) (hTi : Integrable T μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    |randomFieldParisiFunctional μh ξ ms qs - randomFieldParisiFunctional (μh.map T) ξ ms qs| ≤
      ∫ h, |h - T h| ∂μh := by
  haveI : IsProbabilityMeasure (μh.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  have hmap : Integrable id (μh.map T) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hT.aemeasurable).2 hTi
  have hLip : ∀ x y : ℝ, |parisiFunctional ξ x ms qs - parisiFunctional ξ y ms qs| ≤ |x - y| :=
    abs_parisiFunctional_sub_field_le ξ ms qs hpos hle
  have hf : Measurable (fun h => parisiFunctional ξ h ms qs) :=
    (lipschitzWith_toNNReal_of_abs_sub_le (L := 1) (by
      intro x y
      simpa only [one_mul] using hLip y x)).continuous.measurable
  rw [randomFieldParisiFunctional_eq_integral hμ ξ ms qs hpos hle,
    randomFieldParisiFunctional_eq_integral hmap ξ ms qs hpos hle,
    integral_map hT.aemeasurable hf.aestronglyMeasurable]
  simpa only [one_mul, id_eq] using Aristotle.abs_integral_lipschitz_coupling
    (L := 1) zero_le_one (by intro x y; simpa only [one_mul] using hLip x y) hμ hTi

/-- Optimizing the parameters preserves the site-law coupling cost.
Only the original Talagrand profile contract is required for boundedness below. -/
theorem abs_randomFieldParisiInf_sub_map_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {T : ℝ → ℝ} (hT : Measurable T) (hTi : Integrable T μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) :
    |randomFieldParisiInf μh ξ - randomFieldParisiInf (μh.map T) ξ| ≤
      ∫ h, |h - T h| ∂μh := by
  have hbelow := bddBelow_randomFieldParisiSet_of_talagrand μh hξ
  have hbelowMap := bddBelow_randomFieldParisiSet_of_talagrand (μh.map T) hξ
  let C := ∫ h, |h - T h| ∂μh
  have hleft : randomFieldParisiInf μh ξ - C ≤ randomFieldParisiInf (μh.map T) ξ := by
    apply le_csInf (randomFieldParisiSet_nonempty (μh.map T) ξ)
    rintro y ⟨k, ms, qs, hsm, hpos, hlt, hmono, hq0, hq1, rfl⟩
    have hi := randomFieldParisiInf_le μh ξ hbelow hsm hpos hlt hmono hq0 hq1
    have hb := (abs_le.1 (abs_randomFieldParisiFunctional_sub_map_le hμ hT hTi ξ ms qs
      hpos (fun i => (hlt i).le))).2
    dsimp only [C]
    linarith
  have hright : randomFieldParisiInf (μh.map T) ξ - C ≤ randomFieldParisiInf μh ξ := by
    apply le_csInf (randomFieldParisiSet_nonempty μh ξ)
    rintro y ⟨k, ms, qs, hsm, hpos, hlt, hmono, hq0, hq1, rfl⟩
    have hi := randomFieldParisiInf_le (μh.map T) ξ hbelowMap hsm hpos hlt hmono hq0 hq1
    have hb := (abs_le.1 (abs_randomFieldParisiFunctional_sub_map_le hμ hT hTi ξ ms qs
      hpos (fun i => (hlt i).le))).1
    dsimp only [C]
    linarith
  exact abs_le.2 ⟨by linarith, by linarith⟩

end SpinGlass
