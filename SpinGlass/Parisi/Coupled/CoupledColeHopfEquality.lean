import SpinGlass.Parisi.Variational.ParisiColeHopfRearrangement

/-!
# Equality propagation through nondegenerate Gaussian layers

An ordered terminal comparison which has equal Cole-Hopf values
must be equal at every real argument when the variance is nonzero.
This is the one-variable input to the equality analysis of (14.378).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

theorem coleHopf_eq_implies_eq_of_lipschitz {A B : ℝ → ℝ} {L₁ L₂ : ℝ}
    (hA : ∀ x y, |A y - A x| ≤ L₁ * |y - x|)
    (hB : ∀ x y, |B y - B x| ≤ L₂ * |y - x|) (hAB : ∀ x, A x ≤ B x)
    {m : ℝ} (hm : 0 ≤ m) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ)
    (he : coleHopf m v A x = coleHopf m v B x) : A = B := by
  have hAg := HasLinearGrowth.of_lipschitz hA
  have hBg := HasLinearGrowth.of_lipschitz hB
  have hAc := (lipschitzWith_toNNReal_of_abs_sub_le hA).continuous
  have hBc := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous
  have hae : (fun z => A (x + z)) =ᵐ[gaussianReal 0 v] fun z => B (x + z) := by
    rcases eq_or_lt_of_le hm with hzero | hpos
    · subst m
      rw [coleHopf_zero, coleHopf_zero] at he
      exact (integral_eq_iff_of_ae_le
        ((hAg.comp_add_const x).toHasExpGrowth.integrable_gaussianReal
          (hAc.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable)
        ((hBg.comp_add_const x).toHasExpGrowth.integrable_gaussianReal
          (hBc.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable)
        (.of_forall fun z => hAB _)).1 he
    · have hE := congrArg (fun a => Real.exp (m * a)) he
      rw [exp_mul_coleHopf hAg hAc.measurable hpos.ne',
        exp_mul_coleHopf hBg hBc.measurable hpos.ne'] at hE
      have hlog := (integral_eq_iff_of_ae_le
        (integrable_exp_mul_comp_add hAg hAc.measurable m v x)
        (integrable_exp_mul_comp_add hBg hBc.measurable m v x)
        (.of_forall fun z => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hAB _) hpos.le))).1 hE
      filter_upwards [hlog] with z hz
      exact mul_left_cancel₀ hpos.ne' (Real.exp_injective hz)
  have hall := Measure.eq_of_ae_eq ((gaussianReal_absolutelyContinuous' 0 hv).ae_eq hae)
    (hAc.comp (continuous_const.add continuous_id)) (hBc.comp (continuous_const.add continuous_id))
  funext z
  simpa only [show x + (z - x) = z by ring] using congrFun hall (z - x)

/-- A strict terminal comparison at one point becomes strict
at every field after a nonzero Gaussian layer, including mass zero. -/
theorem coleHopf_lt_of_exists_lt {A B : ℝ → ℝ} {L₁ L₂ : ℝ}
    (hA : ∀ x y, |A y - A x| ≤ L₁ * |y - x|)
    (hB : ∀ x y, |B y - B x| ≤ L₂ * |y - x|) (hAB : ∀ x, A x ≤ B x)
    (hstrict : ∃ x, A x < B x) {m : ℝ} (hm : 0 ≤ m) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    coleHopf m v A x < coleHopf m v B x := by
  apply lt_of_le_of_ne (coleHopf_mono (HasLinearGrowth.of_lipschitz hA)
    (lipschitzWith_toNNReal_of_abs_sub_le hA).continuous.measurable
    (HasLinearGrowth.of_lipschitz hB) (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
    hAB m v x)
  intro he
  have hall := coleHopf_eq_implies_eq_of_lipschitz hA hB hAB hm hv x he
  obtain ⟨z, hz⟩ := hstrict
  exact hz.ne (congrFun hall z)

end SpinGlass
