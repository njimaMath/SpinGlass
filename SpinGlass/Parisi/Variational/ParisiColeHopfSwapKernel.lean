import SpinGlass.Parisi.Variational.ParisiExponentialMix

/-!
# The concrete normalized kernel for Cole-Hopf rearrangement

The dual density is the actual Gaussian tilt of the first composed
operator. Its comparison with each shifted suffix uses normalized
exponential convexity, and equality identifies those actual tilts.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

noncomputable def coleHopfSwapKernel (m n : ℝ) (v w : ℝ≥0) (A : ℝ → ℝ) (x : ℝ)
    (yz : ℝ × ℝ) : ℝ :=
  Real.exp (n * A (x + yz.1 + yz.2) + (m - n) *
    (coleHopf n w A (x + yz.2) - coleHopf m v (coleHopf n w A) x))

noncomputable def coleHopfSwapFirstLogTilt (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  m * (A (x + y + z) - coleHopf m v A (x + y))

noncomputable def coleHopfSwapSecondLogTilt (m n : ℝ) (v w : ℝ≥0) (A : ℝ → ℝ) (x z : ℝ) : ℝ :=
  m * (coleHopf n w A (x + z) - coleHopf m v (coleHopf n w A) x)

theorem exp_coleHopfSwap_mix_eq {m n : ℝ} (hm : m ≠ 0) (v w : ℝ≥0)
    (A : ℝ → ℝ) (x y z : ℝ) :
    Real.exp ((n / m) * coleHopfSwapFirstLogTilt m v A x y z +
      (1 - n / m) * coleHopfSwapSecondLogTilt m n v w A x z) =
      coleHopfSwapKernel m n v w A x (y, z) / Real.exp (n * coleHopf m v A (x + y)) := by
  unfold coleHopfSwapFirstLogTilt coleHopfSwapSecondLogTilt coleHopfSwapKernel
  rw [← Real.exp_sub]
  congr 1
  field_simp
  ring

/-- Every actual one-dimensional kernel section is integrable.
No exponential moment assumption is made on an external site field. -/
theorem integrable_coleHopfSwapKernel_section {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) (m n : ℝ) (v w : ℝ≥0) (x y : ℝ) :
    Integrable (fun z => coleHopfSwapKernel m n v w A x (y, z)) (gaussianReal 0 v) := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hAg := HasLinearGrowth.of_lipschitz hL
  have hB := abs_coleHopf_sub_le_of_lipschitz n hAm hL w
  have hBg := HasLinearGrowth.of_lipschitz hB
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
  have hG := ((hAg.comp_add_const (x + y)).exp_mul n).mul
    (((hBg.comp_add_const x).add_const (-coleHopf m v (coleHopf n w A) x)).exp_mul (m - n))
  have hi := hG.integrable_gaussianReal (μ := 0) (v := v)
    ((Real.measurable_exp.comp (measurable_const.mul
      (hAm.comp (measurable_const.add measurable_id)))).mul
      (Real.measurable_exp.comp (measurable_const.mul
        ((hBm.comp (measurable_const.add measurable_id)).add measurable_const)))).aestronglyMeasurable
  apply hi.congr (.of_forall fun z => ?_)
  unfold coleHopfSwapKernel
  dsimp only
  rw [← Real.exp_add]
  congr 1

/-- The normalized dual bound at each actual shifted field, for
positive ordered masses. This is the concrete Holder comparison in (14.385). -/
theorem integral_coleHopfSwapKernel_le_of_pos {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m n : ℝ} (hn : 0 < n) (hnm : n ≤ m)
    (v w : ℝ≥0) (x y : ℝ) :
    (∫ z, coleHopfSwapKernel m n v w A x (y, z) ∂gaussianReal 0 v) ≤
      Real.exp (n * coleHopf m v A (x + y)) := by
  have hm : 0 < m := hn.trans_le hnm
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hAg := HasLinearGrowth.of_lipschitz hL
  have hB := abs_coleHopf_sub_le_of_lipschitz n hAm hL w
  have hBg := HasLinearGrowth.of_lipschitz hB
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
  have hf : Measurable (coleHopfSwapFirstLogTilt m v A x y) :=
    measurable_const.mul ((hAm.comp (measurable_const.add measurable_id)).sub measurable_const)
  have hg : Measurable (coleHopfSwapSecondLogTilt m n v w A x) :=
    measurable_const.mul ((hBm.comp (measurable_const.add measurable_id)).sub measurable_const)
  have hmix := integral_exp_convex_mix_le_one hf hg
    (integrable_coleHopfQ hAg hAm hm.ne' v (x + y))
    (integrable_coleHopfQ hBg hBm hm.ne' v x)
    (integral_coleHopfQ hAg hAm hm.ne' v (x + y))
    (integral_coleHopfQ hBg hBm hm.ne' v x)
    (a := n / m) ⟨div_nonneg hn.le hm.le, (div_le_one hm).2 hnm⟩
  simp_rw [exp_coleHopfSwap_mix_eq hm.ne' v w A x y] at hmix
  rw [integral_div] at hmix
  exact (div_le_one (Real.exp_pos _)).1 hmix

/-- Equality in the concrete dual comparison identifies the two
actual normalized logarithmic Gaussian tilts almost surely. -/
theorem ae_eq_coleHopfSwap_tilts_of_integral_eq {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m n : ℝ} (hn : 0 < n) (hnm : n < m)
    (v w : ℝ≥0) (x y : ℝ)
    (he : (∫ z, coleHopfSwapKernel m n v w A x (y, z) ∂gaussianReal 0 v) =
      Real.exp (n * coleHopf m v A (x + y))) :
    coleHopfSwapFirstLogTilt m v A x y =ᵐ[gaussianReal 0 v]
      coleHopfSwapSecondLogTilt m n v w A x := by
  have hm : 0 < m := hn.trans hnm
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hAg := HasLinearGrowth.of_lipschitz hL
  have hB := abs_coleHopf_sub_le_of_lipschitz n hAm hL w
  have hBg := HasLinearGrowth.of_lipschitz hB
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
  have hf : Measurable (coleHopfSwapFirstLogTilt m v A x y) :=
    measurable_const.mul ((hAm.comp (measurable_const.add measurable_id)).sub measurable_const)
  have hg : Measurable (coleHopfSwapSecondLogTilt m n v w A x) :=
    measurable_const.mul ((hBm.comp (measurable_const.add measurable_id)).sub measurable_const)
  apply ae_eq_of_integral_exp_convex_mix_eq_one hf hg
    (integrable_coleHopfQ hAg hAm hm.ne' v (x + y))
    (integrable_coleHopfQ hBg hBm hm.ne' v x)
    (integral_coleHopfQ hAg hAm hm.ne' v (x + y))
    (integral_coleHopfQ hBg hBm hm.ne' v x)
    (a := n / m) ⟨div_pos hn hm, (div_lt_one hm).2 hnm⟩
  simp_rw [exp_coleHopfSwap_mix_eq hm.ne' v w A x y]
  rw [integral_div, he, div_self (Real.exp_pos _).ne']

end SpinGlass
