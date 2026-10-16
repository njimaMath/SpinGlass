import SpinGlass.Parisi.Variational.ParisiColeHopfSwapZeroKernel

/-!
# Cole-Hopf rearrangement with the genuine zero-mass branch

The centered Gaussian dual kernel has exactly zero mean. Its actual
entropy comparison proves the rearrangement and identifies equality.
Strict convexity therefore also gives strictness at inner mass zero.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

theorem integral_integral_coleHopfSwapZeroKernel_eq_zero {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m : ℝ} (hm : m ≠ 0)
    (v w : ℝ≥0) (x : ℝ) :
    (∫ y, ∫ z, coleHopfSwapZeroKernel m v w A x (y, z) ∂gaussianReal 0 v ∂gaussianReal 0 w) = 0 := by
  have hK := integrable_coleHopfSwapZeroKernel_prod hAm hA hm v w x
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hAg := HasLinearGrowth.of_lipschitz hL
  have hinner (z : ℝ) : (∫ y, coleHopfSwapZeroKernel m v w A x (y, z) ∂gaussianReal 0 w) = 0 := by
    unfold coleHopfSwapZeroKernel
    dsimp only
    have harg (y : ℝ) : x + y + z = x + z + y := by ring
    simp_rw [harg]
    have hAi : Integrable (fun y => A (x + z + y)) (gaussianReal 0 w) :=
      ((hAg.comp_add_const (x + z)).toHasExpGrowth).integrable_gaussianReal
        (hAm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    rw [integral_const_mul, integral_sub hAi (integrable_const _), integral_const, probReal_univ,
      one_smul, ← coleHopf_zero, sub_self, mul_zero]
  rw [integral_integral_swap (f := fun y z => coleHopfSwapZeroKernel m v w A x (y, z)) hK]
  simp_rw [hinner]
  simp only [integral_zero]

/-- The zero-inner-mass part of (14.383), using its actual Gaussian
expectation branch rather than division by mass zero. -/
theorem coleHopf_swap_zero_le {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m : ℝ} (hm : 0 < m)
    (v w : ℝ≥0) (x : ℝ) :
    coleHopf m v (coleHopf 0 w A) x ≤ coleHopf 0 w (coleHopf m v A) x := by
  have hK := integrable_coleHopfSwapZeroKernel_prod hAm hA hm.ne' v w x
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hD := abs_coleHopf_sub_le_of_lipschitz m hAm hL v
  have hDg := HasLinearGrowth.of_lipschitz hD
  have hDm := (lipschitzWith_toNNReal_of_abs_sub_le hD).continuous.measurable
  have hDi : Integrable (fun y => coleHopf m v A (x + y)) (gaussianReal 0 w) :=
    (hDg.comp_add_const x).toHasExpGrowth.integrable_gaussianReal
      (hDm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  have hb := integral_mono hK.integral_prod_left
    (hDi.sub (integrable_const (coleHopf m v (coleHopf 0 w A) x)))
    (fun y => integral_coleHopfSwapZeroKernel_le hAm hA hm v w x y)
  simp only [Pi.sub_apply] at hb
  rw [integral_integral_coleHopfSwapZeroKernel_eq_zero hAm hA hm.ne', integral_sub hDi (integrable_const _),
    integral_const, probReal_univ, one_smul, ← coleHopf_zero] at hb
  exact sub_nonneg.1 hb

/-- Equality of the actual zero-mass compositions forces agreement
of their normalized tilts at almost every shifted field. -/
theorem ae_ae_eq_coleHopfSwapZero_tilts_of_swap_eq {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m : ℝ} (hm : 0 < m)
    (v w : ℝ≥0) (x : ℝ)
    (he : coleHopf m v (coleHopf 0 w A) x = coleHopf 0 w (coleHopf m v A) x) :
    ∀ᵐ y ∂gaussianReal 0 w, coleHopfSwapFirstLogTilt m v A x y =ᵐ[gaussianReal 0 v]
      coleHopfSwapSecondLogTilt m 0 v w A x := by
  have hK := integrable_coleHopfSwapZeroKernel_prod hAm hA hm.ne' v w x
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hD := abs_coleHopf_sub_le_of_lipschitz m hAm hL v
  have hDg := HasLinearGrowth.of_lipschitz hD
  have hDm := (lipschitzWith_toNNReal_of_abs_sub_le hD).continuous.measurable
  have hDi : Integrable (fun y => coleHopf m v A (x + y)) (gaussianReal 0 w) :=
    (hDg.comp_add_const x).toHasExpGrowth.integrable_gaussianReal
      (hDm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  have hmean : (∫ y, coleHopf m v A (x + y) - coleHopf m v (coleHopf 0 w A) x ∂gaussianReal 0 w) = 0 := by
    rw [integral_sub hDi (integrable_const _), integral_const, probReal_univ, one_smul,
      ← coleHopf_zero, ← he, sub_self]
  have hfib := (integral_eq_iff_of_ae_le hK.integral_prod_left
    (hDi.sub (integrable_const (coleHopf m v (coleHopf 0 w A) x)))
    (.of_forall fun y => integral_coleHopfSwapZeroKernel_le hAm hA hm v w x y)).1
      ((integral_integral_coleHopfSwapZeroKernel_eq_zero hAm hA hm.ne' v w x).trans hmean.symm)
  filter_upwards [hfib] with y hy
  exact ae_eq_coleHopfSwapZero_tilts_of_integral_eq hAm hA hm v w x y hy

/-- Strictness in (14.384) also holds at inner mass zero. The
actual Gaussian expectation and entropy equality conditions would
otherwise make the strictly convex suffix affine on a segment. -/
theorem coleHopf_swap_zero_lt {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) (hconv : StrictConvexOn ℝ univ A)
    {m : ℝ} (hm : 0 < m) {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0) (x : ℝ) :
    coleHopf m v (coleHopf 0 w A) x < coleHopf 0 w (coleHopf m v A) x := by
  apply lt_of_le_of_ne (coleHopf_swap_zero_le hAm hA hm v w x)
  intro he
  have hid := coleHopfSwap_ae_tilts_implies_shift_identity hAm hA hm.ne' hv hw x
    (ae_ae_eq_coleHopfSwapZero_tilts_of_swap_eq hAm hA hm v w x he)
  have h00 := hid 0 0
  have h10 := hid 1 0
  have h01 := hid 0 1
  have h11 := hid 1 1
  simp only [add_zero, show x + 1 + 1 = x + 2 by ring] at h00 h10 h01 h11
  have hstrict : A ((1 / 2 : ℝ) * x + (1 / 2 : ℝ) * (x + 2)) <
      (1 / 2 : ℝ) * A x + (1 / 2 : ℝ) * A (x + 2) :=
    hconv.2 (mem_univ x) (mem_univ (x + 2)) (by linarith : x ≠ x + 2)
      (by norm_num) (by norm_num) (by norm_num)
  have hmid : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * (x + 2) = x + 1 := by ring
  rw [hmid] at hstrict
  linarith

end SpinGlass
