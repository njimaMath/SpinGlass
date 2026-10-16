import SpinGlass.Parisi.Variational.ParisiColeHopfSwapKernel
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Cole-Hopf rearrangement at positive masses

The actual normalized Gaussian kernel is integrable in both variables.
Fubini and the concrete dual comparison prove the rearrangement, and
its equality case forces additive separation of the suffix shifts.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

theorem measurable_coleHopfSwapKernel {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) (m n : ℝ) (v w : ℝ≥0) (x : ℝ) :
    Measurable (coleHopfSwapKernel m n v w A x) := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le
    (abs_coleHopf_sub_le_of_lipschitz n hAm hL w)).continuous.measurable
  exact Real.measurable_exp.comp ((measurable_const.mul
    (hAm.comp ((measurable_const.add measurable_fst).add measurable_snd))).add
      (measurable_const.mul ((hBm.comp (measurable_const.add measurable_snd)).sub measurable_const)))

/-- The actual dual comparison supplies a Gaussian-integrable
envelope for the norm of every inner integral, proving product integrability. -/
theorem integrable_coleHopfSwapKernel_prod {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m n : ℝ} (hn : 0 < n) (hnm : n ≤ m)
    (v w : ℝ≥0) (x : ℝ) :
    Integrable (coleHopfSwapKernel m n v w A x) ((gaussianReal 0 w).prod (gaussianReal 0 v)) := by
  have hKm := measurable_coleHopfSwapKernel hAm hA m n v w x
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hD := abs_coleHopf_sub_le_of_lipschitz m hAm hL v
  have hDg := HasLinearGrowth.of_lipschitz hD
  have hDm := (lipschitzWith_toNNReal_of_abs_sub_le hD).continuous.measurable
  have hDi := integrable_exp_mul_comp_add hDg hDm n w x
  apply (integrable_prod_iff hKm.aestronglyMeasurable).2
  refine ⟨.of_forall fun y => integrable_coleHopfSwapKernel_section hAm hA m n v w x y, ?_⟩
  apply hDi.mono' hKm.aestronglyMeasurable.norm.integral_prod_right'
  refine .of_forall fun y => ?_
  have hnorm (z : ℝ) : ‖coleHopfSwapKernel m n v w A x (y, z)‖ = coleHopfSwapKernel m n v w A x (y, z) := by
    unfold coleHopfSwapKernel
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp_rw [hnorm]
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun z => (Real.exp_pos _).le)]
  exact integral_coleHopfSwapKernel_le_of_pos hAm hA hn hnm v w x y

/-- Integrating the actual dual kernel first in the suffix Gaussian
variable gives the exponential of the first composed Cole-Hopf value. -/
theorem integral_integral_coleHopfSwapKernel_eq {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m n : ℝ} (hm : m ≠ 0) (hn : n ≠ 0)
    (v w : ℝ≥0) (x : ℝ) :
    (∫ z, ∫ y, coleHopfSwapKernel m n v w A x (y, z) ∂gaussianReal 0 w ∂gaussianReal 0 v) =
      Real.exp (n * coleHopf m v (coleHopf n w A) x) := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hAg := HasLinearGrowth.of_lipschitz hL
  have hB := abs_coleHopf_sub_le_of_lipschitz n hAm hL w
  have hBg := HasLinearGrowth.of_lipschitz hB
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
  let c := coleHopf m v (coleHopf n w A) x
  have hinner (z : ℝ) : (∫ y, coleHopfSwapKernel m n v w A x (y, z) ∂gaussianReal 0 w) =
      Real.exp (n * coleHopf n w A (x + z) + (m - n) * (coleHopf n w A (x + z) - c)) := by
    unfold coleHopfSwapKernel
    dsimp only
    have harg (y : ℝ) : x + y + z = x + z + y := by ring
    simp_rw [harg, Real.exp_add]
    rw [integral_mul_const, ← exp_mul_coleHopf hAg hAm hn, ← Real.exp_add]
  simp_rw [hinner]
  have hfactor (z : ℝ) :
      Real.exp (n * coleHopf n w A (x + z) + (m - n) * (coleHopf n w A (x + z) - c)) =
      Real.exp (-(m - n) * c) * Real.exp (m * coleHopf n w A (x + z)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [hfactor]
  rw [integral_const_mul, ← exp_mul_coleHopf hBg hBm hm, ← Real.exp_add]
  congr 1
  dsimp only [c]
  ring

/-- The positive-mass form of (14.383), from the actual Gaussian
integrals. Variances may be zero and the masses need not be at most one. -/
theorem coleHopf_swap_le_of_pos {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m n : ℝ} (hn : 0 < n) (hnm : n ≤ m)
    (v w : ℝ≥0) (x : ℝ) :
    coleHopf m v (coleHopf n w A) x ≤ coleHopf n w (coleHopf m v A) x := by
  have hm : 0 < m := hn.trans_le hnm
  have hK := integrable_coleHopfSwapKernel_prod hAm hA hn hnm v w x
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hD := abs_coleHopf_sub_le_of_lipschitz m hAm hL v
  have hDg := HasLinearGrowth.of_lipschitz hD
  have hDm := (lipschitzWith_toNNReal_of_abs_sub_le hD).continuous.measurable
  have hb := integral_mono hK.integral_prod_left (integrable_exp_mul_comp_add hDg hDm n w x)
    (fun y => integral_coleHopfSwapKernel_le_of_pos hAm hA hn hnm v w x y)
  have hswap := integral_integral_swap (f := fun y z => coleHopfSwapKernel m n v w A x (y, z)) hK
  rw [integral_integral_coleHopfSwapKernel_eq hAm hA hm.ne' hn.ne'] at hswap
  rw [hswap, ← exp_mul_coleHopf hDg hDm hn.ne'] at hb
  exact le_of_mul_le_mul_left (Real.exp_le_exp.1 hb) hn

/-- Equality of the actual positive-mass compositions forces the
normalized first and second Gaussian tilts to agree at almost every shift. -/
theorem ae_ae_eq_coleHopfSwap_tilts_of_swap_eq {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m n : ℝ} (hn : 0 < n) (hnm : n < m)
    (v w : ℝ≥0) (x : ℝ)
    (he : coleHopf m v (coleHopf n w A) x = coleHopf n w (coleHopf m v A) x) :
    ∀ᵐ y ∂gaussianReal 0 w, coleHopfSwapFirstLogTilt m v A x y =ᵐ[gaussianReal 0 v]
      coleHopfSwapSecondLogTilt m n v w A x := by
  have hm : 0 < m := hn.trans hnm
  have hK := integrable_coleHopfSwapKernel_prod hAm hA hn hnm.le v w x
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hD := abs_coleHopf_sub_le_of_lipschitz m hAm hL v
  have hDg := HasLinearGrowth.of_lipschitz hD
  have hDm := (lipschitzWith_toNNReal_of_abs_sub_le hD).continuous.measurable
  have hDi := integrable_exp_mul_comp_add hDg hDm n w x
  have hswap := integral_integral_swap (f := fun y z => coleHopfSwapKernel m n v w A x (y, z)) hK
  rw [integral_integral_coleHopfSwapKernel_eq hAm hA hm.ne' hn.ne', he,
    exp_mul_coleHopf hDg hDm hn.ne'] at hswap
  have hfib := (integral_eq_iff_of_ae_le hK.integral_prod_left hDi
    (.of_forall fun y => integral_coleHopfSwapKernel_le_of_pos hAm hA hn hnm.le v w x y)).1 hswap
  filter_upwards [hfib] with y hy
  exact ae_eq_coleHopfSwap_tilts_of_integral_eq hAm hA hn hnm v w x y hy

/-- Agreement of the concrete logarithmic tilts under nonzero
Gaussian variances forces additive separation at every real shift. -/
theorem coleHopfSwap_ae_tilts_implies_shift_identity {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m n : ℝ} (hm : m ≠ 0)
    {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0) (x : ℝ)
    (hae : ∀ᵐ y ∂gaussianReal 0 w, coleHopfSwapFirstLogTilt m v A x y =ᵐ[gaussianReal 0 v]
      coleHopfSwapSecondLogTilt m n v w A x) :
    ∀ y z : ℝ, A (x + y + z) - coleHopf m v A (x + y) =
      coleHopf n w A (x + z) - coleHopf m v (coleHopf n w A) x := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hAc := (lipschitzWith_toNNReal_of_abs_sub_le hL).continuous
  have hBc := (lipschitzWith_toNNReal_of_abs_sub_le (abs_coleHopf_sub_le_of_lipschitz n hAm hL w)).continuous
  have hDc := (lipschitzWith_toNNReal_of_abs_sub_le (abs_coleHopf_sub_le_of_lipschitz m hAm hL v)).continuous
  have hinner : ∀ᵐ y ∂gaussianReal 0 w, ∀ z : ℝ,
      A (x + y + z) - coleHopf m v A (x + y) =
        coleHopf n w A (x + z) - coleHopf m v (coleHopf n w A) x := by
    filter_upwards [hae] with y hy
    have hf : Continuous (coleHopfSwapFirstLogTilt m v A x y) :=
      continuous_const.mul ((hAc.comp (continuous_const.add continuous_id)).sub continuous_const)
    have hg : Continuous (coleHopfSwapSecondLogTilt m n v w A x) :=
      continuous_const.mul ((hBc.comp (continuous_const.add continuous_id)).sub continuous_const)
    have heq := Measure.eq_of_ae_eq ((gaussianReal_absolutelyContinuous' 0 hv).ae_eq hy) hf hg
    intro z
    exact mul_left_cancel₀ hm (congrFun heq z)
  intro y z
  have hzy : (fun y => A (x + y + z) - coleHopf m v A (x + y)) =ᵐ[gaussianReal 0 w]
      (fun _ => coleHopf n w A (x + z) - coleHopf m v (coleHopf n w A) x) := by
    filter_upwards [hinner] with y hy
    exact hy z
  have hfc : Continuous (fun y => A (x + y + z) - coleHopf m v A (x + y)) :=
    (hAc.comp ((continuous_const.add continuous_id).add continuous_const)).sub
      (hDc.comp (continuous_const.add continuous_id))
  exact congrFun (Measure.eq_of_ae_eq ((gaussianReal_absolutelyContinuous' 0 hw).ae_eq hzy)
    hfc continuous_const) y

/-- For nonzero Gaussian variances, equality of the actual positive
mass compositions forces additive separation at every pair of real shifts. -/
theorem coleHopf_swap_eq_implies_shift_identity {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m n : ℝ} (hn : 0 < n) (hnm : n < m)
    {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0) (x : ℝ)
    (he : coleHopf m v (coleHopf n w A) x = coleHopf n w (coleHopf m v A) x) :
    ∀ y z : ℝ, A (x + y + z) - coleHopf m v A (x + y) =
      coleHopf n w A (x + z) - coleHopf m v (coleHopf n w A) x := by
  exact coleHopfSwap_ae_tilts_implies_shift_identity hAm hA (hn.trans hnm).ne' hv hw x
    (ae_ae_eq_coleHopfSwap_tilts_of_swap_eq hAm hA hn hnm v w x he)

/-- The strict positive-mass part of (14.384). Equality would make
the strictly convex suffix affine on a nontrivial segment. -/
theorem coleHopf_swap_lt_of_pos {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) (hconv : StrictConvexOn ℝ univ A)
    {m n : ℝ} (hn : 0 < n) (hnm : n < m) {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0) (x : ℝ) :
    coleHopf m v (coleHopf n w A) x < coleHopf n w (coleHopf m v A) x := by
  have hle := coleHopf_swap_le_of_pos hAm hA hn hnm.le v w x
  apply lt_of_le_of_ne hle
  intro he
  have hid := coleHopf_swap_eq_implies_shift_identity hAm hA hn hnm hv hw x he
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
  simp only [hmid] at hstrict
  linarith

end SpinGlass
