import SpinGlass.Parisi.Variational.ParisiColeHopfSwapPositive
import SpinGlass.Parisi.Variational.ParisiNormalizedEntropy

/-!
# The actual dual kernel at zero inner mass

The suffix at mass zero is its Gaussian expectation. Its normalized
outer tilt gives a centered kernel with zero iterated mean. The
entropy comparison controls each shifted section and its equality case.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

noncomputable def coleHopfSwapZeroDensity (m : ℝ) (v w : ℝ≥0) (A : ℝ → ℝ) (x z : ℝ) : ℝ :=
  coleHopfQ m v (coleHopf 0 w A) x z

noncomputable def coleHopfSwapZeroKernel (m : ℝ) (v w : ℝ≥0) (A : ℝ → ℝ) (x : ℝ)
    (yz : ℝ × ℝ) : ℝ :=
  coleHopfSwapZeroDensity m v w A x yz.2 * (A (x + yz.1 + yz.2) - coleHopf 0 w A (x + yz.2))

theorem coleHopfSwapZeroDensity_expGrowth {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) (m : ℝ) (v w : ℝ≥0) (x : ℝ) :
    HasExpGrowth (coleHopfSwapZeroDensity m v w A x) := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hB := abs_coleHopf_sub_le_of_lipschitz 0 hAm hL w
  have hBg := HasLinearGrowth.of_lipschitz hB
  exact ((hBg.comp_add_const x).add_const (-coleHopf m v (coleHopf 0 w A) x)).exp_mul m

theorem integrable_coleHopfSwapZeroKernel_section {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) (m : ℝ) (v w : ℝ≥0) (x y : ℝ) :
    Integrable (fun z => coleHopfSwapZeroKernel m v w A x (y, z)) (gaussianReal 0 v) := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hAg := HasLinearGrowth.of_lipschitz hL
  have hB := abs_coleHopf_sub_le_of_lipschitz 0 hAm hL w
  have hBg := HasLinearGrowth.of_lipschitz hB
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
  have hG := (coleHopfSwapZeroDensity_expGrowth hAm hA m v w x).mul
    ((hAg.comp_add_const (x + y)).toHasExpGrowth.sub (hBg.comp_add_const x).toHasExpGrowth)
  exact hG.integrable_gaussianReal (μ := 0) (v := v)
    ((measurable_coleHopfQ hBm m v x).mul
      ((hAm.comp (measurable_const.add measurable_id)).sub
        (hBm.comp (measurable_const.add measurable_id)))).aestronglyMeasurable

/-- Linear growth of the shifted suffix and the actual Gaussian
tilt give product integrability of the signed centered kernel. -/
theorem integrable_coleHopfSwapZeroKernel_prod {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m : ℝ} (hm : m ≠ 0)
    (v w : ℝ≥0) (x : ℝ) :
    Integrable (coleHopfSwapZeroKernel m v w A x) ((gaussianReal 0 w).prod (gaussianReal 0 v)) := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hAg := HasLinearGrowth.of_lipschitz hL
  have hB := abs_coleHopf_sub_le_of_lipschitz 0 hAm hL w
  have hBg := HasLinearGrowth.of_lipschitz hB
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
  have hQm : Measurable (coleHopfSwapZeroDensity m v w A x) := measurable_coleHopfQ hBm m v x
  have hQi : Integrable (coleHopfSwapZeroDensity m v w A x) (gaussianReal 0 v) :=
    integrable_coleHopfQ hBg hBm hm v x
  have hQpos (z : ℝ) : 0 < coleHopfSwapZeroDensity m v w A x z := coleHopfQ_pos _ _ _ _ _
  have hGz : Integrable (fun z => |A (x + z) - coleHopf 0 w A (x + z)| * coleHopfSwapZeroDensity m v w A x z)
      (gaussianReal 0 v) :=
    (((hAg.comp_add_const x).toHasExpGrowth.sub (hBg.comp_add_const x).toHasExpGrowth).abs.mul
      (coleHopfSwapZeroDensity_expGrowth hAm hA m v w x)).integrable_gaussianReal
        ((((hAm.comp (measurable_const.add measurable_id)).sub
          (hBm.comp (measurable_const.add measurable_id))).norm).mul hQm).aestronglyMeasurable
  have hYa : Integrable (fun y : ℝ => |y|) (gaussianReal 0 w) := IsGaussian.integrable_id.abs
  have hbound := (hYa.mul_prod hQi).add (hGz.comp_snd (gaussianReal 0 w))
  have hKm : Measurable (coleHopfSwapZeroKernel m v w A x) :=
    (hQm.comp measurable_snd).mul
      ((hAm.comp ((measurable_const.add measurable_fst).add measurable_snd)).sub
        (hBm.comp (measurable_const.add measurable_snd)))
  apply hbound.mono' hKm.aestronglyMeasurable
  refine .of_forall fun yz => ?_
  rcases yz with ⟨y, z⟩
  change |coleHopfSwapZeroDensity m v w A x z * (A (x + y + z) - coleHopf 0 w A (x + z))| ≤
    |y| * coleHopfSwapZeroDensity m v w A x z +
      |A (x + z) - coleHopf 0 w A (x + z)| * coleHopfSwapZeroDensity m v w A x z
  have ha := hA (x + z) (x + y + z)
  rw [show x + y + z - (x + z) = y by ring] at ha
  have hd := (abs_sub_le (A (x + y + z)) (A (x + z)) (coleHopf 0 w A (x + z))).trans
    (add_le_add ha le_rfl)
  rw [abs_mul, abs_of_pos (hQpos z)]
  calc
    _ ≤ coleHopfSwapZeroDensity m v w A x z * (|y| + |A (x + z) - coleHopf 0 w A (x + z)|) :=
      mul_le_mul_of_nonneg_left hd (hQpos z).le
    _ = _ := by ring

/-- The actual weighted logarithmic tilt difference is exactly the
mass times the centered-kernel pressure difference. -/
theorem integral_coleHopfSwapZero_logTilt_diff_eq {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m : ℝ} (hm : m ≠ 0)
    (v w : ℝ≥0) (x y : ℝ) :
    (∫ z, Real.exp (coleHopfSwapSecondLogTilt m 0 v w A x z) *
      (coleHopfSwapFirstLogTilt m v A x y z - coleHopfSwapSecondLogTilt m 0 v w A x z) ∂gaussianReal 0 v) =
      m * ((∫ z, coleHopfSwapZeroKernel m v w A x (y, z) ∂gaussianReal 0 v) -
        (coleHopf m v A (x + y) - coleHopf m v (coleHopf 0 w A) x)) := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hB := abs_coleHopf_sub_le_of_lipschitz 0 hAm hL w
  have hBg := HasLinearGrowth.of_lipschitz hB
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
  have hQi : Integrable (coleHopfSwapZeroDensity m v w A x) (gaussianReal 0 v) := integrable_coleHopfQ hBg hBm hm v x
  have hQn : (∫ z, coleHopfSwapZeroDensity m v w A x z ∂gaussianReal 0 v) = 1 := integral_coleHopfQ hBg hBm hm v x
  have hpoint (z : ℝ) : Real.exp (coleHopfSwapSecondLogTilt m 0 v w A x z) *
      (coleHopfSwapFirstLogTilt m v A x y z - coleHopfSwapSecondLogTilt m 0 v w A x z) =
      m * (coleHopfSwapZeroKernel m v w A x (y, z) -
        (coleHopf m v A (x + y) - coleHopf m v (coleHopf 0 w A) x) * coleHopfSwapZeroDensity m v w A x z) := by
    unfold coleHopfSwapFirstLogTilt coleHopfSwapSecondLogTilt coleHopfSwapZeroKernel coleHopfSwapZeroDensity coleHopfQ
    dsimp only
    ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_sub (integrable_coleHopfSwapZeroKernel_section hAm hA m v w x y) (hQi.const_mul _),
    integral_const_mul, hQn, mul_one]

/-- The weighted logarithmic tilt difference is Gaussian-integrable,
as a linear combination of the actual centered kernel and normalized density. -/
theorem integrable_coleHopfSwapZero_logTilt_diff {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m : ℝ} (hm : m ≠ 0)
    (v w : ℝ≥0) (x y : ℝ) :
    Integrable (fun z => Real.exp (coleHopfSwapSecondLogTilt m 0 v w A x z) *
      (coleHopfSwapFirstLogTilt m v A x y z - coleHopfSwapSecondLogTilt m 0 v w A x z)) (gaussianReal 0 v) := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hB := abs_coleHopf_sub_le_of_lipschitz 0 hAm hL w
  have hBg := HasLinearGrowth.of_lipschitz hB
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
  have hQi : Integrable (coleHopfSwapZeroDensity m v w A x) (gaussianReal 0 v) := integrable_coleHopfQ hBg hBm hm v x
  have hi := ((integrable_coleHopfSwapZeroKernel_section hAm hA m v w x y).sub
    (hQi.const_mul (coleHopf m v A (x + y) - coleHopf m v (coleHopf 0 w A) x))).const_mul m
  apply hi.congr (.of_forall fun z => ?_)
  simp only [Pi.sub_apply]
  unfold coleHopfSwapFirstLogTilt coleHopfSwapSecondLogTilt coleHopfSwapZeroKernel coleHopfSwapZeroDensity coleHopfQ
  dsimp only
  ring

/-- The actual zero-mass dual comparison at each shifted field. -/
theorem integral_coleHopfSwapZeroKernel_le {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m : ℝ} (hm : 0 < m) (v w : ℝ≥0) (x y : ℝ) :
    (∫ z, coleHopfSwapZeroKernel m v w A x (y, z) ∂gaussianReal 0 v) ≤
      coleHopf m v A (x + y) - coleHopf m v (coleHopf 0 w A) x := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hAg := HasLinearGrowth.of_lipschitz hL
  have hB := abs_coleHopf_sub_le_of_lipschitz 0 hAm hL w
  have hBg := HasLinearGrowth.of_lipschitz hB
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
  have hb := integral_exp_mul_sub_le_zero
    (f := coleHopfSwapFirstLogTilt m v A x y) (g := coleHopfSwapSecondLogTilt m 0 v w A x)
    (integrable_coleHopfQ hAg hAm hm.ne' v (x + y)) (integrable_coleHopfQ hBg hBm hm.ne' v x)
    (integrable_coleHopfSwapZero_logTilt_diff hAm hA hm.ne' v w x y)
    (integral_coleHopfQ hAg hAm hm.ne' v (x + y)) (integral_coleHopfQ hBg hBm hm.ne' v x)
  rw [integral_coleHopfSwapZero_logTilt_diff_eq hAm hA hm.ne'] at hb
  apply sub_nonpos.1
  exact le_of_mul_le_mul_left (by simpa only [mul_zero] using hb) hm

/-- Equality of the actual zero-mass section bound identifies the
normalized Gaussian tilts, including the Gaussian expectation suffix. -/
theorem ae_eq_coleHopfSwapZero_tilts_of_integral_eq {A : ℝ → ℝ} (hAm : Measurable A)
    (hA : ∀ x y, |A y - A x| ≤ |y - x|) {m : ℝ} (hm : 0 < m) (v w : ℝ≥0) (x y : ℝ)
    (he : (∫ z, coleHopfSwapZeroKernel m v w A x (y, z) ∂gaussianReal 0 v) =
      coleHopf m v A (x + y) - coleHopf m v (coleHopf 0 w A) x) :
    coleHopfSwapFirstLogTilt m v A x y =ᵐ[gaussianReal 0 v] coleHopfSwapSecondLogTilt m 0 v w A x := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hA
  have hAg := HasLinearGrowth.of_lipschitz hL
  have hB := abs_coleHopf_sub_le_of_lipschitz 0 hAm hL w
  have hBg := HasLinearGrowth.of_lipschitz hB
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
  apply ae_eq_of_integral_exp_mul_sub_eq_zero
    (f := coleHopfSwapFirstLogTilt m v A x y) (g := coleHopfSwapSecondLogTilt m 0 v w A x)
    (integrable_coleHopfQ hAg hAm hm.ne' v (x + y)) (integrable_coleHopfQ hBg hBm hm.ne' v x)
    (integrable_coleHopfSwapZero_logTilt_diff hAm hA hm.ne' v w x y)
    (integral_coleHopfQ hAg hAm hm.ne' v (x + y)) (integral_coleHopfQ hBg hBm hm.ne' v x)
  rw [integral_coleHopfSwapZero_logTilt_diff_eq hAm hA hm.ne', he, sub_self, mul_zero]

end SpinGlass
