import SpinGlass.Parisi.Variational.ParisiColeHopfRearrangement

/-!
# Shared Gaussian Cole-Hopf comparison and equality

The common-mark case of (14.374) is the normalized exponential
comparison with equal weights. At a positive mass and nonzero variance,
strict convexity of the actual suffix forces equality of the effective
fields, as required by (14.381).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

noncomputable def sharedPairColeHopf (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  coleHopf m v (fun z => A (x + z) + A (y + z)) 0

noncomputable def sharedPairLogTilt (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (x z : ℝ) : ℝ :=
  (2 * m) * (A (x + z) - coleHopf (2 * m) v A x)

theorem sharedPairColeHopf_zero {A : ℝ → ℝ} (hAm : Measurable A)
    {L : ℝ} (hA : ∀ x y, |A y - A x| ≤ L * |y - x|)
    (v : ℝ≥0) (x y : ℝ) :
    sharedPairColeHopf 0 v A x y = coleHopf 0 v A x + coleHopf 0 v A y := by
  have hAg := HasLinearGrowth.of_lipschitz hA
  have hi (a : ℝ) : Integrable (fun z => A (a + z)) (gaussianReal 0 v) :=
    (hAg.comp_add_const a).toHasExpGrowth.integrable_gaussianReal
      (hAm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  simp only [sharedPairColeHopf, coleHopf_zero, zero_add]
  exact integral_add (hi x) (hi y)

theorem sharedPairColeHopf_self (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (x : ℝ) :
    sharedPairColeHopf m v A x x = 2 * coleHopf (2 * m) v A x := by
  by_cases hm : m = 0
  · subst m
    simp only [sharedPairColeHopf, mul_zero, coleHopf_zero, zero_add,
      ← two_mul, integral_const_mul]
  · have h2m : 2 * m ≠ 0 := mul_ne_zero (by norm_num) hm
    simp only [sharedPairColeHopf, coleHopf_of_ne hm, coleHopf_of_ne h2m, zero_add]
    have harg (z : ℝ) : m * (A (x + z) + A (x + z)) = (2 * m) * A (x + z) := by ring
    simp_rw [harg]
    field_simp

/-- The exact normalized common-mark integral is the exponential
of the difference between the paired and scalar recursive values. -/
theorem integral_exp_sharedPair_mix_eq {A : ℝ → ℝ} (hAm : Measurable A)
    {L : ℝ} (hA : ∀ x y, |A y - A x| ≤ L * |y - x|)
    {m : ℝ} (hm : m ≠ 0) (v : ℝ≥0) (x y : ℝ) :
    (∫ z, Real.exp ((1 / 2 : ℝ) * sharedPairLogTilt m v A x z +
      (1 / 2 : ℝ) * sharedPairLogTilt m v A y z) ∂gaussianReal 0 v) =
      Real.exp (m * (sharedPairColeHopf m v A x y -
        (coleHopf (2 * m) v A x + coleHopf (2 * m) v A y))) := by
  let C := fun z => A (x + z) + A (y + z)
  have hCg : HasLinearGrowth C := HasLinearGrowth.of_lipschitz (L := 2 * L) (fun a b => by
    calc
      |C b - C a| = |(A (x + b) - A (x + a)) + (A (y + b) - A (y + a))| := by
        congr 1
        dsimp [C]
        ring
      _ ≤ |A (x + b) - A (x + a)| + |A (y + b) - A (y + a)| := abs_add_le _ _
      _ ≤ L * |b - a| + L * |b - a| := by
        simpa only [add_sub_add_left_eq_sub] using add_le_add (hA (x + a) (x + b)) (hA (y + a) (y + b))
      _ = (2 * L) * |b - a| := by ring)
  have hCm : Measurable C :=
    (hAm.comp (measurable_const.add measurable_id)).add
      (hAm.comp (measurable_const.add measurable_id))
  have hfactor (z : ℝ) :
      Real.exp ((1 / 2 : ℝ) * sharedPairLogTilt m v A x z +
        (1 / 2 : ℝ) * sharedPairLogTilt m v A y z) =
      Real.exp (-(m * (coleHopf (2 * m) v A x + coleHopf (2 * m) v A y))) *
        Real.exp (m * C z) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [sharedPairLogTilt, C]
    ring
  simp_rw [hfactor]
  rw [integral_const_mul]
  have hexp := exp_mul_coleHopf hCg hCm hm v 0
  simp only [zero_add] at hexp
  rw [← hexp, ← Real.exp_add]
  congr 1
  dsimp [sharedPairColeHopf, C]
  ring

/-- The common-mark part of (14.374), including zero mass and
zero variance, proved from the actual normalized Gaussian densities. -/
theorem sharedPairColeHopf_le {A : ℝ → ℝ} (hAm : Measurable A)
    {L : ℝ} (hA : ∀ x y, |A y - A x| ≤ L * |y - x|)
    {m : ℝ} (hm : 0 ≤ m) (v : ℝ≥0) (x y : ℝ) :
    sharedPairColeHopf m v A x y ≤ coleHopf (2 * m) v A x + coleHopf (2 * m) v A y := by
  rcases eq_or_lt_of_le hm with hzero | hpos
  · subst m
    simpa only [mul_zero] using (sharedPairColeHopf_zero hAm hA v x y).le
  · have h2m : 2 * m ≠ 0 := mul_ne_zero (by norm_num) hpos.ne'
    have hAg := HasLinearGrowth.of_lipschitz hA
    have hfm (a : ℝ) : Measurable (sharedPairLogTilt m v A a) := by
      unfold sharedPairLogTilt
      fun_prop
    have hfi (a : ℝ) : Integrable (fun z => Real.exp (sharedPairLogTilt m v A a z))
        (gaussianReal 0 v) := integrable_coleHopfQ hAg hAm h2m v a
    have hfn (a : ℝ) : (∫ z, Real.exp (sharedPairLogTilt m v A a z) ∂gaussianReal 0 v) = 1 :=
      integral_coleHopfQ hAg hAm h2m v a
    have h := integral_exp_convex_mix_le_one (hfm x) (hfm y) (hfi x) (hfi y)
      (hfn x) (hfn y) (a := (1 / 2 : ℝ)) (by norm_num)
    norm_num only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num] at h
    rw [integral_exp_sharedPair_mix_eq hAm hA hpos.ne'] at h
    have harg := Real.exp_le_exp.1 (h.trans_eq (Real.exp_zero.symm))
    have hd := le_of_mul_le_mul_left (show m * (_ - _) ≤ m * 0 by simpa using harg) hpos
    linarith

/-- Equality at positive shared mass forces equality of the
two normalized logarithmic Gaussian tilts. -/
theorem ae_eq_sharedPairLogTilt_of_eq {A : ℝ → ℝ} (hAm : Measurable A)
    {L : ℝ} (hA : ∀ x y, |A y - A x| ≤ L * |y - x|)
    {m : ℝ} (hm : 0 < m) (v : ℝ≥0) (x y : ℝ)
    (he : sharedPairColeHopf m v A x y = coleHopf (2 * m) v A x + coleHopf (2 * m) v A y) :
    sharedPairLogTilt m v A x =ᵐ[gaussianReal 0 v] sharedPairLogTilt m v A y := by
  have h2m : 2 * m ≠ 0 := mul_ne_zero (by norm_num) hm.ne'
  have hAg := HasLinearGrowth.of_lipschitz hA
  have hfm (a : ℝ) : Measurable (sharedPairLogTilt m v A a) := by
    unfold sharedPairLogTilt
    fun_prop
  have hfi (a : ℝ) : Integrable (fun z => Real.exp (sharedPairLogTilt m v A a z))
      (gaussianReal 0 v) := integrable_coleHopfQ hAg hAm h2m v a
  have hfn (a : ℝ) : (∫ z, Real.exp (sharedPairLogTilt m v A a z) ∂gaussianReal 0 v) = 1 :=
    integral_coleHopfQ hAg hAm h2m v a
  apply ae_eq_of_integral_exp_convex_mix_eq_one (hfm x) (hfm y) (hfi x) (hfi y)
    (hfn x) (hfn y) (a := (1 / 2 : ℝ)) (by norm_num)
  norm_num only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
  rw [integral_exp_sharedPair_mix_eq hAm hA hm.ne', he, sub_self, mul_zero, Real.exp_zero]

/-- Nonzero Gaussian variance upgrades the almost sure equality
of normalized tilts to equality at every real shift. -/
theorem sharedPair_eq_implies_shift_identity {A : ℝ → ℝ} (hAm : Measurable A)
    {L : ℝ} (hA : ∀ x y, |A y - A x| ≤ L * |y - x|)
    {m : ℝ} (hm : 0 < m) {v : ℝ≥0} (hv : v ≠ 0) (x y : ℝ)
    (he : sharedPairColeHopf m v A x y = coleHopf (2 * m) v A x + coleHopf (2 * m) v A y) :
    ∀ z, A (x + z) - coleHopf (2 * m) v A x = A (y + z) - coleHopf (2 * m) v A y := by
  have hae := ae_eq_sharedPairLogTilt_of_eq hAm hA hm v x y he
  have hAc := (lipschitzWith_toNNReal_of_abs_sub_le hA).continuous
  have hc (a : ℝ) : Continuous (sharedPairLogTilt m v A a) :=
    continuous_const.mul ((hAc.comp (continuous_const.add continuous_id)).sub continuous_const)
  have hall := Measure.eq_of_ae_eq ((gaussianReal_absolutelyContinuous' 0 hv).ae_eq hae) (hc x) (hc y)
  intro z
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hm.ne') (congrFun hall z)

/-- The common-mark equality condition (14.381). It follows
from strict convexity and the actual Gaussian comparison. -/
theorem sharedPairColeHopf_eq_implies_fields_eq {A : ℝ → ℝ} (hAm : Measurable A)
    {L : ℝ} (hA : ∀ x y, |A y - A x| ≤ L * |y - x|)
    (hconv : StrictConvexOn ℝ univ A) {m : ℝ} (hm : 0 < m)
    {v : ℝ≥0} (hv : v ≠ 0) (x y : ℝ)
    (he : sharedPairColeHopf m v A x y = coleHopf (2 * m) v A x + coleHopf (2 * m) v A y) :
    x = y := by
  by_contra hne
  have hid := sharedPair_eq_implies_shift_identity hAm hA hm hv x y he
  have hx := hid (-x)
  have hy := hid (-y)
  have hs := hconv.2 (mem_univ (x - y)) (mem_univ (y - x))
    (by intro heq; apply hne; linarith : x - y ≠ y - x)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hs
  rw [show (1 / 2 : ℝ) * (x - y) + (1 / 2 : ℝ) * (y - x) = 0 by ring] at hs
  simp only [add_neg_cancel, ← sub_eq_add_neg] at hx hy
  linarith

theorem sharedPairColeHopf_lt_of_fields_ne {A : ℝ → ℝ} (hAm : Measurable A)
    {L : ℝ} (hA : ∀ x y, |A y - A x| ≤ L * |y - x|)
    (hconv : StrictConvexOn ℝ univ A) {m : ℝ} (hm : 0 < m)
    {v : ℝ≥0} (hv : v ≠ 0) {x y : ℝ} (hne : x ≠ y) :
    sharedPairColeHopf m v A x y < coleHopf (2 * m) v A x + coleHopf (2 * m) v A y :=
  lt_of_le_of_ne (sharedPairColeHopf_le hAm hA hm.le v x y)
    (fun he => hne (sharedPairColeHopf_eq_implies_fields_eq hAm hA hconv hm hv x y he))

end SpinGlass
