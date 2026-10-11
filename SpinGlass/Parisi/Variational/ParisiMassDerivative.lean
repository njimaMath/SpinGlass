import SpinGlass.Parisi.Minimizer.QVariation.Recursion
import SpinGlass.Parisi.ARISTOTLE
import Common.Mathlib.Analysis.Calculus.MeasurableParamDeriv
import Common.Mathlib.Probability.PointProcess.CascadeColeHopf

/-!
# Mass calculus for concrete Cole-Hopf layers

The layer in (14.193)-(14.194) agrees with the analytic mass transform,
including its expectation branch at zero mass. Centering a Lipschitz input
gives Gaussian envelopes independent of the realized external field. These
are local inputs to the inserted-mass calculation in Section 14.7.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal BigOperators

namespace SpinGlass

/-- Identify the project's actual Cole-Hopf operator with the analytic mass
transform, including zero mass. -/
theorem coleHopf_eq_massTransform (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (x : ℝ) :
    coleHopf m v A x = Aristotle.massTransform (gaussianReal 0 v) (fun z => A (x + z)) m := by
  unfold coleHopf Aristotle.massTransform Aristotle.logLaplace
  split_ifs
  · rfl
  · simp only [div_eq_mul_inv, mul_one, mul_comm]

/-- Standard Gaussian coordinates put all variances in one probability space,
which permits constants uniform over bounded variance ranges. -/
theorem coleHopf_eq_massTransform_standard {A : ℝ → ℝ} (hA : Measurable A)
    (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    coleHopf m v A x = Aristotle.massTransform (gaussianReal 0 1)
      (fun z => A (x + Real.sqrt v * z)) m := by
  rw [coleHopf_eq_massTransform]
  unfold Aristotle.massTransform Aristotle.logLaplace
  split_ifs
  · exact integral_gaussianReal_eq_integral_sqrt_mul v
      (hA.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  · congr 2
    exact integral_gaussianReal_eq_integral_sqrt_mul v
      ((hA.comp (measurable_const.add measurable_id)).const_mul m).exp.aestronglyMeasurable

/-- The zero-mass derivative is half the variance of the actual layer input.
The Gaussian variance itself may also vanish. This completes the zero-mass
case of the local exponent calculus accompanying (14.259). -/
theorem hasDerivAt_coleHopf_exponent_zero {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (fun m => coleHopf m v A x)
      (((∫ z, A (x + z) ^ 2 ∂gaussianReal 0 v) -
        (∫ z, A (x + z) ∂gaussianReal 0 v) ^ 2) / 2) 0 := by
  have hX : Measurable (fun z => A (x + z)) :=
    hAm.comp (measurable_const.add measurable_id)
  have henv : Integrable (fun z => Real.exp (1 * |A (x + z)|)) (gaussianReal 0 v) := by
    obtain ⟨a, b, hb, hbound⟩ := hA.comp_add_const x
    have hg : HasLinearGrowth (fun z => |A (x + z)|) :=
      ⟨a, b, hb, by simpa only [abs_abs] using hbound⟩
    exact (hg.exp_mul 1).integrable_gaussianReal
      ((continuous_abs.measurable.comp hX).const_mul 1).exp.aestronglyMeasurable
  simpa only [coleHopf_eq_massTransform] using
    Aristotle.hasDerivAt_massTransform_zero hX (a := 1) zero_lt_one henv

/-- The mass derivative in (14.259), extended at zero by half the variance.
Both branches use the project's Gaussian layer and tilt. -/
noncomputable def coleHopfMassDeriv (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  if m = 0 then
    ((∫ z, A (x + z) ^ 2 ∂gaussianReal 0 v) -
      (∫ z, A (x + z) ∂gaussianReal 0 v) ^ 2) / 2
  else
    (1 / m) * ((∫ z, A (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v) -
      coleHopf m v A x)

/-- Differentiate the concrete Gaussian layer at every mass, including zero. -/
theorem hasDerivAt_coleHopf_mass {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (v : ℝ≥0) (x m : ℝ) :
    HasDerivAt (fun b => coleHopf b v A x) (coleHopfMassDeriv m v A x) m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simpa [coleHopfMassDeriv] using
      hasDerivAt_coleHopf_exponent_zero hA hAm v x
  · simpa only [coleHopfMassDeriv, ite_eq_right hm] using
      hasDerivAt_coleHopf_exponent hA hAm hm v x

/-- The actual Gaussian layer is analytic at every mass, including zero.
Linear growth of its input supplies the needed Gaussian exponential envelope. -/
theorem analyticAt_coleHopf_mass {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (v : ℝ≥0) (x m : ℝ) :
    AnalyticAt ℝ (fun b => coleHopf b v A x) m := by
  let a : ℝ := |m| + 1
  have hX : Measurable (fun z => A (x + z)) :=
    hAm.comp (measurable_const.add measurable_id)
  obtain ⟨c, d, hd, hbound⟩ := hA.comp_add_const x
  have hg : HasLinearGrowth (fun z => |A (x + z)|) :=
    ⟨c, d, hd, by simpa only [abs_abs] using hbound⟩
  have hint : Integrable (fun z => Real.exp (a * |A (x + z)|)) (gaussianReal 0 v) :=
    (hg.exp_mul a).integrable_gaussianReal
      ((continuous_abs.measurable.comp hX).const_mul a).exp.aestronglyMeasurable
  have hm : m ∈ Ioo (-a) a := by
    dsimp [a]
    constructor <;> linarith [neg_abs_le m, le_abs_self m]
  simpa only [coleHopf_eq_massTransform] using
    Aristotle.analyticOnNhd_massTransform hX hint m hm

/-- Translating an external field commutes with the mass derivative. -/
theorem coleHopfMassDeriv_translate {A : ℝ → ℝ}
    (hA : HasLinearGrowth A) (hAm : Measurable A) (m c x : ℝ) (v : ℝ≥0) :
    coleHopfMassDeriv m v (fun y => A (c + y)) x = coleHopfMassDeriv m v A (c + x) := by
  rw [← (hasDerivAt_coleHopf_mass (hA.comp_add_const c)
    (hAm.comp (measurable_const.add measurable_id)) v x m).deriv,
    ← (hasDerivAt_coleHopf_mass hA hAm v (c + x) m).deriv]
  simp only [coleHopf_translate]

/-- The mass derivative is continuous in the spatial argument. This supplies
measurability for its average over an arbitrary external-field law. -/
theorem continuous_coleHopfMassDeriv {A : ℝ → ℝ}
    (hAc : Continuous A) (hA : HasLinearGrowth A) (m : ℝ) (v : ℝ≥0) :
    Continuous (coleHopfMassDeriv m v A) := by
  have hval : Continuous (fun x => coleHopf m v A x) := by
    simpa only [Function.comp_def, Real.toNNReal_coe, id_eq] using
      (continuous_coleHopf hAc hA m).comp
        (continuous_id.prodMk (continuous_const (y := (v : ℝ))))
  rcases eq_or_ne m 0 with rfl | hm
  · have hmean : Continuous (fun x => ∫ z, A (x + z) ∂gaussianReal 0 v) := by
      simpa only [coleHopfQ_zero, mul_one] using
        continuous_integral_mul_coleHopfQ' hAc hA 0 hAc hA.toHasExpGrowth v
    have hsq : Continuous (fun x => ∫ z, A (x + z) ^ 2 ∂gaussianReal 0 v) := by
      simpa only [coleHopfQ_zero, mul_one, Pi.pow_apply] using
        continuous_integral_mul_coleHopfQ' hAc hA 0 (hAc.pow 2)
          (hA.toHasExpGrowth.pow 2) v
    change Continuous (fun x => coleHopfMassDeriv 0 v A x)
    simpa [coleHopfMassDeriv] using (hsq.sub (hmean.pow 2)).div_const 2
  · have htilt := continuous_integral_mul_coleHopfQ' hAc hA m hAc hA.toHasExpGrowth v
    change Continuous (fun x => coleHopfMassDeriv m v A x)
    simp only [coleHopfMassDeriv, ite_eq_right hm]
    exact (continuous_const (y := 1 / m)).mul (htilt.sub hval)

/-- A single uniform Gaussian envelope controls the second mass derivative
for every Lipschitz input and every variance at most `V`. The constant depends
only on `V`, including at zero mass and zero variance. -/
theorem exists_uniform_coleHopf_mass_second_derivative_bound (V : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (A : ℝ → ℝ), Measurable A →
      (∀ x y, |A y - A x| ≤ |y - x|) → ∀ (v : ℝ≥0), v ≤ V → ∀ x : ℝ,
      ContDiffOn ℝ 2 (fun m => coleHopf m v A x) (Icc (0 : ℝ) 1) ∧
        ∀ m ∈ Icc (0 : ℝ) 1, |deriv (deriv (fun m => coleHopf m v A x)) m| ≤ M := by
  let Y : ℝ → ℝ := fun z => Real.sqrt V * |z|
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hY0 : ∀ z, 0 ≤ Y z := fun z => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hint : Integrable (fun z => Real.exp (2 * Y z)) (gaussianReal 0 1) := by
    simpa only [Y, ← mul_assoc] using
      integrable_exp_mul_abs_gaussianReal 0 1 (2 * Real.sqrt V)
  obtain ⟨M, hM, hbound⟩ := Aristotle.uniform_mass_second_derivative_bound
    hY (.of_forall hY0) hint
  refine ⟨M, hM, fun A hAm hA v hv x => ?_⟩
  have hX : Measurable (fun z => A (x + Real.sqrt v * z)) := by fun_prop
  have hcenter : ∀ z, |A (x + Real.sqrt v * z) - A x| ≤ Y z := by
    intro z
    calc
      _ ≤ |(x + Real.sqrt v * z) - x| := hA x _
      _ = Real.sqrt v * |z| := by
        rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Y z := mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (by exact_mod_cast hv)) (abs_nonneg _)
  have heq : (fun m => coleHopf m v A x) = Aristotle.massTransform (gaussianReal 0 1)
      (fun z => A (x + Real.sqrt v * z)) :=
    funext (fun m => coleHopf_eq_massTransform_standard hAm m v x)
  rw [heq]
  exact hbound (fun z => A (x + Real.sqrt v * z)) (A x) hX (.of_forall hcenter)

/-- A quadratic mass remainder, uniform over all one-Lipschitz inputs,
spatial arguments and variances below V. The coefficient depends only on V;
neither the input's additive constant nor a recursion level count enters it. -/
theorem exists_uniform_coleHopf_mass_taylor_bound (V : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (A : ℝ → ℝ), Measurable A →
      (∀ x y, |A y - A x| ≤ |y - x|) → ∀ (v : ℝ≥0), v ≤ V → ∀ x : ℝ,
      ∀ m ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        |coleHopf b v A x - coleHopf m v A x - coleHopfMassDeriv m v A x * (b - m)| ≤
          M * (b - m) ^ 2 := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_coleHopf_mass_second_derivative_bound V
  refine ⟨M / 2, by positivity, fun A hAm hLip v hv x m hm b hb => ?_⟩
  have hAg : HasLinearGrowth A := HasLinearGrowth.of_lipschitz
    (L := 1) (by simpa only [one_mul] using hLip)
  have hLipD : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |deriv (fun c => coleHopf c v A x) s - deriv (fun c => coleHopf c v A x) t| ≤
        M * |s - t| := by
    intro s hs t ht
    have hh := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (f := deriv (fun c => coleHopf c v A x))
      (fun c _ => (analyticAt_coleHopf_mass hAg hAm v x c).deriv.differentiableAt)
      (fun c hc => by simpa only [Real.norm_eq_abs] using (hbound A hAm hLip v hv x).2 c hc)
      ht hs
    simpa only [Real.norm_eq_abs] using hh
  have hh := Aristotle.abs_taylor_one_le zero_le_one hM.le
    (hbound A hAm hLip v hv x).1.continuousOn
    (fun c _ => (hasDerivAt_coleHopf_mass hAg hAm v x c).differentiableAt.hasDerivAt)
    hLipD hm hb
  rw [(hasDerivAt_coleHopf_mass hAg hAm v x m).deriv] at hh
  exact hh

/-- The first mass derivative and centered value have bounds depending only
on the variance ceiling. The neighborhood of `[0,1]` supports propagation
of mass derivatives through preceding fixed Cole-Hopf levels. -/
theorem exists_uniform_coleHopf_mass_first_derivative_bound (V : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (A : ℝ → ℝ), Measurable A →
      (∀ x y, |A y - A x| ≤ |y - x|) → ∀ (v : ℝ≥0), v ≤ V → ∀ x : ℝ,
      (∀ m ∈ Ioo (-3 : ℝ) 3, DifferentiableAt ℝ (fun b => coleHopf b v A x) m) ∧
      (∀ m ∈ Icc (-2 : ℝ) 2, |deriv (fun b => coleHopf b v A x) m| ≤ M) ∧
      ∀ m ∈ Icc (-2 : ℝ) 2, |coleHopf m v A x - A x| ≤ M := by
  let Y : ℝ → ℝ := fun z => Real.sqrt V * |z|
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hY0 : ∀ z, 0 ≤ Y z := fun z => mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hint : ∀ c : ℝ, Integrable (fun z => Real.exp (c * Y z)) (gaussianReal 0 1) := by
    intro c
    simpa only [Y, ← mul_assoc] using
      integrable_exp_mul_abs_gaussianReal 0 1 (c * Real.sqrt V)
  obtain ⟨M, hM, hbound⟩ := Aristotle.massTransform_deriv_bound hY hY0 hint
  refine ⟨M + 1, by linarith, fun A hAm hA v hv x => ?_⟩
  have hX : Measurable (fun z => A (x + Real.sqrt v * z)) := by fun_prop
  have hcenter : ∀ z, |A (x + Real.sqrt v * z) - A x| ≤ Y z := by
    intro z
    calc
      _ ≤ |(x + Real.sqrt v * z) - x| := hA x _
      _ = Real.sqrt v * |z| := by
        rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Y z := mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (by exact_mod_cast hv)) (abs_nonneg _)
  have hb := hbound (fun z => A (x + Real.sqrt v * z)) (A x) hX hcenter
  have heq : (fun m => coleHopf m v A x) = Aristotle.massTransform (gaussianReal 0 1)
      (fun z => A (x + Real.sqrt v * z)) :=
    funext (fun m => coleHopf_eq_massTransform_standard hAm m v x)
  rw [← heq] at hb
  have hMle : M ≤ M + 1 := le_add_of_nonneg_right zero_le_one
  exact ⟨hb.1, (fun m hm => (hb.2.1 m hm).trans hMle),
    fun m hm => (hb.2.2 m hm).trans hMle⟩

/-- A finite first field moment suffices to differentiate an averaged layer
on the admissible mass interval. The derivative bound is independent of the
realized field, so no exponential moment of its law is required. -/
theorem hasDerivWithinAt_integral_coleHopf_mass
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    (v : ℝ≥0) (x : ℝ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun b => ∫ h, coleHopf b v A (h + x) ∂μh)
      (∫ h, coleHopfMassDeriv m v A (h + x) ∂μh) (Icc (0 : ℝ) 1) m := by
  have hLip' : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  have hAc := (lipschitzWith_toNNReal_of_abs_sub_le hLip').continuous
  have hAg := HasLinearGrowth.of_lipschitz hLip'
  obtain ⟨M, _, hbound⟩ := exists_uniform_coleHopf_mass_first_derivative_bound v
  have hF : ∀ b : ℝ, Continuous (fun h => coleHopf b v A (h + x)) := by
    intro b
    simpa only [Function.comp_def, Real.toNNReal_coe, Pi.add_apply, id_eq] using
      (continuous_coleHopf hAc hAg b).comp
        ((continuous_id.add continuous_const).prodMk (continuous_const (y := (v : ℝ))))
  have hbase : Integrable (fun h => coleHopf 0 v A (h + x)) μh := by
    refine ((integrable_const |coleHopf 0 v A x|).add hμ.abs).mono'
      (hF 0).aestronglyMeasurable (.of_forall fun h => ?_)
    rw [Real.norm_eq_abs]
    have hb := abs_coleHopf_sub_le_of_lipschitz 0 hAm hLip' v x (h + x)
    have ha := abs_sub_abs_le_abs_sub (coleHopf 0 v A (h + x)) (coleHopf 0 v A x)
    simp only [id_eq, Pi.add_apply, one_mul, add_sub_cancel_right] at hb ⊢
    linarith
  refine Aristotle.hasDerivWithinAt_integral_Icc zero_lt_one hm
    (fun b _ => (hF b).aestronglyMeasurable)
    ((continuous_coleHopfMassDeriv hAc hAg m v).comp
      (continuous_id.add continuous_const)).aestronglyMeasurable
    hbase (integrable_const M) (.of_forall fun h b _ =>
      (hasDerivAt_coleHopf_mass hAg hAm v (h + x) b).hasDerivWithinAt) ?_
  refine .of_forall fun h b hb => ?_
  rw [← (hasDerivAt_coleHopf_mass hAg hAm v (h + x) b).deriv]
  exact (hbound A hAm hLip v le_rfl (h + x)).2.1 b ⟨by linarith [hb.1], by linarith [hb.2]⟩

/-- The transported mass derivative, with the actual preceding cascade tilt.
This is the operator form of the recursive differentiation in (14.240). -/
noncomputable def coleHopfIterateMassDeriv {j : ℕ} (ms : Fin j → ℝ)
    (vs : Fin j → ℝ≥0) (v : ℝ≥0) (A : ℝ → ℝ) (m x : ℝ) : ℝ :=
  ∫ zs, coleHopfMassDeriv m v A (x + ∑ p, zs p)
    ∂cascadeTiltMeasure j ms (fun p => gaussianReal 0 (vs p))
      (fun zs => ENNReal.ofReal (Real.exp (coleHopf m v A (x + ∑ p, zs p))))

/-- Propagate a concrete mass variation through every preceding positive-mass
Cole-Hopf level. The varied mass may be zero or one. -/
theorem hasDerivAt_coleHopfIterate_mass_layer_of_mem_Ioo {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    (v : ℝ≥0) {m : ℝ} (hm : m ∈ Ioo (-2 : ℝ) 2) (x : ℝ) :
    HasDerivAt (fun b => coleHopfIterate j ms vs (coleHopf b v A) x)
      (coleHopfIterateMassDeriv ms vs v A m x) m := by
  have hLip' : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  have hAc := (lipschitzWith_toNNReal_of_abs_sub_le hLip').continuous
  have hAg := HasLinearGrowth.of_lipschitz hLip'
  obtain ⟨M, _, hbound⟩ := exists_uniform_coleHopf_mass_first_derivative_bound v
  let δ : ℝ := min (m + 2) (2 - m)
  have hδ : 0 < δ := lt_min (by linarith [hm.1]) (by linarith [hm.2])
  refine hasDerivAt_coleHopfIterate_ball ms vs (G := fun b => coleHopf b v A)
    (G' := fun b => coleHopfMassDeriv b v A) (L := 1) (C := M) (δ := δ)
    hδ hpos hle
    (fun b => (continuous_coleHopfMassDeriv hAc hAg b v).measurable)
    (fun b _ y => hasDerivAt_coleHopf_mass hAg hAm v y b) ?_ ?_ x
  · intro b hb y
    rw [Metric.mem_ball, Real.dist_eq] at hb
    have hab := abs_lt.1 hb
    have hδ1 : δ ≤ m + 2 := min_le_left _ _
    have hδ2 : δ ≤ 2 - m := min_le_right _ _
    rw [← (hasDerivAt_coleHopf_mass hAg hAm v y b).deriv]
    exact (hbound A hAm hLip v le_rfl y).2.1 b
      ⟨by linarith [hab.1], by linarith [hab.2]⟩
  · exact fun b x y => abs_coleHopf_sub_le_of_lipschitz b hAm hLip' v x y

/-- The admissible mass interval has a genuine neighborhood on which the
propagated mass derivative exists, also at mass zero and mass one. -/
theorem hasDerivAt_coleHopfIterate_mass_layer {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    (v : ℝ≥0) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    HasDerivAt (fun b => coleHopfIterate j ms vs (coleHopf b v A) x)
      (coleHopfIterateMassDeriv ms vs v A m x) m :=
  hasDerivAt_coleHopfIterate_mass_layer_of_mem_Ioo ms vs hpos hle hAm hLip v
    ⟨by linarith [hm.1], by linarith [hm.2]⟩ x

/-- With no preceding levels, the transported mass derivative is the actual
single-layer derivative. -/
theorem coleHopfIterateMassDeriv_zero {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|) (v : ℝ≥0)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    coleHopfIterateMassDeriv (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → ℝ≥0) v A m x = coleHopfMassDeriv m v A x := by
  have hd := hasDerivAt_coleHopfIterate_mass_layer
    (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0)
    (fun p => Fin.elim0 p) (fun p => Fin.elim0 p) hAm hLip v hm x
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  exact hd.unique (hasDerivAt_coleHopf_mass (HasLinearGrowth.of_lipschitz hL) hAm v x m)

/-- The propagated derivative bound also holds on a neighborhood of the
admissible mass interval. Its constant depends only on the variance ceiling. -/
theorem exists_uniform_coleHopfIterate_mass_derivative_bound_neighborhood (V : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (j : ℕ) (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0),
      (∀ i, 0 < ms i) → (∀ i, ms i ≤ 1) → ∀ (A : ℝ → ℝ), Measurable A →
      (∀ x y, |A y - A x| ≤ |y - x|) → ∀ (v : ℝ≥0), v ≤ V →
      ∀ m ∈ Icc (-2 : ℝ) 2, ∀ x : ℝ, |coleHopfIterateMassDeriv ms vs v A m x| ≤ M := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_coleHopf_mass_first_derivative_bound V
  refine ⟨M, hM, fun j ms vs hpos hle A hAm hLip v hv m hm x => ?_⟩
  have hLip' : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  have hAg := HasLinearGrowth.of_lipschitz hLip'
  have hG := abs_coleHopf_sub_le_of_lipschitz m hAm hLip' v
  apply abs_integral_cascadeTiltMeasure_le ms vs hpos hle
    (lipschitzWith_toNNReal_of_abs_sub_le hG).continuous.measurable hG x
  intro y
  rw [← (hasDerivAt_coleHopf_mass hAg hAm v y m).deriv]
  exact (hbound A hAm hLip v hv y).2.1 m hm

/-- The cascade average of the mass derivative has a uniform bound. Its
constant depends only on the varied variance ceiling, not on the preceding
level count, masses, variances, or realized external field. -/
theorem exists_uniform_coleHopfIterate_mass_derivative_bound (V : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (j : ℕ) (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0),
      (∀ i, 0 < ms i) → (∀ i, ms i ≤ 1) → ∀ (A : ℝ → ℝ), Measurable A →
      (∀ x y, |A y - A x| ≤ |y - x|) → ∀ (v : ℝ≥0), v ≤ V →
      ∀ m ∈ Icc (0 : ℝ) 1, ∀ x : ℝ, |coleHopfIterateMassDeriv ms vs v A m x| ≤ M := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_coleHopf_mass_first_derivative_bound V
  refine ⟨M, hM, fun j ms vs hpos hle A hAm hLip v hv m hm x => ?_⟩
  have hLip' : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  have hAg := HasLinearGrowth.of_lipschitz hLip'
  have hG : ∀ x y, |coleHopf m v A y - coleHopf m v A x| ≤ 1 * |y - x| :=
    abs_coleHopf_sub_le_of_lipschitz m hAm hLip' v
  have hGm := (lipschitzWith_toNNReal_of_abs_sub_le hG).continuous.measurable
  apply abs_integral_cascadeTiltMeasure_le ms vs hpos hle hGm hG x
  intro y
  rw [← (hasDerivAt_coleHopf_mass hAg hAm v y m).deriv]
  exact (hbound A hAm hLip v hv y).2.1 m ⟨by linarith [hm.1], by linarith [hm.2]⟩

/-- The transported mass derivative is measurable in the spatial parameter.
This avoids imposing regularity on the external-field law. -/
theorem measurable_coleHopfIterateMassDeriv_of_mem_Ioo {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    (v : ℝ≥0) {m : ℝ} (hm : m ∈ Ioo (-2 : ℝ) 2) :
    Measurable (coleHopfIterateMassDeriv ms vs v A m) := by
  apply measurable_deriv_param
    (Φ := fun b x => coleHopfIterate j ms vs (coleHopf b v A) x)
    (fun b => ?_) (fun x =>
      hasDerivAt_coleHopfIterate_mass_layer_of_mem_Ioo ms vs hpos hle hAm hLip v hm x)
  have hLip' : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  have hG := abs_coleHopf_sub_le_of_lipschitz b hAm hLip' v
  exact (lipschitzWith_toNNReal_of_abs_sub_le
    (abs_coleHopfIterate_sub_le j ms vs
      (lipschitzWith_toNNReal_of_abs_sub_le hG).continuous.measurable hG)).continuous.measurable

/-- Measurability of the transported derivative on the admissible mass interval. -/
theorem measurable_coleHopfIterateMassDeriv {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    (v : ℝ≥0) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    Measurable (coleHopfIterateMassDeriv ms vs v A m) :=
  measurable_coleHopfIterateMassDeriv_of_mem_Ioo ms vs hpos hle hAm hLip v
    ⟨by linarith [hm.1], by linarith [hm.2]⟩

/-- Differentiate a propagated mass layer averaged over any integrable spatial
shift. This also applies to a field together with its independent root Gaussian. -/
theorem hasDerivAt_integral_coleHopfIterate_mass_layer_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hHm : Measurable H) (hH : Integrable H μ)
    {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    (v : ℝ≥0) (x : ℝ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun b => ∫ ω, coleHopfIterate j ms vs (coleHopf b v A) (H ω + x) ∂μ)
      (∫ ω, coleHopfIterateMassDeriv ms vs v A m (H ω + x) ∂μ) m := by
  have hLip' : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  have hF : ∀ b, ∀ y z,
      |coleHopfIterate j ms vs (coleHopf b v A) z -
        coleHopfIterate j ms vs (coleHopf b v A) y| ≤ 1 * |z - y| := by
    intro b
    have hG := abs_coleHopf_sub_le_of_lipschitz b hAm hLip' v
    exact abs_coleHopfIterate_sub_le j ms vs
      (lipschitzWith_toNNReal_of_abs_sub_le hG).continuous.measurable hG
  have hFm : ∀ b, Measurable (fun ω => coleHopfIterate j ms vs (coleHopf b v A) (H ω + x)) :=
    fun b => (lipschitzWith_toNNReal_of_abs_sub_le (hF b)).continuous.measurable.comp
      (hHm.add measurable_const)
  have hbase : Integrable (fun ω => coleHopfIterate j ms vs (coleHopf m v A) (H ω + x)) μ := by
    refine ((integrable_const |coleHopfIterate j ms vs (coleHopf m v A) x|).add hH.abs).mono'
      (hFm m).aestronglyMeasurable (.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have hb := hF m x (H ω + x)
    have ha := abs_sub_abs_le_abs_sub
      (coleHopfIterate j ms vs (coleHopf m v A) (H ω + x))
      (coleHopfIterate j ms vs (coleHopf m v A) x)
    simp only [Pi.add_apply, one_mul, add_sub_cancel_right] at hb ⊢
    linarith
  obtain ⟨M, _, hbound⟩ := exists_uniform_coleHopfIterate_mass_derivative_bound_neighborhood v
  have hball : ∀ b ∈ Metric.ball m (1 / 2), b ∈ Ioo (-2 : ℝ) 2 := by
    intro b hb
    rw [Metric.mem_ball, Real.dist_eq] at hb
    have hab := abs_lt.1 hb
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds m (by norm_num : (0 : ℝ) < 1 / 2))
    (F' := fun b ω => coleHopfIterateMassDeriv ms vs v A b (H ω + x))
    (bound := fun _ => M) (.of_forall fun b => (hFm b).aestronglyMeasurable)
    hbase ?_ ?_ (integrable_const M) ?_).2
  · exact ((measurable_coleHopfIterateMassDeriv ms vs hpos hle hAm hLip v hm).comp
      (hHm.add measurable_const)).aestronglyMeasurable
  · exact .of_forall fun ω b hb => by
      rw [Real.norm_eq_abs]
      exact hbound j ms vs hpos hle A hAm hLip v le_rfl b
        (Ioo_subset_Icc_self (hball b hb)) (H ω + x)
  · exact .of_forall fun ω b hb =>
      hasDerivAt_coleHopfIterate_mass_layer_of_mem_Ioo
        ms vs hpos hle hAm hLip v (hball b hb) (H ω + x)

/-- A single layer can be differentiated under the law in an open mass
neighborhood, including when the varied mass is zero. -/
theorem hasDerivAt_integral_coleHopf_mass_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hHm : Measurable H) (hH : Integrable H μ)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    (v : ℝ≥0) (x : ℝ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun b => ∫ ω, coleHopf b v A (H ω + x) ∂μ)
      (∫ ω, coleHopfMassDeriv m v A (H ω + x) ∂μ) m := by
  simpa only [coleHopfIterate_zero, coleHopfIterateMassDeriv_zero hAm hLip v hm] using
    hasDerivAt_integral_coleHopfIterate_mass_layer_comp hHm hH
      (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0)
      (fun p => Fin.elim0 p) (fun p => Fin.elim0 p) hAm hLip v x hm

/-- The same averaged derivative restricted to the admissible mass interval. -/
theorem hasDerivWithinAt_integral_coleHopfIterate_mass_layer_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hHm : Measurable H) (hH : Integrable H μ)
    {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    (v : ℝ≥0) (x : ℝ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun b => ∫ ω, coleHopfIterate j ms vs (coleHopf b v A) (H ω + x) ∂μ)
      (∫ ω, coleHopfIterateMassDeriv ms vs v A m (H ω + x) ∂μ)
      (Icc (0 : ℝ) 1) m := by
  have hLip' : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  have hF : ∀ b, ∀ y z,
      |coleHopfIterate j ms vs (coleHopf b v A) z -
        coleHopfIterate j ms vs (coleHopf b v A) y| ≤ 1 * |z - y| := by
    intro b
    have hG := abs_coleHopf_sub_le_of_lipschitz b hAm hLip' v
    exact abs_coleHopfIterate_sub_le j ms vs
      (lipschitzWith_toNNReal_of_abs_sub_le hG).continuous.measurable hG
  have hFm : ∀ b, Measurable (fun ω => coleHopfIterate j ms vs (coleHopf b v A) (H ω + x)) :=
    fun b => (lipschitzWith_toNNReal_of_abs_sub_le (hF b)).continuous.measurable.comp
      (hHm.add measurable_const)
  have hbase : Integrable (fun ω => coleHopfIterate j ms vs (coleHopf 0 v A) (H ω + x)) μ := by
    refine ((integrable_const |coleHopfIterate j ms vs (coleHopf 0 v A) x|).add hH.abs).mono'
      (hFm 0).aestronglyMeasurable (.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have hb := hF 0 x (H ω + x)
    have ha := abs_sub_abs_le_abs_sub
      (coleHopfIterate j ms vs (coleHopf 0 v A) (H ω + x))
      (coleHopfIterate j ms vs (coleHopf 0 v A) x)
    simp only [Pi.add_apply, one_mul, add_sub_cancel_right] at hb ⊢
    linarith
  obtain ⟨M, _, hbound⟩ := exists_uniform_coleHopfIterate_mass_derivative_bound v
  exact Aristotle.hasDerivWithinAt_integral_Icc zero_lt_one hm
    (fun b _ => (hFm b).aestronglyMeasurable)
    ((measurable_coleHopfIterateMassDeriv ms vs hpos hle hAm hLip v hm).comp
      (hHm.add measurable_const)).aestronglyMeasurable
    hbase (integrable_const M) (.of_forall fun ω b hb =>
      (hasDerivAt_coleHopfIterate_mass_layer
        ms vs hpos hle hAm hLip v hb (H ω + x)).hasDerivWithinAt)
    (.of_forall fun ω b hb => hbound j ms vs hpos hle A hAm hLip v le_rfl b hb (H ω + x))

/-- Differentiation of the cascade-propagated mass variation under a site law
with a finite first moment, including admissible one-sided endpoint derivatives.
The domination is uniform in the realized field. -/
theorem hasDerivWithinAt_integral_coleHopfIterate_mass_layer
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    (v : ℝ≥0) (x : ℝ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun b => ∫ h, coleHopfIterate j ms vs (coleHopf b v A) (h + x) ∂μh)
      (∫ h, coleHopfIterateMassDeriv ms vs v A m (h + x) ∂μh)
      (Icc (0 : ℝ) 1) m :=
  hasDerivWithinAt_integral_coleHopfIterate_mass_layer_comp measurable_id hμ
    ms vs hpos hle hAm hLip v x hm

/-- Average the propagated derivative over the i.i.d. site law and its
independent root Gaussian, in the nesting used by the Parisi functional. -/
theorem hasDerivWithinAt_integral_integral_coleHopfIterate_mass_layer
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    (v v₀ : ℝ≥0) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun b => ∫ h, ∫ z₀, coleHopfIterate j ms vs (coleHopf b v A) (h + z₀)
        ∂gaussianReal 0 v₀ ∂μh)
      (∫ h, ∫ z₀, coleHopfIterateMassDeriv ms vs v A m (h + z₀)
        ∂gaussianReal 0 v₀ ∂μh) (Icc (0 : ℝ) 1) m := by
  let μ := μh.prod (gaussianReal 0 v₀)
  let H : ℝ × ℝ → ℝ := fun p => p.1 + p.2
  have hHm : Measurable H := measurable_fst.add measurable_snd
  have hzg : HasLinearGrowth id := ⟨0, 1, zero_le_one, by simp⟩
  have hz : Integrable id (gaussianReal 0 v₀) :=
    hzg.toHasExpGrowth.integrable_gaussianReal measurable_id.aestronglyMeasurable
  have hH : Integrable H μ := (hμ.comp_fst _).add (hz.comp_snd _)
  have hd := hasDerivWithinAt_integral_coleHopfIterate_mass_layer_comp hHm hH
    ms vs hpos hle hAm hLip v 0 hm
  have hLip' : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  have hF : ∀ b, Integrable
      (fun p : ℝ × ℝ => coleHopfIterate j ms vs (coleHopf b v A) (H p)) μ := by
    intro b
    have hG := abs_coleHopf_sub_le_of_lipschitz b hAm hLip' v
    have hL := abs_coleHopfIterate_sub_le j ms vs
      (lipschitzWith_toNNReal_of_abs_sub_le hG).continuous.measurable hG
    refine ((integrable_const |coleHopfIterate j ms vs (coleHopf b v A) 0|).add hH.abs).mono'
      ((lipschitzWith_toNNReal_of_abs_sub_le hL).continuous.measurable.comp
        hHm).aestronglyMeasurable
      (.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    have hb := hL 0 (H p)
    have ha := abs_sub_abs_le_abs_sub
      (coleHopfIterate j ms vs (coleHopf b v A) (H p))
      (coleHopfIterate j ms vs (coleHopf b v A) 0)
    simp only [Pi.add_apply, one_mul, sub_zero] at hb ⊢
    linarith
  obtain ⟨M, _, hbound⟩ := exists_uniform_coleHopfIterate_mass_derivative_bound v
  have hD : Integrable (fun p : ℝ × ℝ => coleHopfIterateMassDeriv ms vs v A m (H p)) μ := by
    refine Integrable.of_bound
      ((measurable_coleHopfIterateMassDeriv ms vs hpos hle hAm hLip v hm).comp
        hHm).aestronglyMeasurable
      M (.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    exact hbound j ms vs hpos hle A hAm hLip v le_rfl m hm (H p)
  have heq : (fun b => ∫ p, coleHopfIterate j ms vs (coleHopf b v A) (H p) ∂μ) =
      fun b => ∫ h, ∫ z₀, coleHopfIterate j ms vs (coleHopf b v A) (h + z₀)
        ∂gaussianReal 0 v₀ ∂μh := by
    funext b
    exact integral_prod _ (hF b)
  have hd' : HasDerivWithinAt
      (fun b => ∫ p, coleHopfIterate j ms vs (coleHopf b v A) (H p) ∂μ)
      (∫ p, coleHopfIterateMassDeriv ms vs v A m (H p) ∂μ) (Icc (0 : ℝ) 1) m := by
    simpa only [add_zero] using hd
  have hdeq : (∫ p, coleHopfIterateMassDeriv ms vs v A m (H p) ∂μ) =
      ∫ h, ∫ z₀, coleHopfIterateMassDeriv ms vs v A m (h + z₀)
        ∂gaussianReal 0 v₀ ∂μh := integral_prod _ hD
  rw [heq, hdeq] at hd'
  exact hd'

/-- Every actual suffix preserves the terminal log-cosh Lipschitz constant,
with no restriction on the level masses. -/
theorem abs_parisiQSuffix_sub_le (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (x y : ℝ) :
    |parisiQSuffix ξ h ms qs r y - parisiQSuffix ξ h ms qs r x| ≤ |y - x| := by
  exact (abs_coleHopfIterate_sub_le (k - r.val) _ _
    (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal h))
    (L := 1) (fun x y => by simpa only [one_mul] using
      abs_parisiLogCoshTerminal_sub_le h x y) x y).trans_eq (one_mul _)

/-- Differentiation under the site-law integral for the concrete suffix layer.
Only a probability law and a finite first moment are needed. This is a local
component of the random-field mass variation in (14.238)-(14.240). -/
theorem hasDerivWithinAt_integral_parisiQSuffix_mass
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (v : ℝ≥0) (x : ℝ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun b => ∫ h, coleHopf b v (parisiQSuffix ξ h ms qs r) x ∂μh)
      (∫ h, coleHopfMassDeriv m v (parisiQSuffix ξ h ms qs r) x ∂μh)
      (Icc (0 : ℝ) 1) m := by
  have hLip := abs_parisiQSuffix_sub_le ξ 0 ms qs r
  have hLip' : ∀ x y, |parisiQSuffix ξ 0 ms qs r y - parisiQSuffix ξ 0 ms qs r x|
      ≤ 1 * |y - x| := by simpa only [one_mul] using hLip
  have hAm := (lipschitzWith_toNNReal_of_abs_sub_le hLip').continuous.measurable
  have hAg := HasLinearGrowth.of_lipschitz hLip'
  have hshift : ∀ h, parisiQSuffix ξ h ms qs r =
      fun y => parisiQSuffix ξ 0 ms qs r (h + y) :=
    fun h => funext (parisiQSuffix_translate ξ h ms qs r)
  have hF : (fun b => ∫ h, coleHopf b v (parisiQSuffix ξ h ms qs r) x ∂μh) =
      fun b => ∫ h, coleHopf b v (parisiQSuffix ξ 0 ms qs r) (h + x) ∂μh := by
    funext b
    exact integral_congr_ae (.of_forall fun h => by
      change coleHopf b v (parisiQSuffix ξ h ms qs r) x =
        coleHopf b v (parisiQSuffix ξ 0 ms qs r) (h + x)
      rw [hshift h, coleHopf_translate])
  have hD : (fun h => coleHopfMassDeriv m v (parisiQSuffix ξ h ms qs r) x) =
      fun h => coleHopfMassDeriv m v (parisiQSuffix ξ 0 ms qs r) (h + x) := by
    funext h
    rw [hshift h, coleHopfMassDeriv_translate hAg hAm]
  rw [hF, hD]
  exact hasDerivWithinAt_integral_coleHopf_mass hμ hAm hLip v x hm

/-- The uniform mass Taylor constant applies to the concrete Parisi suffix,
independently of the field, the level count, and all recursion parameters.
Only the upper bound `V` on the varied Gaussian layer enters the constant. -/
theorem exists_uniform_parisiQSuffix_mass_second_derivative_bound (V : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (ξ : ℝ → ℝ) (h : ℝ) (k : ℕ)
      (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
      (v : ℝ≥0), v ≤ V → ∀ x : ℝ,
      ContDiffOn ℝ 2 (fun m => coleHopf m v (parisiQSuffix ξ h ms qs r) x)
        (Icc (0 : ℝ) 1) ∧ ∀ m ∈ Icc (0 : ℝ) 1,
        |deriv (deriv (fun m => coleHopf m v (parisiQSuffix ξ h ms qs r) x)) m| ≤ M := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_coleHopf_mass_second_derivative_bound V
  refine ⟨M, hM, fun ξ h k ms qs r v hv x => ?_⟩
  have hLip := abs_parisiQSuffix_sub_le ξ h ms qs r
  exact hbound _ (lipschitzWith_toNNReal_of_abs_sub_le
    (L := 1) (by simpa only [one_mul] using hLip)).continuous.measurable hLip v hv x

/-- Averaging the uniform quadratic remainder requires only an integrable
spatial shift. In particular an arbitrary finite-first-moment field and an
independent root Gaussian are allowed, with no exponential field moment. -/
theorem exists_uniform_integral_coleHopf_mass_taylor_bound (V : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {H : Ω → ℝ},
      Measurable H → Integrable H μ → ∀ (A : ℝ → ℝ), Measurable A →
      (∀ x y, |A y - A x| ≤ |y - x|) → ∀ (v : ℝ≥0), v ≤ V →
      ∀ m ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        |(∫ ω, coleHopf b v A (H ω) ∂μ) - (∫ ω, coleHopf m v A (H ω) ∂μ) -
          (∫ ω, coleHopfMassDeriv m v A (H ω) ∂μ) * (b - m)| ≤ M * (b - m) ^ 2 := by
  obtain ⟨M, hM, hTaylor⟩ := exists_uniform_coleHopf_mass_taylor_bound V
  obtain ⟨C, _, hbound⟩ := exists_uniform_coleHopf_mass_first_derivative_bound V
  refine ⟨M, hM, ?_⟩
  intro Ω _ μ _ H hHm hH A hAm hLip v hv m hm b hb
  have hLip' : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  have hAc := (lipschitzWith_toNNReal_of_abs_sub_le hLip').continuous
  have hAg := HasLinearGrowth.of_lipschitz hLip'
  have hF : ∀ c, Integrable (fun ω => coleHopf c v A (H ω)) μ := by
    intro c
    have hL := abs_coleHopf_sub_le_of_lipschitz c hAm hLip' v
    refine ((integrable_const |coleHopf c v A 0|).add hH.abs).mono'
      ((lipschitzWith_toNNReal_of_abs_sub_le hL).continuous.measurable.comp
        hHm).aestronglyMeasurable (.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have hl := hL 0 (H ω)
    have ha := abs_sub_abs_le_abs_sub (coleHopf c v A (H ω)) (coleHopf c v A 0)
    simp only [Pi.add_apply, one_mul, sub_zero] at hl ⊢
    linarith
  have hD : Integrable (fun ω => coleHopfMassDeriv m v A (H ω)) μ := by
    refine Integrable.of_bound
      ((continuous_coleHopfMassDeriv hAc hAg m v).measurable.comp
        hHm).aestronglyMeasurable C (.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, ← (hasDerivAt_coleHopf_mass hAg hAm v (H ω) m).deriv]
    exact (hbound A hAm hLip v hv (H ω)).2.1 m ⟨by linarith [hm.1], by linarith [hm.2]⟩
  have hh : |∫ ω, coleHopf b v A (H ω) - coleHopf m v A (H ω) -
      coleHopfMassDeriv m v A (H ω) * (b - m) ∂μ| ≤ M * (b - m) ^ 2 := by
    have h := norm_integral_le_of_norm_le_const
      (μ := μ) (C := M * (b - m) ^ 2)
      (f := fun ω => coleHopf b v A (H ω) - coleHopf m v A (H ω) -
        coleHopfMassDeriv m v A (H ω) * (b - m))
      (.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using hTaylor A hAm hLip v hv (H ω) m hm b hb)
    simpa [Real.norm_eq_abs] using h
  have he : (∫ ω, coleHopf b v A (H ω) - coleHopf m v A (H ω) -
      coleHopfMassDeriv m v A (H ω) * (b - m) ∂μ) =
      (∫ ω, coleHopf b v A (H ω) - coleHopf m v A (H ω) ∂μ) -
        (∫ ω, coleHopfMassDeriv m v A (H ω) * (b - m) ∂μ) :=
    integral_sub ((hF b).sub (hF m)) (hD.mul_const (b - m))
  rw [he, integral_sub (hF b) (hF m), integral_mul_const] at hh
  exact hh

end SpinGlass
