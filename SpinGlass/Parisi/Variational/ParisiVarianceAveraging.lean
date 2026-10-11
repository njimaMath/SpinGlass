import SpinGlass.Parisi.Variational.ParisiVarianceResponse

/-!
# Averaging the concrete variance response

The local spatial moments have bounds uniform in variance and position.
Consequently their variance derivatives can be averaged against any fixed
probability measure, including the preceding cascade tilt. The assumptions on
spatial regularity are discharged for the actual Parisi suffix below.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The actual split moment is continuous in the evaluation point. -/
theorem continuous_coleHopfSplitSpatialMoment {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 4) (m a v : ℝ) :
    Continuous (fun x => coleHopfSplitSpatialMoment j m a A x v) := by
  obtain ⟨C, hC⟩ := hb
  have hB := contDiff_four_coleHopf hA hC m v.toNNReal
  obtain ⟨K, hK⟩ := exists_bound_iteratedDeriv_coleHopf_four hA hC m v.toNNReal
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  have hBL := abs_coleHopf_sub_le_of_lipschitz m hA.continuous.measurable hL v.toNNReal
  have hG : HasExpGrowth (fun x => (iteratedDeriv j (coleHopf m v.toNNReal A) x) ^ 2) :=
    HasExpGrowth.of_bounded fun x => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hK j hj x) 2
  have hGj := hB.continuous_iteratedDeriv j (by exact_mod_cast (Finset.mem_Icc.1 hj).2)
  exact continuous_integral_mul_coleHopfQ' hB.continuous
    (HasLinearGrowth.of_lipschitz hBL) m (hGj.pow 2) hG (a - v).toNNReal

/-- Bounds for the two moments which dominate the variance derivatives.
They are independent of the split variance and evaluation point. The suffix
constant `C` is fixed here; no global MIN uniformity is asserted. -/
theorem coleHopfSplitSpatialMoment_one_two_bounds {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (a v x : ℝ) :
    |coleHopfSplitSpatialMoment 1 m a A x v| ≤ C ^ 2 ∧
      |coleHopfSplitSpatialMoment 2 m a A x v| ≤ (C + 2 * C ^ 2) ^ 2 := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hBL := abs_coleHopf_sub_le_of_lipschitz m hA.continuous.measurable hL v.toNNReal
  have hBc := (lipschitzWith_toNNReal_of_abs_sub_le hBL).continuous
  have hBg := HasLinearGrowth.of_lipschitz hBL
  have hB4 := contDiff_four_coleHopf hA hb m v.toNNReal
  have hb1 : ∀ y, |iteratedDeriv 1 (coleHopf m v.toNNReal A) y| ≤ C :=
    fun y => (iteratedDeriv_coleHopf_one_two_bounds hA hb m v.toNNReal y).1
  have hb2 : ∀ y, |iteratedDeriv 2 (coleHopf m v.toNNReal A) y| ≤ C + 2 * C ^ 2 := by
    intro y
    have h := (iteratedDeriv_coleHopf_one_two_bounds hA hb m v.toNNReal y).2
    rw [abs_of_nonneg hm.1] at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right hm.2 (sq_nonneg C)])
  constructor
  · exact abs_integral_mul_coleHopfQ_le' hBg hBc.measurable m
      ((hB4.continuous_iteratedDeriv 1 (by norm_num)).pow 2).measurable
      (fun y => by rw [Pi.pow_apply, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb1 y) 2)
      (a - v).toNNReal x
  · exact abs_integral_mul_coleHopfQ_le' hBg hBc.measurable m
      ((hB4.continuous_iteratedDeriv 2 (by norm_num)).pow 2).measurable
      (fun y => by rw [Pi.pow_apply, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb2 y) 2)
      (a - v).toNNReal x

/-- Conditional analytic bridge for a fixed regular Lipschitz input. Its
hypotheses are derived from the actual suffix in the book-level specialization. -/
theorem hasDerivWithinAt_coleHopfSplitMassResponse {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m a v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivWithinAt (coleHopfSplitMassResponse m a A x)
      (coleHopfSplitSpatialMoment 1 m a A x v / 2) (Icc (0 : ℝ) a) v := by
  rw [coleHopfSplitMassResponse_eq, coleHopfSplitSpatialMoment_eq hA.continuous.measurable hLip]
  exact Aristotle.hasDerivWithinAt_splitMassResponse hA hb hm ha hv x

/-- Conditional moment dissipation for a fixed regular Lipschitz input. -/
theorem hasDerivWithinAt_coleHopfSplitSpatialMoment {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m a v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivWithinAt (coleHopfSplitSpatialMoment 1 m a A x)
      (-coleHopfSplitSpatialMoment 2 m a A x v) (Icc (0 : ℝ) a) v := by
  rw [coleHopfSplitSpatialMoment_eq hA.continuous.measurable hLip,
    coleHopfSplitSpatialMoment_eq hA.continuous.measurable hLip]
  exact Aristotle.hasDerivWithinAt_splitSpatialMoment hA hb hm ha hv x

/-- Variance differentiation under any fixed probability law. A measurable
evaluation point suffices because the response and its derivative are bounded. -/
theorem hasDerivWithinAt_integral_coleHopfSplitMassResponse_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m a v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) a) :
    HasDerivWithinAt (fun w => ∫ ω, coleHopfSplitMassResponse m a A (H ω) w ∂μ)
      ((∫ ω, coleHopfSplitSpatialMoment 1 m a A (H ω) v ∂μ) / 2)
      (Icc (0 : ℝ) a) v := by
  obtain ⟨C, hC⟩ := hb
  have hbase : Integrable (fun ω => coleHopfSplitMassResponse m a A (H ω) 0) μ := by
    simpa only [coleHopfSplitMassResponse_zero] using integrable_const (0 : ℝ)
  have hd := Aristotle.hasDerivWithinAt_integral_Icc ha hv
    (fun w _ => ((measurable_coleHopfSplitMassResponse hA.continuous.measurable hLip hm a w).comp
      hH).aestronglyMeasurable)
    (((continuous_coleHopfSplitSpatialMoment hA ⟨C, hC⟩ hLip
      (j := 1) (by norm_num) m a v).measurable.comp hH).div_const 2).aestronglyMeasurable
    hbase (integrable_const (C ^ 2 / 2))
    (.of_forall fun ω w hw => hasDerivWithinAt_coleHopfSplitMassResponse
      hA ⟨C, hC⟩ hLip hm ha hw (H ω))
    (.of_forall fun ω w _ => by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right
        (coleHopfSplitSpatialMoment_one_two_bounds hA hC hLip hm a w (H ω)).1 (by norm_num))
  simpa only [integral_div, Function.comp_def] using hd

/-- Dissipation remains valid after averaging the actual spatial moment. -/
theorem hasDerivWithinAt_integral_coleHopfSplitSpatialMoment_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m a v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) a) :
    HasDerivWithinAt (fun w => ∫ ω, coleHopfSplitSpatialMoment 1 m a A (H ω) w ∂μ)
      (-(∫ ω, coleHopfSplitSpatialMoment 2 m a A (H ω) v ∂μ)) (Icc (0 : ℝ) a) v := by
  obtain ⟨C, hC⟩ := hb
  have hmeas : ∀ j ∈ Finset.Icc 1 4, ∀ w,
      Measurable (fun ω => coleHopfSplitSpatialMoment j m a A (H ω) w) := fun j hj w =>
    (continuous_coleHopfSplitSpatialMoment hA ⟨C, hC⟩ hLip hj m a w).measurable.comp hH
  have hbase : Integrable (fun ω => coleHopfSplitSpatialMoment 1 m a A (H ω) 0) μ :=
    Integrable.of_bound (hmeas 1 (by norm_num) 0).aestronglyMeasurable (C ^ 2)
      (.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact (coleHopfSplitSpatialMoment_one_two_bounds hA hC hLip hm a 0 (H ω)).1)
  have hd := Aristotle.hasDerivWithinAt_integral_Icc ha hv
    (fun w _ => (hmeas 1 (by norm_num) w).aestronglyMeasurable)
    (hmeas 2 (by norm_num) v).neg.aestronglyMeasurable hbase
    (integrable_const ((C + 2 * C ^ 2) ^ 2))
    (.of_forall fun ω w hw => hasDerivWithinAt_coleHopfSplitSpatialMoment
      hA ⟨C, hC⟩ hLip hm ha hw (H ω))
    (.of_forall fun ω w _ => by
      rw [abs_neg]
      exact (coleHopfSplitSpatialMoment_one_two_bounds hA hC hLip hm a w (H ω)).2)
  simpa only [integral_neg] using hd

/-- The variance derivative for the actual suffix under an arbitrary fixed
probability law, with all regularity discharged from the recursion. -/
theorem hasDerivWithinAt_integral_parisiQSuffix_splitMassResponse_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    {m a v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) a) :
    HasDerivWithinAt
      (fun w => ∫ ω, coleHopfSplitMassResponse m a (parisiQSuffix ξ h ms qs r) (H ω) w ∂μ)
      ((∫ ω, coleHopfSplitSpatialMoment 1 m a (parisiQSuffix ξ h ms qs r) (H ω) v ∂μ) / 2)
      (Icc (0 : ℝ) a) v := by
  obtain ⟨hA, hb⟩ := parisiQSuffix_spatial_regular_four ξ h ms qs r
  exact hasDerivWithinAt_integral_coleHopfSplitMassResponse_comp hH hA hb
    (abs_parisiQSuffix_sub_le ξ h ms qs r) hm ha hv

/-- The response is integrable under any probability law of its evaluation
point. Its uniform bound removes any moment requirement on that law. -/
theorem integrable_coleHopfSplitMassResponse_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (a v : ℝ) :
    Integrable (fun ω => coleHopfSplitMassResponse m a A (H ω) v) μ := by
  obtain ⟨M, _, hB⟩ := exists_uniform_coleHopfSplitMassResponse_bound v.toNNReal
  exact Integrable.of_bound
    ((measurable_coleHopfSplitMassResponse hAm hLip hm a v).comp hH).aestronglyMeasurable
    M (.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact hB A hAm hLip m hm a v (H ω) le_rfl)

/-- Concavity of the actual suffix response survives a fixed probability-law
average, including zero mass and degenerate total variance. -/
theorem concaveOn_integral_parisiQSuffix_splitMassResponse_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    {m a : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 ≤ a) :
    ConcaveOn ℝ (Icc (0 : ℝ) a)
      (fun v => ∫ ω, coleHopfSplitMassResponse m a (parisiQSuffix ξ h ms qs r) (H ω) v ∂μ) := by
  have hA := (parisiQSuffix_spatial_regular_four ξ h ms qs r).1
  have hint : ∀ v ∈ Icc (0 : ℝ) a,
      Integrable (fun ω => (1 : ℝ) *
        coleHopfSplitMassResponse m a (parisiQSuffix ξ h ms qs r) (H ω) v) μ := by
    intro v hv
    simpa only [one_mul] using
      (integrable_coleHopfSplitMassResponse_comp (μ := μ) hH hA.continuous.measurable
        (abs_parisiQSuffix_sub_le ξ h ms qs r) hm a v)
  simpa only [one_mul] using Aristotle.concaveOn_integral_weighted
    (μ := μ) (W := fun _ => (1 : ℝ))
    (F := fun ω v => coleHopfSplitMassResponse m a (parisiQSuffix ξ h ms qs r) (H ω) v)
    (.of_forall fun _ => zero_le_one)
    (.of_forall fun ω => concaveOn_parisiQSuffix_splitMassResponse ξ h ms qs r hm ha (H ω))
    hint

/-- The actual suffix dissipation identity after the same fixed-law average. -/
theorem hasDerivWithinAt_integral_parisiQSuffix_splitSpatialMoment_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    {m a v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) a) :
    HasDerivWithinAt
      (fun w => ∫ ω, coleHopfSplitSpatialMoment 1 m a (parisiQSuffix ξ h ms qs r) (H ω) w ∂μ)
      (-(∫ ω, coleHopfSplitSpatialMoment 2 m a (parisiQSuffix ξ h ms qs r) (H ω) v ∂μ))
      (Icc (0 : ℝ) a) v := by
  obtain ⟨hA, hb⟩ := parisiQSuffix_spatial_regular_four ξ h ms qs r
  exact hasDerivWithinAt_integral_coleHopfSplitSpatialMoment_comp hH hA hb
    (abs_parisiQSuffix_sub_le ξ h ms qs r) hm ha hv

end SpinGlass
