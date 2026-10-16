import SpinGlass.Parisi.Analytic.Convexity
import SpinGlass.Parisi.Variational.ParisiVarianceAveraging

/-!
# Variance calculus through a fixed Parisi prefix

The baseline cascade weight does not depend on the split variance. The local
response and squared spatial moments can therefore be integrated against that
probability measure. This gives the operator form of (14.240)-(14.243).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The spatial moment transported by the same fixed baseline law as the
inserted-mass response. -/
noncomputable def coleHopfIterateSplitSpatialMoment {j : ℕ} (s : ℕ)
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (m a : ℝ) (A : ℝ → ℝ) (x v : ℝ) : ℝ :=
  ∫ zs, coleHopfSplitSpatialMoment s m a A (x + ∑ p, zs p) v
    ∂cascadeTiltMeasure j ms (fun p => gaussianReal 0 (vs p))
      (fun zs => ENNReal.ofReal (Real.exp (coleHopf m a.toNNReal A (x + ∑ p, zs p))))

private theorem splitBaseline_isProbabilityMeasure {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|) (m a x : ℝ) :
    IsProbabilityMeasure (cascadeTiltMeasure j ms (fun p => gaussianReal 0 (vs p))
      (fun zs => ENNReal.ofReal (Real.exp (coleHopf m a.toNNReal A (x + ∑ p, zs p))))) := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hB := abs_coleHopf_sub_le_of_lipschitz m hAm hL a.toNNReal
  exact isProbabilityMeasure_cascadeTiltMeasure_comp_add_sum ms vs hpos hle
    (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable hB x

/-- The first variance derivative of the full prefix response is half its
transported squared-gradient moment. Both variance endpoints are admissible. -/
theorem hasDerivWithinAt_coleHopfIterateSplitMassResponse {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ s ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv s A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m a v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivWithinAt (coleHopfIterateSplitMassResponse ms vs m a A x)
      (coleHopfIterateSplitSpatialMoment 1 ms vs m a A x v / 2) (Icc (0 : ℝ) a) v := by
  have := splitBaseline_isProbabilityMeasure ms vs hpos hle hA.continuous.measurable hLip m a x
  exact hasDerivWithinAt_integral_coleHopfSplitMassResponse_comp
    (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))
    hA hb hLip hm ha hv

/-- The transported gradient moment dissipates by the transported squared
second-derivative moment, as in (14.243). -/
theorem hasDerivWithinAt_coleHopfIterateSplitSpatialMoment {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ s ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv s A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m a v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivWithinAt (coleHopfIterateSplitSpatialMoment 1 ms vs m a A x)
      (-coleHopfIterateSplitSpatialMoment 2 ms vs m a A x v) (Icc (0 : ℝ) a) v := by
  have := splitBaseline_isProbabilityMeasure ms vs hpos hle hA.continuous.measurable hLip m a x
  exact hasDerivWithinAt_integral_coleHopfSplitSpatialMoment_comp
    (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))
    hA hb hLip hm ha hv

/-- The fixed-prefix moments inherit bounds independent of the evaluation
point and the split variance. The input suffix bound is fixed. -/
theorem coleHopfIterateSplitSpatialMoment_one_two_bounds {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ s ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv s A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (a v x : ℝ) :
    |coleHopfIterateSplitSpatialMoment 1 ms vs m a A x v| ≤ C ^ 2 ∧
      |coleHopfIterateSplitSpatialMoment 2 ms vs m a A x v| ≤ (C + 2 * C ^ 2) ^ 2 := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hB := abs_coleHopf_sub_le_of_lipschitz m hA.continuous.measurable hL a.toNNReal
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
  exact ⟨abs_integral_cascadeTiltMeasure_le ms vs hpos hle hBm hB x
      (fun y => (coleHopfSplitSpatialMoment_one_two_bounds hA hb hLip hm a v y).1),
    abs_integral_cascadeTiltMeasure_le ms vs hpos hle hBm hB x
      (fun y => (coleHopfSplitSpatialMoment_one_two_bounds hA hb hLip hm a v y).2)⟩

/-- Measurability in position follows from the actual propagated inserted-mass
derivative. This bridge uses a positive outer mass and admissible variance. -/
theorem measurable_coleHopfIterateSplitMassResponse_of_pos {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {a v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) a) :
    Measurable (fun x => coleHopfIterateSplitMassResponse ms vs m a A x v) := by
  apply measurable_deriv_param
    (Φ := fun b x => coleHopfIterate j ms vs
      (coleHopf m (a - v).toNNReal (coleHopf b v.toNNReal A)) x)
    (fun b => ?_)
    (fun x => hasDerivAt_coleHopfIterate_split_mass_of_pos ms vs hpos hle hAm hLip hm hm1 hv x)
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hB := abs_coleHopf_sub_le_of_lipschitz b hAm hL v.toNNReal
  have hG := abs_coleHopf_sub_le_of_lipschitz m
    (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable hB (a - v).toNNReal
  exact measurable_coleHopfIterate ms vs
    (lipschitzWith_toNNReal_of_abs_sub_le hG).continuous.measurable hG

/-- Endpoint derivative measurability identifies the first transported moment
as a measurable function of the evaluation point. -/
theorem measurable_coleHopfIterateSplitSpatialMoment_one_of_pos {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ s ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv s A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {a v : ℝ}
    (ha : 0 < a) (hv : v ∈ Icc (0 : ℝ) a) :
    Measurable (fun x => coleHopfIterateSplitSpatialMoment 1 ms vs m a A x v) := by
  have hD := measurable_derivWithin_param_Icc_of_measurableOn ha hv
    (fun w hw => measurable_coleHopfIterateSplitMassResponse_of_pos
      ms vs hpos hle hA.continuous.measurable hLip hm hm1 hw)
    (fun x => hasDerivWithinAt_coleHopfIterateSplitMassResponse
      ms vs hpos hle hA hb hLip ⟨hm.le, hm1⟩ ha hv x)
  have heq : (fun x => coleHopfIterateSplitSpatialMoment 1 ms vs m a A x v) =
      fun x => (coleHopfIterateSplitSpatialMoment 1 ms vs m a A x v / 2) * 2 := by
    funext x
    ring
  rw [heq]
  exact hD.mul_const 2

/-- The second transported spatial moment is measurable at both admissible
variance endpoints by differentiating the first transported moment. -/
theorem measurable_coleHopfIterateSplitSpatialMoment_two_of_pos {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ s ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv s A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {a v : ℝ}
    (ha : 0 < a) (hv : v ∈ Icc (0 : ℝ) a) :
    Measurable (fun x => coleHopfIterateSplitSpatialMoment 2 ms vs m a A x v) := by
  have hD := measurable_derivWithin_param_Icc_of_measurableOn ha hv
    (fun w hw => measurable_coleHopfIterateSplitSpatialMoment_one_of_pos
      ms vs hpos hle hA hb hLip hm hm1 ha hw)
    (fun x => hasDerivWithinAt_coleHopfIterateSplitSpatialMoment
      ms vs hpos hle hA hb hLip ⟨hm.le, hm1⟩ ha hv x)
  have hDn := hD.neg
  change Measurable (fun x => -(-coleHopfIterateSplitSpatialMoment 2 ms vs m a A x v)) at hDn
  simpa only [neg_neg] using hDn

/-- The empty inserted interval has zero response before and after the
fixed-prefix average. -/
theorem coleHopfIterateSplitMassResponse_zero {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (m a : ℝ) (A : ℝ → ℝ) (x : ℝ) :
    coleHopfIterateSplitMassResponse ms vs m a A x 0 = 0 := by
  simp only [coleHopfIterateSplitMassResponse, coleHopfSplitMassResponse_zero, integral_zero]

/-- Variance differentiation after a probability-law average of the complete
prefix response. Only measurability of the field/shift is needed at this stage. -/
theorem hasDerivWithinAt_integral_coleHopfIterateSplitMassResponse_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ s ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv s A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {a v : ℝ}
    (ha : 0 < a) (hv : v ∈ Icc (0 : ℝ) a) :
    HasDerivWithinAt (fun w => ∫ ω, coleHopfIterateSplitMassResponse ms vs m a A (H ω) w ∂μ)
      ((∫ ω, coleHopfIterateSplitSpatialMoment 1 ms vs m a A (H ω) v ∂μ) / 2)
      (Icc (0 : ℝ) a) v := by
  obtain ⟨C, hC⟩ := hb
  have hbase : Integrable (fun ω => coleHopfIterateSplitMassResponse ms vs m a A (H ω) 0) μ := by
    simpa only [coleHopfIterateSplitMassResponse_zero] using integrable_const (0 : ℝ)
  have hd := Aristotle.hasDerivWithinAt_integral_Icc ha hv
    (fun w hw => ((measurable_coleHopfIterateSplitMassResponse_of_pos
      ms vs hpos hle hA.continuous.measurable hLip hm hm1 hw).comp hH).aestronglyMeasurable)
    (((measurable_coleHopfIterateSplitSpatialMoment_one_of_pos
      ms vs hpos hle hA ⟨C, hC⟩ hLip hm hm1 ha hv).comp hH).div_const 2).aestronglyMeasurable
    hbase (integrable_const (C ^ 2 / 2))
    (.of_forall fun ω w hw => hasDerivWithinAt_coleHopfIterateSplitMassResponse
      ms vs hpos hle hA ⟨C, hC⟩ hLip ⟨hm.le, hm1⟩ ha hw (H ω))
    (.of_forall fun ω w _ => by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right
        (coleHopfIterateSplitSpatialMoment_one_two_bounds ms vs hpos hle
          hA hC hLip ⟨hm.le, hm1⟩ a w (H ω)).1 (by norm_num))
  simpa only [integral_div, Function.comp_def] using hd

/-- Dissipation after the complete prefix and probability-law average. This
is the negative curvature identity underlying (14.247). -/
theorem hasDerivWithinAt_integral_coleHopfIterateSplitSpatialMoment_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ s ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv s A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {a v : ℝ}
    (ha : 0 < a) (hv : v ∈ Icc (0 : ℝ) a) :
    HasDerivWithinAt (fun w => ∫ ω, coleHopfIterateSplitSpatialMoment 1 ms vs m a A (H ω) w ∂μ)
      (-(∫ ω, coleHopfIterateSplitSpatialMoment 2 ms vs m a A (H ω) v ∂μ))
      (Icc (0 : ℝ) a) v := by
  obtain ⟨C, hC⟩ := hb
  have hmeas : ∀ w ∈ Icc (0 : ℝ) a,
      Measurable (fun ω => coleHopfIterateSplitSpatialMoment 1 ms vs m a A (H ω) w) :=
    fun w hw => (measurable_coleHopfIterateSplitSpatialMoment_one_of_pos
      ms vs hpos hle hA ⟨C, hC⟩ hLip hm hm1 ha hw).comp hH
  have hbase : Integrable (fun ω => coleHopfIterateSplitSpatialMoment 1 ms vs m a A (H ω) 0) μ :=
    Integrable.of_bound (hmeas 0 ⟨le_rfl, ha.le⟩).aestronglyMeasurable (C ^ 2)
      (.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact (coleHopfIterateSplitSpatialMoment_one_two_bounds ms vs hpos hle
          hA hC hLip ⟨hm.le, hm1⟩ a 0 (H ω)).1)
  have hd := Aristotle.hasDerivWithinAt_integral_Icc ha hv
    (fun w hw => (hmeas w hw).aestronglyMeasurable)
    ((measurable_coleHopfIterateSplitSpatialMoment_two_of_pos ms vs hpos hle
      hA ⟨C, hC⟩ hLip hm hm1 ha hv).comp hH).neg.aestronglyMeasurable
    hbase (integrable_const ((C + 2 * C ^ 2) ^ 2))
    (.of_forall fun ω w hw => hasDerivWithinAt_coleHopfIterateSplitSpatialMoment
      ms vs hpos hle hA ⟨C, hC⟩ hLip ⟨hm.le, hm1⟩ ha hw (H ω))
    (.of_forall fun ω w _ => by
      rw [abs_neg]
      exact (coleHopfIterateSplitSpatialMoment_one_two_bounds ms vs hpos hle
        hA hC hLip ⟨hm.le, hm1⟩ a w (H ω)).2)
  simpa only [integral_neg] using hd

/-- The full response inherits a bound depending only on the inserted variance
ceiling. Neither the preceding level count nor its masses enter this constant. -/
theorem exists_uniform_coleHopfIterateSplitMassResponse_bound (V : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (j : ℕ) (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0),
      (∀ p, 0 < ms p) → (∀ p, ms p ≤ 1) → ∀ (A : ℝ → ℝ), Measurable A →
      (∀ x y, |A y - A x| ≤ |y - x|) → ∀ m ∈ Icc (0 : ℝ) 1,
      ∀ (a v x : ℝ), v.toNNReal ≤ V →
      |coleHopfIterateSplitMassResponse ms vs m a A x v| ≤ M := by
  obtain ⟨M, hM, hB⟩ := exists_uniform_coleHopfSplitMassResponse_bound V
  refine ⟨M, hM, fun j ms vs hpos hle A hAm hLip m hm a v x hv => ?_⟩
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hG := abs_coleHopf_sub_le_of_lipschitz m hAm hL a.toNNReal
  exact abs_integral_cascadeTiltMeasure_le ms vs hpos hle
    (lipschitzWith_toNNReal_of_abs_sub_le hG).continuous.measurable hG x
    (fun y => hB A hAm hLip m hm a v y hv)

/-- A probability-law average of the transported response is integrable at
every admissible split variance. -/
theorem integrable_coleHopfIterateSplitMassResponse_comp_of_pos
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {a v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) a) :
    Integrable (fun ω => coleHopfIterateSplitMassResponse ms vs m a A (H ω) v) μ := by
  obtain ⟨M, _, hB⟩ := exists_uniform_coleHopfIterateSplitMassResponse_bound v.toNNReal
  exact Integrable.of_bound
    ((measurable_coleHopfIterateSplitMassResponse_of_pos ms vs hpos hle hAm hLip hm hm1 hv).comp
      hH).aestronglyMeasurable M (.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact hB j ms vs hpos hle A hAm hLip m ⟨hm.le, hm1⟩ a v (H ω) le_rfl)

/-- Concavity of the actual suffix response after the preceding baseline
cascade average, including degenerate variance and zero matching mass. -/
theorem concaveOn_parisiQSuffix_prefixSplitMassResponse {j : ℕ}
    (pms : Fin j → ℝ) (pvs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < pms p) (hle : ∀ p, pms p ≤ 1)
    (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    {m a : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 ≤ a) (x : ℝ) :
    ConcaveOn ℝ (Icc (0 : ℝ) a)
      (coleHopfIterateSplitMassResponse pms pvs m a (parisiQSuffix ξ h ms qs r) x) := by
  have hA := (parisiQSuffix_spatial_regular_four ξ h ms qs r).1
  have := splitBaseline_isProbabilityMeasure pms pvs hpos hle
    hA.continuous.measurable (abs_parisiQSuffix_sub_le ξ h ms qs r) m a x
  exact concaveOn_integral_parisiQSuffix_splitMassResponse_comp
    (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))
    ξ h ms qs r hm ha

/-- Concavity survives the complete prefix and field-law averages. This uses
the actual suffix and the fixed baseline weights in (14.240), with their
measurability and integrability proved rather than assumed. -/
theorem concaveOn_integral_parisiQSuffix_prefixSplitMassResponse_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {j : ℕ}
    (pms : Fin j → ℝ) (pvs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < pms p) (hle : ∀ p, pms p ≤ 1)
    (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    ConcaveOn ℝ (Icc (0 : ℝ) a)
      (fun v => ∫ ω, coleHopfIterateSplitMassResponse pms pvs m a
        (parisiQSuffix ξ h ms qs r) (H ω) v ∂μ) := by
  have hA := (parisiQSuffix_spatial_regular_four ξ h ms qs r).1
  have hint : ∀ v ∈ Icc (0 : ℝ) a,
      Integrable (fun ω => (1 : ℝ) * coleHopfIterateSplitMassResponse pms pvs m a
        (parisiQSuffix ξ h ms qs r) (H ω) v) μ := by
    intro v hv
    simpa only [one_mul] using
      (integrable_coleHopfIterateSplitMassResponse_comp_of_pos (μ := μ) hH
        pms pvs hpos hle hA.continuous.measurable (abs_parisiQSuffix_sub_le ξ h ms qs r) hm hm1 hv)
  simpa only [one_mul] using Aristotle.concaveOn_integral_weighted
    (μ := μ) (W := fun _ => (1 : ℝ))
    (F := fun ω v => coleHopfIterateSplitMassResponse pms pvs m a
      (parisiQSuffix ξ h ms qs r) (H ω) v)
    (.of_forall fun _ => zero_le_one)
    (.of_forall fun ω => concaveOn_parisiQSuffix_prefixSplitMassResponse
      pms pvs hpos hle ξ h ms qs r ⟨hm.le, hm1⟩ ha (H ω)) hint

/-- Book-level specialization of the full variance-response derivative to an
actual Parisi suffix. All suffix regularity and domination are proved. -/
theorem hasDerivWithinAt_integral_parisiQSuffix_prefixSplitMassResponse_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {j : ℕ}
    (pms : Fin j → ℝ) (pvs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < pms p) (hle : ∀ p, pms p ≤ 1)
    (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {a v : ℝ}
    (ha : 0 < a) (hv : v ∈ Icc (0 : ℝ) a) :
    HasDerivWithinAt
      (fun w => ∫ ω, coleHopfIterateSplitMassResponse pms pvs m a
        (parisiQSuffix ξ h ms qs r) (H ω) w ∂μ)
      ((∫ ω, coleHopfIterateSplitSpatialMoment 1 pms pvs m a
        (parisiQSuffix ξ h ms qs r) (H ω) v ∂μ) / 2) (Icc (0 : ℝ) a) v := by
  obtain ⟨hA, hb⟩ := parisiQSuffix_spatial_regular_four ξ h ms qs r
  exact hasDerivWithinAt_integral_coleHopfIterateSplitMassResponse_comp hH
    pms pvs hpos hle hA hb (abs_parisiQSuffix_sub_le ξ h ms qs r) hm hm1 ha hv

/-- Book-level specialization of the negative curvature after the prefix and
field-law averages, without extra suffix derivative assumptions. -/
theorem hasDerivWithinAt_integral_parisiQSuffix_prefixSplitSpatialMoment_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {j : ℕ}
    (pms : Fin j → ℝ) (pvs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < pms p) (hle : ∀ p, pms p ≤ 1)
    (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {a v : ℝ}
    (ha : 0 < a) (hv : v ∈ Icc (0 : ℝ) a) :
    HasDerivWithinAt
      (fun w => ∫ ω, coleHopfIterateSplitSpatialMoment 1 pms pvs m a
        (parisiQSuffix ξ h ms qs r) (H ω) w ∂μ)
      (-(∫ ω, coleHopfIterateSplitSpatialMoment 2 pms pvs m a
        (parisiQSuffix ξ h ms qs r) (H ω) v ∂μ)) (Icc (0 : ℝ) a) v := by
  obtain ⟨hA, hb⟩ := parisiQSuffix_spatial_regular_four ξ h ms qs r
  exact hasDerivWithinAt_integral_coleHopfIterateSplitSpatialMoment_comp hH
    pms pvs hpos hle hA hb (abs_parisiQSuffix_sub_le ξ h ms qs r) hm hm1 ha hv

end SpinGlass
