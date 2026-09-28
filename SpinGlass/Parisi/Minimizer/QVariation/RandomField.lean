import SpinGlass.Parisi.Minimizer.QVariation.Derivative
import SpinGlass.Parisi.Field.RandomFieldFunctional

/-!
# RandomField

External-field law integration and overlap stationarity.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

/-! ### I.i.d. random external fields -/

/-- A dominated left derivative can be averaged by extending each integrand linearly to the
right.  This extension is only an auxiliary function; the conclusion concerns the original
integral on its admissible left half-line. -/
theorem hasDerivWithinAt_integral_of_dominated_left
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f D : ℝ → α → ℝ} {d bound : α → ℝ} {a b : ℝ} (hab : a < b)
    (hfm : ∀ u, Measurable (f u)) (hfi : Integrable (f b) μ)
    (hdm : Measurable d) (hbi : Integrable bound μ)
    (hDb : ∀ x, ∀ u ∈ Ioo a b, ‖D u x‖ ≤ bound x)
    (hdb : ∀ x, ‖d x‖ ≤ bound x)
    (hD : ∀ x, ∀ u ∈ Ioo a b, HasDerivAt (fun v => f v x) (D u x) u)
    (hd : ∀ x, HasDerivWithinAt (fun u => f u x) (d x) (Iic b) b) :
    HasDerivWithinAt (fun u => ∫ x, f u x ∂μ) (∫ x, d x ∂μ) (Iic b) b := by
  let E : ℝ → α → ℝ := fun u x =>
    if u ≤ b then f u x else f b x + (u - b) * d x
  let DE : ℝ → α → ℝ := fun u x => if u < b then D u x else d x
  have hEm : ∀ u, Measurable (E u) := by
    intro u
    by_cases hu : u ≤ b
    · simpa only [E, if_pos hu] using hfm u
    · simp only [E, if_neg hu]
      exact (hfm b).add (hdm.const_mul (u - b))
  have hEi : Integrable (E b) μ := by simpa [E] using hfi
  have hDEm : Measurable (DE b) := by simpa [DE] using hdm
  have hDEb : ∀ᵐ x ∂μ, ∀ u ∈ Ioo a (b + 1), ‖DE u x‖ ≤ bound x := by
    filter_upwards [] with x
    intro u hu
    by_cases hub : u < b
    · simpa [DE, hub] using hDb x u ⟨hu.1, hub⟩
    · simpa [DE, hub] using hdb x
  have hEd : ∀ᵐ x ∂μ, ∀ u ∈ Ioo a (b + 1),
      HasDerivAt (fun v => E v x) (DE u x) u := by
    filter_upwards [] with x
    intro u hu
    rcases lt_trichotomy u b with hub | rfl | hbu
    · have heq : (fun v => E v x) =ᶠ[nhds u] fun v => f v x := by
        filter_upwards [eventually_lt_nhds hub] with v hv
        simp [E, hv.le]
      simpa [DE, hub] using (hD x u ⟨hu.1, hub⟩).congr_of_eventuallyEq heq
    · simpa [E, DE] using hasDerivAt_linear_right_extension (hd x)
    · have haff : HasDerivAt (fun v => f b x + (v - b) * d x) (d x) u := by
        simpa using (((hasDerivAt_id u).sub_const b).mul_const (d x)).const_add (f b x)
      have heq : (fun v => E v x) =ᶠ[nhds u]
          fun v => f b x + (v - b) * d x := by
        filter_upwards [eventually_gt_nhds hbu] with v hv
        simp [E, not_le.mpr hv]
      simpa [DE, not_lt.mpr hbu.le] using haff.congr_of_eventuallyEq heq
  have hfull := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds hab (by linarith : b < b + 1))
    (Filter.Eventually.of_forall fun u => (hEm u).aestronglyMeasurable) hEi
    hDEm.aestronglyMeasurable hDEb hbi hEd).2
  have heq : (fun u => ∫ x, f u x ∂μ) =ᶠ[nhdsWithin b (Iic b)]
      fun u => ∫ x, E u x ∂μ := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    change u ≤ b at hu
    simp [E, hu]
  simpa only [DE, lt_self_iff_false, if_false] using
    hfull.hasDerivWithinAt.congr_of_eventuallyEq heq (by simp [E])

/-- The book-level moment after averaging the common site variable against its probability
law. -/
def randomFieldParisiQMoment (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) : ℝ :=
  ∫ h, parisiQMoment ξ h ms qs r ∂μh

/-- The concrete moment is measurable in the external-field coordinate. -/
theorem measurable_parisiQMoment_externalField {ξ : ℝ → ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hm : ParisiMAdmissible ms) :
    Measurable fun h => parisiQMoment ξ h ms qs r := by
  obtain ⟨hA, C, hA', hA''c, hA'b, hA''b⟩ :=
    parisiQSuffix_deriv_regular (ξ := ξ) (h := 0) qs r hm
  let A : ℝ → ℝ := parisiQSuffix ξ 0 ms qs r
  let A' : ℝ → ℝ := parisiQSuffixDeriv ξ 0 ms qs r
  let vR : ℝ≥0 := Real.toNNReal
    (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r))
  let vL : ℝ≥0 := Real.toNNReal
    (deriv ξ (qs r) - deriv ξ (qExt qs r.val))
  let f : ℝ → ℝ := coleHopfSplitMoment (mExt ms (r.val + 1))
    (mExt ms r.val) vR vL A A'
  let B : ℝ → ℝ := coleHopf (mExt ms (r.val + 1)) vR A
  let G : ℝ → ℝ := coleHopf (mExt ms r.val) vL B
  have hfc : Continuous f := continuous_coleHopfSplitMoment hA hA' hA'b
  have hAm : Measurable A := measurable_of_hasDerivAt hA
  have hAlip : ∀ x y, |A y - A x| ≤ 1 * |y - x| :=
    ProbabilityTheory.abs_sub_le_mul_abs_sub_of_hasDerivAt hA hA'b
  have hBlip : ∀ x y, |B y - B x| ≤ 1 * |y - x| :=
    abs_coleHopf_sub_le_of_lipschitz _ hAm hAlip _
  have hBm : Measurable B :=
    (lipschitzWith_toNNReal_of_abs_sub_le hBlip).continuous.measurable
  have hGlip : ∀ x y, |G y - G x| ≤ 1 * |y - x| :=
    abs_coleHopf_sub_le_of_lipschitz _ hBm hBlip _
  have hGm : Measurable G :=
    (lipschitzWith_toNNReal_of_abs_sub_le hGlip).continuous.measurable
  have hfh (h x : ℝ) :
      coleHopfSplitMoment (mExt ms (r.val + 1)) (mExt ms r.val) vR vL
          (parisiQSuffix ξ h ms qs r) (parisiQSuffixDeriv ξ h ms qs r) x =
        f (h + x) := by
    have hAt : parisiQSuffix ξ h ms qs r = fun y => A (h + y) := by
      funext y
      exact parisiQSuffix_translate ξ h ms qs r y
    have hA't : parisiQSuffixDeriv ξ h ms qs r = fun y => A' (h + y) := by
      funext y
      exact parisiQSuffixDeriv_translate ξ h ms qs r y
    rw [hAt, hA't]
    exact coleHopfSplitMoment_translate _ _ _ _ A A' h x
  have hGh (h x : ℝ) :
      coleHopf (mExt ms r.val) vL
          (coleHopf (mExt ms (r.val + 1)) vR (parisiQSuffix ξ h ms qs r)) x =
        G (h + x) := by
    have hAt : parisiQSuffix ξ h ms qs r = fun y => A (h + y) := by
      funext y
      exact parisiQSuffix_translate ξ h ms qs r y
    rw [hAt]
    have hinner : coleHopf (mExt ms (r.val + 1)) vR (fun y => A (h + y)) =
        fun y => B (h + y) := by
      funext y
      exact coleHopf_translate _ _ A h y
    rw [hinner]
    exact coleHopf_translate _ _ B h x
  by_cases hr : r.val = 0
  · have heq : (fun h => parisiQMoment ξ h ms qs r) = fun h => f h := by
      funext h
      unfold parisiQMoment
      rw [if_pos hr]
      simpa [vR, vL] using hfh h 0
    rw [heq]
    exact hfc.measurable
  · have hprefix_pos : ∀ p, 0 < parisiQPrefixMasses ms r p := fun p =>
      hm.mExt_pos (by simp [parisiQPrefixMasses])
    have hprefix_le : ∀ p, parisiQPrefixMasses ms r p ≤ 1 := fun p =>
      mExt_le_one (fun i => (hm.2.2 i).le) _
    let F : ℝ → ℝ := fun y =>
      ∫ zs, f (y + ∑ p, zs p)
        ∂cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
          (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
          (fun zs => ENNReal.ofReal (Real.exp (G (y + ∑ p, zs p))))
    have hFm : Measurable F :=
      measurable_integral_cascadeTiltMeasure_comp_add_sum
        (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
        hprefix_pos hprefix_le hGm hGlip hfc.measurable
    have heq : (fun h => parisiQMoment ξ h ms qs r) =
        fun h => ∫ z₀, F (h + z₀) ∂gaussianReal 0 (parisiVar ξ qs 0) := by
      funext h
      unfold parisiQMoment
      rw [if_neg hr]
      apply integral_congr_ae
      filter_upwards [] with z₀
      change (∫ zs, coleHopfSplitMoment (mExt ms (r.val + 1))
          (mExt ms r.val) vR vL (parisiQSuffix ξ h ms qs r)
            (parisiQSuffixDeriv ξ h ms qs r) (z₀ + ∑ p, zs p)
        ∂cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
          (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
          (fun zs => ENNReal.ofReal (Real.exp
            (coleHopf (mExt ms r.val) vL
              (coleHopf (mExt ms (r.val + 1)) vR
                (parisiQSuffix ξ h ms qs r)) (z₀ + ∑ p, zs p))))) = F (h + z₀)
      unfold F
      have hmeasure :
          cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
            (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
            (fun zs => ENNReal.ofReal (Real.exp
              (coleHopf (mExt ms r.val) vL
                (coleHopf (mExt ms (r.val + 1)) vR
                  (parisiQSuffix ξ h ms qs r)) (z₀ + ∑ p, zs p)))) =
          cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
            (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
            (fun zs => ENNReal.ofReal (Real.exp (G (h + z₀ + ∑ p, zs p)))) := by
        congr 1
        funext zs
        rw [hGh]
        apply congrArg ENNReal.ofReal
        apply congrArg Real.exp
        apply congrArg G
        ring
      rw [hmeasure]
      apply integral_congr_ae
      filter_upwards [] with zs
      rw [hfh]
      congr 1
      ring
    rw [heq]
    exact (hFm.comp (measurable_fst.add measurable_snd)).stronglyMeasurable
      |>.integral_prod_right'.measurable

theorem integrable_parisiQMoment_externalField {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (hm : ParisiMAdmissible ms) :
    Integrable (fun h => parisiQMoment ξ h ms qs r) μh :=
  Integrable.of_bound (measurable_parisiQMoment_externalField qs r hm).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs]
      exact abs_parisiQMoment_le_one qs r hm)

/-- Talagrand's nondegeneracy condition for the external-field law, in the form
`$0 < \mathbb E h^2 < \infty$`. -/
structure NondegenerateExternalFieldLaw (μh : Measure ℝ) : Prop where
  sq_integrable : Integrable (fun h : ℝ => h ^ 2) μh
  second_moment_pos : 0 < ∫ h, h ^ 2 ∂μh

/-- At a zero first overlap, the first moment is a continuous function of the external field. -/
theorem continuous_parisiQMoment_first_of_eq_zero {ξ : ℝ → ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hqzero : qs 0 = 0) :
    Continuous fun h => parisiQMoment ξ h ms qs 0 := by
  have hlevelpos : ∀ i, 0 < parisiLevelMasses ms i := by
    intro i
    rw [parisiLevelMasses_apply]
    exact hm.mExt_pos (by omega)
  let B' : ℝ → ℝ := coleHopfIterateDeriv (k + 1) (parisiLevelMasses ms)
    (parisiLevelVars ξ qs) (parisiLogCoshTerminal 0)
    (parisiLogCoshTerminalDeriv 0)
  obtain ⟨hB, C, hB', hB''c, hB'b, hB''b⟩ :=
    coleHopfIterate_logCosh_regular (parisiLevelMasses ms) (parisiLevelVars ξ qs) 0 hlevelpos
  have hB'c : Continuous B' :=
    continuous_iff_continuousAt.2 fun x => (hB' x).continuousAt
  have heq : (fun h => parisiQMoment ξ h ms qs 0) = fun h => B' h ^ 2 := by
    funext h
    rw [parisiQMoment_first_eq_sq_full_deriv ms qs hqzero,
      coleHopfIterateDeriv_parisiLogCoshTerminal_translate
        (parisiLevelMasses ms) (parisiLevelVars ξ qs) hlevelpos h]
  rw [heq]
  exact hB'c.pow 2

/-- Averaging over the site law preserves continuity of the first moment at the collapsed
variance endpoint. -/
theorem continuousAt_randomFieldParisiQMoment_first_qUpdate_zero
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ}
    (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) :
    ContinuousAt
      (fun u => randomFieldParisiQMoment μh ξ ms (qUpdate qs 0 u) 0) 0 := by
  unfold randomFieldParisiQMoment
  exact continuousAt_of_dominated
    (Filter.Eventually.of_forall fun u =>
      (measurable_parisiQMoment_externalField (qUpdate qs 0 u) 0 hm).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun u =>
      Filter.Eventually.of_forall fun h => by
        rw [Real.norm_eq_abs]
        exact abs_parisiQMoment_le_one (qUpdate qs 0 u) 0 hm)
    (integrable_const (μ := μh) (1 : ℝ))
    (Filter.Eventually.of_forall fun h =>
      continuousAt_parisiQMoment_first_qUpdate_zero qs hm hξ)

/-- The nondegenerate site law makes the averaged first moment strictly positive. -/
theorem randomFieldParisiQMoment_first_pos {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hqzero : qs 0 = 0)
    (hμ : NondegenerateExternalFieldLaw μh) :
    0 < randomFieldParisiQMoment μh ξ ms qs 0 := by
  have hmm : Measurable fun h => parisiQMoment ξ h ms qs 0 :=
    (continuous_parisiQMoment_first_of_eq_zero qs hm hqzero).measurable
  have hmi : Integrable (fun h => parisiQMoment ξ h ms qs 0) μh :=
    Integrable.of_bound hmm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun h => by
        rw [Real.norm_eq_abs]
        exact abs_parisiQMoment_le_one qs 0 hm)
  have hsuppSq : 0 < μh (Function.support fun h : ℝ => h ^ 2) := by
    rw [← integral_pos_iff_support_of_nonneg (fun h => sq_nonneg h) hμ.sq_integrable]
    exact hμ.second_moment_pos
  have hsubset : Function.support (fun h : ℝ => h ^ 2) ⊆
      Function.support (fun h => parisiQMoment ξ h ms qs 0) := by
    intro h hh
    have hh0 : h ≠ 0 := by
      intro heq
      apply hh
      simp [heq]
    exact ne_of_gt (parisiQMoment_first_pos_of_ne_zero qs hm hqzero hh0)
  unfold randomFieldParisiQMoment
  rw [integral_pos_iff_support_of_nonneg
    (fun h => parisiQMoment_nonneg ξ h ms qs 0) hmi]
  exact hsuppSq.trans_le (measure_mono hsubset)

/-- At a final overlap equal to one, the averaged final moment is strictly below one. -/
theorem randomFieldParisiQMoment_last_lt_one {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hqlast : qs (Fin.last k) = 1) :
    randomFieldParisiQMoment μh ξ ms qs (Fin.last k) < 1 := by
  unfold randomFieldParisiQMoment
  apply integral_lt_one_of_measurable_of_lt
  · exact measurable_parisiQMoment_externalField qs (Fin.last k) hm
  · exact fun h => abs_parisiQMoment_le_one qs (Fin.last k) hm
  · exact fun h => parisiQMoment_last_lt_one qs hm hqlast

/-- The averaged concrete moment is the same expectation of any product-coordinate of the
i.i.d. external-field vector. -/
theorem randomFieldParisiQMoment_eq_integral_externalFieldVec_apply
    {N : ℕ} (i : Fin N) {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (hm : ParisiMAdmissible ms) :
    randomFieldParisiQMoment μh ξ ms qs r =
      ∫ hVec, parisiQMoment ξ (hVec i) ms qs r ∂externalFieldVecLaw N μh := by
  unfold randomFieldParisiQMoment
  exact (integral_externalFieldVec_apply N μh i
    (fun h => parisiQMoment ξ h ms qs r)
    (measurable_parisiQMoment_externalField qs r hm).aestronglyMeasurable).symm

/-- The averaged `X₀` is obtained by sampling any coordinate of the i.i.d. external-field
vector. -/
theorem randomFieldParisiX₀_eq_integral_externalFieldVec_apply
    {N : ℕ} (i : Fin N) {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1) :
    randomFieldParisiX₀ μh ξ ms qs =
      ∫ hVec, parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (hVec i + x)))
        ∂externalFieldVecLaw N μh := by
  unfold randomFieldParisiX₀
  exact (integral_externalFieldVec_apply N μh i
    (fun h => parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x))))
    (measurable_parisiX₀_logCosh ξ ms qs hpos hle).aestronglyMeasurable).symm

/-- The law-level Parisi functional is the expectation obtained by sampling any one coordinate
of the i.i.d. external-field vector.  Thus the thermodynamic functional depends on the common
site law, rather than on the number of sampled sites or the chosen coordinate. -/
theorem randomFieldParisiFunctional_eq_integral_externalFieldVec_apply
    {N : ℕ} (i : Fin N) {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1) :
    randomFieldParisiFunctional μh ξ ms qs =
      ∫ hVec, parisiFunctional ξ (hVec i) ms qs ∂externalFieldVecLaw N μh := by
  rw [randomFieldParisiFunctional_eq_integral hμh ξ ms qs hpos hle]
  exact (integral_externalFieldVec_apply N μh i
    (fun h => parisiFunctional ξ h ms qs)
    (integrable_parisiFunctional_externalField hμh ξ ms qs hpos hle).aestronglyMeasurable).symm

/-- Differentiate the averaged `X₀` after supplying a common local integrable bound for the
fixed-field derivatives.  This is the measure-theoretic bridge from the pointwise split
derivative to the moment averaged over the common i.i.d. site law. -/
theorem hasDerivAt_randomFieldParisiX₀_qUpdate_of_dominated
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) {q : ℝ}
    {D : ℝ → ℝ → ℝ} {bound : ℝ → ℝ} {s : Set ℝ}
    (hs : s ∈ nhds q)
    (hF_meas : ∀ᶠ u in nhds q, AEStronglyMeasurable
      (fun h => parisiX₀ ξ ms (qUpdate qs r u)
        (fun x => Real.log (Real.cosh (h + x)))) μh)
    (hF_int : Integrable
      (fun h => parisiX₀ ξ ms (qUpdate qs r q)
        (fun x => Real.log (Real.cosh (h + x)))) μh)
    (hD_meas : AEStronglyMeasurable (D q) μh)
    (hbound : ∀ᵐ h ∂μh, ∀ u ∈ s, ‖D u h‖ ≤ bound h)
    (hbound_int : Integrable bound μh)
    (hdiff : ∀ᵐ h ∂μh, ∀ u ∈ s, HasDerivAt
      (fun v => parisiX₀ ξ ms (qUpdate qs r v)
        (fun x => Real.log (Real.cosh (h + x)))) (D u h) u) :
    HasDerivAt (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
      (∫ h, D q h ∂μh) q := by
  unfold randomFieldParisiX₀
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hD_meas
    hbound hbound_int hdiff).2

/-- Differentiation under the external-field integral, with the domination and measurability
hypotheses discharged by the concrete recursion and the named condition on `$ξ$`. -/
theorem hasDerivAt_randomFieldParisiX₀_qUpdate_concrete
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hμh : Integrable (fun h : ℝ => h) μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs)
    (hleftq : qExt qs r.val < qs r) (hrightq : qs r < qExt qs (r.val + 2)) :
    HasDerivAt (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
      ((-1 / 2 : ℝ) * deriv (deriv ξ) (qs r) *
        (mExt ms (r.val + 1) - mExt ms r.val) *
          randomFieldParisiQMoment μh ξ ms qs r) (qs r) := by
  let qL : ℝ := qExt qs r.val
  let qR : ℝ := qExt qs (r.val + 2)
  let gap : ℝ := mExt ms (r.val + 1) - mExt ms r.val
  let D : ℝ → ℝ → ℝ := fun u h =>
    (-1 / 2 : ℝ) * deriv (deriv ξ) u * gap *
      parisiQMoment ξ h ms (qUpdate qs r u) r
  let K : ℝ := (1 / 2 : ℝ) * gap * deriv (deriv ξ) 1
  have hqLmem : qL ∈ Icc (0 : ℝ) 1 := by
    exact qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _
  have hqRmem : qR ∈ Icc (0 : ℝ) 1 := by
    exact qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _
  have hqmem : qs r ∈ Icc (0 : ℝ) 1 := hq.mem_Icc r
  have hs : Ioo qL qR ∈ nhds (qs r) := Ioo_mem_nhds hleftq hrightq
  have hFmeas : ∀ᶠ u in nhds (qs r), AEStronglyMeasurable
      (fun h => parisiX₀ ξ ms (qUpdate qs r u)
        (fun x => Real.log (Real.cosh (h + x)))) μh :=
    Filter.Eventually.of_forall fun u =>
      (measurable_parisiX₀_logCosh ξ ms (qUpdate qs r u)
        hm.2.1 (fun p => (hm.2.2 p).le)).aestronglyMeasurable
  have hFint : Integrable
      (fun h => parisiX₀ ξ ms (qUpdate qs r (qs r))
        (fun x => Real.log (Real.cosh (h + x)))) μh := by
    have heq : qUpdate qs r (qs r) = qs := by
      funext p
      by_cases hp : p = r
      · subst p
        simp
      · simp [qUpdate, hp]
    rw [heq]
    exact integrable_parisiX₀_logCosh hμh ξ ms qs hm.2.1 (fun p => (hm.2.2 p).le)
  have hDmeas : AEStronglyMeasurable (D (qs r)) μh := by
    have hmom := measurable_parisiQMoment_externalField (ξ := ξ)
      (qUpdate qs r (qs r)) r hm
    simpa [D] using
      (hmom.const_mul ((-1 / 2 : ℝ) * deriv (deriv ξ) (qs r) * gap)).aestronglyMeasurable
  have hbound : ∀ᵐ h ∂μh, ∀ u ∈ Ioo qL qR, ‖D u h‖ ≤ K := by
    filter_upwards [] with h
    intro u hu
    have humem : u ∈ Ioc (0 : ℝ) 1 :=
      ⟨hqLmem.1.trans_lt hu.1, hu.2.le.trans hqRmem.2⟩
    have hsecpos : 0 < deriv (deriv ξ) u :=
      hξ.second_pos u ⟨humem.1.le, humem.2⟩ (ne_of_gt humem.1)
    have hsecle : deriv (deriv ξ) u ≤ deriv (deriv ξ) 1 :=
      hξ.monotoneOn_second humem ⟨zero_lt_one, le_rfl⟩ humem.2
    have hgap : 0 < gap := hm.mExt_gap_pos r
    have hM := abs_parisiQMoment_le_one (ξ := ξ) (h := h) (qUpdate qs r u) r hm
    have hhalf : |(-1 / 2 : ℝ)| = 1 / 2 := by norm_num
    dsimp [D, K]
    rw [abs_mul, abs_mul, abs_mul, hhalf,
      abs_of_nonneg hsecpos.le, abs_of_nonneg hgap.le]
    calc
      1 / 2 * deriv (deriv ξ) u * gap *
          |parisiQMoment ξ h ms (qUpdate qs r u) r| ≤
          1 / 2 * deriv (deriv ξ) u * gap * 1 := by gcongr
      _ ≤ 1 / 2 * deriv (deriv ξ) 1 * gap * 1 := by gcongr
      _ = 1 / 2 * gap * deriv (deriv ξ) 1 := by ring
  have hboundInt : Integrable (fun _ : ℝ => K) μh := integrable_const K
  have hdiff : ∀ᵐ h ∂μh, ∀ u ∈ Ioo qL qR, HasDerivAt
      (fun v => parisiX₀ ξ ms (qUpdate qs r v)
        (fun x => Real.log (Real.cosh (h + x)))) (D u h) u := by
    filter_upwards [] with h
    intro u hu
    let qu := qUpdate qs r u
    have humem : u ∈ Icc (0 : ℝ) 1 :=
      ⟨hqLmem.1.trans (hu.1.le), hu.2.le.trans hqRmem.2⟩
    have hquself : qu r = u := qUpdate_self qs r u
    have hquleft : qExt qu r.val = qL := by
      exact qExt_qUpdate_of_lt qs r u (by omega)
    have hquright : qExt qu (r.val + 2) = qR := by
      exact qExt_qUpdate_of_gt qs r u (by omega)
    have hleft : deriv ξ (qExt qu r.val) < deriv ξ (qu r) := by
      rw [hquleft, hquself]
      exact hξ.strictMonoOn_deriv hqLmem humem hu.1
    have hright : deriv ξ (qu r) < deriv ξ (qExt qu (r.val + 2)) := by
      rw [hquself, hquright]
      exact hξ.strictMonoOn_deriv humem hqRmem hu.2
    have hξderiv := hξ.hasDeriv_deriv u humem
    rw [← hquself] at hξderiv
    have hd := hasDerivAt_parisiX₀_qUpdate (ξ := ξ) (h := h)
      qu r hm hξderiv hleft hright
    have hupdate : (fun v => qUpdate qu r v) = fun v => qUpdate qs r v := by
      funext v
      funext p
      simp [qu, qUpdate]
    have hfun :
        (fun v => parisiX₀ ξ ms (qUpdate qu r v)
          (parisiLogCoshTerminal h)) =
        fun v => parisiX₀ ξ ms (qUpdate qs r v)
          (parisiLogCoshTerminal h) := by
      funext v
      rw [congrFun hupdate v]
    rw [hfun] at hd
    change HasDerivAt
      (fun v => parisiX₀ ξ ms (qUpdate qs r v) (parisiLogCoshTerminal h)) (D u h) u
    simpa [D, gap, qu, hquself] using hd
  have hd := hasDerivAt_randomFieldParisiX₀_qUpdate_of_dominated
    ms qs r hs hFmeas hFint hDmeas hbound hboundInt hdiff
  have hqsupdate : qUpdate qs r (qs r) = qs := by
    funext p
    simp [qUpdate]
  convert hd using 1
  unfold D randomFieldParisiQMoment gap
  rw [hqsupdate]
  rw [← integral_const_mul]

/-- No admissible overlap vector lowers the random-field Parisi functional when the mass
parameters and the common i.i.d. site law are fixed. -/
def IsRandomFieldParisiQMinimizer (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) : Prop :=
  ParisiQAdmissible qs ∧
    ∀ qs', ParisiQAdmissible qs' →
      randomFieldParisiFunctional μh ξ ms qs ≤ randomFieldParisiFunctional μh ξ ms qs'

/-- Admissible random-field minimization gives the constrained one-coordinate comparison. -/
lemma IsRandomFieldParisiQMinimizer.le_qUpdate
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ}
    {qs : Fin (k + 1) → ℝ} (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    (r : Fin (k + 1)) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hleft : ∀ p, p < r → qs p < u) (hright : ∀ p, r < p → u < qs p) :
    randomFieldParisiFunctional μh ξ ms qs ≤
      randomFieldParisiFunctional μh ξ ms (qUpdate qs r u) :=
  hmin.2 _ (hmin.1.qUpdate r hu0 hu1 hleft hright)

/-- Strict endpoint inequalities turn a global random-field minimizer into a local minimum
along each overlap coordinate. -/
lemma IsRandomFieldParisiQMinimizer.isLocalMin_qUpdate
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) (r : Fin (k + 1)) :
    IsLocalMin (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u))
      (qs r) :=
  parisiQMin_isLocalMin hmin hq0 hq1 r

/-- At the lower endpoint, constrained random-field minimality forces a nonnegative right
derivative. -/
lemma IsRandomFieldParisiQMinimizer.first_deriv_nonneg
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ}
    {qs : Fin (k + 1) → ℝ} (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    (hq0 : qs 0 = 0) {d : ℝ}
    (hd : HasDerivAt
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs 0 u)) d (qs 0)) :
    0 ≤ d :=
  parisiQMin_first_deriv_nonneg hmin hq0 hd

/-- At the upper endpoint, constrained random-field minimality forces a nonpositive left
derivative. -/
lemma IsRandomFieldParisiQMinimizer.last_derivWithin_nonpos
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ}
    {qs : Fin (k + 1) → ℝ} (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    (hq1 : qs (Fin.last k) = 1) {d : ℝ}
    (hd : HasDerivWithinAt
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs (Fin.last k) u)) d
      (Iic (qs (Fin.last k))) (qs (Fin.last k))) : d ≤ 0 :=
  parisiQMin_last_derivWithin_nonpos hmin hq1 hd

/-- The full-derivative version of the constrained endpoint sign lemma. -/
lemma IsRandomFieldParisiQMinimizer.last_deriv_nonpos
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ}
    {qs : Fin (k + 1) → ℝ} (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    (hq1 : qs (Fin.last k) = 1) {d : ℝ}
    (hd : HasDerivAt
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs (Fin.last k) u)) d
      (qs (Fin.last k))) : d ≤ 0 :=
  parisiQMin_last_derivWithin_nonpos hmin hq1 hd.hasDerivWithinAt

/-- The random-field theta-sum written over the free overlap coordinates. -/
theorem randomFieldParisiFunctional_eq_theta_fin_sum (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    randomFieldParisiFunctional μh ξ ms qs
      = Real.log 2 + randomFieldParisiX₀ μh ξ ms qs
        + (1 / 2) * ∑ p : Fin (k + 1),
            parisiTheta ξ (qs p) * (mExt ms (p.val + 1) - mExt ms p.val)
        - (1 / 2) * parisiTheta ξ 1 := by
  rw [randomFieldParisiFunctional_eq_theta_sum, ← Fin.sum_univ_eq_sum_range]
  simp only [qExt_succ_of_lt qs (Fin.isLt _)]

/-- Along one overlap coordinate, the random-field functional is its averaged `X₀` plus the
same theta term as in the deterministic-field functional. -/
theorem randomFieldParisiFunctional_qUpdate_eq (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (u : ℝ) :
    randomFieldParisiFunctional μh ξ ms (qUpdate qs r u)
      = parisiQConst ξ ms qs r
        + (randomFieldParisiX₀ μh ξ ms (qUpdate qs r u)
          + (1 / 2) * (mExt ms (r.val + 1) - mExt ms r.val) * parisiTheta ξ u) := by
  classical
  rw [randomFieldParisiFunctional_eq_theta_fin_sum, parisiTheta_sum_qUpdate]
  unfold parisiQConst
  ring

/-- The averaged concrete recursion is continuous along every admissible overlap variation,
including variations based at zero or one. -/
theorem continuousWithinAt_randomFieldParisiX₀_qUpdate
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs) :
    ContinuousWithinAt
      (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
      (Icc (0 : ℝ) 1) (qs r) := by
  have hqmem : qs r ∈ Icc (0 : ℝ) 1 := hq.mem_Icc r
  have hdu : Filter.Tendsto (fun u => deriv ξ u)
      (nhdsWithin (qs r) (Icc (0 : ℝ) 1)) (nhds (deriv ξ (qs r))) :=
    hξ.deriv_continuous (qs r) hqmem
  have hunif := tendsto_uniform_parisiX₀_qUpdate qs r id hm hdu
  have hsame : qUpdate qs r (qs r) = qs := by
    funext p
    by_cases hp : p = r
    · subst p
      simp
    · simp [qUpdate, hp]
  show Filter.Tendsto
    (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
    (nhdsWithin (qs r) (Icc (0 : ℝ) 1))
    (nhds (randomFieldParisiX₀ μh ξ ms (qUpdate qs r (qs r))))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  filter_upwards [hunif (ε / 2) hhalf] with u hu
  unfold randomFieldParisiX₀
  rw [dist_eq, hsame, ← integral_sub
    (integrable_parisiX₀_logCosh hμh ξ ms (qUpdate qs r u)
      hm.2.1 (fun p => (hm.2.2 p).le))
    (integrable_parisiX₀_logCosh hμh ξ ms qs
      hm.2.1 (fun p => (hm.2.2 p).le))]
  have hb := norm_integral_le_of_norm_le_const
    (μ := μh)
    (f := fun h =>
      parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h) -
        parisiX₀ ξ ms qs (parisiLogCoshTerminal h))
    (C := ε / 2) (Filter.Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs]
      simpa only [id_eq, hsame] using (hu h).le)
  rw [Real.norm_eq_abs] at hb
  have hb' :
      |∫ h,
          (parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h) -
            parisiX₀ ξ ms qs (parisiLogCoshTerminal h)) ∂μh| ≤ ε / 2 := by
    simpa using hb
  exact hb'.trans_lt (half_lt_self hε)

/-- The random-field Parisi functional is continuous at constrained overlap endpoints. -/
theorem continuousWithinAt_randomFieldParisiFunctional_qUpdate
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs) :
    ContinuousWithinAt
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u))
      (Icc (0 : ℝ) 1) (qs r) := by
  let C : ℝ := parisiQConst ξ ms qs r
  let c : ℝ := (1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val)
  have hX := continuousWithinAt_randomFieldParisiX₀_qUpdate ms qs r hμh hm hξ hq
  have hqmem : qs r ∈ Icc (0 : ℝ) 1 := hq.mem_Icc r
  have hθ : ContinuousAt (parisiTheta ξ) (qs r) :=
    (hasDerivAt_parisiTheta (hξ.hasDeriv _ hqmem)
      (hξ.hasDeriv_deriv _ hqmem)).continuousAt
  have hright : ContinuousWithinAt
      (fun u => C + (randomFieldParisiX₀ μh ξ ms (qUpdate qs r u) +
        c * parisiTheta ξ u)) (Icc (0 : ℝ) 1) (qs r) :=
    continuousWithinAt_const.add (hX.add
      (continuousWithinAt_const.mul hθ.continuousWithinAt))
  have hfun :
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u)) =
        fun u => C + (randomFieldParisiX₀ μh ξ ms (qUpdate qs r u) +
          c * parisiTheta ξ u) := by
    funext u
    exact randomFieldParisiFunctional_qUpdate_eq μh ξ ms qs r u
  rw [hfun]
  exact hright

/-- The random-field version of (14.220).  The moment `M` includes the expectation over the
common law of an i.i.d. external-field coordinate. -/
theorem hasDerivAt_randomFieldParisiFunctional_qUpdate
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) {q ξ₂ M : ℝ}
    (hX₀ : HasDerivAt
      (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
      ((-1 / 2 : ℝ) * ξ₂ * (mExt ms (r.val + 1) - mExt ms r.val) * M) q)
    (hξ : HasDerivAt ξ (deriv ξ q) q)
    (hξ' : HasDerivAt (deriv ξ) ξ₂ q) :
    HasDerivAt (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u))
      ((1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) * ξ₂ * (-M + q)) q := by
  let C : ℝ := parisiQConst ξ ms qs r
  let c : ℝ := (1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val)
  have hθ := hasDerivAt_parisiTheta hξ hξ'
  have hbase := hX₀.add (hθ.const_mul c)
  have hall := (hasDerivAt_const q C).add hbase
  have hfun :
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u))
        = (fun u => C +
          (randomFieldParisiX₀ μh ξ ms (qUpdate qs r u) + c * parisiTheta ξ u)) := by
    funext u
    rw [randomFieldParisiFunctional_qUpdate_eq]
  rw [hfun]
  refine hall.congr_deriv ?_
  dsimp [c]
  ring

/-- The random-field form of (14.220) obtained from the concrete Parisi recursion and
differentiation under the external-field integral. -/
theorem hasDerivAt_randomFieldParisiFunctional_qUpdate_concrete
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs)
    (hleftq : qExt qs r.val < qs r)
    (hrightq : qs r < qExt qs (r.val + 2)) :
    HasDerivAt (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u))
      ((1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) *
        deriv (deriv ξ) (qs r) *
          (-randomFieldParisiQMoment μh ξ ms qs r + qs r)) (qs r) := by
  apply hasDerivAt_randomFieldParisiFunctional_qUpdate ms qs r
    (hasDerivAt_randomFieldParisiX₀_qUpdate_concrete ms qs r hμh hm hξ hq
      hleftq hrightq)
    (hξ.hasDeriv (qs r) (hq.mem_Icc r))
    (hξ.hasDeriv_deriv (qs r) (hq.mem_Icc r))

/-- At an interior local minimum of the random-field functional, (14.220) gives the averaged
stationarity equation. -/
theorem randomFieldParisiQ_eq_moment_of_isLocalMin
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) {q ξ₂ M : ℝ}
    (hmin : IsLocalMin
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u)) q)
    (hX₀ : HasDerivAt
      (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
      ((-1 / 2 : ℝ) * ξ₂ * (mExt ms (r.val + 1) - mExt ms r.val) * M) q)
    (hξ : HasDerivAt ξ (deriv ξ q) q)
    (hξ' : HasDerivAt (deriv ξ) ξ₂ q)
    (hm : mExt ms (r.val + 1) ≠ mExt ms r.val) (hξ₂ : ξ₂ ≠ 0) : q = M := by
  have hd := hasDerivAt_randomFieldParisiFunctional_qUpdate ms qs r hX₀ hξ hξ'
  have hz := hmin.hasDerivAt_eq_zero hd
  have hc : (1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) * ξ₂ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) hξ₂
    exact sub_ne_zero.mpr hm
  have hz' :
      ((1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) * ξ₂) * (-M + q) = 0 := by
    simpa [mul_assoc] using hz
  have hlast : -M + q = 0 := (mul_eq_zero.mp hz').resolve_left hc
  linarith

/-- The averaged stationarity equation with the mass gap supplied by admissibility. -/
theorem randomFieldParisiQ_eq_moment_of_isLocalMin_of_admissible
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) {q ξ₂ M : ℝ}
    (hm : ParisiMAdmissible ms) (hξ₂ : 0 < ξ₂)
    (hmin : IsLocalMin
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u)) q)
    (hX₀ : HasDerivAt
      (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
      ((-1 / 2 : ℝ) * ξ₂ * (mExt ms (r.val + 1) - mExt ms r.val) * M) q)
    (hξ : HasDerivAt ξ (deriv ξ q) q)
    (hξ' : HasDerivAt (deriv ξ) ξ₂ q) : q = M := by
  apply randomFieldParisiQ_eq_moment_of_isLocalMin ms qs r hmin hX₀ hξ hξ'
  · exact ne_of_gt (hm.mExt_gap_pos r) |>.imp fun heq => sub_eq_zero.mpr heq
  · exact ne_of_gt hξ₂

/-- Conditional reduction of Proposition 14.7.5 for a common i.i.d. external-field law.
Here `M r` includes the outer expectation over that law; its derivative and endpoint bounds
remain hypotheses. -/
theorem randomFieldParisiQ_strict_chain_and_eq_moment_of_isMin_of_derivatives
    {μh : Measure ℝ} {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (M ξ₂ : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    (hX₀ : ∀ r, HasDerivAt
      (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs r u))
      ((-1 / 2 : ℝ) * ξ₂ r * (mExt ms (r.val + 1) - mExt ms r.val) * M r) (qs r))
    (hξ : ∀ r, HasDerivAt ξ (deriv ξ (qs r)) (qs r))
    (hξ' : ∀ r, HasDerivAt (deriv ξ) (ξ₂ r) (qs r))
    (hξ₂ : ∀ r, 0 < ξ₂ r) (hMfirst : 0 < M 0) (hMlast : M (Fin.last k) < 1) :
    (∀ r : ℕ, r ≤ k + 1 → qExt qs r < qExt qs (r + 1)) ∧
      ∀ r, qs r = M r := by
  have hd (r : Fin (k + 1)) :=
    hasDerivAt_randomFieldParisiFunctional_qUpdate ms qs r (hX₀ r) (hξ r) (hξ' r)
  have hq0 : 0 < qs 0 := by
    by_contra hn
    have hz : qs 0 = 0 := le_antisymm (not_lt.mp hn) hmin.1.2.1
    have hnonneg := hmin.first_deriv_nonneg hz (hd 0)
    have hgap : 0 < mExt ms ((0 : Fin (k + 1)).val + 1) -
        mExt ms (0 : Fin (k + 1)).val := hm.mExt_gap_pos 0
    have hcoef : 0 < (1 / 2 : ℝ) *
        (mExt ms ((0 : Fin (k + 1)).val + 1) - mExt ms (0 : Fin (k + 1)).val) * ξ₂ 0 :=
      mul_pos (mul_pos (by norm_num) hgap) (hξ₂ 0)
    have hneg : -M 0 + qs 0 < 0 := by rw [hz]; linarith
    nlinarith
  have hq1 : qs (Fin.last k) < 1 := by
    by_contra hn
    have ho : qs (Fin.last k) = 1 := le_antisymm hmin.1.2.2 (not_lt.mp hn)
    have hnonpos := hmin.last_deriv_nonpos ho (hd (Fin.last k))
    have hgap : 0 < mExt ms ((Fin.last k).val + 1) - mExt ms (Fin.last k).val :=
      hm.mExt_gap_pos (Fin.last k)
    have hcoef : 0 < (1 / 2 : ℝ) *
        (mExt ms ((Fin.last k).val + 1) - mExt ms (Fin.last k).val) * ξ₂ (Fin.last k) :=
      mul_pos (mul_pos (by norm_num) hgap) (hξ₂ (Fin.last k))
    have hpos : 0 < -M (Fin.last k) + qs (Fin.last k) := by rw [ho]; linarith
    nlinarith
  refine ⟨fun r hr => qExt_strict_succ hmin.1.1 hq0 hq1 hr, ?_⟩
  intro r
  exact randomFieldParisiQ_eq_moment_of_isLocalMin_of_admissible ms qs r hm (hξ₂ r)
    (hmin.isLocalMin_qUpdate ms qs hq0 hq1 r) (hX₀ r) (hξ r) (hξ' r)

/-- Proposition 14.7.5 after its endpoint inequalities are established.  The derivatives and
moments in the stationarity equations come from the concrete recursion and the external-field
integral. -/
theorem randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin_of_endpoints
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) :
    (∀ n : ℕ, n ≤ k + 1 → qExt qs n < qExt qs (n + 1)) ∧
      ∀ r, qs r = randomFieldParisiQMoment μh ξ ms qs r := by
  have hchain : ∀ n : ℕ, n ≤ k + 1 → qExt qs n < qExt qs (n + 1) :=
    fun n hn => qExt_strict_succ hmin.1.1 hq0 hq1 hn
  refine ⟨hchain, ?_⟩
  intro r
  have hqmem : qs r ∈ Icc (0 : ℝ) 1 := hmin.1.mem_Icc r
  have hqpos : 0 < qs r := hq0.trans_le (hmin.1.monotone (Fin.zero_le r))
  have hξ₂pos : 0 < deriv (deriv ξ) (qs r) :=
    hξ.second_pos _ hqmem (ne_of_gt hqpos)
  have hleftq : qExt qs r.val < qs r := by
    simpa [qExt_succ_of_lt qs r.isLt] using hchain r.val (by omega)
  have hrightq : qs r < qExt qs (r.val + 2) := by
    simpa [qExt_succ_of_lt qs r.isLt] using hchain (r.val + 1) (by omega)
  have hd := hasDerivAt_randomFieldParisiX₀_qUpdate_concrete ms qs r hμh hm hξ
    hmin.1 hleftq hrightq
  exact randomFieldParisiQ_eq_moment_of_isLocalMin_of_admissible ms qs r hm hξ₂pos
    (hmin.isLocalMin_qUpdate ms qs hq0 hq1 r) hd
    (hξ.hasDeriv _ hqmem) (hξ.hasDeriv_deriv _ hqmem)

/-- A nondegenerate external-field law rules out a collapsed first overlap by an admissible
right-hand variation.  No positivity assumption on `ξ''(0)` is used: positivity away from zero
and continuity of the concrete first moment give a short interval on which the functional is
strictly decreasing. -/
theorem randomFieldParisiQ_first_pos_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    0 < qs 0 := by
  by_contra hn
  have hqzero : qs 0 = 0 := le_antisymm (not_lt.mp hn) hmin.1.2.1
  let M : ℝ → ℝ := fun u =>
    randomFieldParisiQMoment μh ξ ms (qUpdate qs 0 u) 0
  let F : ℝ → ℝ := fun u =>
    randomFieldParisiFunctional μh ξ ms (qUpdate qs 0 u)
  have hM0 : 0 < M 0 := by
    have hsame : qUpdate qs 0 0 = qs :=
      qUpdate_eq_of_eq qs 0 hqzero
    change 0 < randomFieldParisiQMoment μh ξ ms (qUpdate qs 0 0) 0
    rw [hsame]
    exact randomFieldParisiQMoment_first_pos qs hm hqzero hμ
  have hMc : ContinuousAt M 0 := by
    exact continuousAt_randomFieldParisiQMoment_first_qUpdate_zero qs hm hξ
  have hMev : ∀ᶠ u in nhds 0, M 0 / 2 < M u :=
    hMc.eventually (Ioi_mem_nhds (half_lt_self hM0))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 hMev
  let qR : ℝ := qExt qs 2
  have hqR : 0 < qR := by
    by_cases hk : k = 0
    · subst k
      dsimp [qR]
      rw [qExt_of_le qs (by omega)]
      norm_num
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      dsimp [qR]
      rw [qExt_succ_of_lt qs (by omega : 1 < k + 1)]
      have h01 : (0 : Fin (k + 1)) < ⟨1, by omega⟩ :=
        Fin.mk_lt_mk.mpr Nat.zero_lt_one
      simpa [hqzero] using hmin.1.1 h01
  let b : ℝ := min (min ε qR) (min (M 0 / 2) 1) / 2
  have hbpos : 0 < b := by
    dsimp [b]
    positivity
  have hbmin : b < min (min ε qR) (min (M 0 / 2) 1) :=
    half_lt_self (by positivity)
  have hbε : b < ε :=
    hbmin.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hbqR : b < qR :=
    hbmin.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hbM : b < M 0 / 2 :=
    hbmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hb1 : b < 1 :=
    hbmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hMlarge : ∀ u ∈ Icc (0 : ℝ) b, M 0 / 2 < M u := by
    intro u hu
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
    exact hu.2.trans_lt hbε
  have hadm : ∀ u ∈ Ioc (0 : ℝ) b,
      ParisiQAdmissible (qUpdate qs 0 u) := by
    intro u hu
    apply hmin.1.qUpdate 0 hu.1.le (hu.2.trans_lt hb1).le
    · intro p hp
      exact (not_lt_of_ge (Fin.zero_le p) hp).elim
    · intro p hp
      by_cases hk : k = 0
      · subst k
        have hp0 : p = 0 := Fin.eq_zero p
        subst p
        exact (lt_irrefl 0 hp).elim
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have hfirst : (⟨1, by omega⟩ : Fin (k + 1)) ≤ p := by
          exact Fin.mk_le_mk.mpr (Nat.one_le_iff_ne_zero.2 (by
            intro hp0
            apply ne_of_gt hp
            exact Fin.ext hp0))
        have hqRle : qR ≤ qs p := by
          dsimp [qR]
          rw [qExt_succ_of_lt qs (by omega : 1 < k + 1)]
          exact hmin.1.monotone hfirst
        exact hu.2.trans_lt hbqR |>.trans_le hqRle
  have hderiv : ∀ u ∈ Ioc (0 : ℝ) b, HasDerivAt F
      ((1 / 2 : ℝ) * (mExt ms 1 - mExt ms 0) * deriv (deriv ξ) u * (-M u + u)) u := by
    intro u hu
    let qu := qUpdate qs 0 u
    have hqu : ParisiQAdmissible qu := hadm u hu
    have humem : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, (hu.2.trans_lt hb1).le⟩
    have hleft : qExt qu 0 < qu 0 := by simp [qu, qUpdate, hu.1]
    have hright : qu 0 < qExt qu 2 := by
      dsimp [qu]
      rw [qUpdate_self, qExt_qUpdate_of_gt qs 0 u (by norm_num)]
      exact hu.2.trans_lt hbqR
    have hd := hasDerivAt_randomFieldParisiFunctional_qUpdate_concrete
      ms qu 0 hμh hm hξ hqu hleft hright
    simpa [F, M, qu, qUpdate, mExt_zero] using hd
  have hderivneg : ∀ u ∈ interior (Icc (0 : ℝ) b), deriv F u < 0 := by
    intro u hu
    rw [interior_Icc] at hu
    have huioc : u ∈ Ioc (0 : ℝ) b := ⟨hu.1, hu.2.le⟩
    have hd := hderiv u huioc
    rw [hd.deriv]
    have hgap : 0 < mExt ms 1 - mExt ms 0 := hm.mExt_gap_pos 0
    have hsecond : 0 < deriv (deriv ξ) u :=
      hξ.second_pos u ⟨hu.1.le, (hu.2.trans hb1).le⟩ (ne_of_gt hu.1)
    have huM : u < M u :=
      (hu.2.trans hbM).trans (hMlarge u ⟨hu.1.le, hu.2.le⟩)
    have hcoef : 0 < (1 / 2 : ℝ) * (mExt ms 1 - mExt ms 0) *
        deriv (deriv ξ) u := mul_pos (mul_pos (by norm_num) hgap) hsecond
    simpa [sub_eq_add_neg, add_comm] using
      mul_neg_of_pos_of_neg hcoef (sub_neg.mpr huM)
  have hFcont : ContinuousOn F (Icc (0 : ℝ) b) := by
    intro u hu
    by_cases hu0 : u = 0
    · subst u
      have hc := (continuousWithinAt_randomFieldParisiFunctional_qUpdate
        ms qs 0 hμh hm hξ hmin.1).mono (Icc_subset_Icc_right hb1.le)
      simpa [F, hqzero] using hc
    · have huioc : u ∈ Ioc (0 : ℝ) b := ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), hu.2⟩
      exact (hderiv u huioc).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn F (Icc (0 : ℝ) b) :=
    strictAntiOn_of_deriv_neg (convex_Icc 0 b) hFcont hderivneg
  have hFbF0 : F b < F 0 := hanti ⟨le_rfl, hbpos.le⟩ ⟨hbpos.le, le_rfl⟩ hbpos
  have hminle : F 0 ≤ F b := by
    have hsame : qUpdate qs 0 0 = qs :=
      qUpdate_eq_of_eq qs 0 hqzero
    change randomFieldParisiFunctional μh ξ ms (qUpdate qs 0 0) ≤
      randomFieldParisiFunctional μh ξ ms (qUpdate qs 0 b)
    rw [hsame]
    exact hmin.le_qUpdate 0 hbpos.le hb1.le
      (fun p hp => (not_lt_of_ge (Fin.zero_le p) hp).elim)
      (fun p hp => by
        have hbmem : b ∈ Ioc (0 : ℝ) b := ⟨hbpos, le_rfl⟩
        have hp' := (hadm b hbmem).1 hp
        have hpne : p ≠ 0 := ne_of_gt hp
        simpa [qUpdate, hpne] using hp')
  linarith

/-- The endpoint derivative is averaged using a common bound independent of the site field.
Only admissible left-hand values are used. -/
theorem hasDerivWithinAt_randomFieldParisiX₀_last_qUpdate
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs)
    (hqlast : qs (Fin.last k) = 1) :
    HasDerivWithinAt
      (fun u => randomFieldParisiX₀ μh ξ ms (qUpdate qs (Fin.last k) u))
      ((-1 / 2 : ℝ) * deriv (deriv ξ) 1 * (1 - mExt ms k) *
        randomFieldParisiQMoment μh ξ ms qs (Fin.last k)) (Iic 1) 1 := by
  let r : Fin (k + 1) := Fin.last k
  let qL := qExt qs r.val
  let gap := mExt ms (r.val + 1) - mExt ms r.val
  let f : ℝ → ℝ → ℝ := fun u h =>
    parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h)
  let D : ℝ → ℝ → ℝ := fun u h =>
    (-1 / 2 : ℝ) * deriv (deriv ξ) u * gap *
      parisiQMoment ξ h ms (qUpdate qs r u) r
  let d : ℝ → ℝ := fun h =>
    (-1 / 2 : ℝ) * deriv (deriv ξ) 1 * gap * parisiQMoment ξ h ms qs r
  let K := (1 / 2 : ℝ) * gap * deriv (deriv ξ) 1
  have hgap : 0 < gap := hm.mExt_gap_pos r
  have hgapEq : gap = 1 - mExt ms k := by simp [gap, r, mExt]
  have hqLlt : qL < 1 := by
    by_cases hk : k = 0
    · subst k
      simp [qL, r, qExt_zero]
    · change qExt qs k < 1
      have hprev : (⟨k - 1, by omega⟩ : Fin (k + 1)) < Fin.last k :=
        Fin.mk_lt_mk.mpr (by simp [Fin.last]; omega)
      rw [qExt, if_neg hk, dif_pos (by omega : k - 1 < k + 1)]
      simpa [hqlast] using hq.1 hprev
  have hqLmem : qL ∈ Icc (0 : ℝ) 1 :=
    qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _
  have hsame : qUpdate qs r 1 = qs :=
    qUpdate_eq_of_eq qs r (by simpa [r] using hqlast)
  have hfm : ∀ u, Measurable (f u) := fun u =>
    measurable_parisiX₀_logCosh ξ ms (qUpdate qs r u) hm.2.1
      (fun p => (hm.2.2 p).le)
  have hfi : Integrable (f 1) μh := by
    dsimp [f]
    rw [hsame]
    exact integrable_parisiX₀_logCosh hμh ξ ms qs hm.2.1 (fun p => (hm.2.2 p).le)
  have hdm : Measurable d :=
    (measurable_parisiQMoment_externalField qs r hm).const_mul _
  have hbound (u : ℝ) (hu : u ∈ Ioc (0 : ℝ) 1) (h : ℝ)
      (Q : Fin (k + 1) → ℝ) :
      ‖(-1 / 2 : ℝ) * deriv (deriv ξ) u * gap * parisiQMoment ξ h ms Q r‖ ≤ K := by
    have hspos := hξ.second_pos u ⟨hu.1.le, hu.2⟩ (ne_of_gt hu.1)
    have hsle := hξ.monotoneOn_second hu ⟨zero_lt_one, le_rfl⟩ hu.2
    have hM := abs_parisiQMoment_le_one (ξ := ξ) (h := h) Q r hm
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      show |(-1 / 2 : ℝ)| = 1 / 2 by norm_num,
      abs_of_nonneg hspos.le, abs_of_nonneg hgap.le]
    calc
      _ ≤ 1 / 2 * deriv (deriv ξ) u * gap * 1 := by gcongr
      _ ≤ 1 / 2 * deriv (deriv ξ) 1 * gap * 1 := by gcongr
      _ = K := by dsimp [K]; ring
  have hDb : ∀ h, ∀ u ∈ Ioo qL 1, ‖D u h‖ ≤ K := by
    intro h u hu
    exact hbound u ⟨hqLmem.1.trans_lt hu.1, hu.2.le⟩ h (qUpdate qs r u)
  have hdb : ∀ h, ‖d h‖ ≤ K := fun h => hbound 1 ⟨zero_lt_one, le_rfl⟩ h qs
  have hD : ∀ h, ∀ u ∈ Ioo qL 1,
      HasDerivAt (fun v => f v h) (D u h) u := by
    intro h u hu
    let qu := qUpdate qs r u
    have humem : u ∈ Icc (0 : ℝ) 1 := ⟨hqLmem.1.trans hu.1.le, hu.2.le⟩
    have hquself : qu r = u := qUpdate_self qs r u
    have hquleft : qExt qu r.val = qL := qExt_qUpdate_of_lt qs r u (by omega)
    have hquright : qExt qu (r.val + 2) = 1 := by
      rw [qExt_qUpdate_of_gt qs r u (by omega)]
      exact qExt_of_le qs (by simp [r])
    have hleft : deriv ξ (qExt qu r.val) < deriv ξ (qu r) := by
      rw [hquleft, hquself]
      exact hξ.strictMonoOn_deriv hqLmem humem hu.1
    have hright : deriv ξ (qu r) < deriv ξ (qExt qu (r.val + 2)) := by
      rw [hquself, hquright]
      exact hξ.strictMonoOn_deriv humem ⟨zero_le_one, le_rfl⟩ hu.2
    have hξd := hξ.hasDeriv_deriv u humem
    rw [← hquself] at hξd
    have hd := hasDerivAt_parisiX₀_qUpdate (ξ := ξ) (h := h) qu r hm hξd hleft hright
    have heq : (fun v => parisiX₀ ξ ms (qUpdate qu r v) (parisiLogCoshTerminal h)) =
        fun v => f v h := by
      funext v
      congr 1
      funext p
      simp [f, qu, qUpdate]
    rw [heq] at hd
    simpa [D, gap, qu, hquself] using hd
  have hd : ∀ h, HasDerivWithinAt (fun u => f u h) (d h) (Iic 1) 1 := by
    intro h
    simpa [f, d, r, hgapEq] using
      hasDerivWithinAt_parisiX₀_last_qUpdate (h := h) qs hm hξ hq hqlast
  have havg := hasDerivWithinAt_integral_of_dominated_left hqLlt hfm hfi hdm
    (integrable_const K : Integrable (fun _ : ℝ => K) μh) hDb hdb hD hd
  have hdEq : (∫ h, d h ∂μh) = (-1 / 2 : ℝ) * deriv (deriv ξ) 1 *
      (1 - mExt ms k) * randomFieldParisiQMoment μh ξ ms qs (Fin.last k) := by
    simp only [d, integral_const_mul, hgapEq, r, randomFieldParisiQMoment]
  rw [hdEq] at havg
  exact havg

/-- The admissible left derivative of the actual law-level functional at the last endpoint. -/
theorem hasDerivWithinAt_randomFieldParisiFunctional_last_qUpdate
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs)
    (hqlast : qs (Fin.last k) = 1) :
    HasDerivWithinAt
      (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs (Fin.last k) u))
      ((1 / 2 : ℝ) * (1 - mExt ms k) * deriv (deriv ξ) 1 *
        (1 - randomFieldParisiQMoment μh ξ ms qs (Fin.last k))) (Iic 1) 1 := by
  let r : Fin (k + 1) := Fin.last k
  let c := (1 / 2 : ℝ) * (1 - mExt ms k)
  have hX := hasDerivWithinAt_randomFieldParisiX₀_last_qUpdate ms qs hμh hm hξ hq hqlast
  have hθ := hasDerivAt_parisiTheta (hξ.hasDeriv 1 ⟨zero_le_one, le_rfl⟩)
    (hξ.hasDeriv_deriv 1 ⟨zero_le_one, le_rfl⟩)
  have hall := (hX.add (hθ.const_mul c).hasDerivWithinAt).const_add
    (parisiQConst ξ ms qs r)
  have heq : (fun u => randomFieldParisiFunctional μh ξ ms (qUpdate qs r u)) =
      fun u => parisiQConst ξ ms qs r +
        (randomFieldParisiX₀ μh ξ ms (qUpdate qs r u) + c * parisiTheta ξ u) := by
    funext u
    simpa [r, c, mExt] using randomFieldParisiFunctional_qUpdate_eq μh ξ ms qs r u
  rw [heq]
  exact hall.congr_deriv (by dsimp [c]; ring)

/-- The last overlap cannot equal one: its admissible left derivative is strictly positive. -/
theorem randomFieldParisiQ_last_lt_one_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hμh : Integrable id μh) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    qs (Fin.last k) < 1 := by
  by_contra hn
  have ho : qs (Fin.last k) = 1 := le_antisymm hmin.1.2.2 (not_lt.mp hn)
  have hd := hasDerivWithinAt_randomFieldParisiFunctional_last_qUpdate
    ms qs hμh hm hξ hmin.1 ho
  have hnonpos := hmin.last_derivWithin_nonpos ho (by simpa [ho] using hd)
  have hM := randomFieldParisiQMoment_last_lt_one (μh := μh) (ξ := ξ) qs hm ho
  have hgap : 0 < 1 - mExt ms k := by
    simpa [mExt] using hm.mExt_gap_pos (Fin.last k)
  have hs : 0 < deriv (deriv ξ) 1 :=
    hξ.second_pos 1 ⟨zero_le_one, le_rfl⟩ (by norm_num)
  have hpos : 0 < (1 / 2 : ℝ) * (1 - mExt ms k) * deriv (deriv ξ) 1 *
      (1 - randomFieldParisiQMoment μh ξ ms qs (Fin.last k)) := by positivity
  linarith

/-- A finite second moment under a probability law supplies the first-moment integrability
needed for the Parisi functional. -/
lemma NondegenerateExternalFieldLaw.integrable_id
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh) :
    Integrable id μh := by
  apply ((integrable_const (1 : ℝ)).add hμ.sq_integrable).mono'
    measurable_id.aestronglyMeasurable
  filter_upwards [] with h
  change ‖h‖ ≤ 1 + h ^ 2
  rw [Real.norm_eq_abs]
  rcases le_total 0 h with hh | hh
  · rw [abs_of_nonneg hh]
    nlinarith [sq_nonneg (h - 1)]
  · rw [abs_of_nonpos hh]
    nlinarith [sq_nonneg (h + 1)]

/-- Proposition 14.7.5 for a nondegenerate probability law of i.i.d. external fields.
All derivatives and endpoint bounds are consequences of the actual recursion. -/
theorem randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    (∀ n : ℕ, n ≤ k + 1 → qExt qs n < qExt qs (n + 1)) ∧
      ∀ r, qs r = randomFieldParisiQMoment μh ξ ms qs r := by
  exact randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin_of_endpoints
    ms qs hμ.integrable_id hm hξ hmin
    (randomFieldParisiQ_first_pos_of_isMin ms qs hμ.integrable_id hm hξ hμ hmin)
    (randomFieldParisiQ_last_lt_one_of_isMin ms qs hμ.integrable_id hm hξ hmin)

/-- A constant site law recovers the deterministic concrete moment, also at zero field. -/
@[simp] theorem randomFieldParisiQMoment_dirac (h : ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) :
    randomFieldParisiQMoment (Measure.dirac h) ξ ms qs r = parisiQMoment ξ h ms qs r := by
  simp [randomFieldParisiQMoment]

/-- A constant external field is nondegenerate exactly when it is nonzero. -/
@[simp] theorem nondegenerateExternalFieldLaw_dirac_iff (h : ℝ) :
    NondegenerateExternalFieldLaw (Measure.dirac h) ↔ h ≠ 0 := by
  constructor
  · intro hμ
    have hp := hμ.second_moment_pos
    simpa using (ne_of_gt (show 0 < h ^ 2 by simpa using hp)).imp
      (fun hz => by simp [hz])
  · intro hh
    refine ⟨?_, ?_⟩
    · exact integrable_dirac (by simp)
    · simpa using sq_pos_of_ne_zero hh

/-- The stationarity moment in Proposition 14.7.5 is explicitly the expectation at any
coordinate of the i.i.d. product law. -/
theorem iidExternalFieldParisiQ_strict_chain_and_eq_moment_of_isMin
    {N : ℕ} (i : Fin N) {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) :
    (∀ n : ℕ, n ≤ k + 1 → qExt qs n < qExt qs (n + 1)) ∧
      ∀ r, qs r = ∫ hVec, parisiQMoment ξ (hVec i) ms qs r
        ∂externalFieldVecLaw N μh := by
  obtain ⟨hchain, hmoment⟩ :=
    randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin ms qs hm hξ hμ hmin
  refine ⟨hchain, fun r => ?_⟩
  rw [hmoment r]
  exact randomFieldParisiQMoment_eq_integral_externalFieldVec_apply i ξ ms qs r hm

end

end SpinGlass
