import SpinGlass.Parisi.Variational.ParisiSpatialRegularity

/-!
# Variance response of a concrete inserted mass

The quantities here use the actual Cole-Hopf layer and its normalized Gaussian
tilt. Fourth-order regularity is derived from the Parisi suffix before applying
the mixed mass/variance identities (14.209)-(14.211). Variance derivatives are
taken within the admissible interval, including its endpoints.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- Real variance coordinates identify the actual and analytic layers, even
when the variance is clamped to zero. -/
theorem coleHopf_toNNReal_eq_gaussianLayer (m v : ℝ) (A : ℝ → ℝ) :
    coleHopf m v.toNNReal A = Aristotle.gaussianLayer m v A := by
  funext x
  exact coleHopf_eq_massTransform m v.toNNReal A x

/-- The analytic tilted mean is the project's normalized Gaussian tilt.
No integrability of `G` is needed for this integral identity. -/
theorem tiltedMean_eq_integral_coleHopfQ {A : ℝ → ℝ}
    (hAg : HasLinearGrowth A) (hAm : Measurable A)
    (G : ℝ → ℝ) (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    Aristotle.tiltedMean (gaussianReal 0 v) (fun z => A (x + z))
        (fun z => G (x + z)) m =
      ∫ z, G (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [Aristotle.tiltedMean]
  · unfold Aristotle.tiltedMean
    rw [← integral_div]
    refine integral_congr_ae (.of_forall fun z => ?_)
    change G (x + z) * Real.exp (m * A (x + z)) /
        (∫ w, Real.exp (m * A (x + w)) ∂gaussianReal 0 v) =
      G (x + z) * coleHopfQ m v A x z
    rw [coleHopfQ_eq hAg hAm hm, mul_div_assoc]

/-- Local inserted-mass derivative in (14.208), in actual layer notation. -/
noncomputable def coleHopfSplitMassResponse (m a : ℝ) (A : ℝ → ℝ) (x v : ℝ) : ℝ :=
  deriv (fun b => coleHopf m (a - v).toNNReal (coleHopf b v.toNNReal A) x) m

/-- The actual squared spatial moment in (14.209) and (14.211). -/
noncomputable def coleHopfSplitSpatialMoment (j : ℕ) (m a : ℝ)
    (A : ℝ → ℝ) (x v : ℝ) : ℝ :=
  ∫ z, (iteratedDeriv j (coleHopf m v.toNNReal A) (x + z)) ^ 2 *
    coleHopfQ m (a - v).toNNReal (coleHopf m v.toNNReal A) x z
    ∂gaussianReal 0 (a - v).toNNReal

/-- The concrete inserted derivative is the analytic split response. -/
theorem coleHopfSplitMassResponse_eq (m a : ℝ) (A : ℝ → ℝ) (x : ℝ) :
    coleHopfSplitMassResponse m a A x = Aristotle.splitMassResponse m a A x := by
  funext v
  simp only [coleHopfSplitMassResponse, Aristotle.splitMassResponse,
    coleHopf_toNNReal_eq_gaussianLayer]

/-- Identify the spatial moment with the squared derivative under the actual
Cole-Hopf tilt, including the zero-mass expectation branch. -/
theorem coleHopfSplitSpatialMoment_eq {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|) (j : ℕ) (m a x : ℝ) :
    coleHopfSplitSpatialMoment j m a A x = Aristotle.splitSpatialMoment j m a A x := by
  funext v
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  have hBL := abs_coleHopf_sub_le_of_lipschitz m hAm hL v.toNNReal
  have hBc := (lipschitzWith_toNNReal_of_abs_sub_le hBL).continuous
  have hBg := HasLinearGrowth.of_lipschitz hBL
  rw [coleHopfSplitSpatialMoment, Aristotle.splitSpatialMoment,
    ← coleHopf_toNNReal_eq_gaussianLayer]
  exact (tiltedMean_eq_integral_coleHopfQ hBg hBc.measurable
    (fun y => (iteratedDeriv j (coleHopf m v.toNNReal A) y) ^ 2) m
    (a - v).toNNReal x).symm

/-- The concrete split moment is nonnegative. -/
theorem coleHopfSplitSpatialMoment_nonneg (j : ℕ) (m a : ℝ)
    (A : ℝ → ℝ) (x v : ℝ) : 0 ≤ coleHopfSplitSpatialMoment j m a A x v :=
  integral_nonneg fun z => mul_nonneg (sq_nonneg _)
    (coleHopfQ_pos m (a - v).toNNReal (coleHopf m v.toNNReal A) x z).le

/-- An empty inserted variance interval has zero mass response. -/
theorem coleHopfSplitMassResponse_zero (m a : ℝ) (A : ℝ → ℝ) (x : ℝ) :
    coleHopfSplitMassResponse m a A x 0 = 0 := by
  rw [coleHopfSplitMassResponse_eq]
  exact Aristotle.splitMassResponse_zero m a A x

/-- A positive fixed outer mass transports a nearby inserted-mass derivative
through its actual Gaussian tilt. -/
theorem hasDerivAt_coleHopfSplit_mass_of_pos {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (a v x : ℝ)
    {b : ℝ} (hb : b ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun c => coleHopf m (a - v).toNNReal (coleHopf c v.toNNReal A) x)
      (coleHopfIterateMassDeriv (fun _ : Fin 1 => m)
        (fun _ : Fin 1 => (a - v).toNNReal) v.toNNReal A b x) b := by
  simpa only [coleHopfIterate_succ, coleHopfIterate_zero] using
    hasDerivAt_coleHopfIterate_mass_layer_of_mem_Ioo
      (fun _ : Fin 1 => m) (fun _ : Fin 1 => (a - v).toNNReal)
      (fun _ => hm) (fun _ => hm1) hAm hLip v.toNNReal hb x

/-- The actual local response is the propagated single-layer mass derivative. -/
theorem coleHopfSplitMassResponse_eq_massDeriv_of_pos {A : ℝ → ℝ}
    (hAm : Measurable A) (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (a v x : ℝ) :
    coleHopfSplitMassResponse m a A x v =
      coleHopfIterateMassDeriv (fun _ : Fin 1 => m)
        (fun _ : Fin 1 => (a - v).toNNReal) v.toNNReal A m x :=
  (hasDerivAt_coleHopfSplit_mass_of_pos hAm hLip hm hm1 a v x
    ⟨by linarith, by linarith⟩).deriv

/-- At zero outer mass the response is the Gaussian average of the actual
zero-mass derivative. The mass derivative is taken in an open neighborhood. -/
theorem coleHopfSplitMassResponse_zero_mass_eq {A : ℝ → ℝ}
    (hAm : Measurable A) (hLip : ∀ x y, |A y - A x| ≤ |y - x|) (a v x : ℝ) :
    coleHopfSplitMassResponse 0 a A x v =
      ∫ z, coleHopfMassDeriv 0 v.toNNReal A (x + z)
        ∂gaussianReal 0 (a - v).toNNReal := by
  have hzg : HasLinearGrowth id := ⟨0, 1, zero_le_one, by simp⟩
  have hz : Integrable id (gaussianReal 0 (a - v).toNNReal) :=
    hzg.toHasExpGrowth.integrable_gaussianReal measurable_id.aestronglyMeasurable
  have hd := hasDerivAt_integral_coleHopf_mass_comp measurable_id hz hAm hLip
    v.toNNReal x (m := 0) ⟨le_rfl, zero_le_one⟩
  simp only [id_eq] at hd
  have heq : (fun b => ∫ z, coleHopf b v.toNNReal A (z + x)
        ∂gaussianReal 0 (a - v).toNNReal) =
      fun b => coleHopf 0 (a - v).toNNReal (coleHopf b v.toNNReal A) x := by
    funext b
    rw [coleHopf_zero]
    exact integral_congr_ae (.of_forall fun z => by simp only [add_comm z x])
  unfold coleHopfSplitMassResponse
  rw [← heq, hd.deriv]
  exact integral_congr_ae (.of_forall fun z => by simp only [add_comm z x])

/-- The local response is measurable in the point where it is evaluated,
including at zero mass. This permits arbitrary probability laws for the field. -/
theorem measurable_coleHopfSplitMassResponse {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (a v : ℝ) :
    Measurable (fun x => coleHopfSplitMassResponse m a A x v) := by
  rcases eq_or_lt_of_le hm.1 with rfl | hm0
  · have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
      simpa only [one_mul] using hLip
    have hAg := HasLinearGrowth.of_lipschitz hL
    have hAc := (lipschitzWith_toNNReal_of_abs_sub_le hL).continuous
    obtain ⟨M, _, hB⟩ := exists_uniform_coleHopf_mass_first_derivative_bound v.toNNReal
    have hDb : ∀ y, |coleHopfMassDeriv 0 v.toNNReal A y| ≤ M := by
      intro y
      rw [← (hasDerivAt_coleHopf_mass hAg hAm v.toNNReal y 0).deriv]
      exact (hB A hAm hLip _ le_rfl y).2.1 0 ⟨by norm_num, by norm_num⟩
    have hc := (continuous_integral_comp_add_gaussianReal
      (continuous_coleHopfMassDeriv hAc hAg 0 v.toNNReal)
      (HasExpGrowth.of_bounded hDb)).comp
      (continuous_id.prodMk (continuous_const (y := ((a - v).toNNReal : ℝ))))
    simpa only [Function.comp_def, Real.toNNReal_coe,
      ← coleHopfSplitMassResponse_zero_mass_eq hAm hLip a v, id_eq] using hc.measurable
  · have heq : (fun x => coleHopfSplitMassResponse m a A x v) =
        coleHopfIterateMassDeriv (fun _ : Fin 1 => m)
          (fun _ : Fin 1 => (a - v).toNNReal) v.toNNReal A m :=
      funext fun x => coleHopfSplitMassResponse_eq_massDeriv_of_pos hAm hLip hm0 hm.2 a v x
    rw [heq]
    exact measurable_coleHopfIterateMassDeriv (fun _ => m) (fun _ => (a - v).toNNReal)
      (fun _ => hm0) (fun _ => hm.2) hAm hLip v.toNNReal hm

/-- A local response is uniformly bounded by its inserted variance ceiling.
The constant is independent of the outer variance, field, and layer input. -/
theorem exists_uniform_coleHopfSplitMassResponse_bound (V : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (A : ℝ → ℝ), Measurable A →
      (∀ x y, |A y - A x| ≤ |y - x|) → ∀ m ∈ Icc (0 : ℝ) 1,
      ∀ (a v x : ℝ), v.toNNReal ≤ V → |coleHopfSplitMassResponse m a A x v| ≤ M := by
  obtain ⟨M, hM, hB⟩ := exists_uniform_coleHopfIterate_mass_derivative_bound V
  refine ⟨M, hM, fun A hAm hLip m hm a v x hv => ?_⟩
  rcases eq_or_lt_of_le hm.1 with rfl | hm0
  · rw [coleHopfSplitMassResponse_zero_mass_eq hAm hLip]
    have h := norm_integral_le_of_norm_le_const
      (μ := gaussianReal 0 (a - v).toNNReal)
      (f := fun z => coleHopfMassDeriv 0 v.toNNReal A (x + z))
      (C := M)
      (.of_forall fun z => ?_)
    · simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using h
    · rw [Real.norm_eq_abs, ← coleHopfIterateMassDeriv_zero hAm hLip v.toNNReal hm]
      exact hB 0 (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ≥0)
        (fun p => Fin.elim0 p) (fun p => Fin.elim0 p) A hAm hLip _ hv 0 hm (x + z)
  · rw [coleHopfSplitMassResponse_eq_massDeriv_of_pos hAm hLip hm0 hm.2]
    exact hB 1 (fun _ => m) (fun _ => (a - v).toNNReal)
      (fun _ => hm0) (fun _ => hm.2) A hAm hLip _ hv m hm x

/-- Matching masses erase the variance split on its whole closed domain.
The identity does not differentiate across a clamped negative variance. -/
theorem coleHopfSplit_matching_mass {A : ℝ → ℝ}
    (hAg : HasLinearGrowth A) (hAm : Measurable A) (m : ℝ)
    {a v : ℝ} (hv : v ∈ Icc (0 : ℝ) a) :
    coleHopf m (a - v).toNNReal (coleHopf m v.toNNReal A) =
      coleHopf m a.toNNReal A := by
  have he : (a - v).toNNReal + v.toNNReal = a.toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.2 hv.2),
      Real.coe_toNNReal _ hv.1, Real.coe_toNNReal _ (hv.1.trans hv.2)]
    ring
  exact funext fun x => (coleHopf_coleHopf hAg hAm m _ _ x).trans (by rw [he])

/-- The local response transported by the preceding baseline cascade.
Its probability law is fixed in `v`, as required by (14.240)-(14.243). -/
noncomputable def coleHopfIterateSplitMassResponse {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (m a : ℝ) (A : ℝ → ℝ) (x v : ℝ) : ℝ :=
  ∫ zs, coleHopfSplitMassResponse m a A (x + ∑ p, zs p) v
    ∂cascadeTiltMeasure j ms (fun p => gaussianReal 0 (vs p))
      (fun zs => ENNReal.ofReal (Real.exp (coleHopf m a.toNNReal A (x + ∑ p, zs p))))

/-- Differentiate an inserted mass through the complete fixed prefix, then
identify the weight with the unsplit recursion at matching mass. This is the
positive-mass bridge in (14.240); no derivative is assumed as an input. -/
theorem hasDerivAt_coleHopfIterate_split_mass_of_pos {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    {a v : ℝ} (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivAt
      (fun b => coleHopfIterate j ms vs
        (coleHopf m (a - v).toNNReal (coleHopf b v.toNNReal A)) x)
      (coleHopfIterateSplitMassResponse ms vs m a A x v) m := by
  let D : ℝ → ℝ → ℝ := fun b =>
    if b ∈ Ioo (-2 : ℝ) 2 then
      coleHopfIterateMassDeriv (fun _ : Fin 1 => m)
        (fun _ : Fin 1 => (a - v).toNNReal) v.toNNReal A b
    else fun _ => 0
  have hDm : ∀ b, Measurable (D b) := by
    intro b
    dsimp only [D]
    split_ifs with hb
    · exact measurable_coleHopfIterateMassDeriv_of_mem_Ioo
        (fun _ : Fin 1 => m) (fun _ : Fin 1 => (a - v).toNNReal)
        (fun _ => hm) (fun _ => hm1) hAm hLip v.toNNReal hb
    · exact measurable_const
  have hball : ∀ b ∈ Metric.ball m (1 / 2), b ∈ Ioo (-2 : ℝ) 2 := by
    intro b hb
    rw [Metric.mem_ball, Real.dist_eq] at hb
    have hab := abs_lt.1 hb
    exact ⟨by linarith, by linarith⟩
  obtain ⟨M, _, hbound⟩ :=
    exists_uniform_coleHopfIterate_mass_derivative_bound_neighborhood v.toNNReal
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hGL : ∀ b y z,
      |coleHopf m (a - v).toNNReal (coleHopf b v.toNNReal A) z -
        coleHopf m (a - v).toNNReal (coleHopf b v.toNNReal A) y| ≤ 1 * |z - y| := by
    intro b
    have hB := abs_coleHopf_sub_le_of_lipschitz b hAm hL v.toNNReal
    exact abs_coleHopf_sub_le_of_lipschitz m
      (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable hB (a - v).toNNReal
  have hd := hasDerivAt_coleHopfIterate_ball ms vs (G' := D) (L := 1) (C := M)
    (δ := 1 / 2) (by norm_num) hpos hle hDm
    (fun b hb y => by
      simpa only [D, ite_eq_left (hball b hb)] using
        hasDerivAt_coleHopfSplit_mass_of_pos hAm hLip hm hm1 a v y (hball b hb))
    (fun b hb y => by
      simp only [D, ite_eq_left (hball b hb)]
      exact hbound 1 (fun _ => m) (fun _ => (a - v).toNNReal)
        (fun _ => hm) (fun _ => hm1) A hAm hLip _ le_rfl b
        (Ioo_subset_Icc_self (hball b hb)) y) hGL x
  have hm' : m ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hDeq : D m = fun y => coleHopfSplitMassResponse m a A y v := by
    simp only [D, ite_eq_left hm']
    exact funext fun y => (coleHopfSplitMassResponse_eq_massDeriv_of_pos hAm hLip hm hm1 a v y).symm
  rw [hDeq, coleHopfSplit_matching_mass (HasLinearGrowth.of_lipschitz hL) hAm m hv] at hd
  exact hd

/-- Append one Cole-Hopf layer at the inner end of an actual iterate. -/
theorem coleHopfIterate_snoc_eq {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) :
    coleHopfIterate (j + 1) (Fin.snoc ms m) (Fin.snoc vs v) A =
      coleHopfIterate j ms vs (coleHopf m v A) := by
  rw [Fin.snoc_eq_append, Fin.snoc_eq_append, coleHopfIterate_append,
    coleHopfIterate_succ, coleHopfIterate_zero]
  simp only [Fin.cons_zero]

/-- The complete split mass derivative can be averaged under any fixed
probability law with an integrable evaluation point. The derivative is the
actual fixed-baseline prefix response in (14.238)-(14.239). -/
theorem hasDerivAt_integral_coleHopfIterate_split_mass_comp_of_pos
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hHm : Measurable H) (hH : Integrable H μ)
    {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A) (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {a v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) a) :
    HasDerivAt
      (fun b => ∫ ω, coleHopfIterate j ms vs
        (coleHopf m (a - v).toNNReal (coleHopf b v.toNNReal A)) (H ω) ∂μ)
      (∫ ω, coleHopfIterateSplitMassResponse ms vs m a A (H ω) v ∂μ) m := by
  have hpos' : ∀ p : Fin (j + 1), 0 < Fin.snoc (α := fun _ => ℝ) ms m p := by
    intro p
    refine Fin.lastCases ?_ (fun r => ?_) p
    · simpa only [Fin.snoc_last] using hm
    · simpa only [Fin.snoc_castSucc] using hpos r
  have hle' : ∀ p : Fin (j + 1), Fin.snoc (α := fun _ => ℝ) ms m p ≤ 1 := by
    intro p
    refine Fin.lastCases ?_ (fun r => ?_) p
    · simpa only [Fin.snoc_last] using hm1
    · simpa only [Fin.snoc_castSucc] using hle r
  have hd := hasDerivAt_integral_coleHopfIterate_mass_layer_comp hHm hH
    (Fin.snoc ms m) (Fin.snoc vs (a - v).toNNReal) hpos' hle' hAm hLip
    v.toNNReal 0 (m := m) ⟨hm.le, hm1⟩
  simp only [coleHopfIterate_snoc_eq, add_zero] at hd
  have hD : ∀ x, coleHopfIterateMassDeriv (Fin.snoc ms m)
      (Fin.snoc vs (a - v).toNNReal) v.toNNReal A m x =
      coleHopfIterateSplitMassResponse ms vs m a A x v := by
    intro x
    have hd' := hasDerivAt_coleHopfIterate_mass_layer
      (Fin.snoc ms m) (Fin.snoc vs (a - v).toNNReal) hpos' hle' hAm hLip
      v.toNNReal (m := m) ⟨hm.le, hm1⟩ x
    simp only [coleHopfIterate_snoc_eq] at hd'
    exact hd'.unique (hasDerivAt_coleHopfIterate_split_mass_of_pos
      ms vs hpos hle hAm hLip hm hm1 hv x)
  have he : (∫ ω, coleHopfIterateMassDeriv (Fin.snoc ms m)
      (Fin.snoc vs (a - v).toNNReal) v.toNNReal A m (H ω) ∂μ) =
      ∫ ω, coleHopfIterateSplitMassResponse ms vs m a A (H ω) v ∂μ :=
    integral_congr_ae (.of_forall fun ω => hD (H ω))
  rw [he] at hd
  exact hd

/-- Formula (14.209) for the actual Parisi suffix. Spatial regularity and
derivative bounds are proved from the recursion; `v=0` and `v=a` are one-sided. -/
theorem hasDerivWithinAt_parisiQSuffix_splitMassResponse
    (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    {m a v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivWithinAt (coleHopfSplitMassResponse m a (parisiQSuffix ξ h ms qs r) x)
      (coleHopfSplitSpatialMoment 1 m a (parisiQSuffix ξ h ms qs r) x v / 2)
      (Icc (0 : ℝ) a) v := by
  obtain ⟨hA, hb⟩ := parisiQSuffix_spatial_regular_four ξ h ms qs r
  rw [coleHopfSplitMassResponse_eq,
    coleHopfSplitSpatialMoment_eq hA.continuous.measurable (abs_parisiQSuffix_sub_le _ _ _ _ _)]
  exact Aristotle.hasDerivWithinAt_splitMassResponse hA hb hm ha hv x

/-- Formula (14.211) for the actual suffix moment. The curvature is the
negative of the concrete squared second-derivative moment. -/
theorem hasDerivWithinAt_parisiQSuffix_splitSpatialMoment
    (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    {m a v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivWithinAt (coleHopfSplitSpatialMoment 1 m a (parisiQSuffix ξ h ms qs r) x)
      (-coleHopfSplitSpatialMoment 2 m a (parisiQSuffix ξ h ms qs r) x v)
      (Icc (0 : ℝ) a) v := by
  obtain ⟨hA, hb⟩ := parisiQSuffix_spatial_regular_four ξ h ms qs r
  rw [coleHopfSplitSpatialMoment_eq hA.continuous.measurable
    (abs_parisiQSuffix_sub_le _ _ _ _ _),
    coleHopfSplitSpatialMoment_eq hA.continuous.measurable (abs_parisiQSuffix_sub_le _ _ _ _ _)]
  exact Aristotle.hasDerivWithinAt_splitSpatialMoment hA hb hm ha hv x

/-- Local concavity in the variance variable for the actual suffix, including
a degenerate total variance. Averaging against preceding weights is separate. -/
theorem concaveOn_parisiQSuffix_splitMassResponse
    (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    {m a : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 ≤ a) (x : ℝ) :
    ConcaveOn ℝ (Icc (0 : ℝ) a)
      (coleHopfSplitMassResponse m a (parisiQSuffix ξ h ms qs r) x) := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · refine ⟨convex_Icc _ _, fun u hu v hv s t hs ht hst => ?_⟩
    have hu0 : u = 0 := le_antisymm hu.2 hu.1
    have hv0 : v = 0 := le_antisymm hv.2 hv.1
    simp [hu0, hv0, coleHopfSplitMassResponse_zero]
  · obtain ⟨hA, hb⟩ := parisiQSuffix_spatial_regular_four ξ h ms qs r
    rw [coleHopfSplitMassResponse_eq]
    exact Aristotle.concaveOn_splitMassResponse hA hb hm ha' x

end SpinGlass
