import SpinGlass.Parisi.Coupled.CoupledOriginalPressure

/-!
# The zero inserted-mass limit in the root coupled comparison

The spatial derivative of the actual Cole-Hopf layer is continuous in its
mass at zero. Bounded gradients allow this limit under every probability
field law. The value limit uses only a finite first field moment.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- Spatial differentiation of the actual layer is its tilted first
moment, including the zero-mass Gaussian expectation. -/
theorem deriv_coleHopf_eq_tiltedMean {A : ℝ → ℝ} (hA : ContDiff ℝ 2 A)
    {C₁ C₂ : ℝ} (hfirst : ∀ y, |deriv A y| ≤ C₁)
    (hsecond : ∀ y, |deriv (deriv A) y| ≤ C₂) (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    deriv (coleHopf m v A) x = Aristotle.tiltedMean (gaussianReal 0 v)
      (fun z => A (x + z)) (fun z => deriv A (x + z)) m := by
  have hAg := HasLinearGrowth.of_bounded_deriv
    (fun y => (hA.differentiable (by norm_num) y).hasDerivAt) hfirst
  rw [tiltedMean_eq_integral_coleHopfQ hAg hA.continuous.measurable]
  exact ((coleHopf_spatial_derivative_formulas hA hfirst hsecond m v).1 x).deriv

/-- The gradient of a smooth bounded-derivative input survives the
zero-mass limit, with zero Gaussian variance allowed. -/
theorem continuousAt_deriv_coleHopf_mass_zero {A : ℝ → ℝ} (hA : ContDiff ℝ 2 A)
    {C₁ C₂ : ℝ} (hfirst : ∀ y, |deriv A y| ≤ C₁)
    (hsecond : ∀ y, |deriv (deriv A) y| ≤ C₂) (v : ℝ≥0) (x : ℝ) :
    ContinuousAt (fun m => deriv (coleHopf m v A) x) 0 := by
  have hAg := HasLinearGrowth.of_bounded_deriv
    (fun y => (hA.differentiable (by norm_num) y).hasDerivAt) hfirst
  have hXm : Measurable (fun z => A (x + z)) :=
    hA.continuous.measurable.comp (measurable_const.add measurable_id)
  have hYm : Measurable (fun z => deriv A (x + z)) :=
    (measurable_deriv A).comp (measurable_const.add measurable_id)
  have henv : Integrable (fun z => Real.exp (1 * |A (x + z)|)) (gaussianReal 0 v) := by
    obtain ⟨a, b, hb, hbound⟩ := hAg.comp_add_const x
    have hg : HasLinearGrowth (fun z => |A (x + z)|) :=
      ⟨a, b, hb, by simpa only [abs_abs] using hbound⟩
    exact (hg.exp_mul 1).integrable_gaussianReal (by fun_prop)
  have hyenv : Integrable
      (fun z => |deriv A (x + z)| * Real.exp (1 * |A (x + z)|)) (gaussianReal 0 v) := by
    apply (henv.const_mul C₁).mono'
      ((continuous_abs.measurable.comp hYm).mul
        (((continuous_abs.measurable.comp hXm).const_mul 1).exp)).aestronglyMeasurable
      (.of_forall fun z => ?_)
    change norm (abs (deriv A (x + z)) * Real.exp (1 * abs (A (x + z)))) ≤
      C₁ * Real.exp (1 * |A (x + z)|)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right (hfirst _) (Real.exp_pos _).le
  have hd := Aristotle.hasDerivAt_tiltedMean hXm hYm (m := 0) (a := 1)
    (by norm_num) henv hyenv
  have he : (fun m => deriv (coleHopf m v A) x) =
      Aristotle.tiltedMean (gaussianReal 0 v) (fun z => A (x + z))
        (fun z => deriv A (x + z)) := by
    funext m
    exact deriv_coleHopf_eq_tiltedMean hA hfirst hsecond m v x
  rw [he]
  exact hd.continuousAt

/-- A probability average of the squared actual gradient converges
at zero mass. Its envelope is one, independently of the field realization. -/
theorem continuousAt_integral_deriv_coleHopf_sq_mass_zero {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hHm : Measurable H) {A : ℝ → ℝ} (hA : ContDiff ℝ 2 A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|) {C : ℝ}
    (hsecond : ∀ y, |deriv (deriv A) y| ≤ C) (v : ℝ≥0) :
    ContinuousAt (fun m => ∫ ω, deriv (coleHopf m v A) (H ω) ^ 2 ∂μ) 0 := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hLip
  have hfirst : ∀ y, |deriv A y| ≤ 1 := by
    intro y
    simpa only [Real.norm_eq_abs, Real.toNNReal_one, NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := y) (lipschitzWith_toNNReal_of_abs_sub_le hL)
  have hB : ∀ m y, |deriv (coleHopf m v A) y| ≤ 1 := by
    intro m y
    have hb := abs_coleHopf_sub_le_of_lipschitz m hA.continuous.measurable hL v
    simpa only [Real.norm_eq_abs, Real.toNNReal_one, NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := y) (lipschitzWith_toNNReal_of_abs_sub_le hb)
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact .of_forall fun m => ((measurable_deriv (coleHopf m v A)).comp hHm).pow_const 2
      |>.aestronglyMeasurable
  · exact .of_forall fun m => .of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [(abs_le.1 (hB m (H ω))).1, (abs_le.1 (hB m (H ω))).2]
  · exact integrable_const 1
  · exact .of_forall fun ω => (continuousAt_deriv_coleHopf_mass_zero hA hfirst hsecond v (H ω)).tendsto.pow 2

/-- No-prefix conditional squares are the squared gradient of the
full positive-mass Cole-Hopf recursion. -/
theorem cascadeTiltTanhSq_zero_eq_deriv_sq {n : ℕ} (ms : Fin n → ℝ) (vs : Fin n → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (x : ℝ) :
    cascadeTiltTanhSq ms vs 0 x =
      deriv (coleHopfIterate n ms vs (parisiLogCoshTerminal 0)) x ^ 2 := by
  rw [cascadeTiltTanhSq_eq_prefix_deriv_sq ms vs hpos hle 0 (by omega)]
  simp only [Nat.sub_zero, zero_add]
  have hms : (fun p : Fin n => ms ⟨p.val, by omega⟩) = ms := by
    funext p
    rfl
  have hvs : (fun p : Fin n => vs ⟨p.val, by omega⟩) = vs := by
    funext p
    rfl
  rw [hms, hvs]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rw [cascadeTiltMeasure]
  dsimp only [cascadeTiltDensity]
  rw [← Pi.one_def, withDensity_one]
  simp only [integral_const, probReal_univ, one_smul]

/-- The first positive inserted mass acts on the driven inner root
piece; every later one-copy level is the original Parisi level. -/
noncomputable def parisiRootResponseMasses {k : ℕ} (ms : Fin k → ℝ) (m : ℝ) :
    Fin (k + 2) → ℝ := Fin.cons m (parisiLevelMasses ms)

noncomputable def parisiRootResponseVars (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (v : ℝ) : Fin (k + 2) → ℝ≥0 :=
  Fin.cons v.toNNReal (parisiLevelVars ξ qs)

/-- The actual zero-coupling moment of the positive root insertion. -/
noncomputable def parisiRootCouplingMoment (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (v m : ℝ) : ℝ :=
  ∫ hz : ℝ × ℝ, deriv (coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs)) (hz.1 + hz.2) ^ 2
    ∂μh.prod (gaussianReal 0 (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal)

/-- The half zero-coupling value of that positive root insertion. -/
noncomputable def parisiRootCouplingZeroValue (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (v m : ℝ) : ℝ :=
  ∫ hz : ℝ × ℝ, coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs) (hz.1 + hz.2)
    ∂μh.prod (gaussianReal 0 (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal)

/-- The root inserted-cascade slope has an actual zero-mass limit
under any probability external-field law. -/
theorem continuousAt_parisiRootCouplingMoment_zero {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (v : ℝ) :
    ContinuousAt (parisiRootCouplingMoment μh ξ ms qs v) 0 := by
  obtain ⟨hA, C, hC⟩ := parisiRootSuffix_spatial_regular_four ξ ms qs
  have hsecond : ∀ y, |deriv (deriv (parisiRootSuffix ξ ms qs)) y| ≤ C := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hC 2 (by decide)
  exact continuousAt_integral_deriv_coleHopf_sq_mass_zero (measurable_fst.add measurable_snd)
    (hA.of_le (by norm_num)) (abs_parisiRootSuffix_sub_le ξ ms qs) hsecond v.toNNReal

theorem parisiRootCouplingMoment_zero {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (v : ℝ) :
    parisiRootCouplingMoment μh ξ ms qs v 0 = parisiRootUSpatialMoment 1 μh ξ ms qs v := by
  have hL : ∀ x y, |parisiRootSuffix ξ ms qs y - parisiRootSuffix ξ ms qs x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiRootSuffix_sub_le ξ ms qs
  have hA := (parisiRootSuffix_spatial_regular_four ξ ms qs).1
  have hb : ∀ y, |deriv (coleHopf 0 v.toNNReal (parisiRootSuffix ξ ms qs)) y| ≤ 1 := by
    intro y
    simpa only [Real.norm_eq_abs, Real.toNNReal_one, NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := y) (lipschitzWith_toNNReal_of_abs_sub_le
        (abs_coleHopf_sub_le_of_lipschitz 0 hA.continuous.measurable hL v.toNNReal))
  have hi : Integrable (fun hz : ℝ × ℝ =>
      deriv (coleHopf 0 v.toNNReal (parisiRootSuffix ξ ms qs)) (hz.1 + hz.2) ^ 2)
      (μh.prod (gaussianReal 0 (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal)) :=
    Integrable.of_bound (((measurable_deriv _).comp (measurable_fst.add measurable_snd)).pow_const 2
      |>.aestronglyMeasurable) 1 (.of_forall fun hz => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [(abs_le.1 (hb (hz.1 + hz.2))).1, (abs_le.1 (hb (hz.1 + hz.2))).2])
  unfold parisiRootCouplingMoment parisiRootUSpatialMoment coleHopfSplitSpatialMoment
  rw [integral_prod _ hi]
  simp only [iteratedDeriv_one, coleHopfQ_zero, mul_one]

/-- The root inserted-cascade value also has its actual zero-mass
limit, using a finite first moment and no exponential field moment. -/
theorem continuousAt_parisiRootCouplingZeroValue_zero {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (v : ℝ) :
    ContinuousAt (parisiRootCouplingZeroValue μh ξ ms qs v) 0 := by
  let w := (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal
  have hzg : HasLinearGrowth id := ⟨0, 1, zero_le_one, by simp⟩
  have hz : Integrable id (gaussianReal 0 w) :=
    hzg.toHasExpGrowth.integrable_gaussianReal measurable_id.aestronglyMeasurable
  have hH : Integrable (fun hz : ℝ × ℝ => hz.1 + hz.2) (μh.prod (gaussianReal 0 w)) :=
    (hμ.comp_fst _).add (hz.comp_snd _)
  have hd := hasDerivAt_integral_coleHopf_mass_comp (measurable_fst.add measurable_snd) hH
    (parisiRootSuffix_spatial_regular_four ξ ms qs).1.continuous.measurable
    (abs_parisiRootSuffix_sub_le ξ ms qs) v.toNNReal 0 (m := 0) ⟨le_rfl, zero_le_one⟩
  unfold parisiRootCouplingZeroValue
  simpa only [add_zero, Pi.add_apply, Prod.fst, Prod.snd] using hd.continuousAt

/-- A Lipschitz layer can be averaged at an integrable spatial shift,
for every mass, without exponential moments of the shift law. -/
theorem integrable_coleHopf_comp_shift {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {H : Ω → ℝ}
    (hHm : Measurable H) (hH : Integrable H μ) {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|) (m : ℝ) (v : ℝ≥0) :
    Integrable (fun ω => coleHopf m v A (H ω)) μ := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by simpa only [one_mul] using hLip
  have hBL := abs_coleHopf_sub_le_of_lipschitz m hAm hL v
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hBL).continuous.measurable.comp hHm
  apply ((integrable_const |coleHopf m v A 0|).add hH.abs).mono' hBm.aestronglyMeasurable
    (.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  have hh := hBL 0 (H ω)
  have ha := abs_sub_abs_le_abs_sub (coleHopf m v A (H ω)) (coleHopf m v A 0)
  simp only [sub_zero, one_mul] at hh
  change |coleHopf m v A (H ω)| ≤ |coleHopf m v A 0| + |H ω|
  linarith

/-- Matching zero root masses merge the two actual Gaussian averages,
so the limiting half zero value is the old Parisi recursion average. -/
theorem parisiRootCouplingZeroValue_zero {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) :
    parisiRootCouplingZeroValue μh ξ ms qs v 0 = ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  let w := (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal
  have hzg : HasLinearGrowth id := ⟨0, 1, zero_le_one, by simp⟩
  have hz : Integrable id (gaussianReal 0 w) :=
    hzg.toHasExpGrowth.integrable_gaussianReal measurable_id.aestronglyMeasurable
  have hH : Integrable (fun hz : ℝ × ℝ => hz.1 + hz.2) (μh.prod (gaussianReal 0 w)) :=
    (hμ.comp_fst _).add (hz.comp_snd _)
  have hA := (parisiRootSuffix_spatial_regular_four ξ ms qs).1
  have hL : ∀ x y, |parisiRootSuffix ξ ms qs y - parisiRootSuffix ξ ms qs x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiRootSuffix_sub_le ξ ms qs
  have hi := integrable_coleHopf_comp_shift (H := fun hz : ℝ × ℝ => hz.1 + hz.2)
    (measurable_fst.add measurable_snd) hH
    hA.continuous.measurable (abs_parisiRootSuffix_sub_le ξ ms qs) 0 v.toNNReal
  unfold parisiRootCouplingZeroValue
  rw [integral_prod _ hi]
  apply integral_congr_ae (.of_forall fun h => ?_)
  rw [← coleHopf_zero]
  change coleHopf 0 (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal
    (coleHopf 0 v.toNNReal (parisiRootSuffix ξ ms qs)) h = _
  rw [coleHopfSplit_matching_mass (HasLinearGrowth.of_lipschitz hL) hA.continuous.measurable 0 hv,
    closedParisiX₀_translate, coleHopfIterate_succ]
  change coleHopf 0 (deriv ξ (qs 0) - deriv ξ 0).toNNReal (parisiRootSuffix ξ ms qs) h =
    coleHopf 0 (parisiVar ξ qs 0) (parisiRootSuffix ξ ms qs) h
  have hvar : parisiVar ξ qs 0 = (deriv ξ (qs 0) - deriv ξ 0).toNNReal := by
    simp only [parisiVar, qExt_zero, qExt_succ_of_lt qs (Nat.succ_pos k)]
    rfl
  rw [hvar]

theorem parisiRootResponseMasses_pos {k : ℕ} (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m) : ∀ i, 0 < parisiRootResponseMasses ms m i := by
  intro i
  refine Fin.cases hm0 (fun j => ?_) i
  change 0 < parisiLevelMasses ms j
  rw [parisiLevelMasses_apply]
  exact hm.mExt_pos (by omega)

theorem parisiRootResponseMasses_le_one {k : ℕ} (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm1 : m ≤ 1) : ∀ i, parisiRootResponseMasses ms m i ≤ 1 := by
  intro i
  refine Fin.cases hm1 (fun j => ?_) i
  change parisiLevelMasses ms j ≤ 1
  rw [parisiLevelMasses_apply]
  exact mExt_le_one (fun r => (hm.2.2 r).le) _

theorem parisiRootResponseMasses_monotone {k : ℕ} (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hmr : m ≤ mExt ms 1) : Monotone (parisiRootResponseMasses ms m) := by
  have hmono : Monotone (parisiLevelMasses ms) := by
    intro i j hij
    simp only [parisiLevelMasses_apply]
    exact hm.monotone_mExt (by change i.val + 1 ≤ j.val + 1; omega)
  have hfirst : m ≤ parisiLevelMasses ms 0 := by
    simpa only [parisiLevelMasses_apply, Fin.val_zero, zero_add] using hmr
  simpa only [parisiRootResponseMasses, Fin.insertNth_zero'] using
    Fin.insertNth_zero_monotone hmono m hfirst

/-- The actual positive root insertion's conditional square is the
spatial moment used in its proved zero-mass limit. -/
theorem cascadeTiltTanhSq_parisi_root_eq (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (v x : ℝ) :
    cascadeTiltTanhSq (parisiRootResponseMasses ms m) (parisiRootResponseVars ξ qs v) 0 x =
      deriv (coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs)) x ^ 2 := by
  rw [cascadeTiltTanhSq_zero_eq_deriv_sq _ _ (parisiRootResponseMasses_pos ms hm hm0)
    (parisiRootResponseMasses_le_one ms hm hm1)]
  simp only [parisiRootResponseMasses, parisiRootResponseVars, coleHopfIterate_succ,
    Fin.cons_zero, Fin.tail_cons, parisiRootSuffix]

end SpinGlass
