import SpinGlass.Parisi.Variational.ParisiVariancePropagation
import SpinGlass.Parisi.Variational.ParisiMassPropagation

/-!
# Complementary outer-mass response

The mirror splitting in Section 14.9 varies the outer mass of two matched
Cole-Hopf layers. Differentiating their semigroup identity expresses this
response as the full mass derivative minus the existing inner-mass response.
All quantities below use the actual Gaussian layers and normalized tilts.
-/

open MeasureTheory ProbabilityTheory Set
open Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

/-- Differentiate the exponential integral when both the outer exponent and
the inner Cole-Hopf mass vary. The Gaussian envelope is derived from the
actual uniform mass and value bounds, including zero Gaussian variances. -/
theorem hasDerivAt_integral_exp_mul_coleHopf_mass
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (v w : ℝ≥0) (x : ℝ) :
    HasDerivAt (fun c => ∫ z, Real.exp (c * coleHopf c v A (x + z)) ∂gaussianReal 0 w)
      (∫ z, (coleHopf m v A (x + z) + m * coleHopfMassDeriv m v A (x + z)) *
        Real.exp (m * coleHopf m v A (x + z)) ∂gaussianReal 0 w) m := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hAc := (lipschitzWith_toNNReal_of_abs_sub_le hL).continuous
  have hAg := HasLinearGrowth.of_lipschitz hL
  have hBc : ∀ c, Continuous (coleHopf c v A) := fun c =>
    (lipschitzWith_toNNReal_of_abs_sub_le
      (abs_coleHopf_sub_le_of_lipschitz c hAm hL v)).continuous
  have hBg : ∀ c, HasLinearGrowth (coleHopf c v A) := fun c =>
    HasLinearGrowth.of_lipschitz (abs_coleHopf_sub_le_of_lipschitz c hAm hL v)
  obtain ⟨M, hM, hbound⟩ := exists_uniform_coleHopf_mass_first_derivative_bound v
  let K := |A x| + M
  have _hK : 0 ≤ K := add_nonneg (abs_nonneg _) hM.le
  have hmass : ∀ c ∈ Metric.ball m (1 / 2), c ∈ Icc (-2 : ℝ) 2 := by
    intro c hc
    rw [Metric.mem_ball, Real.dist_eq] at hc
    have hh := abs_lt.1 hc
    exact ⟨by linarith, by linarith⟩
  have hD : ∀ c ∈ Metric.ball m (1 / 2), ∀ y,
      |coleHopfMassDeriv c v A y| ≤ M := by
    intro c hc y
    rw [← (hasDerivAt_coleHopf_mass hAg hAm v y c).deriv]
    exact (hbound A hAm hLip v le_rfl y).2.1 c (hmass c hc)
  have hvalue : ∀ c ∈ Metric.ball m (1 / 2), ∀ z,
      |coleHopf c v A (x + z)| ≤ K + |z| := by
    intro c hc z
    have hh := (hbound A hAm hLip v le_rfl (x + z)).2.2 c (hmass c hc)
    have hA := hLip x (x + z)
    rw [add_sub_cancel_left] at hA
    have ht := abs_sub_abs_le_abs_sub (coleHopf c v A (x + z)) (A (x + z))
    have ht' := abs_sub_abs_le_abs_sub (A (x + z)) (A x)
    dsimp only [K]
    linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 w) (F := fun c z => Real.exp (c * coleHopf c v A (x + z)))
    (F' := fun c z => (coleHopf c v A (x + z) + c * coleHopfMassDeriv c v A (x + z)) *
      Real.exp (c * coleHopf c v A (x + z)))
    (bound := fun z => Real.exp (3 * K + 2 * M) * Real.exp (3 * |z|))
    (s := Metric.ball m (1 / 2)) (Metric.ball_mem_nhds _ (by norm_num))
    (.of_forall fun c =>
      (((hBc c).measurable.comp (measurable_const.add measurable_id)).const_mul c).exp
        |>.aestronglyMeasurable)
    (integrable_exp_mul_comp_add (hBg m) (hBc m).measurable m w x)
    (by
      have hDm : Measurable (fun z : ℝ => coleHopfMassDeriv m v A (x + z)) :=
        (continuous_coleHopfMassDeriv hAc hAg m v).measurable.comp
        (measurable_const.add measurable_id)
      have hBm : Measurable (fun z : ℝ => coleHopf m v A (x + z)) :=
        (hBc m).measurable.comp (measurable_const.add measurable_id)
      exact ((hBm.add (hDm.const_mul m)).mul ((hBm.const_mul m).exp)).aestronglyMeasurable)
    ?_ ((integrable_exp_mul_abs_gaussianReal 0 w 3).const_mul _) ?_).2
  · refine .of_forall fun z c hc => ?_
    have hcabs : |c| ≤ 2 := abs_le.2 (hmass c hc)
    have hb := hvalue c hc z
    have hd := hD c hc (x + z)
    have hsum : |coleHopf c v A (x + z) + c * coleHopfMassDeriv c v A (x + z)| ≤
        K + |z| + 2 * M := by
      have hh := abs_add_le (coleHopf c v A (x + z)) (c * coleHopfMassDeriv c v A (x + z))
      rw [abs_mul] at hh
      have hmul := mul_le_mul hcabs hd (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      linarith
    have hexp : Real.exp (c * coleHopf c v A (x + z)) ≤ Real.exp (2 * (K + |z|)) := by
      apply Real.exp_le_exp.2
      exact (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul hcabs hb (abs_nonneg _) (by norm_num))
    have hsumexp : K + |z| + 2 * M ≤ Real.exp (K + |z| + 2 * M) := by
      linarith [Real.add_one_le_exp (K + |z| + 2 * M)]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (K + |z| + 2 * M) * Real.exp (2 * (K + |z|)) :=
        mul_le_mul (hsum.trans hsumexp) hexp (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (3 * K + 2 * M) * Real.exp (3 * |z|) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  · refine .of_forall fun z c _ => ?_
    have hd := ((hasDerivAt_id c).mul (hasDerivAt_coleHopf_mass hAg hAm v (x + z) c)).exp
    exact hd.congr_deriv (by simp only [Pi.mul_apply, id_eq, one_mul]; ring)

/-- Differentiating the matched-mass semigroup decomposes the full mass
derivative into the outer derivative and the Gaussian-transported inner
derivative. The identity is concrete, including either zero variance. -/
theorem coleHopfMassDeriv_split_add
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (v w : ℝ≥0) (x : ℝ) :
    coleHopfMassDeriv m w (coleHopf m v A) x +
      (∫ z, coleHopfMassDeriv m v A (x + z) *
        coleHopfQ m w (coleHopf m v A) x z ∂gaussianReal 0 w) =
      coleHopfMassDeriv m (w + v) A x := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hAg := HasLinearGrowth.of_lipschitz hL
  have hAc := (lipschitzWith_toNNReal_of_abs_sub_le hL).continuous
  let B := coleHopf m v A
  let D := coleHopfMassDeriv m v A
  let E : ℝ → ℝ := fun y => Real.exp (m * B y)
  let I := ∫ z, E (x + z) ∂gaussianReal 0 w
  have hBL : ∀ y z, |B z - B y| ≤ 1 * |z - y| :=
    abs_coleHopf_sub_le_of_lipschitz m hAm hL v
  have hBc := (lipschitzWith_toNNReal_of_abs_sub_le hBL).continuous
  have hBg := HasLinearGrowth.of_lipschitz hBL
  have hDc : Continuous D := continuous_coleHopfMassDeriv hAc hAg m v
  obtain ⟨M, _, hbound⟩ := exists_uniform_coleHopf_mass_first_derivative_bound v
  have hDb : ∀ y, |D y| ≤ M := by
    intro y
    dsimp only [D]
    rw [← (hasDerivAt_coleHopf_mass hAg hAm v y m).deriv]
    exact (hbound A hAm hLip v le_rfl y).2.1 m ⟨by linarith, by linarith⟩
  have hDg := HasExpGrowth.of_bounded hDb
  have hEm : Measurable E := (hBc.measurable.const_mul m).exp
  have hEg : HasExpGrowth E := hBg.exp_mul m
  have hBm : Measurable (fun z : ℝ => B (x + z) * E (x + z)) :=
    (hBc.measurable.mul hEm).comp (measurable_const.add measurable_id)
  have hDm : Measurable (fun z : ℝ => D (x + z) * E (x + z)) :=
    (hDc.measurable.mul hEm).comp (measurable_const.add measurable_id)
  have hBint : Integrable (fun z => B (x + z) * E (x + z)) (gaussianReal 0 w) :=
    ((hBg.toHasExpGrowth.mul hEg).comp_add_const x).integrable_gaussianReal
      hBm.aestronglyMeasurable
  have hDint : Integrable (fun z => D (x + z) * E (x + z)) (gaussianReal 0 w) :=
    ((hDg.mul hEg).comp_add_const x).integrable_gaussianReal
      hDm.aestronglyMeasurable
  have hIpos : 0 < I := integral_exp_mul_comp_add_pos hBg hBc.measurable m w x
  have hI := hasDerivAt_integral_exp_mul_coleHopf_mass hAm hLip hm hm1 v w x
  have hfun : ∀ᶠ c in 𝓝 m, coleHopf c w (coleHopf c v A) x =
      Real.log (∫ z, Real.exp (c * coleHopf c v A (x + z)) ∂gaussianReal 0 w) / c := by
    filter_upwards [isOpen_ne.mem_nhds hm.ne'] with c hc
    rw [coleHopf_of_ne hc, one_div, inv_mul_eq_div]
  have hd := ((hI.log hIpos.ne').div (hasDerivAt_id m) hm.ne').congr_of_eventuallyEq hfun
  have hsem : (fun c => coleHopf c w (coleHopf c v A) x) =
      fun c => coleHopf c (w + v) A x :=
    funext fun c => coleHopf_coleHopf hAg hAm c w v x
  rw [hsem] at hd
  have hEq : ((∫ z, (B (x + z) + m * D (x + z)) * E (x + z) ∂gaussianReal 0 w) /
        I * m - Real.log I) / m ^ 2 = coleHopfMassDeriv m (w + v) A x := by
    simpa only [id_eq, mul_one] using hd.unique (hasDerivAt_coleHopf_mass hAg hAm (w + v) x m)
  have hInt : (∫ z, (B (x + z) + m * D (x + z)) * E (x + z) ∂gaussianReal 0 w) =
      (∫ z, B (x + z) * E (x + z) ∂gaussianReal 0 w) +
        m * (∫ z, D (x + z) * E (x + z) ∂gaussianReal 0 w) := by
    simp_rw [add_mul, mul_assoc]
    rw [integral_add hBint (hDint.const_mul m), integral_const_mul]
  have hBQ : (∫ z, B (x + z) * coleHopfQ m w B x z ∂gaussianReal 0 w) =
      (∫ z, B (x + z) * E (x + z) ∂gaussianReal 0 w) / I := by
    rw [← integral_div]
    exact integral_congr_ae (.of_forall fun z => by
      beta_reduce
      rw [coleHopfQ_eq hBg hBc.measurable hm.ne', mul_div_assoc])
  have hDQ : (∫ z, D (x + z) * coleHopfQ m w B x z ∂gaussianReal 0 w) =
      (∫ z, D (x + z) * E (x + z) ∂gaussianReal 0 w) / I := by
    rw [← integral_div]
    exact integral_congr_ae (.of_forall fun z => by
      beta_reduce
      rw [coleHopfQ_eq hBg hBc.measurable hm.ne', mul_div_assoc])
  have hcalc : (((∫ z, B (x + z) * E (x + z) ∂gaussianReal 0 w) +
        m * (∫ z, D (x + z) * E (x + z) ∂gaussianReal 0 w)) / I * m - Real.log I) / m ^ 2 =
      coleHopfMassDeriv m w B x + (∫ z, D (x + z) * E (x + z) ∂gaussianReal 0 w) / I := by
    rw [coleHopfMassDeriv, ite_eq_right hm.ne', hBQ, coleHopf_of_ne hm.ne']
    change _ = 1 / m * ((∫ z, B (x + z) * E (x + z) ∂gaussianReal 0 w) / I -
      1 / m * Real.log I) + _
    field_simp
    ring
  rw [hInt, hcalc] at hEq
  change coleHopfMassDeriv m w B x + (∫ z, D (x + z) * coleHopfQ m w B x z
    ∂gaussianReal 0 w) = _
  rw [hDQ]
  exact hEq

/-- A single positive-mass cascade tilt is exactly the normalized Gaussian
Cole-Hopf tilt. This identity averages bounded measurable signed observables. -/
theorem integral_cascadeTiltMeasure_one_eq_coleHopfQ
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (v : ℝ≥0) (x : ℝ)
    {F : ℝ → ℝ} (hFm : Measurable F) {C : ℝ} (hF : ∀ y, |F y| ≤ C) :
    (∫ zs, F (x + ∑ p, zs p)
      ∂cascadeTiltMeasure 1 (fun _ => m) (fun _ => gaussianReal 0 v)
        (fun zs => ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p))))) =
      ∫ z, F (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hGm : Measurable (fun zs : Fin 1 → ℝ =>
      ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (hAm.comp (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))))
  have hGpos : ∀ zs : Fin 1 → ℝ,
      0 < ENNReal.ofReal (Real.exp (A (x + ∑ p, zs p))) :=
    fun _ => ENNReal.ofReal_pos.2 (Real.exp_pos _)
  have hfin := lintegral_ofReal_exp_comp_add_sum_pi_gaussianReal_ne_top
    (fun _ : Fin 1 => v) hL x
  have hobs : Measurable (fun zs : Fin 1 → ℝ => F (x + ∑ p, zs p)) :=
    hFm.comp (measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))
  have hi := (integrable_toReal_cascadeTiltDensity 1 (fun _ => m)
    (fun _ => gaussianReal 0 v) hGm hGpos (fun _ => hm) (fun _ => hm1) hfin).bdd_mul
    hobs.aestronglyMeasurable (.of_forall fun zs => by
      rw [Real.norm_eq_abs]
      exact hF _)
  have his : Integrable (fun zs : Fin 1 → ℝ =>
      (cascadeTiltDensity 1 (fun _ => m) (fun _ => gaussianReal 0 v)
        (fun ys => ENNReal.ofReal (Real.exp (A (x + ∑ p, ys p)))) zs).toReal •
          F (x + ∑ p, zs p)) (Measure.pi (fun _ => gaussianReal 0 v)) := by
    simpa only [smul_eq_mul, mul_comm] using hi
  rw [integral_cascadeTiltMeasure 1 (fun _ => m) (fun _ => gaussianReal 0 v)
    hGm hGpos (fun _ => hm) (fun _ => hm1) hfin,
    integral_pi_fin_succ (fun _ : Fin 1 => gaussianReal 0 v) his]
  apply integral_congr_ae
  refine .of_forall fun z => ?_
  simp_rw [cascadeTiltDensity_gaussian_eq_exp_tiltLog 1 (fun _ => m)
    (fun _ => v) (fun _ => hm) hL]
  simp [coleHopfIterateTiltLog, coleHopfIterate_succ, coleHopfQ, mul_comm]

/-- The local inner response is its Gaussian-transported single-layer mass
derivative, with the actual normalized weight. -/
theorem coleHopfSplitMassResponse_eq_integral_massDeriv_of_pos
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (a v x : ℝ) :
    coleHopfSplitMassResponse m a A x v =
      ∫ z, coleHopfMassDeriv m v.toNNReal A (x + z) *
        coleHopfQ m (a - v).toNNReal (coleHopf m v.toNNReal A) x z
          ∂gaussianReal 0 (a - v).toNNReal := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hB := abs_coleHopf_sub_le_of_lipschitz m hAm hL v.toNNReal
  have hBm := (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
  have hDm := (continuous_coleHopfMassDeriv
    (lipschitzWith_toNNReal_of_abs_sub_le hL).continuous
    (HasLinearGrowth.of_lipschitz hL) m v.toNNReal).measurable
  obtain ⟨M, _, hbound⟩ := exists_uniform_coleHopf_mass_first_derivative_bound v.toNNReal
  have hD : ∀ y, |coleHopfMassDeriv m v.toNNReal A y| ≤ M := by
    intro y
    rw [← (hasDerivAt_coleHopf_mass (HasLinearGrowth.of_lipschitz hL) hAm v.toNNReal y m).deriv]
    exact (hbound A hAm hLip _ le_rfl y).2.1 m ⟨by linarith, by linarith⟩
  rw [coleHopfSplitMassResponse_eq_massDeriv_of_pos hAm hLip hm hm1,
    coleHopfIterateMassDeriv]
  exact integral_cascadeTiltMeasure_one_eq_coleHopfQ hBm
    (by simpa only [one_mul] using hB) hm hm1 _ x hDm hD

/-- The local mirror response varies the outer mass while keeping the inner
mass fixed. Its variance coordinate is the outer variance. -/
noncomputable def coleHopfOuterSplitMassResponse (m a : ℝ)
    (A : ℝ → ℝ) (x w : ℝ) : ℝ :=
  coleHopfMassDeriv m w.toNNReal (coleHopf m (a - w).toNNReal A) x

/-- An empty outer variance interval has zero outer-mass response. -/
theorem coleHopfOuterSplitMassResponse_zero (m a : ℝ) (A : ℝ → ℝ) (x : ℝ) :
    coleHopfOuterSplitMassResponse m a A x 0 = 0 := by
  simp [coleHopfOuterSplitMassResponse, coleHopfMassDeriv, gaussianReal_zero_var, coleHopfQ]

/-- The mirror response is the derivative of the actual outer Cole-Hopf
mass, including a zero outer variance and the terminal matching mass one. -/
theorem hasDerivAt_coleHopfOuterSplit_mass {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|) (m a w x : ℝ) :
    HasDerivAt (fun b => coleHopf b w.toNNReal (coleHopf m (a - w).toNNReal A) x)
      (coleHopfOuterSplitMassResponse m a A x w) m := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hB := abs_coleHopf_sub_le_of_lipschitz m hAm hL (a - w).toNNReal
  exact hasDerivAt_coleHopf_mass (HasLinearGrowth.of_lipschitz hB)
    (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable w.toNNReal x m

/-- The two concrete responses complement each other on the admissible
variance interval. This is the mirror of the inner-mass formula (14.240). -/
theorem coleHopfOuterSplitMassResponse_eq_sub {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {a w : ℝ}
    (hw : w ∈ Icc (0 : ℝ) a) (x : ℝ) :
    coleHopfOuterSplitMassResponse m a A x w =
      coleHopfMassDeriv m a.toNNReal A x - coleHopfSplitMassResponse m a A x (a - w) := by
  have he : w.toNNReal + (a - w).toNNReal = a.toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal _ hw.1,
      Real.coe_toNNReal _ (sub_nonneg.2 hw.2), Real.coe_toNNReal _ (hw.1.trans hw.2)]
    ring
  have hh := coleHopfMassDeriv_split_add hAm hLip hm hm1 (a - w).toNNReal w.toNNReal x
  rw [he] at hh
  rw [coleHopfSplitMassResponse_eq_integral_massDeriv_of_pos hAm hLip hm hm1]
  simp only [sub_sub_cancel]
  exact eq_sub_of_add_eq hh

/-- Transport the actual mirror response through the fixed unsplit prefix
weights. These weights are independent of the outer split variance. -/
noncomputable def coleHopfIterateOuterSplitMassResponse {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (m a : ℝ) (A : ℝ → ℝ) (x w : ℝ) : ℝ :=
  ∫ zs, coleHopfOuterSplitMassResponse m a A (x + ∑ p, zs p) w
    ∂cascadeTiltMeasure j ms (fun p => gaussianReal 0 (vs p))
      (fun zs => ENNReal.ofReal (Real.exp (coleHopf m a.toNNReal A (x + ∑ p, zs p))))

/-- The zero outer response remains zero through every fixed prefix. -/
theorem coleHopfIterateOuterSplitMassResponse_zero {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (m a : ℝ) (A : ℝ → ℝ) (x : ℝ) :
    coleHopfIterateOuterSplitMassResponse ms vs m a A x 0 = 0 := by
  simp only [coleHopfIterateOuterSplitMassResponse,
    coleHopfOuterSplitMassResponse_zero, integral_zero]

/-- At matching masses the mirror prefix response is the actual propagated
outer-layer mass derivative. -/
theorem coleHopfIterateOuterSplitMassResponse_eq_massDeriv {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|) (m : ℝ)
    {a w : ℝ} (hw : w ∈ Icc (0 : ℝ) a) (x : ℝ) :
    coleHopfIterateOuterSplitMassResponse ms vs m a A x w =
      coleHopfIterateMassDeriv ms vs w.toNNReal (coleHopf m (a - w).toNNReal A) m x := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hc := coleHopfSplit_matching_mass (HasLinearGrowth.of_lipschitz hL) hAm m
    (show a - w ∈ Icc (0 : ℝ) a from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
  simp only [sub_sub_cancel] at hc
  simp only [coleHopfIterateMassDeriv, hc,
    coleHopfIterateOuterSplitMassResponse, coleHopfOuterSplitMassResponse]

/-- The mirror response differentiates the full preceding recursion, with
no mass derivative left as a hypothesis. -/
theorem hasDerivAt_coleHopfIterate_outer_split_mass {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) {a w : ℝ}
    (hw : w ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivAt (fun b => coleHopfIterate j ms vs
      (coleHopf b w.toNNReal (coleHopf m (a - w).toNNReal A)) x)
      (coleHopfIterateOuterSplitMassResponse ms vs m a A x w) m := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hB := abs_coleHopf_sub_le_of_lipschitz m hAm hL (a - w).toNNReal
  rw [coleHopfIterateOuterSplitMassResponse_eq_massDeriv ms vs hAm hLip m hw]
  exact hasDerivAt_coleHopfIterate_mass_layer ms vs hpos hle
    (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
    (by simpa only [one_mul] using hB) _ hm x

/-- The complement identity survives all preceding cascade weights. Both
integrands are uniformly bounded before subtraction under the probability law. -/
theorem coleHopfIterateOuterSplitMassResponse_eq_sub {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {a w : ℝ}
    (hw : w ∈ Icc (0 : ℝ) a) (x : ℝ) :
    coleHopfIterateOuterSplitMassResponse ms vs m a A x w =
      coleHopfIterateMassDeriv ms vs a.toNNReal A m x -
        coleHopfIterateSplitMassResponse ms vs m a A x (a - w) := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hAc := (lipschitzWith_toNNReal_of_abs_sub_le hL).continuous
  have hB := abs_coleHopf_sub_le_of_lipschitz m hAm hL a.toNNReal
  let ν := cascadeTiltMeasure j ms (fun p => gaussianReal 0 (vs p))
    (fun zs => ENNReal.ofReal (Real.exp (coleHopf m a.toNNReal A (x + ∑ p, zs p))))
  have : IsProbabilityMeasure ν := isProbabilityMeasure_cascadeTiltMeasure_comp_add_sum
    ms vs hpos hle (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable hB x
  have hcoords : Measurable (fun zs : Fin j → ℝ => x + ∑ p, zs p) :=
    measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)
  obtain ⟨M, _, hbound⟩ := exists_uniform_coleHopf_mass_first_derivative_bound a.toNNReal
  have hfull : Integrable (fun zs => coleHopfMassDeriv m a.toNNReal A (x + ∑ p, zs p)) ν :=
    Integrable.of_bound
      ((continuous_coleHopfMassDeriv hAc (HasLinearGrowth.of_lipschitz hL)
        m a.toNNReal).measurable.comp hcoords).aestronglyMeasurable M
      (.of_forall fun zs => by
        rw [Real.norm_eq_abs,
          ← (hasDerivAt_coleHopf_mass (HasLinearGrowth.of_lipschitz hL) hAm
            a.toNNReal (x + ∑ p, zs p) m).deriv]
        exact (hbound A hAm hLip _ le_rfl _).2.1 m ⟨by linarith, by linarith⟩)
  obtain ⟨C, _, hsplit⟩ := exists_uniform_coleHopfSplitMassResponse_bound (a - w).toNNReal
  have hinner : Integrable (fun zs => coleHopfSplitMassResponse m a A (x + ∑ p, zs p) (a - w)) ν :=
    Integrable.of_bound
      ((measurable_coleHopfSplitMassResponse hAm hLip ⟨hm.le, hm1⟩ a (a - w)).comp
        hcoords).aestronglyMeasurable C (.of_forall fun zs => by
          rw [Real.norm_eq_abs]
          exact hsplit A hAm hLip m ⟨hm.le, hm1⟩ a (a - w) _ le_rfl)
  change (∫ zs, coleHopfOuterSplitMassResponse m a A (x + ∑ p, zs p) w ∂ν) =
    (∫ zs, coleHopfMassDeriv m a.toNNReal A (x + ∑ p, zs p) ∂ν) -
      ∫ zs, coleHopfSplitMassResponse m a A (x + ∑ p, zs p) (a - w) ∂ν
  rw [← integral_sub hfull hinner]
  exact integral_congr_ae (.of_forall fun zs =>
    coleHopfOuterSplitMassResponse_eq_sub hAm hLip hm hm1 hw _)

/-- The actual transported outer response is measurable in the field or
evaluation point; its proof uses the propagated mass derivative. -/
theorem measurable_coleHopfIterateOuterSplitMassResponse {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) {a w : ℝ}
    (hw : w ∈ Icc (0 : ℝ) a) :
    Measurable (fun x => coleHopfIterateOuterSplitMassResponse ms vs m a A x w) := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hB := abs_coleHopf_sub_le_of_lipschitz m hAm hL (a - w).toNNReal
  have heq := funext fun x =>
    coleHopfIterateOuterSplitMassResponse_eq_massDeriv ms vs hAm hLip m hw x
  rw [heq]
  exact measurable_coleHopfIterateMassDeriv ms vs hpos hle
    (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
    (by simpa only [one_mul] using hB) _ hm

/-- A uniform mirror response bound depends only on the outer variance
ceiling, independently of the prefix length, masses and external field. -/
theorem exists_uniform_coleHopfIterateOuterSplitMassResponse_bound (V : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (j : ℕ) (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0),
      (∀ p, 0 < ms p) → (∀ p, ms p ≤ 1) → ∀ (A : ℝ → ℝ), Measurable A →
      (∀ x y, |A y - A x| ≤ |y - x|) → ∀ m ∈ Icc (0 : ℝ) 1,
      ∀ (a w x : ℝ), w ∈ Icc (0 : ℝ) a → w.toNNReal ≤ V →
        |coleHopfIterateOuterSplitMassResponse ms vs m a A x w| ≤ M := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_coleHopfIterate_mass_derivative_bound V
  refine ⟨M, hM, fun j ms vs hpos hle A hAm hLip m hm a w x hw hv => ?_⟩
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hB := abs_coleHopf_sub_le_of_lipschitz m hAm hL (a - w).toNNReal
  rw [coleHopfIterateOuterSplitMassResponse_eq_massDeriv ms vs hAm hLip m hw]
  exact hbound j ms vs hpos hle (coleHopf m (a - w).toNNReal A)
    (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
    (by simpa only [one_mul] using hB) _ hv m hm x

/-- Outer-mass differentiation commutes with an arbitrary probability-law
field average having a finite first moment. Mass one and zero variances remain
included, without an exponential field-moment assumption. -/
theorem hasDerivAt_integral_coleHopfIterate_outer_split_mass_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hHm : Measurable H) (hH : Integrable H μ) {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) {a w : ℝ}
    (hw : w ∈ Icc (0 : ℝ) a) :
    HasDerivAt (fun b => ∫ ω, coleHopfIterate j ms vs
      (coleHopf b w.toNNReal (coleHopf m (a - w).toNNReal A)) (H ω) ∂μ)
      (∫ ω, coleHopfIterateOuterSplitMassResponse ms vs m a A (H ω) w ∂μ) m := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by
    simpa only [one_mul] using hLip
  have hB := abs_coleHopf_sub_le_of_lipschitz m hAm hL (a - w).toNNReal
  have hd := hasDerivAt_integral_coleHopfIterate_mass_layer_comp hHm hH
    ms vs hpos hle (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
    (by simpa only [one_mul] using hB) w.toNNReal 0 hm
  simp only [add_zero] at hd
  convert hd using 1
  exact integral_congr_ae (.of_forall fun ω =>
    coleHopfIterateOuterSplitMassResponse_eq_massDeriv ms vs hAm hLip m hw _)

/-- Mirror spatial moments use the actual inner interval of the matched
split, with the same fixed baseline prefix weights. -/
noncomputable def coleHopfIterateOuterSplitSpatialMoment {j : ℕ} (s : ℕ)
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (m a : ℝ) (A : ℝ → ℝ) (x w : ℝ) : ℝ :=
  coleHopfIterateSplitSpatialMoment s ms vs m a A x (a - w)

/-- The outer response increases with half the actual transported squared
gradient moment. Both variance endpoints use admissible one-sided derivatives. -/
theorem hasDerivWithinAt_coleHopfIterateOuterSplitMassResponse {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ s ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv s A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m a w : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (ha : 0 < a)
    (hw : w ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivWithinAt (coleHopfIterateOuterSplitMassResponse ms vs m a A x)
      (coleHopfIterateOuterSplitSpatialMoment 1 ms vs m a A x w / 2)
      (Icc (0 : ℝ) a) w := by
  have hmaps : ∀ y ∈ Icc (0 : ℝ) a, a - y ∈ Icc (0 : ℝ) a :=
    fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hr := (hasDerivWithinAt_coleHopfIterateSplitMassResponse ms vs hpos hle
    hA hb hLip ⟨hm.le, hm1⟩ ha (hmaps w hw) x).comp w
    ((hasDerivAt_id w).const_sub a).hasDerivWithinAt hmaps
  have hd := (hasDerivWithinAt_const w (Icc (0 : ℝ) a)
    (coleHopfIterateMassDeriv ms vs a.toNNReal A m x)).sub hr
  have hder : (0 : ℝ) - coleHopfIterateSplitSpatialMoment 1 ms vs m a A x (a - w) / 2 * -1 =
      coleHopfIterateOuterSplitSpatialMoment 1 ms vs m a A x w / 2 := by
    unfold coleHopfIterateOuterSplitSpatialMoment
    ring
  exact (hd.congr_deriv hder).congr_of_mem
    (fun y hy => coleHopfIterateOuterSplitMassResponse_eq_sub ms vs hpos hle
      hA.continuous.measurable hLip hm hm1 hy x) hw

/-- The mirror gradient moment increases by the actual squared second
derivative moment. This is the positive curvature counterpart of (14.243). -/
theorem hasDerivWithinAt_coleHopfIterateOuterSplitSpatialMoment {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ s ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv s A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m a w : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hw : w ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivWithinAt (coleHopfIterateOuterSplitSpatialMoment 1 ms vs m a A x)
      (coleHopfIterateOuterSplitSpatialMoment 2 ms vs m a A x w) (Icc (0 : ℝ) a) w := by
  have hmaps : ∀ y ∈ Icc (0 : ℝ) a, a - y ∈ Icc (0 : ℝ) a :=
    fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hd := (hasDerivWithinAt_coleHopfIterateSplitSpatialMoment ms vs hpos hle
    hA hb hLip hm ha (hmaps w hw) x).comp w
    ((hasDerivAt_id w).const_sub a).hasDerivWithinAt hmaps
  change HasDerivWithinAt (fun y => coleHopfIterateSplitSpatialMoment 1 ms vs m a A x (a - y))
    (coleHopfIterateSplitSpatialMoment 2 ms vs m a A x (a - w)) (Icc (0 : ℝ) a) w
  simpa only [Function.comp_def, neg_mul, mul_neg_one, neg_neg] using hd

/-- The mirror complement identity after a probability-law field average.
Uniform mass bounds prove the integrability needed for the subtraction. -/
theorem integral_coleHopfIterateOuterSplitMassResponse_eq_sub
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {a w : ℝ}
    (hw : w ∈ Icc (0 : ℝ) a) :
    (∫ ω, coleHopfIterateOuterSplitMassResponse ms vs m a A (H ω) w ∂μ) =
      (∫ ω, coleHopfIterateMassDeriv ms vs a.toNNReal A m (H ω) ∂μ) -
        ∫ ω, coleHopfIterateSplitMassResponse ms vs m a A (H ω) (a - w) ∂μ := by
  obtain ⟨M, _, hbound⟩ := exists_uniform_coleHopfIterate_mass_derivative_bound a.toNNReal
  have hfull : Integrable (fun ω => coleHopfIterateMassDeriv ms vs a.toNNReal A m (H ω)) μ :=
    Integrable.of_bound
      ((measurable_coleHopfIterateMassDeriv ms vs hpos hle hAm hLip
        a.toNNReal ⟨hm.le, hm1⟩).comp hH).aestronglyMeasurable M (.of_forall fun ω => by
          rw [Real.norm_eq_abs]
          exact hbound j ms vs hpos hle A hAm hLip _ le_rfl m ⟨hm.le, hm1⟩ (H ω))
  have hinner := integrable_coleHopfIterateSplitMassResponse_comp_of_pos (μ := μ) hH
    ms vs hpos hle hAm hLip hm hm1
    (show a - w ∈ Icc (0 : ℝ) a from ⟨by linarith [hw.2], by linarith [hw.1]⟩)
  rw [← integral_sub hfull hinner]
  exact integral_congr_ae (.of_forall fun ω =>
    coleHopfIterateOuterSplitMassResponse_eq_sub ms vs hpos hle hAm hLip hm hm1 hw (H ω))

/-- The mirror variance derivative after the complete prefix and arbitrary
probability-law field averages. No field moment is needed for this bounded
response derivative. -/
theorem hasDerivWithinAt_integral_coleHopfIterateOuterSplitMassResponse_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ s ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv s A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m a w : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (ha : 0 < a)
    (hw : w ∈ Icc (0 : ℝ) a) :
    HasDerivWithinAt
      (fun u => ∫ ω, coleHopfIterateOuterSplitMassResponse ms vs m a A (H ω) u ∂μ)
      ((∫ ω, coleHopfIterateOuterSplitSpatialMoment 1 ms vs m a A (H ω) w ∂μ) / 2)
      (Icc (0 : ℝ) a) w := by
  have hmaps : ∀ y ∈ Icc (0 : ℝ) a, a - y ∈ Icc (0 : ℝ) a :=
    fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hr := (hasDerivWithinAt_integral_coleHopfIterateSplitMassResponse_comp (μ := μ) hH
    ms vs hpos hle hA hb hLip hm hm1 ha (hmaps w hw)).comp w
    ((hasDerivAt_id w).const_sub a).hasDerivWithinAt hmaps
  have hd := (hasDerivWithinAt_const w (Icc (0 : ℝ) a)
    (∫ ω, coleHopfIterateMassDeriv ms vs a.toNNReal A m (H ω) ∂μ)).sub hr
  have hder : (0 : ℝ) - (∫ ω, coleHopfIterateSplitSpatialMoment 1 ms vs m a A (H ω) (a - w) ∂μ) / 2
      * -1 = (∫ ω, coleHopfIterateOuterSplitSpatialMoment 1 ms vs m a A (H ω) w ∂μ) / 2 := by
    unfold coleHopfIterateOuterSplitSpatialMoment
    ring
  exact (hd.congr_deriv hder).congr_of_mem
    (fun y hy => integral_coleHopfIterateOuterSplitMassResponse_eq_sub hH
      ms vs hpos hle hA.continuous.measurable hLip hm hm1 hy) hw

/-- The mirror curvature after both prefix and field-law averages is the
positive second spatial moment, with both admissible endpoints included. -/
theorem hasDerivWithinAt_integral_coleHopfIterateOuterSplitSpatialMoment_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ s ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv s A x| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m a w : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (ha : 0 < a)
    (hw : w ∈ Icc (0 : ℝ) a) :
    HasDerivWithinAt
      (fun u => ∫ ω, coleHopfIterateOuterSplitSpatialMoment 1 ms vs m a A (H ω) u ∂μ)
      (∫ ω, coleHopfIterateOuterSplitSpatialMoment 2 ms vs m a A (H ω) w ∂μ)
      (Icc (0 : ℝ) a) w := by
  have hmaps : ∀ y ∈ Icc (0 : ℝ) a, a - y ∈ Icc (0 : ℝ) a :=
    fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hd := (hasDerivWithinAt_integral_coleHopfIterateSplitSpatialMoment_comp (μ := μ) hH
    ms vs hpos hle hA hb hLip hm hm1 ha (hmaps w hw)).comp w
    ((hasDerivAt_id w).const_sub a).hasDerivWithinAt hmaps
  simpa only [Function.comp_def, coleHopfIterateOuterSplitSpatialMoment,
    neg_mul, mul_neg_one, neg_neg] using hd

/-- Specialize the mirror variance derivative to the actual Parisi suffix;
its fourth-order regularity and domination follow from the recursion. -/
theorem hasDerivWithinAt_integral_parisiQSuffix_prefixOuterSplitMassResponse_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {j : ℕ}
    (pms : Fin j → ℝ) (pvs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < pms p) (hle : ∀ p, pms p ≤ 1)
    (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    {m a w : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (ha : 0 < a)
    (hw : w ∈ Icc (0 : ℝ) a) :
    HasDerivWithinAt
      (fun u => ∫ ω, coleHopfIterateOuterSplitMassResponse pms pvs m a
        (parisiQSuffix ξ h ms qs r) (H ω) u ∂μ)
      ((∫ ω, coleHopfIterateOuterSplitSpatialMoment 1 pms pvs m a
        (parisiQSuffix ξ h ms qs r) (H ω) w ∂μ) / 2) (Icc (0 : ℝ) a) w := by
  obtain ⟨hA, hb⟩ := parisiQSuffix_spatial_regular_four ξ h ms qs r
  exact hasDerivWithinAt_integral_coleHopfIterateOuterSplitMassResponse_comp hH
    pms pvs hpos hle hA hb (abs_parisiQSuffix_sub_le ξ h ms qs r) hm hm1 ha hw

/-- The actual suffix mirror curvature is a concrete averaged second spatial
moment, with no derivative or endpoint moment assumed in its hypotheses. -/
theorem hasDerivWithinAt_integral_parisiQSuffix_prefixOuterSplitSpatialMoment_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {j : ℕ}
    (pms : Fin j → ℝ) (pvs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < pms p) (hle : ∀ p, pms p ≤ 1)
    (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    {m a w : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (ha : 0 < a)
    (hw : w ∈ Icc (0 : ℝ) a) :
    HasDerivWithinAt
      (fun u => ∫ ω, coleHopfIterateOuterSplitSpatialMoment 1 pms pvs m a
        (parisiQSuffix ξ h ms qs r) (H ω) u ∂μ)
      (∫ ω, coleHopfIterateOuterSplitSpatialMoment 2 pms pvs m a
        (parisiQSuffix ξ h ms qs r) (H ω) w ∂μ) (Icc (0 : ℝ) a) w := by
  obtain ⟨hA, hb⟩ := parisiQSuffix_spatial_regular_four ξ h ms qs r
  exact hasDerivWithinAt_integral_coleHopfIterateOuterSplitSpatialMoment_comp hH
    pms pvs hpos hle hA hb (abs_parisiQSuffix_sub_le ξ h ms qs r) hm hm1 ha hw

/-- The actual mirror suffix response is convex after the full prefix and
probability-law field averages, also when the total variance is zero. -/
theorem convexOn_integral_parisiQSuffix_prefixOuterSplitMassResponse_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hH : Measurable H) {j : ℕ}
    (pms : Fin j → ℝ) (pvs : Fin j → ℝ≥0)
    (hpos : ∀ p, 0 < pms p) (hle : ∀ p, pms p ≤ 1)
    (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    ConvexOn ℝ (Icc (0 : ℝ) a)
      (fun w => ∫ ω, coleHopfIterateOuterSplitMassResponse pms pvs m a
        (parisiQSuffix ξ h ms qs r) (H ω) w ∂μ) := by
  have hA := (parisiQSuffix_spatial_regular_four ξ h ms qs r).1
  have hLip := abs_parisiQSuffix_sub_le ξ h ms qs r
  have hc := concaveOn_integral_parisiQSuffix_prefixSplitMassResponse_comp (μ := μ) hH
    pms pvs hpos hle ξ h ms qs r hm hm1 ha
  have hmaps : ∀ y ∈ Icc (0 : ℝ) a, a - y ∈ Icc (0 : ℝ) a :=
    fun y hy => ⟨by linarith [hy.2], by linarith [hy.1]⟩
  refine ⟨convex_Icc 0 a, ?_⟩
  intro u hu v hv α β hα hβ hsum
  have hcomb := (convex_Icc (0 : ℝ) a) hu hv hα hβ hsum
  have hl := hc.2 (hmaps u hu) (hmaps v hv) hα hβ hsum
  simp only [smul_eq_mul] at hl hcomb ⊢
  have hmix : a - (α * u + β * v) = α * (a - u) + β * (a - v) := by
    nlinarith [hsum]
  rw [← hmix] at hl
  rw [integral_coleHopfIterateOuterSplitMassResponse_eq_sub hH pms pvs hpos hle
      hA.continuous.measurable hLip hm hm1 hcomb,
    integral_coleHopfIterateOuterSplitMassResponse_eq_sub hH pms pvs hpos hle
      hA.continuous.measurable hLip hm hm1 hu,
    integral_coleHopfIterateOuterSplitMassResponse_eq_sub hH pms pvs hpos hle
      hA.continuous.measurable hLip hm hm1 hv]
  have hK : α * (∫ ω, coleHopfIterateMassDeriv pms pvs a.toNNReal
      (parisiQSuffix ξ h ms qs r) m (H ω) ∂μ) +
        β * (∫ ω, coleHopfIterateMassDeriv pms pvs a.toNNReal
          (parisiQSuffix ξ h ms qs r) m (H ω) ∂μ) =
      ∫ ω, coleHopfIterateMassDeriv pms pvs a.toNNReal
        (parisiQSuffix ξ h ms qs r) m (H ω) ∂μ := by
    rw [← add_mul, hsum, one_mul]
  nlinarith only [hl, hK]

end SpinGlass
