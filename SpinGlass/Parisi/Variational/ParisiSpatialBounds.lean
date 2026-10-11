import SpinGlass.Parisi.Variational.ParisiSpatialRegularity

/-!
# Sharp spatial bounds for the Parisi recursion

Talagrand, Vol. II, (14.271) follows from the stronger invariant
`0 ≤ A''` and `A'' + (A')² ≤ 1`. Its preservation uses the actual
Cole-Hopf derivatives and Jensen under the normalized Gaussian tilt.
Zero mass and zero variance are included.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- Actual first and second spatial derivatives of a Cole-Hopf layer with
bounded input derivatives. The formulas include zero mass and variance. -/
theorem coleHopf_spatial_derivative_formulas {A : ℝ → ℝ}
    (hA : ContDiff ℝ 2 A) {C₁ C₂ : ℝ}
    (hfirst : ∀ x, |deriv A x| ≤ C₁)
    (hsecond : ∀ x, |deriv (deriv A) x| ≤ C₂)
    (m : ℝ) (v : ℝ≥0) :
    (∀ x, HasDerivAt (coleHopf m v A)
      (∫ z, deriv A (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v) x) ∧
    (∀ x, HasDerivAt (deriv (coleHopf m v A))
      ((∫ z, (deriv (deriv A) (x + z) + m * deriv A (x + z) ^ 2) *
        coleHopfQ m v A x z ∂gaussianReal 0 v) - m * deriv (coleHopf m v A) x ^ 2) x) := by
  have hAd : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hA₁ : ContDiff ℝ 1 (deriv A) := (contDiff_succ_iff_deriv.1 hA).2.2
  have hA₁d : Differentiable ℝ (deriv A) := hA₁.differentiable one_ne_zero
  have hA₁m := hA₁.continuous.measurable
  have hA₂m := (hA₁.continuous_deriv le_rfl).measurable
  have hAg := HasLinearGrowth.of_bounded_deriv (fun x => (hAd x).hasDerivAt) hfirst
  have hA₁g := HasExpGrowth.of_bounded hfirst
  have hA₂g := HasExpGrowth.of_bounded hsecond
  rcases eq_or_ne m 0 with rfl | hm
  · have hzero : coleHopf 0 v A = fun y => ∫ z, A (y + z) ∂gaussianReal 0 v :=
      funext fun y => coleHopf_zero v A y
    have hd : ∀ x, HasDerivAt (coleHopf 0 v A)
        (∫ z, deriv A (x + z) ∂gaussianReal 0 v) x := by
      intro x
      rw [hzero]
      exact hasDerivAt_integral_comp_add_gaussianReal
        (fun y => (hAd y).hasDerivAt) hAg.toHasExpGrowth hA₁g hA₁m 0 v x
    have heq : deriv (coleHopf 0 v A) =
        fun x => ∫ z, deriv A (x + z) ∂gaussianReal 0 v :=
      funext fun x => (hd x).deriv
    refine ⟨fun x => by simpa only [coleHopfQ_zero, mul_one] using hd x, ?_⟩
    intro x
    simp only [coleHopfQ_zero, zero_mul, add_zero, mul_one, sub_zero]
    rw [heq]
    exact hasDerivAt_integral_comp_add_gaussianReal
      (fun y => (hA₁d y).hasDerivAt) hA₁g hA₂g hA₂m 0 v x
  · have hd : ∀ x, HasDerivAt (coleHopf m v A)
        (∫ z, deriv A (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v) x :=
      fun x => hasDerivAt_coleHopf (fun y => (hAd y).hasDerivAt)
        hAg hA₁g hA₁m hm v x
    have heq : deriv (coleHopf m v A) =
        fun x => ∫ z, deriv A (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v :=
      funext fun x => (hd x).deriv
    refine ⟨hd, fun x => ?_⟩
    rw [heq]
    exact hasDerivAt_integral_deriv_mul_coleHopfQ
      (fun y => (hAd y).hasDerivAt) (fun y => (hA₁d y).hasDerivAt)
      hAg hA₁g hA₂g hA₂m hm v x

private lemma integrable_bounded_mul_coleHopfQ {A G : ℝ → ℝ}
    (hAg : HasLinearGrowth A) (hAm : Measurable A) (hGm : Measurable G)
    {C : ℝ} (hG : ∀ y, |G y| ≤ C) (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    Integrable (fun z => G (x + z) * coleHopfQ m v A x z) (gaussianReal 0 v) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [coleHopfQ_zero, mul_one]
    exact ((HasExpGrowth.of_bounded hG).comp_add_const x).integrable_gaussianReal
      (hGm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  · exact integrable_mul_coleHopfQ hAg hAm hm (HasExpGrowth.of_bounded hG) hGm v x

private lemma integral_coleHopfQ_all_mass {A : ℝ → ℝ}
    (hAg : HasLinearGrowth A) (hAm : Measurable A) (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    ∫ z, coleHopfQ m v A x z ∂gaussianReal 0 v = 1 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [coleHopfQ_zero, integral_const, probReal_univ, smul_eq_mul, one_mul]
  · exact integral_coleHopfQ hAg hAm hm v x

private lemma sq_integral_bounded_mul_coleHopfQ_le {A G : ℝ → ℝ}
    (hAg : HasLinearGrowth A) (hAm : Measurable A) (hGm : Measurable G)
    {C : ℝ} (hG : ∀ y, |G y| ≤ C) (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    (∫ z, G (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v) ^ 2 ≤
      ∫ z, G (x + z) ^ 2 * coleHopfQ m v A x z ∂gaussianReal 0 v := by
  let c := ∫ z, G (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v
  have hGsq : ∀ y, |G y ^ 2| ≤ C ^ 2 := fun y => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hG y) 2
  have h₁ := integrable_bounded_mul_coleHopfQ hAg hAm hGm hG m v x
  have h₂ := integrable_bounded_mul_coleHopfQ hAg hAm (hGm.pow_const 2) hGsq m v x
  have hQ : Integrable (coleHopfQ m v A x) (gaussianReal 0 v) := by
    simpa only [one_mul] using integrable_bounded_mul_coleHopfQ hAg hAm
      measurable_const (fun _ => (by norm_num : |(1 : ℝ)| ≤ 1)) m v x
  have hnn : 0 ≤ ∫ z, (G (x + z) - c) ^ 2 * coleHopfQ m v A x z
      ∂gaussianReal 0 v :=
    integral_nonneg fun z => mul_nonneg (sq_nonneg _) (coleHopfQ_pos m v A x z).le
  have hexp : ∫ z, (G (x + z) - c) ^ 2 * coleHopfQ m v A x z ∂gaussianReal 0 v =
      (∫ z, G (x + z) ^ 2 * coleHopfQ m v A x z ∂gaussianReal 0 v) -
        2 * c * c + c ^ 2 := by
    have hi : ∀ z, (G (x + z) - c) ^ 2 * coleHopfQ m v A x z =
        G (x + z) ^ 2 * coleHopfQ m v A x z -
          2 * c * (G (x + z) * coleHopfQ m v A x z) + c ^ 2 * coleHopfQ m v A x z :=
      fun z => by ring
    simp_rw [hi]
    have hs : Integrable (fun z => G (x + z) ^ 2 * coleHopfQ m v A x z -
        2 * c * (G (x + z) * coleHopfQ m v A x z)) (gaussianReal 0 v) :=
      h₂.sub (h₁.const_mul _)
    have hq : Integrable (fun z => c ^ 2 * coleHopfQ m v A x z) (gaussianReal 0 v) :=
      hQ.const_mul _
    have hlin : Integrable (fun z => 2 * c * (G (x + z) * coleHopfQ m v A x z))
        (gaussianReal 0 v) := h₁.const_mul _
    rw [integral_add hs hq, integral_sub h₂ hlin, integral_const_mul, integral_const_mul,
      integral_coleHopfQ_all_mass hAg hAm, mul_one]
  rw [hexp] at hnn
  dsimp only [c] at hnn
  nlinarith

/-- A Cole-Hopf layer preserves the sharp invariant underlying (14.271).
The bound is independent of its mass in [0,1] and its Gaussian variance. -/
theorem coleHopf_sharp_spatial_bounds {A : ℝ → ℝ} (hA : ContDiff ℝ 2 A)
    (hsharp : ∀ x, 0 ≤ deriv (deriv A) x ∧
      deriv (deriv A) x + deriv A x ^ 2 ≤ 1)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : ℝ≥0) (x : ℝ) :
    0 ≤ deriv (deriv (coleHopf m v A)) x ∧
      deriv (deriv (coleHopf m v A)) x + deriv (coleHopf m v A) x ^ 2 ≤ 1 := by
  have hfirst : ∀ y, |deriv A y| ≤ 1 := fun y => by
    apply abs_le.2
    constructor <;> nlinarith [(hsharp y).1, (hsharp y).2]
  have hsecond : ∀ y, |deriv (deriv A) y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (hsharp y).1]
    nlinarith [(hsharp y).2, sq_nonneg (deriv A y)]
  have hA₁ : ContDiff ℝ 1 (deriv A) := (contDiff_succ_iff_deriv.1 hA).2.2
  have hA₁m := hA₁.continuous.measurable
  have hA₂m := (hA₁.continuous_deriv le_rfl).measurable
  have hAg := HasLinearGrowth.of_bounded_deriv
    (fun y => ((hA.differentiable (by norm_num)) y).hasDerivAt) hfirst
  have h₁ := integrable_bounded_mul_coleHopfQ hAg hA.continuous.measurable
    hA₁m hfirst m v x
  have h₂ := integrable_bounded_mul_coleHopfQ hAg hA.continuous.measurable
    hA₂m hsecond m v x
  have hsq : ∀ y, |deriv A y ^ 2| ≤ 1 := fun y => by
    rw [abs_pow]
    nlinarith [hfirst y, abs_nonneg (deriv A y)]
  have h₃ := integrable_bounded_mul_coleHopfQ hAg hA.continuous.measurable
    (hA₁m.pow_const 2) hsq m v x
  obtain ⟨hd, hdd⟩ := coleHopf_spatial_derivative_formulas hA hfirst hsecond m v
  have heq : deriv (deriv (coleHopf m v A)) x =
      (∫ z, deriv (deriv A) (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v) +
      m * (∫ z, deriv A (x + z) ^ 2 * coleHopfQ m v A x z ∂gaussianReal 0 v) -
      m * deriv (coleHopf m v A) x ^ 2 := by
    rw [(hdd x).deriv]
    simp_rw [add_mul, mul_assoc]
    rw [integral_add h₂ (h₃.const_mul m), integral_const_mul]
  have hJ := sq_integral_bounded_mul_coleHopfQ_le hAg hA.continuous.measurable
    hA₁m hfirst m v x
  rw [← (hd x).deriv] at hJ
  have hpos : 0 ≤ ∫ z, deriv (deriv A) (x + z) * coleHopfQ m v A x z
      ∂gaussianReal 0 v :=
    integral_nonneg fun z => mul_nonneg (hsharp (x + z)).1 (coleHopfQ_pos m v A x z).le
  have hsum : (∫ z, deriv (deriv A) (x + z) * coleHopfQ m v A x z
      ∂gaussianReal 0 v) +
      (∫ z, deriv A (x + z) ^ 2 * coleHopfQ m v A x z ∂gaussianReal 0 v) ≤ 1 := by
    have hQ : Integrable (coleHopfQ m v A x) (gaussianReal 0 v) := by
      simpa only [one_mul] using integrable_bounded_mul_coleHopfQ hAg
        hA.continuous.measurable measurable_const
        (fun _ => (by norm_num : |(1 : ℝ)| ≤ 1)) m v x
    rw [← integral_add h₂ h₃, ← integral_coleHopfQ_all_mass hAg hA.continuous.measurable m v x]
    apply integral_mono (h₂.add h₃) hQ
    intro z
    simpa only [Pi.add_apply, ← add_mul, one_mul] using
      mul_le_mul_of_nonneg_right (hsharp (x + z)).2 (coleHopfQ_pos m v A x z).le
  rw [heq]
  constructor
  · nlinarith [mul_nonneg hm.1 (sub_nonneg.2 hJ)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hm.2) (sub_nonneg.2 hJ)]

/-- The log-cosh terminal satisfies the sharp invariant with equality. -/
theorem parisiLogCoshTerminal_sharp_spatial_bounds (h x : ℝ) :
    0 ≤ deriv (deriv (parisiLogCoshTerminal h)) x ∧
      deriv (deriv (parisiLogCoshTerminal h)) x +
        deriv (parisiLogCoshTerminal h) x ^ 2 ≤ 1 := by
  have h₁ : deriv (parisiLogCoshTerminal h) = parisiLogCoshTerminalDeriv h :=
    funext fun y => (hasDerivAt_parisiLogCoshTerminal h y).deriv
  rw [h₁, (hasDerivAt_parisiLogCoshTerminalDeriv h x).deriv]
  simp only [parisiLogCoshTerminalDeriv, parisiLogCoshTerminalDeriv2]
  constructor
  · linarith [Real.tanh_sq_lt_one (h + x)]
  · ring_nf; exact le_rfl

/-- Preservation through any finite recursion. Fourth-order regularity supplies
the actual derivatives; the sharp bound itself has no dependence on the count. -/
theorem coleHopfIterate_sharp_spatial_bounds {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A)
    {C : ℝ} (hb : ∀ i ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv i A x| ≤ C)
    (hsharp : ∀ x, 0 ≤ deriv (deriv A) x ∧
      deriv (deriv A) x + deriv A x ^ 2 ≤ 1)
    {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hm : ∀ p, ms p ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    0 ≤ deriv (deriv (coleHopfIterate j ms vs A)) x ∧
      deriv (deriv (coleHopfIterate j ms vs A)) x +
        deriv (coleHopfIterate j ms vs A) x ^ 2 ≤ 1 := by
  induction j generalizing x with
  | zero => exact hsharp x
  | succ j ih =>
      obtain ⟨hB, _, _⟩ := coleHopfIterate_spatial_regular_four
        (Fin.tail ms) (Fin.tail vs) hA ⟨C, hb⟩
      rw [coleHopfIterate_succ]
      exact coleHopf_sharp_spatial_bounds (hB.of_le (by norm_num))
        (fun y => ih (Fin.tail ms) (Fin.tail vs) (fun p => hm p.succ) y) (hm 0) (vs 0) x

/-- Sharp bounds (14.271) for the actual suffix, including all endpoint
variances. They are uniform in the admissible parameters and the level count. -/
theorem parisiQSuffix_sharp_spatial_bounds (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (x : ℝ) :
    0 ≤ deriv (deriv (parisiQSuffix ξ h ms qs r)) x ∧
      deriv (deriv (parisiQSuffix ξ h ms qs r)) x +
        deriv (parisiQSuffix ξ h ms qs r) x ^ 2 ≤ 1 := by
  obtain ⟨C, hC⟩ := exists_bound_iteratedDeriv_parisiLogCoshTerminal_four h
  apply coleHopfIterate_sharp_spatial_bounds (contDiff_parisiLogCoshTerminal h 4) hC
    (parisiLogCoshTerminal_sharp_spatial_bounds h)
  intro p
  exact ⟨(hm.mExt_pos (by omega)).le,
    mExt_le_one (fun i => (hm.2.2 i).le) _⟩

/-- The zero-field log-cosh curvature is exactly the profile in (14.274). -/
theorem deriv_deriv_parisiLogCoshTerminal_zero (x : ℝ) :
    deriv (deriv (parisiLogCoshTerminal 0)) x = 1 / Real.cosh x ^ 2 := by
  have h₁ : deriv (parisiLogCoshTerminal 0) = Real.tanh := by
    funext y
    simpa only [parisiLogCoshTerminalDeriv, zero_add] using
      (hasDerivAt_parisiLogCoshTerminal 0 y).deriv
  rw [h₁, (Aristotle.hasDerivAt_real_tanh x).deriv]

/-- Quantitative curvature propagation (14.274) for an arbitrary finite
zero-field recursion. Only the sum of the variances enters the lower bound. -/
theorem coleHopfIterate_logCosh_curvature_lower {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0)
    (hm : ∀ p, ms p ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    Real.exp (-2 * ∑ p, (vs p : ℝ)) / Real.cosh x ^ 2 ≤
      deriv (deriv (coleHopfIterate j ms vs (parisiLogCoshTerminal 0))) x := by
  induction j generalizing x with
  | zero => simp only [Fin.sum_univ_zero, mul_zero, Real.exp_zero,
      coleHopfIterate_zero, deriv_deriv_parisiLogCoshTerminal_zero, le_refl]
  | succ j ih =>
      let A := coleHopfIterate j (Fin.tail ms) (Fin.tail vs) (parisiLogCoshTerminal 0)
      obtain ⟨hT, hTb⟩ := coleHopfIterate_spatial_regular_four
        (Fin.tail ms) (Fin.tail vs) (contDiff_parisiLogCoshTerminal 0 4)
        (exists_bound_iteratedDeriv_parisiLogCoshTerminal_four 0)
      obtain ⟨C, hC⟩ := exists_bound_iteratedDeriv_parisiLogCoshTerminal_four 0
      have hsharp : ∀ y, 0 ≤ deriv (deriv A) y ∧
          deriv (deriv A) y + deriv A y ^ 2 ≤ 1 := fun y =>
        coleHopfIterate_sharp_spatial_bounds (contDiff_parisiLogCoshTerminal 0 4) hC
          (parisiLogCoshTerminal_sharp_spatial_bounds 0) _ _ (fun p => hm p.succ) y
      have hfirst : ∀ y, |deriv A y| ≤ 1 := fun y => by
        apply abs_le.2
        constructor <;> nlinarith [(hsharp y).1, (hsharp y).2]
      have hsecond : ∀ y, deriv (deriv A) y ≤ 1 := fun y => by
        nlinarith [(hsharp y).2, sq_nonneg (deriv A y)]
      have hlower : ∀ y, Real.exp (-2 * ∑ p, (Fin.tail vs p : ℝ)) /
          Real.cosh y ^ 2 ≤ deriv (deriv A) y := fun y =>
        ih (Fin.tail ms) (Fin.tail vs) (fun p => hm p.succ) y
      have h := Aristotle.gaussian_mass_curvature_lower (hT.of_le (by norm_num))
        (Real.exp_pos _).le (hm 0) hfirst hsecond hlower (vs 0) x
      have heq : (fun y => Aristotle.massTransform (gaussianReal 0 (vs 0))
          (fun z => A (y + z)) (ms 0)) = coleHopf (ms 0) (vs 0) A :=
        funext fun y => (coleHopf_eq_massTransform _ _ _ _).symm
      rw [heq] at h
      rw [coleHopfIterate_succ, Fin.sum_univ_succ]
      convert h using 1
      rw [← Real.exp_add]
      congr 2
      simp only [Fin.tail]
      ring

private lemma integral_gaussian_add_even {A : ℝ → ℝ}
    (hAm : Measurable A) (heven : Function.Even A) (v : ℝ≥0) :
    Function.Even (fun x => ∫ z, A (x + z) ∂gaussianReal 0 v) := by
  intro x
  have hmap := integral_map (μ := gaussianReal 0 v) (f := fun z => A (-x + z))
    measurable_neg.aemeasurable
    ((hAm.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (μ := (gaussianReal 0 v).map (fun z : ℝ => -z)))
  rw [gaussianReal_map_neg, neg_zero] at hmap
  calc
    _ = ∫ z, A (-x + -z) ∂gaussianReal 0 v := hmap
    _ = _ := integral_congr_ae (.of_forall fun z => by
      dsimp only
      rw [show -x + -z = -(x + z) by ring, heven])

/-- Gaussian Cole-Hopf layers preserve evenness, including zero mass. -/
theorem coleHopf_even {A : ℝ → ℝ} (hAm : Measurable A)
    (heven : Function.Even A) (m : ℝ) (v : ℝ≥0) : Function.Even (coleHopf m v A) := by
  intro x
  have hplain := integral_gaussian_add_even hAm heven v x
  have hexp := integral_gaussian_add_even
    (Real.measurable_exp.comp (measurable_const.mul hAm))
    (show Function.Even (fun y => Real.exp (m * A y)) from fun y => by
      dsimp only
      rw [heven]) v x
  dsimp only at hplain hexp
  simp only [Function.comp_def, Pi.mul_apply] at hexp
  unfold coleHopf
  split_ifs
  · exact hplain
  · rw [hexp]

/-- Evenness propagates through the actual finite recursion. -/
theorem coleHopfIterate_even {A : ℝ → ℝ} (hAm : Measurable A)
    {L : ℝ} (hLip : ∀ x y, |A y - A x| ≤ L * |y - x|)
    (heven : Function.Even A) {j : ℕ} (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) :
    Function.Even (coleHopfIterate j ms vs A) := by
  induction j with
  | zero => exact heven
  | succ j ih =>
      rw [coleHopfIterate_succ]
      have hB := abs_coleHopfIterate_sub_le j (Fin.tail ms) (Fin.tail vs) hAm hLip
      exact coleHopf_even (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable
        (ih _ _) (ms 0) (vs 0)

/-- An even differentiable function has zero derivative at the origin. -/
theorem deriv_zero_of_even {A : ℝ → ℝ} (heven : Function.Even A)
    (hd : DifferentiableAt ℝ A 0) : deriv A 0 = 0 := by
  have hn : HasDerivAt (fun x : ℝ => -x) (-1) 0 := by
    convert (hasDerivAt_id (0 : ℝ)).neg using 1 <;> rfl
  have hdneg : HasDerivAt A (deriv A 0) (-0) := by simpa only [neg_zero] using hd.hasDerivAt
  have hneg := hdneg.comp 0 hn
  simp only [Function.comp_def, mul_neg_one] at hneg
  have heq : (fun x => A (-x)) = A := funext heven
  rw [heq] at hneg
  have h := hneg.unique hd.hasDerivAt
  linarith

/-- Jensen for the actual derivative of a zero-mass layer. This is the
conditional Gaussian comparison used for the first overlap in (14.270). -/
theorem coleHopf_zero_spatial_deriv_sq_le_integral {A : ℝ → ℝ}
    (hA : ContDiff ℝ 2 A) {C₁ C₂ : ℝ}
    (hfirst : ∀ x, |deriv A x| ≤ C₁)
    (hsecond : ∀ x, |deriv (deriv A) x| ≤ C₂) (v : ℝ≥0) (x : ℝ) :
    deriv (coleHopf 0 v A) x ^ 2 ≤ ∫ z, deriv A (x + z) ^ 2 ∂gaussianReal 0 v := by
  have hAg := HasLinearGrowth.of_bounded_deriv
    (fun y => ((hA.differentiable (by norm_num)) y).hasDerivAt) hfirst
  have hA₁ : ContDiff ℝ 1 (deriv A) := (contDiff_succ_iff_deriv.1 hA).2.2
  have h := sq_integral_bounded_mul_coleHopfQ_le hAg hA.continuous.measurable
    hA₁.continuous.measurable hfirst 0 v x
  rw [← ((coleHopf_spatial_derivative_formulas hA hfirst hsecond 0 v).1 x).deriv] at h
  simpa only [coleHopfQ_zero, mul_one] using h

end SpinGlass
