import SpinGlass.Parisi.Minimizer.QVariation.Recursion

/-!
# Derivative

Scalar-field overlap moments, derivatives, and stationarity.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

/-- Talagrand's concrete moment
`E(W₁ ⋯ W_{r-1} A'_r(ζ_r)^2)` for the overlap coordinate represented by `r`. -/
def parisiQMoment (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) : ℝ :=
  if r.val = 0 then
    coleHopfSplitMoment (mExt ms (r.val + 1)) (mExt ms r.val)
      (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)))
      (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)))
      (parisiQSuffix ξ h ms qs r) (parisiQSuffixDeriv ξ h ms qs r) 0
  else
    ∫ z₀, ∫ zs, coleHopfSplitMoment (mExt ms (r.val + 1)) (mExt ms r.val)
        (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)))
        (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)))
        (parisiQSuffix ξ h ms qs r) (parisiQSuffixDeriv ξ h ms qs r)
        (z₀ + ∑ p, zs p)
      ∂cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
        (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
        (fun zs => ENNReal.ofReal (Real.exp
          (coleHopf (mExt ms r.val)
            (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)))
            (coleHopf (mExt ms (r.val + 1))
              (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)))
              (parisiQSuffix ξ h ms qs r)) (z₀ + ∑ p, zs p))))
      ∂gaussianReal 0 (parisiVar ξ qs 0)

/-- The actual `parisiX₀` derivative, with the abstract moment replaced by the concrete recursive
expectation in `parisiQMoment`. This is (14.219) propagated through all earlier levels. -/
theorem hasDerivAt_parisiX₀_qUpdate
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} {ms : Fin k → ℝ}
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (hm : ParisiMAdmissible ms) {ξ₂ : ℝ}
    (hξ' : HasDerivAt (deriv ξ) ξ₂ (qs r))
    (hleft : deriv ξ (qExt qs r.val) < deriv ξ (qs r))
    (hright : deriv ξ (qs r) < deriv ξ (qExt qs (r.val + 2))) :
    HasDerivAt
      (fun u => parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h))
      ((-1 / 2 : ℝ) * ξ₂ * (mExt ms (r.val + 1) - mExt ms r.val) *
        parisiQMoment ξ h ms qs r) (qs r) := by
  obtain ⟨hA, C, hA', hA''c, hA'b, hA''b⟩ :=
    parisiQSuffix_deriv_regular (ξ := ξ) (h := h) qs r hm
  by_cases hr : r.val = 0
  · have hrfin : r = 0 := Fin.ext hr
    subst r
    have hd := hasDerivAt_coleHopf_coleHopf_q
      (ξ := ξ) (ξ₂ := ξ₂) (qL := qExt qs 0) (q := qs 0) (qR := qExt qs 2)
      (m := mExt ms 1) (m' := 0) (A := parisiQSuffix ξ h ms qs 0)
      (A' := parisiQSuffixDeriv ξ h ms qs 0)
      (A'' := parisiQSuffixDeriv2 ξ h ms qs 0) hA hA' hA''c hA'b hA''b
      (ne_of_gt (hm.mExt_pos (by omega : 0 < 1))) hξ' hleft hright 0
    have hfun :
        (fun u => parisiX₀ ξ ms (qUpdate qs 0 u) (parisiLogCoshTerminal h)) =
          (fun u => coleHopf 0 (Real.toNNReal (deriv ξ u - deriv ξ (qExt qs 0)))
            (coleHopf (mExt ms 1)
              (Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ u))
              (parisiQSuffix ξ h ms qs 0)) 0) := by
      funext u
      exact parisiX₀_first_qUpdate_eq_split qs hm u
    rw [hfun]
    convert hd using 1 <;> simp [parisiQMoment, mExt_zero]
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    have hfun :
        (fun u => parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h)) =
          (fun u => ∫ z₀, coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
            (parisiQPrefixVars ξ qs r)
            (fun y => coleHopf (mExt ms r.val)
              (Real.toNNReal (deriv ξ u - deriv ξ (qExt qs r.val)))
              (coleHopf (mExt ms (r.val + 1))
                (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ u))
                (parisiQSuffix ξ h ms qs r)) y) z₀
            ∂gaussianReal 0 (parisiVar ξ qs 0)) := by
      funext u
      unfold parisiX₀
      rw [parisiVar_qUpdate_before qs r u (by omega : 0 < r.val)]
      apply integral_congr_ae
      filter_upwards [] with z₀
      exact parisiRecGauss_qUpdate_eq_split qs r hm hrpos u z₀
    rw [hfun]
    have hd := hasDerivAt_integral_coleHopfIterate_q
      (ξ := ξ) (ξ₂ := ξ₂) (qL := qExt qs r.val) (q := qs r)
      (qR := qExt qs (r.val + 2)) (m := mExt ms (r.val + 1))
      (m' := mExt ms r.val) (A := parisiQSuffix ξ h ms qs r)
      (A' := parisiQSuffixDeriv ξ h ms qs r)
      (A'' := parisiQSuffixDeriv2 ξ h ms qs r)
      (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
      hA hA' hA''c hA'b hA''b
      (fun p => hm.mExt_pos (by simp [parisiQPrefixMasses]))
      (fun p => mExt_le_one (fun i => (hm.2.2 i).le) _)
      (ne_of_gt (hm.mExt_pos (by omega : 0 < r.val + 1))) hξ' hleft hright
      (parisiVar ξ qs 0) 0
    convert hd using 1
    simp only [zero_add]
    unfold parisiQMoment
    rw [if_neg hr]
    unfold coleHopfSplitMoment
    simp only [integral_const_mul]
    ring

/-- The concrete recursive moment always lies in the closed unit interval in absolute value. -/
theorem abs_parisiQMoment_le_one {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hm : ParisiMAdmissible ms) : |parisiQMoment ξ h ms qs r| ≤ 1 := by
  obtain ⟨hA, C, hA', hA''c, hA'b, hA''b⟩ :=
    parisiQSuffix_deriv_regular (ξ := ξ) (h := h) qs r hm
  by_cases hr : r.val = 0
  · unfold parisiQMoment
    rw [if_pos hr]
    exact abs_coleHopfSplitMoment_le_one hA hA' hA'b 0
  · let A : ℝ → ℝ := parisiQSuffix ξ h ms qs r
    let B : ℝ → ℝ := coleHopf (mExt ms (r.val + 1))
      (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r))) A
    let G : ℝ → ℝ := coleHopf (mExt ms r.val)
      (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val))) B
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
    have hprefix_pos : ∀ p, 0 < parisiQPrefixMasses ms r p := fun p =>
      hm.mExt_pos (by simp [parisiQPrefixMasses])
    have hprefix_le : ∀ p, parisiQPrefixMasses ms r p ≤ 1 := fun p =>
      mExt_le_one (fun i => (hm.2.2 i).le) _
    have hcascade : ∀ z₀ : ℝ,
        |∫ zs, coleHopfSplitMoment (mExt ms (r.val + 1)) (mExt ms r.val)
            (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)))
            (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)))
            A (parisiQSuffixDeriv ξ h ms qs r) (z₀ + ∑ p, zs p)
          ∂cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
            (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
            (fun zs => ENNReal.ofReal (Real.exp (G (z₀ + ∑ p, zs p))))| ≤ 1 := by
      intro z₀
      apply abs_integral_cascadeTiltMeasure_le
        (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
        hprefix_pos hprefix_le hGm hGlip z₀
      intro y
      exact abs_coleHopfSplitMoment_le_one hA hA' hA'b y
    unfold parisiQMoment
    rw [if_neg hr]
    change |∫ z₀, ∫ zs, coleHopfSplitMoment (mExt ms (r.val + 1)) (mExt ms r.val)
        (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)))
        (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)))
        A (parisiQSuffixDeriv ξ h ms qs r) (z₀ + ∑ p, zs p)
      ∂cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
        (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
        (fun zs => ENNReal.ofReal (Real.exp (G (z₀ + ∑ p, zs p))))
      ∂gaussianReal 0 (parisiVar ξ qs 0)| ≤ 1
    have hb := norm_integral_le_of_norm_le_const
      (μ := gaussianReal 0 (parisiVar ξ qs 0))
      (f := fun z₀ => ∫ zs, coleHopfSplitMoment (mExt ms (r.val + 1))
        (mExt ms r.val)
        (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)))
        (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)))
        A (parisiQSuffixDeriv ξ h ms qs r) (z₀ + ∑ p, zs p)
        ∂cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
          (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
          (fun zs => ENNReal.ofReal (Real.exp (G (z₀ + ∑ p, zs p)))))
      (C := 1) (Filter.Eventually.of_forall fun z₀ => by
        rw [Real.norm_eq_abs]
        exact hcascade z₀)
    simpa [probReal_univ, Real.norm_eq_abs] using hb

theorem parisiQMoment_nonneg (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) :
    0 ≤ parisiQMoment ξ h ms qs r := by
  unfold parisiQMoment
  split_ifs
  · exact coleHopfSplitMoment_nonneg _ _ _ _ _ _ _
  · apply integral_nonneg
    intro z₀
    apply integral_nonneg
    intro zs
    exact coleHopfSplitMoment_nonneg _ _ _ _ _ _ _

theorem parisiQMoment_first_eq_sq_full_deriv {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hqzero : qs 0 = 0) :
    parisiQMoment ξ h ms qs 0 =
      coleHopfIterateDeriv (k + 1) (parisiLevelMasses ms) (parisiLevelVars ξ qs)
        (parisiLogCoshTerminal h) (parisiLogCoshTerminalDeriv h) 0 ^ 2 := by
  have hvL : Real.toNNReal (deriv ξ (qs 0) - deriv ξ (qExt qs 0)) = 0 := by
    rw [hqzero, qExt_zero]
    simp
  have hinner := parisiQFirstInner_eq_coleHopfIterateDeriv
    (ξ := ξ) (h := h) ms qs 0
  unfold parisiQMoment
  simp only [Fin.val_zero, zero_add]
  unfold coleHopfSplitMoment
  rw [hvL]
  simp only [gaussianReal_zero_var, integral_dirac, add_zero]
  rw [hinner]
  simp only [if_true, mExt_zero, coleHopfQ, zero_mul, Real.exp_zero, mul_one]

/-- The first concrete moment varies continuously from the admissible endpoint `q₁ = 0`.
This is the nearby-sign input needed when `ξ''(0)` itself vanishes. -/
theorem continuousAt_parisiQMoment_first_qUpdate_zero
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} {ms : Fin k → ℝ}
    (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) :
    ContinuousAt (fun u => parisiQMoment ξ h ms (qUpdate qs 0 u) 0) 0 := by
  obtain ⟨hA, C, hA', hA''c, hA'b, hA''b⟩ :=
    parisiQSuffix_deriv_regular (ξ := ξ) (h := h) qs 0 hm
  let S : (ℝ × ℝ) × ℝ → ℝ := fun p =>
    coleHopfSplitMoment (mExt ms 1) 0 (Real.toNNReal p.1.1)
      (Real.toNNReal p.1.2) (parisiQSuffix ξ h ms qs 0)
      (parisiQSuffixDeriv ξ h ms qs 0) p.2
  have hSc : Continuous S :=
    continuous_coleHopfSplitMoment_zero_outer_var hA hA' hA'b
  let P : ℝ → (ℝ × ℝ) × ℝ := fun u =>
    ((deriv ξ (qExt qs 2) - deriv ξ u,
      deriv ξ u - deriv ξ (qExt qs 0)), 0)
  have hPc : ContinuousAt P 0 := by
    have hd0 : ContinuousAt (deriv ξ) 0 :=
      (hξ.hasDeriv_deriv 0 ⟨le_rfl, zero_le_one⟩).continuousAt
    exact ((continuousAt_const.sub hd0).prodMk
      (hd0.sub continuousAt_const)).prodMk continuousAt_const
  have hc : ContinuousAt (fun u => S (P u)) 0 :=
    ContinuousAt.comp hSc.continuousAt hPc
  apply hc.congr_of_eventuallyEq
  filter_upwards [] with u
  have hext : qExt (qUpdate qs 0 u) 2 = qExt qs 2 :=
    qExt_qUpdate_of_gt qs 0 u (n := 2) (by norm_num)
  unfold parisiQMoment S P
  simp only [Fin.val_zero, if_true, qUpdate_self, qExt_zero]
  rw [hext, parisiQSuffix_qUpdate, parisiQSuffixDeriv_qUpdate]
  simp [mExt_zero]

/-- When the first overlap is zero, every nonzero external field gives a strictly positive
first concrete moment. -/
theorem parisiQMoment_first_pos_of_ne_zero {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hqzero : qs 0 = 0) (hh : h ≠ 0) :
    0 < parisiQMoment ξ h ms qs 0 := by
  have hlevelpos : ∀ i, 0 < parisiLevelMasses ms i := by
    intro i
    rw [parisiLevelMasses_apply]
    exact hm.mExt_pos (by omega)
  let d : ℝ := coleHopfIterateDeriv (k + 1) (parisiLevelMasses ms)
    (parisiLevelVars ξ qs) (parisiLogCoshTerminal h)
    (parisiLogCoshTerminalDeriv h) 0
  have hd : d ≠ 0 :=
    coleHopfIterateDeriv_parisiLogCoshTerminal_ne_zero
      (parisiLevelMasses ms) (parisiLevelVars ξ qs) hlevelpos hh
  rw [parisiQMoment_first_eq_sq_full_deriv ms qs hqzero]
  exact sq_pos_of_ne_zero hd

/-- At the upper endpoint, the concrete final moment is strictly below one.  The strictness
comes from `$|\tanh x|<1$` and is preserved by the preceding Cole-Hopf cascade and the root
Gaussian average. -/
theorem parisiQMoment_last_lt_one {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hqlast : qs (Fin.last k) = 1) :
    parisiQMoment ξ h ms qs (Fin.last k) < 1 := by
  let r : Fin (k + 1) := Fin.last k
  obtain ⟨hA, C, hA', hA''c, hA'b, hA''b⟩ :=
    parisiQSuffix_deriv_regular (ξ := ξ) (h := h) qs r hm
  have hrval : r.val = k := by simp [r]
  have hAeq : parisiQSuffix ξ h ms qs r = parisiLogCoshTerminal h := by
    unfold parisiQSuffix
    exact coleHopfIterate_eq_terminal_of_eq_zero (by omega) _ _ _
  have hA'eq : parisiQSuffixDeriv ξ h ms qs r = parisiLogCoshTerminalDeriv h := by
    unfold parisiQSuffixDeriv
    exact coleHopfIterateDeriv_eq_terminal_of_eq_zero (by omega) _ _ _ _
  have hqright : qExt qs (r.val + 2) = 1 := qExt_of_le qs (by simp [hrval])
  have hvR : Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)) = 0 := by
    rw [hqright]
    have hr : r = Fin.last k := rfl
    rw [hr, hqlast]
    simp
  let f : ℝ → ℝ := fun x =>
    coleHopfSplitMoment (mExt ms (r.val + 1)) (mExt ms r.val)
      (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)))
      (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)))
      (parisiQSuffix ξ h ms qs r) (parisiQSuffixDeriv ξ h ms qs r) x
  have hfc : Continuous f :=
    continuous_coleHopfSplitMoment hA hA' hA'b
  have hfb : ∀ x, |f x| ≤ 1 := fun x =>
    abs_coleHopfSplitMoment_le_one hA hA' hA'b x
  have hflt : ∀ x, f x < 1 := by
    intro x
    dsimp [f]
    rw [hvR]
    apply coleHopfSplitMoment_lt_one_of_zero_right hA hA'
    intro y
    rw [hA'eq]
    exact abs_parisiLogCoshTerminalDeriv_lt_one h y
  by_cases hk : k = 0
  · subst k
    unfold parisiQMoment
    rw [if_pos (by simp)]
    exact hflt 0
  · have hrpos : 0 < r.val := by omega
    let A : ℝ → ℝ := parisiQSuffix ξ h ms qs r
    let B : ℝ → ℝ := coleHopf (mExt ms (r.val + 1))
      (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r))) A
    let G : ℝ → ℝ := coleHopf (mExt ms r.val)
      (Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val))) B
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
    have hprefix_pos : ∀ p, 0 < parisiQPrefixMasses ms r p := fun p =>
      hm.mExt_pos (by simp [parisiQPrefixMasses])
    have hprefix_le : ∀ p, parisiQPrefixMasses ms r p ≤ 1 := fun p =>
      mExt_le_one (fun i => (hm.2.2 i).le) _
    let F : ℝ → ℝ := fun z₀ =>
      ∫ zs, f (z₀ + ∑ p, zs p)
        ∂cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
          (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
          (fun zs => ENNReal.ofReal (Real.exp (G (z₀ + ∑ p, zs p))))
    have hFm : Measurable F :=
      measurable_integral_cascadeTiltMeasure_comp_add_sum
        (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
        hprefix_pos hprefix_le hGm hGlip hfc.measurable
    have hFb : ∀ z₀, |F z₀| ≤ 1 := by
      intro z₀
      exact abs_integral_cascadeTiltMeasure_le
        (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
        hprefix_pos hprefix_le hGm hGlip z₀ hfb
    have hFlt : ∀ z₀, F z₀ < 1 := by
      intro z₀
      let μ := cascadeTiltMeasure (r.val - 1) (parisiQPrefixMasses ms r)
        (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs r p))
        (fun zs => ENNReal.ofReal (Real.exp (G (z₀ + ∑ p, zs p))))
      letI : IsProbabilityMeasure μ :=
        isProbabilityMeasure_cascadeTiltMeasure_comp_add_sum
          (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
          hprefix_pos hprefix_le hGm hGlip z₀
      apply integral_lt_one_of_measurable_of_lt
      · exact hfc.measurable.comp (measurable_const.add
          (Finset.measurable_sum _ fun p _ => measurable_pi_apply p))
      · exact fun zs => hfb _
      · exact fun zs => hflt _
    have hroot : ∫ z₀, F z₀ ∂gaussianReal 0 (parisiVar ξ qs 0) < 1 :=
      integral_lt_one_of_measurable_of_lt hFm hFb hFlt
    unfold parisiQMoment
    rw [if_neg (by simpa [r] using ne_of_gt hrpos)]
    change (∫ z₀, F z₀ ∂gaussianReal 0 (parisiVar ξ qs 0)) < 1
    exact hroot

/-- After absorbing the exponent-one terminal layer, differentiation of its remaining variance
produces the final concrete moment, including the case with no mass parameters. -/
theorem hasDerivAt_parisiLastAbsorbed
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} {ms : Fin k → ℝ}
    (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs)
    (hqlast : qs (Fin.last k) = 1) :
    let r : Fin (k + 1) := Fin.last k
    let a : ℝ := deriv ξ 1 - deriv ξ (qExt qs r.val)
    let w₀ : ℝ≥0 := if r.val = 0 then 0 else parisiVar ξ qs 0
    HasDerivAt
      (fun s => ∫ z₀, coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
        (parisiQPrefixVars ξ qs r)
        (fun y => coleHopf (mExt ms r.val) (Real.toNNReal s)
          (parisiLogCoshTerminal h) y + (a - s) / 2) z₀ ∂gaussianReal 0 w₀)
      ((-(1 - mExt ms r.val) / 2) * parisiQMoment ξ h ms qs r) a := by
  dsimp only
  let r : Fin (k + 1) := Fin.last k
  let a : ℝ := deriv ξ 1 - deriv ξ (qExt qs r.val)
  let w₀ : ℝ≥0 := if r.val = 0 then 0 else parisiVar ξ qs 0
  have hrval : r.val = k := by simp [r]
  have hqLlt : qExt qs r.val < 1 := by
    by_cases hk : k = 0
    · subst k
      simp [r, qExt_zero]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      change qExt qs k < 1
      have hprev : (⟨k - 1, by omega⟩ : Fin (k + 1)) < Fin.last k := by
        exact Fin.mk_lt_mk.mpr (by simp [Fin.last]; omega)
      rw [qExt, if_neg hk, dif_pos (by omega : k - 1 < k + 1)]
      simpa [hqlast] using hq.1 hprev
  have hqLmem : qExt qs r.val ∈ Icc (0 : ℝ) 1 :=
    qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _
  have ha : 0 < a := by
    dsimp [a]
    exact sub_pos.mpr (hξ.strictMonoOn_deriv hqLmem ⟨zero_le_one, le_rfl⟩ hqLlt)
  have hmnonneg : 0 ≤ mExt ms r.val := by
    by_cases hr0 : r.val = 0
    · rw [hr0, mExt_zero]
    · exact (hm.mExt_pos (Nat.pos_of_ne_zero hr0)).le
  have hmle : mExt ms r.val ≤ 1 := mExt_le_one (fun i => (hm.2.2 i).le) _
  have hd := hasDerivAt_integral_coleHopfIterate_absorbed_last
    (a := a) (s₀ := a)
    (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
    (fun p => hm.mExt_pos (by simp [parisiQPrefixMasses]))
    (fun p => mExt_le_one (fun i => (hm.2.2 i).le) _)
    hmnonneg hmle ha
    (hasDerivAt_parisiLogCoshTerminal h)
    (hasDerivAt_parisiLogCoshTerminalDeriv h)
    (continuous_parisiLogCoshTerminalDeriv2 h)
    (fun y => (abs_parisiLogCoshTerminalDeriv_lt_one h y).le)
    (abs_parisiLogCoshTerminalDeriv2_le_one h) w₀
  convert hd using 1
  have hAg : HasLinearGrowth (parisiLogCoshTerminal h) :=
    HasLinearGrowth.of_bounded_deriv (hasDerivAt_parisiLogCoshTerminal h)
      (fun y => (abs_parisiLogCoshTerminalDeriv_lt_one h y).le)
  have hAm : Measurable (parisiLogCoshTerminal h) :=
    measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal h)
  have hA'm : Measurable (parisiLogCoshTerminalDeriv h) :=
    measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminalDeriv h)
  have hinner (y : ℝ) :
      (1 / 2 : ℝ) * ∫ z,
          (parisiLogCoshTerminalDeriv2 h (y + z) +
            mExt ms r.val * parisiLogCoshTerminalDeriv h (y + z) ^ 2) *
            coleHopfQ (mExt ms r.val) (Real.toNNReal a)
              (parisiLogCoshTerminal h) y z ∂gaussianReal 0 (Real.toNNReal a) - 1 / 2 =
        (-(1 - mExt ms r.val) / 2) *
          ∫ z, parisiLogCoshTerminalDeriv h (y + z) ^ 2 *
            coleHopfQ (mExt ms r.val) (Real.toNNReal a)
              (parisiLogCoshTerminal h) y z ∂gaussianReal 0 (Real.toNNReal a) := by
    let Q : ℝ → ℝ := fun z => coleHopfQ (mExt ms r.val) (Real.toNNReal a)
      (parisiLogCoshTerminal h) y z
    have hQi : Integrable Q (gaussianReal 0 (Real.toNNReal a)) := by
      by_cases hm0 : mExt ms r.val = 0
      · simpa [Q, hm0, coleHopfQ_zero] using
          (integrable_const (μ := gaussianReal 0 (Real.toNNReal a)) (1 : ℝ))
      · exact integrable_coleHopfQ hAg hAm hm0 _ _
    have hQone : ∫ z, Q z ∂gaussianReal 0 (Real.toNNReal a) = 1 := by
      by_cases hm0 : mExt ms r.val = 0
      · simp [Q, hm0, coleHopfQ_zero]
      · exact integral_coleHopfQ hAg hAm hm0 _ _
    have hsqg : HasExpGrowth fun x => parisiLogCoshTerminalDeriv h x ^ 2 :=
      HasExpGrowth.of_bounded (C := 1) fun x => by
        rw [abs_pow]
        nlinarith [abs_nonneg (parisiLogCoshTerminalDeriv h x),
          (abs_parisiLogCoshTerminalDeriv_lt_one h x).le]
    have hsqI : Integrable (fun z => parisiLogCoshTerminalDeriv h (y + z) ^ 2 * Q z)
        (gaussianReal 0 (Real.toNNReal a)) := by
      by_cases hm0 : mExt ms r.val = 0
      · simp only [Q, hm0, coleHopfQ_zero, mul_one]
        exact (hsqg.comp_add_const y).integrable_gaussianReal
          ((hA'm.pow_const 2).comp (measurable_const.add measurable_id)).aestronglyMeasurable
      · exact integrable_mul_coleHopfQ hAg hAm hm0 hsqg
          (hA'm.pow_const 2) _ _
    have hexpand :
        (∫ z, (parisiLogCoshTerminalDeriv2 h (y + z) +
              mExt ms r.val * parisiLogCoshTerminalDeriv h (y + z) ^ 2) * Q z
            ∂gaussianReal 0 (Real.toNNReal a)) =
          1 + (mExt ms r.val - 1) *
            ∫ z, parisiLogCoshTerminalDeriv h (y + z) ^ 2 * Q z
              ∂gaussianReal 0 (Real.toNNReal a) := by
      have hpoint : ∀ z,
          (parisiLogCoshTerminalDeriv2 h (y + z) +
              mExt ms r.val * parisiLogCoshTerminalDeriv h (y + z) ^ 2) * Q z =
            Q z + (mExt ms r.val - 1) *
              (parisiLogCoshTerminalDeriv h (y + z) ^ 2 * Q z) := by
        intro z
        simp only [parisiLogCoshTerminalDeriv2, parisiLogCoshTerminalDeriv]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
        integral_add hQi (hsqI.const_mul (mExt ms r.val - 1)),
        integral_const_mul, hQone]
    change (1 / 2 : ℝ) * ∫ z,
        (parisiLogCoshTerminalDeriv2 h (y + z) +
          mExt ms r.val * parisiLogCoshTerminalDeriv h (y + z) ^ 2) * Q z
          ∂gaussianReal 0 (Real.toNNReal a) - 1 / 2 = _
    rw [hexpand]
    ring
  simp_rw [hinner]
  simp_rw [integral_const_mul]
  congr 1
  by_cases hk : k = 0
  · subst k
    let B : ℝ → ℝ := coleHopf 0 (Real.toNNReal a) (parisiLogCoshTerminal h)
    have hBlip : ∀ x y, |B y - B x| ≤ 1 * |y - x| :=
      abs_coleHopf_sub_le_of_lipschitz 0 hAm
        (ProbabilityTheory.abs_sub_le_mul_abs_sub_of_hasDerivAt
          (hasDerivAt_parisiLogCoshTerminal h)
          (fun y => (abs_parisiLogCoshTerminalDeriv_lt_one h y).le)) _
    have hBm : Measurable B :=
      (lipschitzWith_toNNReal_of_abs_sub_le hBlip).continuous.measurable
    let μ := cascadeTiltMeasure 0 (parisiQPrefixMasses ms 0)
      (fun p => gaussianReal 0 (parisiQPrefixVars ξ qs 0 p))
      (fun zs => ENNReal.ofReal (Real.exp (B (0 + ∑ p, zs p))))
    letI : IsProbabilityMeasure μ :=
      isProbabilityMeasure_cascadeTiltMeasure_comp_add_sum
        (parisiQPrefixMasses ms 0) (parisiQPrefixVars ξ qs 0)
        (fun p => Fin.elim0 p) (fun p => Fin.elim0 p) hBm hBlip 0
    simp [r, w₀, a, parisiQMoment, coleHopfSplitMoment, parisiQSuffix,
      parisiQSuffixDeriv, hqlast, coleHopfQ_zero, B, μ, probReal_univ]
    change _ = μ.real Set.univ * _
    rw [probReal_univ, one_mul]
    have hq0 : qs 0 = 1 := by simpa using hqlast
    have hqright : qExt qs 2 = 1 := qExt_of_le qs (by omega)
    have hmright : mExt ms 1 = 1 := mExt_eq_one_of_le ms (by omega)
    simp [hq0, hqright, hmright, coleHopfQ, coleHopfIterateDeriv]
  · have hrpos : 0 < r.val := by simp [r, Nat.pos_of_ne_zero hk]
    have hAeq : parisiQSuffix ξ h ms qs r = parisiLogCoshTerminal h := by
      unfold parisiQSuffix
      exact coleHopfIterate_eq_terminal_of_eq_zero (by omega) _ _ _
    have hA'eq : parisiQSuffixDeriv ξ h ms qs r =
        parisiLogCoshTerminalDeriv h := by
      unfold parisiQSuffixDeriv
      exact coleHopfIterateDeriv_eq_terminal_of_eq_zero (by omega) _ _ _ _
    have hqright : qExt qs (r.val + 2) = 1 := qExt_of_le qs (by simp [hrval])
    have hvR : Real.toNNReal
        (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r)) = 0 := by
      rw [hqright, show qs r = 1 by simpa [r] using hqlast]
      simp
    have hvL : Real.toNNReal (deriv ξ (qs r) - deriv ξ (qExt qs r.val)) =
        Real.toNNReal a := by
      rw [show qs r = 1 by simpa [r] using hqlast]
    have hmright : mExt ms (r.val + 1) = 1 := by
      rw [hrval]
      exact mExt_eq_one_of_le ms (by omega)
    have hw₀ : w₀ = parisiVar ξ qs 0 := by simp [w₀, ne_of_gt hrpos]
    unfold parisiQMoment
    rw [if_neg (ne_of_gt hrpos), hAeq, hA'eq, hvR, hvL, hmright, hw₀]
    simp only [coleHopfSplitMoment, gaussianReal_zero_var, integral_dirac, add_zero,
      mul_one]
    have hCH : coleHopf 1 0 (parisiLogCoshTerminal h) = parisiLogCoshTerminal h := by
      funext x
      exact coleHopf_zero_var 1 (parisiLogCoshTerminal h) x
    have hQ0 : ∀ y, coleHopfQ 1 0 (parisiLogCoshTerminal h) y 0 = 1 := by
      intro y
      simp [coleHopfQ, hCH]
    simp_rw [hCH, hQ0]
    simp [r]

/-- The theta-sum form of the Parisi functional, indexed by `Fin (k + 1)` rather than naturals. -/
theorem hasDerivWithinAt_parisiX₀_last_qUpdate
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} {ms : Fin k → ℝ}
    (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hξ : TalagrandXiCondition ξ) (hq : ParisiQAdmissible qs)
    (hqlast : qs (Fin.last k) = 1) :
    HasDerivWithinAt
      (fun u => parisiX₀ ξ ms (qUpdate qs (Fin.last k) u) (parisiLogCoshTerminal h))
      ((-1 / 2 : ℝ) * deriv (deriv ξ) 1 *
        (1 - mExt ms k) * parisiQMoment ξ h ms qs (Fin.last k)) (Iic 1) 1 := by
  let r : Fin (k + 1) := Fin.last k
  let a : ℝ := deriv ξ 1 - deriv ξ (qExt qs r.val)
  let w₀ : ℝ≥0 := if r.val = 0 then 0 else parisiVar ξ qs 0
  let S : ℝ → ℝ := fun u => deriv ξ u - deriv ξ (qExt qs r.val)
  let J : ℝ → ℝ := fun s => ∫ z₀,
    coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r)
      (fun y => coleHopf (mExt ms r.val) (Real.toNNReal s)
        (parisiLogCoshTerminal h) y + (a - s) / 2) z₀ ∂gaussianReal 0 w₀
  have hJ : HasDerivAt J
      ((-(1 - mExt ms r.val) / 2) * parisiQMoment ξ h ms qs r) a :=
    hasDerivAt_parisiLastAbsorbed qs hm hξ hq hqlast
  have hS : HasDerivAt S (deriv (deriv ξ) 1) 1 :=
    (hξ.hasDeriv_deriv 1 ⟨zero_le_one, le_rfl⟩).sub_const _
  have hd : HasDerivAt (fun u => J (S u))
      (((-(1 - mExt ms r.val) / 2) * parisiQMoment ξ h ms qs r) *
        deriv (deriv ξ) 1) 1 := by
    have hJ' : HasDerivAt J
        ((-(1 - mExt ms r.val) / 2) * parisiQMoment ξ h ms qs r) (S 1) := hJ
    simpa only [Function.comp_def] using hJ'.comp 1 hS
  have hAg : HasLinearGrowth (parisiLogCoshTerminal h) :=
    HasLinearGrowth.of_bounded_deriv (hasDerivAt_parisiLogCoshTerminal h)
      (fun y => (abs_parisiLogCoshTerminalDeriv_lt_one h y).le)
  have hAm : Measurable (parisiLogCoshTerminal h) :=
    measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal h)
  have hAeq : parisiQSuffix ξ h ms qs r = parisiLogCoshTerminal h := by
    unfold parisiQSuffix
    exact coleHopfIterate_eq_terminal_of_eq_zero (by simp [r]) _ _ _
  have hmright : mExt ms (r.val + 1) = 1 :=
    mExt_eq_one_of_le ms (by simp [r])
  have hqright : qExt qs (r.val + 2) = 1 := qExt_of_le qs (by simp [r])
  have heq : ∀ u ∈ Icc (0 : ℝ) 1,
      parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h) = J (S u) := by
    intro u hu
    have hdiff : 0 ≤ deriv ξ 1 - deriv ξ u := sub_nonneg.mpr
      (hξ.strictMonoOn_deriv.monotoneOn hu ⟨zero_le_one, le_rfl⟩ hu.2)
    have hinner : coleHopf 1 (Real.toNNReal (deriv ξ 1 - deriv ξ u))
        (parisiLogCoshTerminal h) =
          fun y => parisiLogCoshTerminal h y + (a - S u) / 2 := by
      funext y
      rw [coleHopf_one_parisiLogCoshTerminal, Real.coe_toNNReal _ hdiff]
      dsimp [a, S]
      ring
    have houter : (fun y => coleHopf (mExt ms r.val) (Real.toNNReal (S u))
        (coleHopf 1 (Real.toNNReal (deriv ξ 1 - deriv ξ u))
          (parisiLogCoshTerminal h)) y) =
        fun y => coleHopf (mExt ms r.val) (Real.toNNReal (S u))
          (parisiLogCoshTerminal h) y + (a - S u) / 2 := by
      rw [hinner]
      funext y
      exact coleHopf_add_const hAg hAm _ _ _ _
    by_cases hk : k = 0
    · subst k
      have hr0 : r = 0 := Fin.eq_zero r
      rw [hr0, parisiX₀_first_qUpdate_eq_split qs hm u]
      rw [show parisiQSuffix ξ h ms qs 0 = parisiLogCoshTerminal h by simpa [hr0] using hAeq]
      rw [show mExt ms 1 = 1 by simpa [hr0] using hmright,
        show qExt qs 2 = 1 by simpa [hr0] using hqright]
      change coleHopf 0 (Real.toNNReal (S u))
        (coleHopf 1 (Real.toNNReal (deriv ξ 1 - deriv ξ u))
          (parisiLogCoshTerminal h)) 0 = _
      rw [hinner, coleHopf_add_const hAg hAm]
      simp [J, w₀, r]
    · have hrpos : 0 < r.val := by simpa [r] using Nat.pos_of_ne_zero hk
      unfold parisiX₀
      rw [parisiVar_qUpdate_before qs r u hrpos]
      dsimp [J]
      rw [show w₀ = parisiVar ξ qs 0 by simp [w₀, ne_of_gt hrpos]]
      apply integral_congr_ae
      filter_upwards [] with z₀
      rw [parisiRecGauss_qUpdate_eq_split qs r hm hrpos u z₀,
        hAeq, hmright, hqright]
      change coleHopfIterate _ _ _
        (fun y => coleHopf (mExt ms r.val) (Real.toNNReal (S u))
          (coleHopf 1 (Real.toNNReal (deriv ξ 1 - deriv ξ u))
            (parisiLogCoshTerminal h)) y) z₀ = _
      rw [houter]
  have hev : (fun u => parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h))
      =ᶠ[nhdsWithin 1 (Iic 1)] fun u => J (S u) := by
    filter_upwards [(eventually_ge_nhds zero_lt_one).filter_mono inf_le_left,
      self_mem_nhdsWithin] with u hu0 hu1
    exact heq u ⟨hu0, hu1⟩
  have hw := hd.hasDerivWithinAt.congr_of_eventuallyEq hev
    (heq 1 ⟨zero_le_one, le_rfl⟩)
  exact hw.congr_deriv (by dsimp [r]; ring)

theorem parisiFunctional_eq_theta_fin_sum (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    parisiFunctional ξ h ms qs
      = Real.log 2 + parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))
        + (1 / 2) * ∑ p : Fin (k + 1),
            parisiTheta ξ (qs p) * (mExt ms (p.val + 1) - mExt ms p.val)
        - (1 / 2) * parisiTheta ξ 1 := by
  rw [parisiFunctional_eq_theta_sum, ← Fin.sum_univ_eq_sum_range]
  simp only [qExt_succ_of_lt qs (Fin.isLt _)]

/-- The part of the theta-sum independent of the coordinate `q_{r+1}`. -/
def parisiQConst (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) : ℝ :=
  Real.log 2
    + (1 / 2) * ∑ p ∈ Finset.univ.erase r,
        parisiTheta ξ (qs p) * (mExt ms (p.val + 1) - mExt ms p.val)
    - (1 / 2) * parisiTheta ξ 1

/-- Along one overlap coordinate, the full Parisi functional is a constant plus `X₀(q)` plus
`(1 / 2) (m_r - m_{r-1}) θ(q)`. This is the form used in passing from the derivative of `X₀` to
(14.220). -/
lemma parisiTheta_sum_qUpdate (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : ℝ) :
    (∑ p : Fin (k + 1),
      parisiTheta ξ (qUpdate qs r u p) * (mExt ms (p.val + 1) - mExt ms p.val)) =
    (∑ p ∈ Finset.univ.erase r,
      parisiTheta ξ (qs p) * (mExt ms (p.val + 1) - mExt ms p.val)) +
      parisiTheta ξ u * (mExt ms (r.val + 1) - mExt ms r.val) := by
  classical
  calc
    (∑ p : Fin (k + 1),
        parisiTheta ξ (qUpdate qs r u p) * (mExt ms (p.val + 1) - mExt ms p.val))
        = (∑ p ∈ Finset.univ.erase r,
            parisiTheta ξ (qUpdate qs r u p) * (mExt ms (p.val + 1) - mExt ms p.val))
          + parisiTheta ξ (qUpdate qs r u r)
              * (mExt ms (r.val + 1) - mExt ms r.val) := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ r)]
    _ = (∑ p ∈ Finset.univ.erase r,
            parisiTheta ξ (qs p) * (mExt ms (p.val + 1) - mExt ms p.val))
          + parisiTheta ξ u * (mExt ms (r.val + 1) - mExt ms r.val) := by
        congr 1
        · refine Finset.sum_congr rfl ?_
          intro p hp
          rw [qUpdate_of_ne qs u (Finset.ne_of_mem_erase hp)]
        · rw [qUpdate_self]

theorem parisiFunctional_qUpdate_eq (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : ℝ) :
    parisiFunctional ξ h ms (qUpdate qs r u)
      = parisiQConst ξ ms qs r
        + (parisiX₀ ξ ms (qUpdate qs r u) (fun x => Real.log (Real.cosh (h + x)))
          + (1 / 2) * (mExt ms (r.val + 1) - mExt ms r.val) * parisiTheta ξ u) := by
  classical
  rw [parisiFunctional_eq_theta_fin_sum, parisiTheta_sum_qUpdate]
  unfold parisiQConst
  ring

/-- `θ'(q) = q ξ''(q)`. -/
theorem hasDerivAt_parisiTheta {ξ : ℝ → ℝ} {q ξ₂ : ℝ}
    (hξ : HasDerivAt ξ (deriv ξ q) q)
    (hξ' : HasDerivAt (deriv ξ) ξ₂ q) :
    HasDerivAt (parisiTheta ξ) (q * ξ₂) q := by
  unfold parisiTheta
  have hfun : id * deriv ξ - ξ = fun x => x * deriv ξ x - ξ x := by
    rfl
  rw [← hfun]
  simpa only [id_eq, one_mul, mul_one, add_sub_cancel_left] using
    ((hasDerivAt_id q).mul hξ').sub hξ

/-- Talagrand's (14.220).

Assume the `q_{r+1}`-derivative of `X₀` has already been propagated through the preceding
Cole--Hopf levels, so that its derivative is
`-(1 / 2) ξ''(q) (m_r - m_{r-1}) M`. Then the derivative of the actual Parisi functional along
that coordinate is

`(1 / 2) (m_r - m_{r-1}) ξ''(q) (-M + q)`.

For Talagrand's application, `M = E(W₁ ⋯ W_{r-1} A_r'(ζ_r)^2)`; the propagation of (14.219)
through the earlier levels is exactly `hasDerivAt_coleHopfIterate_split` /
`hasDerivAt_integral_coleHopfIterate_split`. -/
theorem hasDerivAt_parisiFunctional_qUpdate
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) {q ξ₂ M : ℝ}
    (hX₀ : HasDerivAt
      (fun u => parisiX₀ ξ ms (qUpdate qs r u) (fun x => Real.log (Real.cosh (h + x))))
      ((-1 / 2 : ℝ) * ξ₂ * (mExt ms (r.val + 1) - mExt ms r.val) * M) q)
    (hξ : HasDerivAt ξ (deriv ξ q) q)
    (hξ' : HasDerivAt (deriv ξ) ξ₂ q) :
    HasDerivAt (fun u => parisiFunctional ξ h ms (qUpdate qs r u))
      ((1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) * ξ₂ * (-M + q)) q := by
  let C : ℝ := parisiQConst ξ ms qs r
  let c : ℝ := (1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val)
  have hθ := hasDerivAt_parisiTheta hξ hξ'
  have hbase := hX₀.add (hθ.const_mul c)
  have hall := (hasDerivAt_const q C).add hbase
  have hfun :
      (fun u => parisiFunctional ξ h ms (qUpdate qs r u))
        = (fun u => C +
          (parisiX₀ ξ ms (qUpdate qs r u) (fun x => Real.log (Real.cosh (h + x)))
            + c * parisiTheta ξ u)) := by
    funext u
    rw [parisiFunctional_qUpdate_eq]
  rw [hfun]
  refine hall.congr_deriv ?_
  dsimp [c]
  ring

/-- The concrete form of (14.220), obtained from the actual Parisi recursion rather than an
assumed derivative of `parisiX₀`. -/
theorem hasDerivAt_parisiFunctional_qUpdate_concrete
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (hm : ParisiMAdmissible ms) {ξ₂ : ℝ}
    (hξ : HasDerivAt ξ (deriv ξ (qs r)) (qs r))
    (hξ' : HasDerivAt (deriv ξ) ξ₂ (qs r))
    (hleft : deriv ξ (qExt qs r.val) < deriv ξ (qs r))
    (hright : deriv ξ (qs r) < deriv ξ (qExt qs (r.val + 2))) :
    HasDerivAt (fun u => parisiFunctional ξ h ms (qUpdate qs r u))
      ((1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) * ξ₂ *
        (-parisiQMoment ξ h ms qs r + qs r)) (qs r) := by
  apply hasDerivAt_parisiFunctional_qUpdate ms qs r
    (hasDerivAt_parisiX₀_qUpdate qs r hm hξ' hleft hright) hξ hξ'

/-! ### The strict overlap chain: (14.221) -/

/-- The strict chain form of Talagrand's (14.221): if the free `q`-coordinates are strictly
increasing and the two endpoints are strict, then every adjacent pair of the extended sequence
`q₀ = 0, q₁, …, q_{k+1}, q_{k+2} = 1` is strictly increasing. -/
theorem qExt_strict_succ {k : ℕ} {qs : Fin (k + 1) → ℝ}
    (hsm : StrictMono qs) (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1)
    {r : ℕ} (hr : r ≤ k + 1) : qExt qs r < qExt qs (r + 1) := by
  rcases r with _ | r
  · rw [qExt_zero, qExt_succ_of_lt qs (Nat.succ_pos k)]
    exact hq0
  · have hrk : r ≤ k := by omega
    rcases lt_or_eq_of_le hrk with hrlt | hrEq
    · rw [qExt_succ_of_lt qs (by omega : r < k + 1),
          qExt_succ_of_lt qs (by omega : r + 1 < k + 1)]
      apply hsm
      simp
    · rw [qExt_succ_of_lt qs (by omega : r < k + 1),
        qExt_of_le qs (by omega : k + 2 ≤ r + 2)]
      have hlast : (⟨r, by omega⟩ : Fin (k + 1)) = Fin.last k := by
        apply Fin.ext
        exact hrEq
      simpa only [hlast] using hq1

/-! ### The stationarity equation: (14.222) -/

/-- The stationary-point implication in Proposition 14.7.5, i.e. (14.222).

At an interior coordinatewise minimum, (14.220) has derivative zero.  If
`m_r - m_{r-1}` and `ξ''(q_r)` are nonzero, this forces `q_r = M`. -/
theorem parisiQ_eq_moment_of_isLocalMin
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) {q ξ₂ M : ℝ}
    (hmin : IsLocalMin (fun u => parisiFunctional ξ h ms (qUpdate qs r u)) q)
    (hX₀ : HasDerivAt
      (fun u => parisiX₀ ξ ms (qUpdate qs r u) (fun x => Real.log (Real.cosh (h + x))))
      ((-1 / 2 : ℝ) * ξ₂ * (mExt ms (r.val + 1) - mExt ms r.val) * M) q)
    (hξ : HasDerivAt ξ (deriv ξ q) q)
    (hξ' : HasDerivAt (deriv ξ) ξ₂ q)
    (hm : mExt ms (r.val + 1) ≠ mExt ms r.val) (hξ₂ : ξ₂ ≠ 0) :
    q = M := by
  have hd := hasDerivAt_parisiFunctional_qUpdate ms qs r hX₀ hξ hξ'
  have hz := hmin.hasDerivAt_eq_zero hd
  have hc : (1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) * ξ₂ ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) hξ₂
    exact sub_ne_zero.mpr hm
  have hz' :
      ((1 / 2 : ℝ) * (mExt ms (r.val + 1) - mExt ms r.val) * ξ₂) * (-M + q) = 0 := by
    simpa [mul_assoc] using hz
  have hlast : -M + q = 0 := (mul_eq_zero.mp hz').resolve_left hc
  linarith

/-- The stationarity implication with the nonvanishing mass gap derived from (14.103). -/
theorem parisiQ_eq_moment_of_isLocalMin_of_admissible
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) {q ξ₂ M : ℝ} (hm : ParisiMAdmissible ms) (hξ₂ : 0 < ξ₂)
    (hmin : IsLocalMin (fun u => parisiFunctional ξ h ms (qUpdate qs r u)) q)
    (hX₀ : HasDerivAt
      (fun u => parisiX₀ ξ ms (qUpdate qs r u) (fun x => Real.log (Real.cosh (h + x))))
      ((-1 / 2 : ℝ) * ξ₂ * (mExt ms (r.val + 1) - mExt ms r.val) * M) q)
    (hξ : HasDerivAt ξ (deriv ξ q) q)
    (hξ' : HasDerivAt (deriv ξ) ξ₂ q) :
    q = M := by
  apply parisiQ_eq_moment_of_isLocalMin ms qs r hmin hX₀ hξ hξ'
  · exact ne_of_gt (hm.mExt_gap_pos r) |>.imp fun heq => sub_eq_zero.mpr heq
  · exact ne_of_gt hξ₂

/-- Conditional abstract reduction of Proposition 14.7.5, in the overlap-coordinate API.

The functions `M` and `ξ₂` record respectively
`E(W₁ ⋯ W_{r-1} A'_r(ζ_r)^2)` and `ξ''(q_r)`. The endpoint assumptions are the two strict
bounds used in Talagrand's proof: the first moment is positive and the last moment is less than
one. Admissible global minimality then gives the strict extended overlap chain (14.221), and
the derivative identity (14.220) gives all the equations (14.222). -/
theorem parisiQ_strict_chain_and_eq_moment_of_isMin
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (M ξ₂ : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hmin : IsParisiQMinimizer ξ h ms qs)
    (hX₀ : ∀ r, HasDerivAt
      (fun u => parisiX₀ ξ ms (qUpdate qs r u) (fun x => Real.log (Real.cosh (h + x))))
      ((-1 / 2 : ℝ) * ξ₂ r * (mExt ms (r.val + 1) - mExt ms r.val) * M r) (qs r))
    (hξ : ∀ r, HasDerivAt ξ (deriv ξ (qs r)) (qs r))
    (hξ' : ∀ r, HasDerivAt (deriv ξ) (ξ₂ r) (qs r))
    (hξ₂ : ∀ r, 0 < ξ₂ r) (hMfirst : 0 < M 0) (hMlast : M (Fin.last k) < 1) :
    (∀ r : ℕ, r ≤ k + 1 → qExt qs r < qExt qs (r + 1)) ∧
      ∀ r, qs r = M r := by
  have hd (r : Fin (k + 1)) :=
    hasDerivAt_parisiFunctional_qUpdate ms qs r (hX₀ r) (hξ r) (hξ' r)
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
  exact parisiQ_eq_moment_of_isLocalMin_of_admissible ms qs r hm (hξ₂ r)
    (hmin.isLocalMin_qUpdate ms qs hq0 hq1 r) (hX₀ r) (hξ r) (hξ' r)

/-- Proposition 14.7.5 after the endpoint inequalities are known: the moment and every
`parisiX₀` derivative are now the concrete ones from the recursion. -/
theorem parisiQ_strict_chain_and_eq_concrete_moment_of_isMin_of_endpoints
    {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hξ : TalagrandXiCondition ξ)
    (hmin : IsParisiQMinimizer ξ h ms qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1) :
    (∀ n : ℕ, n ≤ k + 1 → qExt qs n < qExt qs (n + 1)) ∧
      ∀ r, qs r = parisiQMoment ξ h ms qs r := by
  have hchain : ∀ n : ℕ, n ≤ k + 1 → qExt qs n < qExt qs (n + 1) :=
    fun n hn => qExt_strict_succ hmin.1.1 hq0 hq1 hn
  refine ⟨hchain, ?_⟩
  intro r
  have hqpos : 0 < qs r := hq0.trans_le (hmin.1.monotone (Fin.zero_le r))
  have hqmem := hmin.1.mem_Icc r
  have hξ₂pos : 0 < deriv (deriv ξ) (qs r) :=
    hξ.second_pos _ hqmem (ne_of_gt hqpos)
  have hleftq : qExt qs r.val < qs r := by
    simpa [qExt_succ_of_lt qs r.isLt] using hchain r.val (by omega)
  have hrightq : qs r < qExt qs (r.val + 2) := by
    simpa [qExt_succ_of_lt qs r.isLt] using hchain (r.val + 1) (by omega)
  have hleft : deriv ξ (qExt qs r.val) < deriv ξ (qs r) :=
    hξ.strictMonoOn_deriv (qExt_mem_Icc hmin.1.monotone hmin.1.2.1 hmin.1.2.2 _)
      hqmem hleftq
  have hright : deriv ξ (qs r) < deriv ξ (qExt qs (r.val + 2)) :=
    hξ.strictMonoOn_deriv hqmem
      (qExt_mem_Icc hmin.1.monotone hmin.1.2.1 hmin.1.2.2 _) hrightq
  apply parisiQ_eq_moment_of_isLocalMin_of_admissible ms qs r hm hξ₂pos
    (hmin.isLocalMin_qUpdate ms qs hq0 hq1 r)
  · change HasDerivAt
      (fun u => parisiX₀ ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h))
      ((-1 / 2 : ℝ) * deriv (deriv ξ) (qs r) *
        (mExt ms (r.val + 1) - mExt ms r.val) * parisiQMoment ξ h ms qs r) (qs r)
    exact hasDerivAt_parisiX₀_qUpdate qs r hm
      (hξ.hasDeriv_deriv _ hqmem) hleft hright
  · exact hξ.hasDeriv _ hqmem
  · exact hξ.hasDeriv_deriv _ hqmem

lemma hasDerivAt_linear_right_extension {f : ℝ → ℝ} {b d : ℝ}
    (hf : HasDerivWithinAt f d (Iic b) b) :
    HasDerivAt (fun u => if u ≤ b then f u else f b + (u - b) * d) d b := by
  let E : ℝ → ℝ := fun u => if u ≤ b then f u else f b + (u - b) * d
  have hl : HasDerivWithinAt E d (Iic b) b :=
    hf.congr_of_eventuallyEq
      (by
        filter_upwards [self_mem_nhdsWithin] with u hu
        change u ≤ b at hu
        simp [E, hu])
      (by simp [E])
  have ha : HasDerivAt (fun u => f b + (u - b) * d) d b := by
    simpa using (((hasDerivAt_id b).sub_const b).mul_const d).const_add (f b)
  have hr : HasDerivWithinAt E d (Ici b) b :=
    ha.hasDerivWithinAt.congr_of_eventuallyEq
      (by
        filter_upwards [self_mem_nhdsWithin] with u hu
        by_cases hub : u ≤ b
        · have hueq : u = b := le_antisymm hub hu
          simp [E, hueq]
        · simp [E, hub])
      (by simp [E])
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr


end

end SpinGlass
