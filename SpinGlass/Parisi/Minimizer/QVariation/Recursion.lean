import SpinGlass.Parisi.Minimizer.QVariation.Terminal

/-!
# Recursion

Concrete Parisi recursion as a Cole-Hopf iterate.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

/-- The masses of all Cole-Hopf levels in `parisiRecGauss`. -/
def parisiLevelMasses {k : ℕ} (ms : Fin k → ℝ) : Fin (k + 1) → ℝ :=
  Fin.snoc ms 1

@[simp] lemma parisiLevelMasses_apply {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1)) :
    parisiLevelMasses ms p = mExt ms (p.val + 1) := by
  refine Fin.lastCases ?_ (fun i => ?_) p
  · simp [parisiLevelMasses, mExt_eq_one_of_le]
  · simp [parisiLevelMasses, mExt_val_succ]

/-- The variances of all Cole-Hopf levels in `parisiRecGauss`. -/
def parisiLevelVars (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ) :
    Fin (k + 1) → ℝ≥0 := fun p => parisiVar ξ qs (p.val + 1)

/-- The Gaussian Parisi recursion is the concrete Cole-Hopf iterate used below. -/
theorem parisiRecGauss_eq_coleHopfIterate {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (z₀ : ℝ) :
    parisiRecGauss ξ ms qs (parisiLogCoshTerminal h) z₀ =
      coleHopfIterate (k + 1) (parisiLevelMasses ms) (parisiLevelVars ξ qs)
        (parisiLogCoshTerminal h) z₀ := by
  unfold parisiRecGauss parisiMarks parisiLevelMasses parisiLevelVars
  apply parisiRec_gaussian_comp_add_sum (L := 1)
  · intro p
    refine Fin.lastCases ?_ (fun i => ?_) p
    · simp
    · simpa using hm.2.1 i
  · exact measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal h)
  · intro x y
    simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le h x y

/-- `parisiX₀` is the outer Gaussian average of the concrete Cole-Hopf iterate. -/
theorem parisiX₀_eq_integral_coleHopfIterate {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) :
    parisiX₀ ξ ms qs (parisiLogCoshTerminal h) =
      ∫ z₀, coleHopfIterate (k + 1) (parisiLevelMasses ms) (parisiLevelVars ξ qs)
        (parisiLogCoshTerminal h) z₀ ∂gaussianReal 0 (parisiVar ξ qs 0) := by
  unfold parisiX₀
  congr 1
  funext z₀
  exact parisiRecGauss_eq_coleHopfIterate qs hm z₀

/-- The positive-exponent levels preceding the two levels adjacent to `r`. -/
def parisiQPrefixMasses {k : ℕ} (ms : Fin k → ℝ) (r : Fin (k + 1)) :
    Fin (r.val - 1) → ℝ := fun p => mExt ms (p.val + 1)

/-- The unchanged variances preceding the two levels adjacent to `r`. -/
def parisiQPrefixVars (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) : Fin (r.val - 1) → ℝ≥0 :=
  fun p => parisiVar ξ qs (p.val + 1)

/-- The masses strictly after the two levels adjacent to the coordinate represented by `r`. -/
def parisiQSuffixMasses {k : ℕ} (ms : Fin k → ℝ) (r : Fin (k + 1)) :
    Fin (k - r.val) → ℝ := fun p => mExt ms (r.val + p.val + 2)

/-- The variances strictly after the two levels adjacent to the coordinate represented by `r`. -/
def parisiQSuffixVars (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) : Fin (k - r.val) → ℝ≥0 :=
  fun p => parisiVar ξ qs (r.val + p.val + 2)

/-- Talagrand's `$A_{r+2}$`, namely the part of the recursion strictly inside the two levels
whose variance split changes when the free coordinate represented by `r` moves. -/
def parisiQSuffix (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) : ℝ → ℝ :=
  coleHopfIterate (k - r.val) (parisiQSuffixMasses ms r) (parisiQSuffixVars ξ qs r)
    (parisiLogCoshTerminal h)

/-- The canonical first derivative of `parisiQSuffix`. -/
def parisiQSuffixDeriv (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) : ℝ → ℝ :=
  coleHopfIterateDeriv (k - r.val) (parisiQSuffixMasses ms r) (parisiQSuffixVars ξ qs r)
    (parisiLogCoshTerminal h) (parisiLogCoshTerminalDeriv h)

/-- The canonical second derivative of `parisiQSuffix`. -/
def parisiQSuffixDeriv2 (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) : ℝ → ℝ :=
  coleHopfIterateDeriv2 (k - r.val) (parisiQSuffixMasses ms r) (parisiQSuffixVars ξ qs r)
    (parisiLogCoshTerminal h) (parisiLogCoshTerminalDeriv h)
    (parisiLogCoshTerminalDeriv2 h)

lemma parisiQSuffixVars_qUpdate (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : ℝ) :
    parisiQSuffixVars ξ (qUpdate qs r u) r = parisiQSuffixVars ξ qs r := by
  funext p
  unfold parisiQSuffixVars
  rw [parisiVar_qUpdate_after]
  omega

lemma parisiQSuffix_qUpdate (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : ℝ) :
    parisiQSuffix ξ h ms (qUpdate qs r u) r = parisiQSuffix ξ h ms qs r := by
  unfold parisiQSuffix
  rw [parisiQSuffixVars_qUpdate]

lemma parisiQSuffixDeriv_qUpdate (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : ℝ) :
    parisiQSuffixDeriv ξ h ms (qUpdate qs r u) r =
      parisiQSuffixDeriv ξ h ms qs r := by
  unfold parisiQSuffixDeriv
  rw [parisiQSuffixVars_qUpdate]

lemma parisiQSuffix_translate (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (x : ℝ) :
    parisiQSuffix ξ h ms qs r x = parisiQSuffix ξ 0 ms qs r (h + x) := by
  have hG : parisiLogCoshTerminal h = fun y => parisiLogCoshTerminal 0 (h + y) := by
    funext y
    simp only [parisiLogCoshTerminal, zero_add]
  unfold parisiQSuffix
  rw [hG]
  exact coleHopfIterate_translate _ _ (parisiLogCoshTerminal 0) h x

lemma parisiQSuffixDeriv_translate (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (x : ℝ) :
    parisiQSuffixDeriv ξ h ms qs r x = parisiQSuffixDeriv ξ 0 ms qs r (h + x) := by
  have hG : parisiLogCoshTerminal h = fun y => parisiLogCoshTerminal 0 (h + y) := by
    funext y
    simp only [parisiLogCoshTerminal, zero_add]
  have hG' : parisiLogCoshTerminalDeriv h =
      fun y => parisiLogCoshTerminalDeriv 0 (h + y) := by
    funext y
    simp only [parisiLogCoshTerminalDeriv, zero_add]
  unfold parisiQSuffixDeriv
  rw [hG, hG']
  exact coleHopfIterateDeriv_translate _ _
    (parisiLogCoshTerminal 0) (parisiLogCoshTerminalDeriv 0) h x

/-- The actual recursive suffix has the regularity and uniform first-derivative bound required
by the split derivative theorem. -/
theorem parisiQSuffix_deriv_regular {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hm : ParisiMAdmissible ms) :
    (∀ x, HasDerivAt (parisiQSuffix ξ h ms qs r) (parisiQSuffixDeriv ξ h ms qs r x) x) ∧
    (∃ C : ℝ,
      (∀ x, HasDerivAt (parisiQSuffixDeriv ξ h ms qs r)
        (parisiQSuffixDeriv2 ξ h ms qs r x) x) ∧
      Continuous (parisiQSuffixDeriv2 ξ h ms qs r) ∧
      (∀ x, |parisiQSuffixDeriv ξ h ms qs r x| ≤ 1) ∧
      ∀ x, |parisiQSuffixDeriv2 ξ h ms qs r x| ≤ C) := by
  apply coleHopfIterate_deriv_regular
  · exact hasDerivAt_parisiLogCoshTerminal h
  · exact hasDerivAt_parisiLogCoshTerminalDeriv h
  · exact continuous_parisiLogCoshTerminalDeriv2 h
  · exact fun x => (abs_parisiLogCoshTerminalDeriv_lt_one h x).le
  · exact abs_parisiLogCoshTerminalDeriv2_le_one h
  · intro p
    apply hm.mExt_pos
    simp

/-- At the first overlap coordinate, the inner derivative in the split moment is exactly the
spatial derivative of the full concrete Cole-Hopf recursion. -/
lemma parisiQFirstInner_eq_coleHopfIterateDeriv {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (x : ℝ) :
    (∫ w, parisiQSuffixDeriv ξ h ms qs 0 (x + w) *
        coleHopfQ (mExt ms 1)
          (Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ (qs 0)))
          (parisiQSuffix ξ h ms qs 0) x w
      ∂gaussianReal 0 (Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ (qs 0)))) =
      coleHopfIterateDeriv (k + 1) (parisiLevelMasses ms) (parisiLevelVars ξ qs)
        (parisiLogCoshTerminal h) (parisiLogCoshTerminalDeriv h) x := by
  have hms : Fin.tail (parisiLevelMasses ms) = parisiQSuffixMasses ms 0 := by
    funext p
    simp [Fin.tail, parisiQSuffixMasses, parisiLevelMasses_apply]
  have hvs : Fin.tail (parisiLevelVars ξ qs) = parisiQSuffixVars ξ qs 0 := by
    funext p
    simp [Fin.tail, parisiLevelVars, parisiQSuffixVars]
  rw [coleHopfIterateDeriv]
  rw [hms, hvs]
  simp only [parisiLevelMasses_apply, Fin.val_zero, zero_add]
  have hv : parisiLevelVars ξ qs 0 =
      Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ (qs 0)) := by
    simp [parisiLevelVars, parisiVar, qExt_succ_of_lt qs (Nat.succ_pos k)]
  rw [hv]
  rfl

/-- For a nonfirst coordinate, the concrete recursion splits into its unchanged prefix, the two
levels whose variances change, and the concrete suffix. -/
theorem parisiRecGauss_qUpdate_eq_split {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hr : 0 < r.val) (u z₀ : ℝ) :
    parisiRecGauss ξ ms (qUpdate qs r u) (parisiLogCoshTerminal h) z₀ =
      coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
        (parisiQPrefixVars ξ qs r)
        (coleHopf (mExt ms r.val)
          (Real.toNNReal (deriv ξ u - deriv ξ (qExt qs r.val)))
          (coleHopf (mExt ms (r.val + 1))
            (Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ u))
            (parisiQSuffix ξ h ms qs r))) z₀ := by
  rw [parisiRecGauss_eq_coleHopfIterate (qUpdate qs r u) hm]
  have hn : k + 1 = (r.val - 1) + (2 + (k - r.val)) := by omega
  rw [coleHopfIterate_split_two_of_eq (r.val - 1) (k - r.val) hn]
  congr 4
  · funext p
    unfold parisiLevelVars parisiQPrefixVars
    change parisiVar ξ (qUpdate qs r u) (p.val + 1) = parisiVar ξ qs (p.val + 1)
    rw [parisiVar_qUpdate_before]
    have hp := p.isLt
    omega
  · rw [parisiLevelMasses_apply]
    apply congrArg (mExt ms)
    change r.val - 1 + 1 = r.val
    omega
  · unfold parisiLevelVars
    have hre : r.val - 1 + 1 = r.val := by omega
    rw [hre, parisiVar_qUpdate_left]
  · apply Fin.ext
    simp
    omega
  · unfold parisiLevelVars
    have hre : r.val - 1 + 1 + 1 = r.val + 1 := by omega
    rw [hre, parisiVar_qUpdate_right]
  · funext p
    rw [parisiLevelMasses_apply]
    unfold parisiQSuffixMasses
    apply congrArg (mExt ms)
    change r.val - 1 + p.val + 2 + 1 = r.val + p.val + 2
    omega
  · funext p
    unfold parisiLevelVars parisiQSuffixVars
    rw [parisiVar_qUpdate_after]
    · apply congrArg (parisiVar ξ qs)
      change r.val - 1 + p.val + 2 + 1 = r.val + p.val + 2
      omega
    · change r.val + 1 < r.val - 1 + p.val + 2 + 1
      omega

/-- At the first coordinate, the changing inner level is followed by the same concrete suffix. -/
theorem parisiRecGauss_first_qUpdate_eq {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (u z₀ : ℝ) :
    parisiRecGauss ξ ms (qUpdate qs 0 u) (parisiLogCoshTerminal h) z₀ =
      coleHopf (mExt ms 1)
        (Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ u))
        (parisiQSuffix ξ h ms qs 0) z₀ := by
  rw [parisiRecGauss_eq_coleHopfIterate (qUpdate qs 0 u) hm,
    coleHopfIterate_succ]
  congr 3
  · funext p
    simp [Fin.tail, parisiQSuffixMasses]
  · funext p
    simp only [Fin.tail, parisiLevelVars, parisiQSuffixVars, Fin.val_succ, Fin.val_zero,
      Nat.sub_zero, Nat.zero_add]
    rw [parisiVar_qUpdate_after]
    simp

/-- The first overlap variation is exactly a two-level split with outer exponent zero. -/
theorem parisiX₀_first_qUpdate_eq_split {ξ : ℝ → ℝ} {h : ℝ} {k : ℕ}
    {ms : Fin k → ℝ} (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (u : ℝ) :
    parisiX₀ ξ ms (qUpdate qs 0 u) (parisiLogCoshTerminal h) =
      coleHopf 0 (Real.toNNReal (deriv ξ u - deriv ξ (qExt qs 0)))
        (coleHopf (mExt ms 1)
          (Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ u))
          (parisiQSuffix ξ h ms qs 0)) 0 := by
  unfold parisiX₀
  rw [coleHopf_zero]
  have hv := parisiVar_qUpdate_left (ξ := ξ) qs (0 : Fin (k + 1)) u
  simp only [Fin.val_zero] at hv
  rw [hv]
  apply integral_congr_ae
  filter_upwards [] with z₀
  simpa using parisiRecGauss_first_qUpdate_eq qs hm u z₀

/-- If `ξ'` converges along an overlap variation, the corresponding concrete `X₀` values
converge uniformly in the external-field shift.  This includes the endpoint where one of the
two adjacent variances collapses to zero. -/
theorem tendsto_uniform_parisiX₀_qUpdate
    {α : Type*} {l : Filter α} {ξ : ℝ → ℝ} {k : ℕ} {ms : Fin k → ℝ}
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : α → ℝ)
    (hm : ParisiMAdmissible ms)
    (hu : Filter.Tendsto (fun a => deriv ξ (u a)) l (nhds (deriv ξ (qs r)))) :
    ∀ ε > 0, ∀ᶠ a in l, ∀ h,
      |parisiX₀ ξ ms (qUpdate qs r (u a)) (parisiLogCoshTerminal h) -
        parisiX₀ ξ ms (qUpdate qs r (qs r)) (parisiLogCoshTerminal h)| < ε := by
  let A : ℝ → ℝ := parisiQSuffix ξ 0 ms qs r
  have hAreg := parisiQSuffix_deriv_regular (ξ := ξ) (h := 0) qs r hm
  have hAm : Measurable A := measurable_of_hasDerivAt hAreg.1
  have hAlip : ∀ x y, |A y - A x| ≤ 1 * |y - x| :=
    ProbabilityTheory.abs_sub_le_mul_abs_sub_of_hasDerivAt hAreg.1 hAreg.2.choose_spec.2.2.1
  let vL : α → ℝ≥0 := fun a =>
    Real.toNNReal (deriv ξ (u a) - deriv ξ (qExt qs r.val))
  let vR : α → ℝ≥0 := fun a =>
    Real.toNNReal (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (u a))
  let vL₀ : ℝ≥0 := Real.toNNReal
    (deriv ξ (qs r) - deriv ξ (qExt qs r.val))
  let vR₀ : ℝ≥0 := Real.toNNReal
    (deriv ξ (qExt qs (r.val + 2)) - deriv ξ (qs r))
  have hvL : Filter.Tendsto vL l (nhds vL₀) := by
    exact continuous_real_toNNReal.continuousAt.tendsto.comp
      (hu.sub_const (deriv ξ (qExt qs r.val)))
  have hvR : Filter.Tendsto vR l (nhds vR₀) := by
    exact continuous_real_toNNReal.continuousAt.tendsto.comp
      (hu.const_sub (deriv ξ (qExt qs (r.val + 2))))
  let T : α → ℝ → ℝ := fun a =>
    coleHopf (mExt ms r.val) (vL a)
      (coleHopf (mExt ms (r.val + 1)) (vR a) A)
  let T₀ : ℝ → ℝ :=
    coleHopf (mExt ms r.val) vL₀
      (coleHopf (mExt ms (r.val + 1)) vR₀ A)
  have hT := tendsto_uniform_coleHopf_two_of_tendsto_var hAm hAlip
    (mExt ms r.val) (mExt ms (r.val + 1)) hvL hvR
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  filter_upwards [hT (ε / 2) hhalf] with a ha
  intro h
  have htranslate (a : α) :
      coleHopf (mExt ms r.val) (vL a)
          (coleHopf (mExt ms (r.val + 1)) (vR a)
            (parisiQSuffix ξ h ms qs r)) = fun x => T a (h + x) := by
    have hAtrans : parisiQSuffix ξ h ms qs r = fun y => A (h + y) := by
      funext y
      exact parisiQSuffix_translate ξ h ms qs r y
    rw [hAtrans]
    have hinner :
        coleHopf (mExt ms (r.val + 1)) (vR a) (fun y => A (h + y)) =
          fun y => coleHopf (mExt ms (r.val + 1)) (vR a) A (h + y) := by
      funext y
      exact coleHopf_translate _ _ A h y
    rw [hinner]
    funext x
    exact coleHopf_translate _ _ _ h x
  have htranslate₀ :
      coleHopf (mExt ms r.val) vL₀
          (coleHopf (mExt ms (r.val + 1)) vR₀
            (parisiQSuffix ξ h ms qs r)) = fun x => T₀ (h + x) := by
    have hAtrans : parisiQSuffix ξ h ms qs r = fun y => A (h + y) := by
      funext y
      exact parisiQSuffix_translate ξ h ms qs r y
    rw [hAtrans]
    have hinner :
        coleHopf (mExt ms (r.val + 1)) vR₀ (fun y => A (h + y)) =
          fun y => coleHopf (mExt ms (r.val + 1)) vR₀ A (h + y) := by
      funext y
      exact coleHopf_translate _ _ A h y
    rw [hinner]
    funext x
    exact coleHopf_translate _ _ _ h x
  by_cases hr : r.val = 0
  · have hre : r = 0 := Fin.ext hr
    subst r
    rw [parisiX₀_first_qUpdate_eq_split qs hm (u a),
      parisiX₀_first_qUpdate_eq_split qs hm (qs 0)]
    have ht :
        coleHopf 0 (Real.toNNReal (deriv ξ (u a) - deriv ξ (qExt qs 0)))
            (coleHopf (mExt ms 1)
              (Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ (u a)))
              (parisiQSuffix ξ h ms qs 0)) 0 = T a h := by
      simpa [vL, vR, mExt_zero] using congrFun (htranslate a) 0
    have ht₀ :
        coleHopf 0 (Real.toNNReal (deriv ξ (qs 0) - deriv ξ (qExt qs 0)))
            (coleHopf (mExt ms 1)
              (Real.toNNReal (deriv ξ (qExt qs 2) - deriv ξ (qs 0)))
              (parisiQSuffix ξ h ms qs 0)) 0 = T₀ h := by
      simpa [vL₀, vR₀, mExt_zero] using congrFun htranslate₀ 0
    rw [ht, ht₀]
    exact (ha h).trans (half_lt_self hε)
  · have hrpos : 0 < r.val := Nat.pos_of_ne_zero hr
    have hTlip (a : α) : ∀ x y, |T a y - T a x| ≤ 1 * |y - x| := by
      dsimp [T]
      exact abs_coleHopf_sub_le_of_lipschitz _
        ((lipschitzWith_toNNReal_of_abs_sub_le
          (abs_coleHopf_sub_le_of_lipschitz _ hAm hAlip (vR a))).continuous.measurable)
        (abs_coleHopf_sub_le_of_lipschitz _ hAm hAlip (vR a)) (vL a)
    have hT₀lip : ∀ x y, |T₀ y - T₀ x| ≤ 1 * |y - x| := by
      dsimp [T₀]
      exact abs_coleHopf_sub_le_of_lipschitz _
        ((lipschitzWith_toNNReal_of_abs_sub_le
          (abs_coleHopf_sub_le_of_lipschitz _ hAm hAlip vR₀)).continuous.measurable)
        (abs_coleHopf_sub_le_of_lipschitz _ hAm hAlip vR₀) vL₀
    have hTm : Measurable (T a) :=
      (lipschitzWith_toNNReal_of_abs_sub_le (hTlip a)).continuous.measurable
    have hT₀m : Measurable T₀ :=
      (lipschitzWith_toNNReal_of_abs_sub_le hT₀lip).continuous.measurable
    have hpref : ∀ x,
        |coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
            (parisiQPrefixVars ξ qs r) (T a) x -
          coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
            (parisiQPrefixVars ξ qs r) T₀ x| ≤ ε / 2 :=
      abs_coleHopfIterate_sub_le_of_sup _ _ hTm (hTlip a) hT₀m hT₀lip
        (fun x => (ha x).le)
    unfold parisiX₀
    rw [parisiVar_qUpdate_before qs r (u a) hrpos,
      parisiVar_qUpdate_before qs r (qs r) hrpos]
    have hrec (a : α) (z₀ : ℝ) :
        parisiRecGauss ξ ms (qUpdate qs r (u a)) (parisiLogCoshTerminal h) z₀ =
          coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
            (parisiQPrefixVars ξ qs r) (T a) (h + z₀) := by
      rw [parisiRecGauss_qUpdate_eq_split qs r hm hrpos (u a) z₀,
        htranslate a, coleHopfIterate_translate]
    have hrec₀ (z₀ : ℝ) :
        parisiRecGauss ξ ms (qUpdate qs r (qs r)) (parisiLogCoshTerminal h) z₀ =
          coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
            (parisiQPrefixVars ξ qs r) T₀ (h + z₀) := by
      rw [parisiRecGauss_qUpdate_eq_split qs r hm hrpos (qs r) z₀,
        htranslate₀, coleHopfIterate_translate]
    have hUaLip := abs_coleHopfIterate_sub_le (r.val - 1)
      (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r) hTm (hTlip a)
    have hU₀Lip := abs_coleHopfIterate_sub_le (r.val - 1)
      (parisiQPrefixMasses ms r) (parisiQPrefixVars ξ qs r) hT₀m hT₀lip
    have hUaM :=
      (lipschitzWith_toNNReal_of_abs_sub_le hUaLip).continuous.measurable
    have hU₀M :=
      (lipschitzWith_toNNReal_of_abs_sub_le hU₀Lip).continuous.measurable
    have hUaI : Integrable (fun z₀ =>
        coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
          (parisiQPrefixVars ξ qs r) (T a) (h + z₀))
        (gaussianReal 0 (parisiVar ξ qs 0)) :=
      ((HasLinearGrowth.of_lipschitz hUaLip).comp_add_const h).toHasExpGrowth
        |>.integrable_gaussianReal
          (hUaM.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    have hU₀I : Integrable (fun z₀ =>
        coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
          (parisiQPrefixVars ξ qs r) T₀ (h + z₀))
        (gaussianReal 0 (parisiVar ξ qs 0)) :=
      ((HasLinearGrowth.of_lipschitz hU₀Lip).comp_add_const h).toHasExpGrowth
        |>.integrable_gaussianReal
          (hU₀M.comp (measurable_const.add measurable_id)).aestronglyMeasurable
    simp_rw [hrec, hrec₀]
    rw [← integral_sub hUaI hU₀I]
    have hbound : ‖∫ z₀,
        coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
            (parisiQPrefixVars ξ qs r) (T a) (h + z₀) -
          coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
            (parisiQPrefixVars ξ qs r) T₀ (h + z₀)
        ∂gaussianReal 0 (parisiVar ξ qs 0)‖ ≤ ε / 2 :=
      by
        have hb := norm_integral_le_of_norm_le_const
          (μ := gaussianReal 0 (parisiVar ξ qs 0))
          (f := fun z₀ =>
            coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
                (parisiQPrefixVars ξ qs r) (T a) (h + z₀) -
              coleHopfIterate (r.val - 1) (parisiQPrefixMasses ms r)
                (parisiQPrefixVars ξ qs r) T₀ (h + z₀))
          (C := ε / 2) (Filter.Eventually.of_forall fun z₀ => by
            simpa only [Real.norm_eq_abs] using hpref (h + z₀))
        simpa using hb
    rw [Real.norm_eq_abs] at hbound
    exact hbound.trans_lt (half_lt_self hε)

end

end SpinGlass
