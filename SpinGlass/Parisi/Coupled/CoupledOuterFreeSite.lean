import SpinGlass.Parisi.Coupled.CoupledOuterFreeAuxiliary

/-!
# The actual free outer-mass one-site recursion

The scalar mass on the outer Gaussian piece may exceed one. Its
paired physical level carries half that mass. The actual scalar
recursion and its field-averaged matching derivative are explicit.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

noncomputable def parisiOuterFreeTotalVars (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (w : ℝ) : Fin (k + 2) → ℝ≥0 :=
  fun i => parisiResponseSplitVars ξ qs p
    (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w) (parisiSplitIndex p i)

theorem parisiOuterFreeTotalVars_prefix (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (w : ℝ) (r : Fin p.val) :
    parisiOuterFreeTotalVars ξ qs p w ⟨r.val, by omega⟩ = parisiOuterMassPrefixVars ξ qs p r := by
  have he : parisiSplitIndex p (⟨r.val, by omega⟩ : Fin (k + 2)) =
      Fin.castAdd ((k - p.val) + 1) r.castSucc := Fin.ext rfl
  unfold parisiOuterFreeTotalVars
  rw [he]
  simp only [parisiResponseSplitVars, Fin.append_left, Fin.snoc_castSucc]

theorem parisiOuterFreeTotalVars_outer (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (w : ℝ) :
    parisiOuterFreeTotalVars ξ qs p w p.castSucc = w.toNNReal := by
  have he : parisiSplitIndex p p.castSucc =
      Fin.castAdd ((k - p.val) + 1) (Fin.last p.val) := Fin.ext rfl
  unfold parisiOuterFreeTotalVars
  rw [he]
  simp only [parisiResponseSplitVars, Fin.append_left, Fin.snoc_last]
  congr 1
  ring

theorem parisiOuterFreeTotalVars_inner (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (w : ℝ) :
    parisiOuterFreeTotalVars ξ qs p w p.succ =
      (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w).toNNReal := by
  have he : parisiSplitIndex p p.succ =
      Fin.natAdd (p.val + 1) (0 : Fin ((k - p.val) + 1)) := Fin.ext (by simp)
  unfold parisiOuterFreeTotalVars
  rw [he]
  simp only [parisiResponseSplitVars, Fin.append_right, Fin.cons_zero]

theorem parisiOuterFreeTotalVars_suffix (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (w : ℝ) (r : Fin (k - p.val)) :
    parisiOuterFreeTotalVars ξ qs p w ⟨p.val + r.val + 2, by omega⟩ = parisiQSuffixVars ξ qs p r := by
  have he : parisiSplitIndex p (⟨p.val + r.val + 2, by omega⟩ : Fin (k + 2)) =
      Fin.natAdd (p.val + 1) r.succ := Fin.ext (by simp; omega)
  unfold parisiOuterFreeTotalVars
  rw [he]
  simp only [parisiResponseSplitVars, Fin.append_right, Fin.cons_succ]

theorem coleHopfIterate_parisiOuterFree_eq_split (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (w b : ℝ) :
    coleHopfIterate (k + 2) (parisiLevelMasses (splitParisiMassLeft ms p b))
      (parisiOuterFreeTotalVars ξ qs p w) (parisiLogCoshTerminal 0) =
      coleHopfIterate p.val (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
        (coleHopf b w.toNNReal (coleHopf (mExt ms (p.val + 1))
          (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w).toNNReal (parisiQSuffix ξ 0 ms qs p))) := by
  rw [coleHopfIterate_split_two_of_eq p.val (k - p.val) (by omega)]
  congr 1
  · funext r
    rw [parisiLevelMasses_splitParisiMassLeft_apply]
    dsimp only
    rw [ite_eq_left r.isLt]
    rfl
  · funext r
    exact parisiOuterFreeTotalVars_prefix ξ qs p w r
  · congr 1
    · rw [parisiLevelMasses_apply]
      exact mExt_splitParisiMassLeft_inserted ms p b
    · exact parisiOuterFreeTotalVars_outer ξ qs p w
    · congr 1
      · rw [parisiLevelMasses_apply]
        change mExt (splitParisiMassLeft ms p b) (p.val + 2) = mExt ms (p.val + 1)
        exact mExt_splitParisiMassLeft_after ms p b (by omega)
      · exact parisiOuterFreeTotalVars_inner ξ qs p w
      · unfold parisiQSuffix
        congr 1
        · funext r
          rw [parisiLevelMasses_splitParisiMassLeft_apply]
          dsimp only
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]
          rfl
        · funext r
          exact parisiOuterFreeTotalVars_suffix ξ qs p w r

noncomputable def parisiOuterFreeZeroValue (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (w b : ℝ) : ℝ :=
  ∫ hz : ℝ × ℝ, coleHopfIterate p.val (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
    (coleHopf b w.toNNReal (coleHopf (mExt ms (p.val + 1))
      (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w).toNNReal (parisiQSuffix ξ 0 ms qs p)))
    (hz.1 + hz.2) ∂μh.prod (gaussianReal 0 (parisiVar ξ qs 0))

noncomputable def parisiOuterFreeCouplingValue (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (w b lam : ℝ) : ℝ :=
  randomFieldPairSiteY₀ μh (parisiOuterFreeCoupledMasses ms p b) (parisiVar ξ qs 0)
    (parisiOuterFreeTotalVars ξ qs p w) lam (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))

/-- The actual scalar free outer split is integrable at every
integrable shift, without bounding its freely varied mass by one. -/
theorem integrable_parisiOuterFreeSplit_comp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {H : Ω → ℝ}
    (hHm : Measurable H) (hH : Integrable H μ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (w b : ℝ) :
    Integrable (fun ω => coleHopfIterate p.val (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
      (coleHopf b w.toNNReal (coleHopf (mExt ms (p.val + 1))
        (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w).toNNReal (parisiQSuffix ξ 0 ms qs p))) (H ω)) μ := by
  let A := parisiQSuffix ξ 0 ms qs p
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiQSuffix_sub_le ξ 0 ms qs p
  have hAm := (parisiQSuffix_spatial_regular_four ξ 0 ms qs p).1.continuous.measurable
  have hB := abs_coleHopf_sub_le_of_lipschitz (mExt ms (p.val + 1)) hAm hL
    (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w).toNNReal
  have hC := abs_coleHopf_sub_le_of_lipschitz b
    (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable hB w.toNNReal
  let F := coleHopfIterate p.val (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
    (coleHopf b w.toNNReal (coleHopf (mExt ms (p.val + 1))
      (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w).toNNReal A))
  have hF : ∀ x y, |F y - F x| ≤ 1 * |y - x| :=
    abs_coleHopfIterate_sub_le p.val _ _ (lipschitzWith_toNNReal_of_abs_sub_le hC).continuous.measurable hC
  apply ((integrable_const |F 0|).add hH.abs).mono'
    ((lipschitzWith_toNNReal_of_abs_sub_le hF).continuous.measurable.comp hHm).aestronglyMeasurable
  exact .of_forall fun ω => by
    change |F (H ω)| ≤ |F 0| + |H ω|
    have hh := hF 0 (H ω)
    have ha := abs_sub_abs_le_abs_sub (F (H ω)) (F 0)
    simp only [sub_zero, one_mul] at hh
    linarith

theorem integrable_parisiOuterFreeSplit_externalField {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (w b : ℝ) :
    Integrable (fun hz : ℝ × ℝ =>
      coleHopfIterate p.val (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
        (coleHopf b w.toNNReal (coleHopf (mExt ms (p.val + 1))
          (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w).toNNReal (parisiQSuffix ξ 0 ms qs p))) (hz.1 + hz.2))
      (μh.prod (gaussianReal 0 (parisiVar ξ qs 0))) := by
  have hz : Integrable id (gaussianReal 0 (parisiVar ξ qs 0)) := IsGaussian.integrable_id
  exact integrable_parisiOuterFreeSplit_comp (measurable_fst.add measurable_snd)
    ((hμ.comp_fst _).add (hz.comp_snd _)) ξ ms qs p w b

theorem hasDerivAt_parisiOuterFreeZeroValue_matching {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (hm : ParisiMAdmissible ms)
    {w : ℝ} (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) :
    HasDerivAt (parisiOuterFreeZeroValue μh ξ ms qs p w) (parisiLeftU μh ξ ms qs p w / 2)
      (mExt ms (p.val + 1)) := by
  have hz : Integrable id (gaussianReal 0 (parisiVar ξ qs 0)) := IsGaussian.integrable_id
  have hd := hasDerivAt_integral_coleHopfIterate_outer_split_mass_comp
    (measurable_fst.add measurable_snd) ((hμ.comp_fst _).add (hz.comp_snd _))
    (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
    (fun r => hm.mExt_pos (by omega)) (fun r => mExt_le_one (fun i => (hm.2.2 i).le) _)
    (parisiQSuffix_spatial_regular_four ξ 0 ms qs p).1.continuous.measurable
    (abs_parisiQSuffix_sub_le ξ 0 ms qs p)
    ⟨(hm.mExt_pos (by omega : 0 < p.val + 1)).le, mExt_le_one (fun i => (hm.2.2 i).le) _⟩ hw
  simp only [Pi.add_apply] at hd
  unfold parisiOuterFreeZeroValue parisiLeftU
  convert! hd using 1
  ring

/-- The actual paired zero-coupling value is twice the scalar
free outer split, including masses above one and the field average. -/
theorem parisiOuterFreeCouplingValue_zero {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (hm : ParisiMAdmissible ms)
    {b : ℝ} (hb : 0 < b) (w : ℝ) :
    parisiOuterFreeCouplingValue μh ξ ms qs p w b 0 = 2 * parisiOuterFreeZeroValue μh ξ ms qs p w b := by
  have hpos := parisiLevelMasses_splitParisiMassLeft_pos ms p hm hb
  have hzero (h : ℝ) : pairSiteY₀ (parisiOuterFreeCoupledMasses ms p b)
      (parisiVar ξ qs 0) (parisiOuterFreeTotalVars ξ qs p w) 0 (fun _ => h)
      (couplingFactorSgn 1 (p.val + 2) 0) (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) =
      2 * ∫ z, logCoshRec (k + 2) (parisiLevelMasses (splitParisiMassLeft ms p b))
        (parisiOuterFreeTotalVars ξ qs p w) (h + z) ∂gaussianReal 0 (parisiVar ξ qs 0) := by
    rw [parisiOuterFreeCoupledMasses_eq_halveBelow]
    have hz := pairSiteY₀_coupling_zero (parisiLevelMasses (splitParisiMassLeft ms p b)) hpos
      (parisiVar ξ qs 0) (parisiOuterFreeTotalVars ξ qs p w) h (τ := p.val + 2) (by omega)
    simpa only [show p.val + 2 - 1 = p.val + 1 by omega] using hz
  unfold parisiOuterFreeCouplingValue randomFieldPairSiteY₀
  simp_rw [hzero, logCoshRec_eq_coleHopfIterate_terminal_zero _ _ hpos,
    coleHopfIterate_parisiOuterFree_eq_split ξ ms qs p w b]
  rw [integral_const_mul]
  unfold parisiOuterFreeZeroValue
  congr 1
  exact (integral_prod _ (integrable_parisiOuterFreeSplit_externalField hμ ξ ms qs p w b)).symm

theorem parisiOuterFreeZeroValue_matching {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    {w : ℝ} (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) :
    parisiOuterFreeZeroValue μh ξ ms qs p w (mExt ms (p.val + 1)) = ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  let a := deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p)
  have hv : a - w ∈ Icc (0 : ℝ) a := ⟨sub_nonneg.2 hw.2, sub_le_self _ hw.1⟩
  have hF := coleHopfIterate_parisiResponseSplit_eq_rootSuffix ξ ms qs p hv
  unfold parisiResponseSplitMasses parisiResponseSplitVars at hF
  rw [coleHopfIterate_append, coleHopfIterate_snoc_eq, coleHopfIterate_succ] at hF
  simp only [Fin.cons_zero, Fin.tail_cons] at hF
  change coleHopfIterate p.val (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
    (coleHopf (mExt ms (p.val + 1)) (a - (a - w)).toNNReal
      (coleHopf (mExt ms (p.val + 1)) (a - w).toNNReal (parisiQSuffix ξ 0 ms qs p))) = parisiRootSuffix ξ ms qs at hF
  rw [show a - (a - w) = w by ring] at hF
  have hi := integrable_parisiOuterFreeSplit_externalField hμ ξ ms qs p w (mExt ms (p.val + 1))
  rw [hF] at hi
  unfold parisiOuterFreeZeroValue
  rw [hF]
  simp_rw [closedParisiX₀_translate, coleHopfIterate_succ]
  change (∫ hz : ℝ × ℝ, parisiRootSuffix ξ ms qs (hz.1 + hz.2)
    ∂μh.prod (gaussianReal 0 (parisiVar ξ qs 0))) =
      ∫ h, coleHopf 0 (parisiVar ξ qs 0) (parisiRootSuffix ξ ms qs) h ∂μh
  simp_rw [coleHopf_zero]
  exact integral_prod _ hi

end SpinGlass
