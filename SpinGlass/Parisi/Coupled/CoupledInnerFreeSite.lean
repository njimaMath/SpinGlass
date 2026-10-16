import SpinGlass.Parisi.Coupled.CoupledInnerFreeAuxiliary

/-!
# The actual free inner-mass one-site recursion

The scalar array retains the old outer mass and varies only the inner mass.
Its Gaussian split is the concrete total law in the coupled comparison.
At zero coupling the paired recursion gives twice this actual scalar value.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

noncomputable def parisiInnerFreeTotalVars (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin k) (v : ℝ) : Fin (k + 2) → ℝ≥0 :=
  fun i => parisiResponseSplitVars ξ qs p.castSucc v (parisiSplitIndex p.castSucc i)

theorem parisiInnerFreeTotalVars_prefix (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin k) (v : ℝ) (r : Fin p.val) :
    parisiInnerFreeTotalVars ξ qs p v ⟨r.val, by omega⟩ = parisiMassPrefixVars ξ qs p r := by
  have he : parisiSplitIndex p.castSucc (⟨r.val, by omega⟩ : Fin (k + 2)) =
      Fin.castAdd ((k - p.val) + 1) r.castSucc := Fin.ext rfl
  unfold parisiInnerFreeTotalVars
  rw [he]
  unfold parisiResponseSplitVars
  simp only [Fin.val_castSucc, Fin.append_left, Fin.snoc_castSucc]
  rfl

theorem parisiInnerFreeTotalVars_outer (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin k) (v : ℝ) :
    parisiInnerFreeTotalVars ξ qs p v ⟨p.val, by omega⟩ =
      (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) - v).toNNReal := by
  have he : parisiSplitIndex p.castSucc (⟨p.val, by omega⟩ : Fin (k + 2)) =
      Fin.castAdd ((k - p.val) + 1) (Fin.last p.val) := Fin.ext rfl
  unfold parisiInnerFreeTotalVars
  rw [he]
  unfold parisiResponseSplitVars
  simp only [Fin.val_castSucc, Fin.append_left, Fin.snoc_last]
  have hq : qExt qs (p.val + 2) = qs p.succ := by
    change qExt qs (p.succ.val + 1) = _
    exact qExt_succ_of_lt qs p.succ.isLt
  rw [hq]

theorem parisiInnerFreeTotalVars_inner (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin k) (v : ℝ) :
    parisiInnerFreeTotalVars ξ qs p v (parisiInnerFreeMassIndex p) = v.toNNReal := by
  have he : parisiSplitIndex p.castSucc (parisiInnerFreeMassIndex p) =
      Fin.natAdd (p.val + 1) (0 : Fin ((k - p.val) + 1)) := Fin.ext (by simp [parisiInnerFreeMassIndex])
  unfold parisiInnerFreeTotalVars
  rw [he]
  unfold parisiResponseSplitVars
  simp only [Fin.val_castSucc, Fin.append_right, Fin.cons_zero]

theorem parisiInnerFreeTotalVars_suffix (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin k) (v : ℝ) (r : Fin (k - p.val)) :
    parisiInnerFreeTotalVars ξ qs p v ⟨p.val + r.val + 2, by omega⟩ =
      parisiQSuffixVars ξ qs p.castSucc r := by
  have he : parisiSplitIndex p.castSucc (⟨p.val + r.val + 2, by omega⟩ : Fin (k + 2)) =
      Fin.natAdd (p.val + 1) r.succ := Fin.ext (by simp; omega)
  unfold parisiInnerFreeTotalVars
  rw [he]
  unfold parisiResponseSplitVars
  simp only [Fin.val_castSucc, Fin.append_right, Fin.cons_succ]

/-- The full free-mass array is exactly the two split Cole-Hopf layers
with the original prefix and suffix. No mass ordering is required. -/
theorem coleHopfIterate_parisiInnerFree_eq_split (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (v b : ℝ) :
    coleHopfIterate (k + 2) (parisiLevelMasses (splitParisiMassRight ms p b))
      (parisiInnerFreeTotalVars ξ qs p v) (parisiLogCoshTerminal 0) =
      coleHopfIterate p.val (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p)
        (coleHopf (ms p) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) - v).toNNReal
          (coleHopf b v.toNNReal (parisiQSuffix ξ 0 ms qs p.castSucc))) := by
  rw [coleHopfIterate_split_two_of_eq p.val (k - p.val) (by omega)]
  congr 4
  · funext r
    rw [parisiLevelMasses_splitParisiMassRight_apply]
    dsimp only
    rw [ite_eq_left (by omega)]
    exact mExt_val_succ ms ⟨r.val, by omega⟩
  · funext r
    exact parisiInnerFreeTotalVars_prefix ξ qs p v r
  · rw [parisiLevelMasses_splitParisiMassRight_apply]
    dsimp only
    rw [ite_eq_left le_rfl]
    exact mExt_val_succ ms p
  · exact parisiInnerFreeTotalVars_outer ξ qs p v
  · rw [parisiLevelMasses_splitParisiMassRight_apply]
    dsimp only
    rw [ite_eq_right (by omega)]
    simp only [ite_true]
  · exact parisiInnerFreeTotalVars_inner ξ qs p v
  · funext r
    rw [parisiLevelMasses_splitParisiMassRight_apply]
    dsimp only
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rfl
  · funext r
    exact parisiInnerFreeTotalVars_suffix ξ qs p v r

/-- Half the zero-coupling value of the free inner split. -/
noncomputable def parisiInnerFreeZeroValue (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (v b : ℝ) : ℝ :=
  ∫ hz : ℝ × ℝ, coleHopfIterate p.val (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p)
    (coleHopf (ms p) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) - v).toNNReal
      (coleHopf b v.toNNReal (parisiQSuffix ξ 0 ms qs p.castSucc))) (hz.1 + hz.2)
    ∂μh.prod (gaussianReal 0 (parisiVar ξ qs 0))

noncomputable def parisiInnerFreeCouplingValue (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (v b lam : ℝ) : ℝ :=
  randomFieldPairSiteY₀ μh (parisiInnerFreeCoupledMasses ms p b) (parisiVar ξ qs 0)
    (parisiInnerFreeTotalVars ξ qs p v) lam (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))

/-- Every free inner mass gives an integrable actual scalar split
at an integrable shift, without exponential moments of the shift law. -/
theorem integrable_parisiInnerFreeSplit_comp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {H : Ω → ℝ}
    (hHm : Measurable H) (hH : Integrable H μ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (v b : ℝ) :
    Integrable (fun ω => coleHopfIterate p.val (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p)
      (coleHopf (ms p) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) - v).toNNReal
        (coleHopf b v.toNNReal (parisiQSuffix ξ 0 ms qs p.castSucc))) (H ω)) μ := by
  let A := parisiQSuffix ξ 0 ms qs p.castSucc
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiQSuffix_sub_le ξ 0 ms qs p.castSucc
  have hAm := (parisiQSuffix_spatial_regular_four ξ 0 ms qs p.castSucc).1.continuous.measurable
  have hB := abs_coleHopf_sub_le_of_lipschitz b hAm hL v.toNNReal
  have hC := abs_coleHopf_sub_le_of_lipschitz (ms p)
    (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable hB
    (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) - v).toNNReal
  let F := coleHopfIterate p.val (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p)
    (coleHopf (ms p) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) - v).toNNReal (coleHopf b v.toNNReal A))
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

/-- The actual free inner zero-coupling value is integrable under
the external-field/root product law with a finite first field moment. -/
theorem integrable_parisiInnerFreeSplit_externalField {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (v b : ℝ) :
    Integrable (fun hz : ℝ × ℝ =>
      coleHopfIterate p.val (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p)
        (coleHopf (ms p) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) - v).toNNReal
          (coleHopf b v.toNNReal (parisiQSuffix ξ 0 ms qs p.castSucc))) (hz.1 + hz.2))
      (μh.prod (gaussianReal 0 (parisiVar ξ qs 0))) := by
  have hz : Integrable id (gaussianReal 0 (parisiVar ξ qs 0)) := IsGaussian.integrable_id
  exact integrable_parisiInnerFreeSplit_comp (measurable_fst.add measurable_snd)
    ((hμ.comp_fst _).add (hz.comp_snd _)) ξ ms qs p v b

/-- The concrete paired recursion at zero coupling equals twice its
actual scalar free-mass value, including the probability field average. -/
theorem parisiInnerFreeCouplingValue_zero {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) {b : ℝ} (hb : 0 < b) (v : ℝ) :
    parisiInnerFreeCouplingValue μh ξ ms qs p v b 0 = 2 * parisiInnerFreeZeroValue μh ξ ms qs p v b := by
  have hpos := parisiLevelMasses_splitParisiMassRight_pos ms p hm hb
  have hzero (h : ℝ) : pairSiteY₀ (parisiInnerFreeCoupledMasses ms p b) (parisiVar ξ qs 0)
      (parisiInnerFreeTotalVars ξ qs p v) 0 (fun _ => h) (couplingFactorSgn 1 (p.val + 2) 0)
      (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) =
      2 * ∫ z, logCoshRec (k + 2) (parisiLevelMasses (splitParisiMassRight ms p b))
        (parisiInnerFreeTotalVars ξ qs p v) (h + z) ∂gaussianReal 0 (parisiVar ξ qs 0) := by
    have hz := pairSiteY₀_coupling_zero (parisiLevelMasses (splitParisiMassRight ms p b)) hpos
      (parisiVar ξ qs 0) (parisiInnerFreeTotalVars ξ qs p v) h (τ := p.val + 2) (by omega)
    simpa only [parisiInnerFreeCoupledMasses, show p.val + 2 - 1 = p.val + 1 by omega] using hz
  unfold parisiInnerFreeCouplingValue randomFieldPairSiteY₀
  simp_rw [hzero,
    logCoshRec_eq_coleHopfIterate_terminal_zero _ _ hpos,
    coleHopfIterate_parisiInnerFree_eq_split ξ ms qs p v b]
  rw [integral_const_mul]
  unfold parisiInnerFreeZeroValue
  congr 1
  exact (integral_prod _ (integrable_parisiInnerFreeSplit_externalField hμ ξ ms qs p v b)).symm

/-- The inserted-mass derivative of the actual zero-coupling value
is the concrete baseline-prefix U-response, not a supplied derivative. -/
theorem hasDerivAt_parisiInnerFreeZeroValue_matching {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (hm : ParisiMAdmissible ms)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) :
    HasDerivAt (parisiInnerFreeZeroValue μh ξ ms qs p v)
      (parisiRightU μh ξ ms qs p v / 2) (ms p) := by
  have hz : Integrable id (gaussianReal 0 (parisiVar ξ qs 0)) := IsGaussian.integrable_id
  have hd := hasDerivAt_integral_coleHopfIterate_split_mass_comp_of_pos
    (measurable_fst.add measurable_snd) ((hμ.comp_fst _).add (hz.comp_snd _))
    (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p)
    (fun r => hm.2.1 _) (fun r => (hm.2.2 _).le)
    (parisiQSuffix_spatial_regular_four ξ 0 ms qs p.castSucc).1.continuous.measurable
    (abs_parisiQSuffix_sub_le ξ 0 ms qs p.castSucc) (hm.2.1 p) (hm.2.2 p).le hv
  simp only [Pi.add_apply] at hd
  unfold parisiInnerFreeZeroValue parisiRightU
  convert! hd using 1
  ring

/-- At the matching mass the actual free scalar value is the
unchanged original Parisi root average, for every admissible variance split. -/
theorem parisiInnerFreeZeroValue_matching {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) :
    parisiInnerFreeZeroValue μh ξ ms qs p v (ms p) = ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  have hP : parisiOuterMassPrefixMasses ms p.castSucc = parisiMassPrefixMasses ms p := by
    funext i
    exact mExt_val_succ ms (⟨i.val, by omega⟩ : Fin k)
  have hV : parisiOuterMassPrefixVars ξ qs p.castSucc = parisiMassPrefixVars ξ qs p := rfl
  have hR : qExt qs (p.castSucc.val + 2) = qs p.succ := qExt_succ_of_lt qs p.succ.isLt
  have hmass : mExt ms (p.castSucc.val + 1) = ms p := mExt_val_succ ms p
  have hF := coleHopfIterate_parisiResponseSplit_eq_rootSuffix ξ ms qs p.castSucc (by
    simpa only [hR] using hv)
  unfold parisiResponseSplitMasses parisiResponseSplitVars at hF
  rw [coleHopfIterate_append, coleHopfIterate_snoc_eq, coleHopfIterate_succ] at hF
  simp only [Fin.cons_zero, Fin.tail_cons] at hF
  rw [hP, hV, hR, hmass] at hF
  change coleHopfIterate p.val (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p)
    (coleHopf (ms p) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) - v).toNNReal
      (coleHopf (ms p) v.toNNReal (parisiQSuffix ξ 0 ms qs p.castSucc))) = parisiRootSuffix ξ ms qs at hF
  have hi := integrable_parisiInnerFreeSplit_externalField hμ ξ ms qs p v (ms p)
  rw [hF] at hi
  unfold parisiInnerFreeZeroValue
  rw [hF]
  simp_rw [closedParisiX₀_translate, coleHopfIterate_succ]
  change (∫ hz : ℝ × ℝ, parisiRootSuffix ξ ms qs (hz.1 + hz.2)
    ∂μh.prod (gaussianReal 0 (parisiVar ξ qs 0))) =
      ∫ h, coleHopf 0 (parisiVar ξ qs 0) (parisiRootSuffix ξ ms qs) h ∂μh
  simp_rw [coleHopf_zero]
  exact integral_prod _ hi

end SpinGlass
