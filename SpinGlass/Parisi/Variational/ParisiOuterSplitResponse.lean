import SpinGlass.Parisi.Variational.ParisiSplitResponse
import SpinGlass.Parisi.Variational.ParisiOuterMassResponse

/-!
# The actual outer-mass Parisi split

The mirror cases of Section 14.9 vary the outer mass of an interval whose
right mass stays fixed. The formulas here identify the closed split arrays
with their concrete prefix, matched Cole-Hopf layers and suffix. The terminal
old mass one is retained, as are the field and independent root averages.
-/

open MeasureTheory ProbabilityTheory Set
open Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

/-- Positive-mass layers before an outer split, including a terminal split. -/
def parisiOuterMassPrefixMasses {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1)) :
    Fin p.val → ℝ := fun r => mExt ms (r.val + 1)

/-- The unchanged Gaussian variances before the outer split. -/
noncomputable def parisiOuterMassPrefixVars (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) : Fin p.val → ℝ≥0 :=
  fun r => parisiVar ξ qs (r.val + 1)

/-- Masses preceding the outer insertion keep their extended coordinates. -/
theorem mExt_splitParisiMassLeft_before {k : ℕ}
    (ms : Fin k → ℝ) (p : Fin (k + 1)) (m : ℝ) {r : ℕ} (hr : r ≤ p.val) :
    mExt (splitParisiMassLeft ms p m) r = mExt ms r := by
  have he := mExt_eraseParisiMass (splitParisiMassLeft ms p m) p r
  rw [erase_splitParisiMassLeft, ite_eq_left hr] at he
  exact he.symm

/-- Masses following the outer insertion shift by one extended coordinate. -/
theorem mExt_splitParisiMassLeft_after {k : ℕ}
    (ms : Fin k → ℝ) (p : Fin (k + 1)) (m : ℝ) {r : ℕ} (hr : p.val < r) :
    mExt (splitParisiMassLeft ms p m) (r + 1) = mExt ms r := by
  have he := mExt_eraseParisiMass (splitParisiMassLeft ms p m) p r
  rw [erase_splitParisiMassLeft, ite_eq_right (by omega)] at he
  exact he.symm

/-- The newly inserted outer mass is the freely varied coordinate. -/
theorem mExt_splitParisiMassLeft_inserted {k : ℕ}
    (ms : Fin k → ℝ) (p : Fin (k + 1)) (m : ℝ) :
    mExt (splitParisiMassLeft ms p m) (p.val + 1) = m := by
  rw [mExt_val_succ _ p]
  exact Fin.insertNth_apply_same _ _ _

/-- The actual outer split recursion: a varied mass acts on the left piece
and the old mass acts on the right piece. This includes p=0, the terminal
interval, and arbitrary closed overlap endpoints. -/
theorem closedParisiX₀_split_left_eq (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (m u h : ℝ) :
    closedParisiX₀ ξ (splitParisiMassLeft ms p m) (splitParisiOverlap qs p u) h =
      ∫ z₀, coleHopfIterate p.val (parisiOuterMassPrefixMasses ms p)
        (parisiOuterMassPrefixVars ξ qs p)
        (coleHopf m (deriv ξ u - deriv ξ (qs p)).toNNReal
          (coleHopf (mExt ms (p.val + 1))
            (deriv ξ (qExt qs (p.val + 2)) - deriv ξ u).toNNReal
            (parisiQSuffix ξ 0 ms qs p))) (h + z₀)
        ∂gaussianReal 0 (parisiVar ξ qs 0) := by
  have hn : k + 2 = p.val + (2 + (k - p.val)) := by omega
  have hi : coleHopfIterate (k + 2) (parisiLevelMasses (splitParisiMassLeft ms p m))
      (parisiLevelVars ξ (splitParisiOverlap qs p u)) (parisiLogCoshTerminal 0) =
      coleHopfIterate p.val (parisiOuterMassPrefixMasses ms p)
        (parisiOuterMassPrefixVars ξ qs p)
        (coleHopf m (deriv ξ u - deriv ξ (qs p)).toNNReal
          (coleHopf (mExt ms (p.val + 1))
            (deriv ξ (qExt qs (p.val + 2)) - deriv ξ u).toNNReal
            (parisiQSuffix ξ 0 ms qs p))) := by
    rw [coleHopfIterate_split_two_of_eq p.val (k - p.val) hn]
    congr 1
    · funext r
      rw [parisiLevelMasses_apply]
      change mExt (splitParisiMassLeft ms p m) (r.val + 1) = mExt ms (r.val + 1)
      exact mExt_splitParisiMassLeft_before ms p m (by omega)
    · funext r
      unfold parisiLevelVars parisiOuterMassPrefixVars
      change parisiVar ξ (splitParisiOverlap qs p u) (r.val + 1) = parisiVar ξ qs (r.val + 1)
      exact parisiVar_splitParisiOverlap_before ξ qs p u (by omega)
    · congr 1
      · rw [parisiLevelMasses_apply]
        exact mExt_splitParisiMassLeft_inserted ms p m
      · unfold parisiLevelVars
        exact parisiVar_splitParisiOverlap_left ξ qs p u
      · congr 1
        · rw [parisiLevelMasses_apply]
          change mExt (splitParisiMassLeft ms p m) (p.val + 2) = mExt ms (p.val + 1)
          exact mExt_splitParisiMassLeft_after ms p m (by omega)
        · unfold parisiLevelVars
          exact parisiVar_splitParisiOverlap_right ξ qs p u
        · unfold parisiQSuffix
          congr 1
          · funext r
            rw [parisiLevelMasses_apply]
            change mExt (splitParisiMassLeft ms p m) (p.val + r.val + 2 + 1) =
              mExt ms (p.val + r.val + 2)
            exact mExt_splitParisiMassLeft_after ms p m (by omega)
          · funext r
            unfold parisiLevelVars parisiQSuffixVars
            change parisiVar ξ (splitParisiOverlap qs p u) (p.val + r.val + 2 + 1) =
              parisiVar ξ qs (p.val + r.val + 2)
            exact parisiVar_splitParisiOverlap_after ξ qs p u (by omega)
  rw [closedParisiX₀_translate, coleHopfIterate_succ]
  change coleHopf 0 (parisiVar ξ (splitParisiOverlap qs p u) 0)
    (coleHopfIterate (k + 2) (parisiLevelMasses (splitParisiMassLeft ms p m))
      (parisiLevelVars ξ (splitParisiOverlap qs p u)) (parisiLogCoshTerminal 0)) h = _
  rw [hi, parisiVar_splitParisiOverlap_before ξ qs p u (by omega), coleHopf_zero]

/-- The actual outer U, averaged under the independent field/root product
law and the unchanged unsplit prefix. -/
noncomputable def parisiLeftU (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (w : ℝ) : ℝ :=
  2 * ∫ hz : ℝ × ℝ, coleHopfIterateOuterSplitMassResponse
    (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
    (mExt ms (p.val + 1)) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))
    (parisiQSuffix ξ 0 ms qs p) (hz.1 + hz.2) w
    ∂μh.prod (gaussianReal 0 (parisiVar ξ qs 0))

/-- Concrete moments governing the first two variance derivatives of outer U. -/
noncomputable def parisiLeftUSpatialMoment (s : ℕ) (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (w : ℝ) : ℝ :=
  ∫ hz : ℝ × ℝ, coleHopfIterateOuterSplitSpatialMoment s
    (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
    (mExt ms (p.val + 1)) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))
    (parisiQSuffix ξ 0 ms qs p) (hz.1 + hz.2) w
    ∂μh.prod (gaussianReal 0 (parisiVar ξ qs 0))

/-- The outer variance coordinate maps the closed overlap interval into its
admissible variance interval, without crossing a clamped zero variance. -/
theorem mapsTo_parisi_outer_variance_coordinate {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {qL qR : ℝ} (hL : qL ∈ Icc (0 : ℝ) 1) (hR : qR ∈ Icc (0 : ℝ) 1) :
    MapsTo (fun u => deriv ξ u - deriv ξ qL) (Icc qL qR)
      (Icc (0 : ℝ) (deriv ξ qR - deriv ξ qL)) := by
  intro u hu
  have humem : u ∈ Icc (0 : ℝ) 1 := ⟨hL.1.trans hu.1, hu.2.trans hR.2⟩
  exact ⟨sub_nonneg.2 (hξ.strictMonoOn_deriv.monotoneOn hL humem hu.1),
    sub_le_sub_right (hξ.strictMonoOn_deriv.monotoneOn humem hR hu.2) _⟩

private theorem integrable_outer_one_lipschitz_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hHm : Measurable H) (hH : Integrable H μ)
    {A : ℝ → ℝ} (hLip : ∀ x y, |A y - A x| ≤ |y - x|) :
    Integrable (fun ω => A (H ω)) μ := by
  have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  refine ((integrable_const |A 0|).add hH.abs).mono'
    ((lipschitzWith_toNNReal_of_abs_sub_le hL).continuous.measurable.comp hHm).aestronglyMeasurable
    (.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  have hb := hLip 0 (H ω)
  have ha := abs_sub_abs_le_abs_sub (A (H ω)) (A 0)
  simp only [Pi.add_apply, sub_zero] at hb ⊢
  linarith

/-- Differentiate the actual outer split after the field and independent
root average. Only a finite first field moment is used; the terminal old mass
one is differentiated in its genuine mass neighborhood. -/
theorem hasDerivAt_integral_closedParisiX₀_split_left_mass
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {u : ℝ}
    (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    HasDerivAt
      (fun b => ∫ h, closedParisiX₀ ξ (splitParisiMassLeft ms p b)
        (splitParisiOverlap qs p u) h ∂μh)
      (parisiLeftU μh ξ ms qs p (deriv ξ u - deriv ξ (qs p)) / 2)
      (mExt ms (p.val + 1)) := by
  let μ := μh.prod (gaussianReal 0 (parisiVar ξ qs 0))
  let H : ℝ × ℝ → ℝ := fun hz => hz.1 + hz.2
  let a := deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p)
  let w := deriv ξ u - deriv ξ (qs p)
  let m := mExt ms (p.val + 1)
  have hHm : Measurable H := measurable_fst.add measurable_snd
  have hzg : HasLinearGrowth id := ⟨0, 1, zero_le_one, by simp⟩
  have hz : Integrable id (gaussianReal 0 (parisiVar ξ qs 0)) :=
    hzg.toHasExpGrowth.integrable_gaussianReal measurable_id.aestronglyMeasurable
  have hH : Integrable H μ := (hμ.comp_fst _).add (hz.comp_snd _)
  have hpos : ∀ r, 0 < parisiOuterMassPrefixMasses ms p r :=
    fun r => hm.mExt_pos (by omega)
  have hle : ∀ r, parisiOuterMassPrefixMasses ms p r ≤ 1 :=
    fun r => mExt_le_one (fun i => (hm.2.2 i).le) _
  have hA := (parisiQSuffix_spatial_regular_four ξ 0 ms qs p).1
  have hLip := abs_parisiQSuffix_sub_le ξ 0 ms qs p
  have hw : w ∈ Icc (0 : ℝ) a := mapsTo_parisi_outer_variance_coordinate hξ
    (hq.mem_Icc p) (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _) hu
  have hmass : m ∈ Icc (0 : ℝ) 1 :=
    ⟨(hm.mExt_pos (by omega)).le, mExt_le_one (fun i => (hm.2.2 i).le) _⟩
  have hd := hasDerivAt_integral_coleHopfIterate_outer_split_mass_comp hHm hH
    (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p) hpos hle
    hA.continuous.measurable hLip hmass hw
  have hright : a - w = deriv ξ (qExt qs (p.val + 2)) - deriv ξ u := by
    dsimp [a, w]
    ring
  rw [hright] at hd
  let F : ℝ → ℝ → ℝ := fun b => coleHopfIterate p.val
    (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
    (coleHopf b w.toNNReal
      (coleHopf m (deriv ξ (qExt qs (p.val + 2)) - deriv ξ u).toNNReal
        (parisiQSuffix ξ 0 ms qs p)))
  have hF : ∀ b, Integrable (fun hz => F b (H hz)) μ := by
    intro b
    have hL : ∀ x y, |parisiQSuffix ξ 0 ms qs p y - parisiQSuffix ξ 0 ms qs p x| ≤
        1 * |y - x| := by simpa only [one_mul] using hLip
    have hB := abs_coleHopf_sub_le_of_lipschitz m hA.continuous.measurable hL
      (deriv ξ (qExt qs (p.val + 2)) - deriv ξ u).toNNReal
    have hC := abs_coleHopf_sub_le_of_lipschitz b
      (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable hB w.toNNReal
    apply integrable_outer_one_lipschitz_comp hHm hH
    simpa only [one_mul] using abs_coleHopfIterate_sub_le p.val
      (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
      (lipschitzWith_toNNReal_of_abs_sub_le hC).continuous.measurable hC
  have he : (fun b => ∫ h, closedParisiX₀ ξ (splitParisiMassLeft ms p b)
      (splitParisiOverlap qs p u) h ∂μh) = fun b => ∫ hz, F b (H hz) ∂μ := by
    funext b
    simp only [closedParisiX₀_split_left_eq]
    exact (integral_prod (fun hz => F b (H hz)) (hF b)).symm
  rw [he]
  convert hd using 1
  dsimp [parisiLeftU, μ, H, a, w, m]
  ring

/-- The inserted outer-mass derivative is half the actual U minus its left
theta correction, including the terminal matching mass one. -/
theorem splitParisiLeftMassDeriv_eq_U
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {u : ℝ}
    (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    splitParisiLeftMassDeriv μh ξ ms qs p u (mExt ms (p.val + 1)) =
      (1 / 2) * (parisiLeftU μh ξ ms qs p (deriv ξ u - deriv ξ (qs p)) -
        (parisiTheta ξ u - parisiTheta ξ (qs p))) := by
  have hpref (i : Fin p.val) :
      splitParisiMassLeft ms p 0 ⟨i.val, by omega⟩ = ms ⟨i.val, by omega⟩ :=
    splitParisiMassLeft_apply_of_lt ms p 0 i.isLt
  have hmp : mExt ms (p.val + 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨(hm.mExt_pos (by omega)).le, mExt_le_one (fun i => (hm.2.2 i).le) _⟩
  have hold := hasDerivWithinAt_randomFieldParisiX₀_mass_update hμ ξ
    (splitParisiMassLeft ms p 0) (splitParisiOverlap qs p u) p
    (fun i => by rw [hpref i]; exact hm.2.1 _)
    (fun i => by rw [hpref i]; exact (hm.2.2 _).le) hmp
  simp only [update_splitParisiMassLeft] at hold
  have hnew := hasDerivAt_integral_closedParisiX₀_split_left_mass hμ hξ ms qs p hm hq hu
  have hM := (hold.derivWithin (uniqueDiffOn_Icc_zero_one _ hmp)).symm.trans
    (hnew.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one _ hmp))
  have hqu : qExt (splitParisiOverlap qs p u) (p.val + 2) = u :=
    qExt_splitParisiOverlap_inserted qs p u
  have hql : qExt (splitParisiOverlap qs p u) (p.val + 1) = qs p := by
    rw [qExt_splitParisiOverlap_before qs p u (by omega)]
    exact qExt_succ_of_lt qs p.isLt
  unfold splitParisiLeftMassDeriv
  rw [hM, hqu, hql]
  ring

/-- The mirror f is twice the actual inserted-mass functional derivative. -/
noncomputable def parisiLeftf (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (u : ℝ) : ℝ :=
  parisiLeftU μh ξ ms qs p (deriv ξ u - deriv ξ (qs p)) -
    (parisiTheta ξ u - parisiTheta ξ (qs p))

/-- Concrete mirror U/f identity for the functional, as used in Section
14.9, with both one-sided mass endpoints in the unchanged domain. -/
theorem hasDerivWithinAt_closedRandomFieldParisiFunctional_split_left_mass_eq_f
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {u : ℝ}
    (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    HasDerivWithinAt
      (fun b => closedRandomFieldParisiFunctional μh ξ
        (splitParisiMassLeft ms p b) (splitParisiOverlap qs p u))
      ((1 / 2) * parisiLeftf μh ξ ms qs p u) (Icc (0 : ℝ) 1)
      (mExt ms (p.val + 1)) := by
  rw [show (1 / 2) * parisiLeftf μh ξ ms qs p u =
    splitParisiLeftMassDeriv μh ξ ms qs p u (mExt ms (p.val + 1)) from
      (splitParisiLeftMassDeriv_eq_U hμ hξ ms qs p hm hq hu).symm]
  exact hasDerivWithinAt_closedRandomFieldParisiFunctional_split_left_mass hμ ξ ms qs
    hm.2.1 (fun i => (hm.2.2 i).le) p u
    ⟨(hm.mExt_pos (by omega)).le, mExt_le_one (fun i => (hm.2.2 i).le) _⟩

/-- The outer U vanishes at an empty left piece, before any minimization. -/
theorem parisiLeftU_zero (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) :
    parisiLeftU μh ξ ms qs p 0 = 0 := by
  simp only [parisiLeftU, coleHopfIterateOuterSplitMassResponse_zero, integral_zero, mul_zero]

/-- The left overlap endpoint has f=0 for the actual outer split. -/
theorem parisiLeftf_left_endpoint (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) :
    parisiLeftf μh ξ ms qs p (qs p) = 0 := by
  simp only [parisiLeftf, sub_self, parisiLeftU_zero]

/-- The outer U derivative is its actual transported gradient moment. The
interval hypothesis includes the terminal interval whenever its left overlap
is strictly below one; both variance endpoints are treated one-sidedly. -/
theorem hasDerivWithinAt_parisiLeftU
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hgap : qs p < qExt qs (p.val + 2)) {w : ℝ}
    (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) :
    HasDerivWithinAt (parisiLeftU μh ξ ms qs p)
      (parisiLeftUSpatialMoment 1 μh ξ ms qs p w)
      (Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) w := by
  have hHm : Measurable (fun hz : ℝ × ℝ => hz.1 + hz.2) := measurable_fst.add measurable_snd
  have ha : 0 < deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) := sub_pos.2
    (hξ.strictMonoOn_deriv (hq.mem_Icc p)
      (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _) hgap)
  have hd := hasDerivWithinAt_integral_parisiQSuffix_prefixOuterSplitMassResponse_comp
    (μ := μh.prod (gaussianReal 0 (parisiVar ξ qs 0))) hHm
    (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
    (fun r => hm.mExt_pos (by omega))
    (fun r => mExt_le_one (fun i => (hm.2.2 i).le) _) ξ 0 ms qs p
    (hm.mExt_pos (by omega : 0 < p.val + 1))
    (mExt_le_one (fun i => (hm.2.2 i).le) _) ha hw
  unfold parisiLeftU parisiLeftUSpatialMoment
  convert hd.const_mul 2 using 1
  all_goals first | rfl | ring

/-- The outer U has positive curvature equal to its concrete second spatial
moment, after every prefix, field and independent root average. -/
theorem hasDerivWithinAt_parisiLeftUSpatialMoment_one
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hgap : qs p < qExt qs (p.val + 2)) {w : ℝ}
    (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) :
    HasDerivWithinAt (parisiLeftUSpatialMoment 1 μh ξ ms qs p)
      (parisiLeftUSpatialMoment 2 μh ξ ms qs p w)
      (Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) w := by
  have hHm : Measurable (fun hz : ℝ × ℝ => hz.1 + hz.2) := measurable_fst.add measurable_snd
  have ha : 0 < deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) := sub_pos.2
    (hξ.strictMonoOn_deriv (hq.mem_Icc p)
      (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _) hgap)
  unfold parisiLeftUSpatialMoment
  exact hasDerivWithinAt_integral_parisiQSuffix_prefixOuterSplitSpatialMoment_comp
    (μ := μh.prod (gaussianReal 0 (parisiVar ξ qs 0))) hHm
    (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
    (fun r => hm.mExt_pos (by omega))
    (fun r => mExt_le_one (fun i => (hm.2.2 i).le) _) ξ 0 ms qs p
    (hm.mExt_pos (by omega : 0 < p.val + 1))
    (mExt_le_one (fun i => (hm.2.2 i).le) _) ha hw

/-- Convexity of the actual outer U, including a zero terminal interval. -/
theorem convexOn_parisiLeftU
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) :
    ConvexOn ℝ (Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p)))
      (parisiLeftU μh ξ ms qs p) := by
  have hHm : Measurable (fun hz : ℝ × ℝ => hz.1 + hz.2) := measurable_fst.add measurable_snd
  have horder : qs p ≤ qExt qs (p.val + 2) := by
    have hh := qExt_le_succ hq.monotone hq.2.1 hq.2.2 (by omega : p.val + 1 ≤ k + 1)
    simpa only [qExt_succ_of_lt qs p.isLt] using hh
  have ha : 0 ≤ deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) := sub_nonneg.2
    (hξ.strictMonoOn_deriv.monotoneOn (hq.mem_Icc p)
      (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _) horder)
  have hc := convexOn_integral_parisiQSuffix_prefixOuterSplitMassResponse_comp
    (μ := μh.prod (gaussianReal 0 (parisiVar ξ qs 0))) hHm
    (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
    (fun r => hm.mExt_pos (by omega))
    (fun r => mExt_le_one (fun i => (hm.2.2 i).le) _) ξ 0 ms qs p
    (hm.mExt_pos (by omega : 0 < p.val + 1))
    (mExt_le_one (fun i => (hm.2.2 i).le) _) ha
  unfold parisiLeftU
  simpa only [smul_eq_mul] using ConvexOn.smul (c := (2 : ℝ)) (by norm_num) hc

/-- The actual mirror f derivative on its closed overlap interval. Its
moment and every differentiation under a field or Gaussian integral have
already been obtained from the recursion. -/
theorem hasDerivWithinAt_parisiLeftf
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hgap : qs p < qExt qs (p.val + 2)) {u : ℝ}
    (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    HasDerivWithinAt (parisiLeftf μh ξ ms qs p)
      (deriv (deriv ξ) u * (parisiLeftUSpatialMoment 1 μh ξ ms qs p
        (deriv ξ u - deriv ξ (qs p)) - u)) (Icc (qs p) (qExt qs (p.val + 2))) u := by
  have hR := qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (p.val + 2)
  have humem : u ∈ Icc (0 : ℝ) 1 := ⟨(hq.mem_Icc p).1.trans hu.1, hu.2.trans hR.2⟩
  have hmaps := mapsTo_parisi_outer_variance_coordinate hξ (hq.mem_Icc p) hR
  have hdw := (hξ.hasDeriv_deriv u humem).sub_const (deriv ξ (qs p))
  have hU := (hasDerivWithinAt_parisiLeftU (μh := μh) hξ ms qs p hm hq hgap (hmaps hu)).comp u
    hdw.hasDerivWithinAt hmaps
  have hθ := (hasDerivAt_parisiTheta (hξ.hasDeriv u humem)
    (hξ.hasDeriv_deriv u humem)).sub_const (parisiTheta ξ (qs p))
  unfold parisiLeftf
  convert hU.sub hθ.hasDerivWithinAt using 1
  all_goals first | rfl | ring

end SpinGlass
