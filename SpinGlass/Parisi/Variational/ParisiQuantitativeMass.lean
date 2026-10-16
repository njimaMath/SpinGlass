import SpinGlass.Parisi.Analytic.Variation
import SpinGlass.Parisi.Variational.ParisiSplitResponse
import SpinGlass.Parisi.Variational.ParisiMassPropagation
import SpinGlass.Parisi.Variational.ParisiOuterSplitResponse

/-!
# Quantitative inserted-mass variation

The constants below are selected before the MIN parameters. The initial
interval has a plain Gaussian prefix, so averaging the single-layer mass
remainder gives a constant independent of the level count and the site law.
The upper-mass endpoint comparison handles short admissible mass intervals
in Talagrand, Vol. II, (14.264).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

private lemma integrable_one_lipschitz_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {H : Ω → ℝ} (hHm : Measurable H) (hH : Integrable H μ)
    {A : ℝ → ℝ} (hLip : ∀ x y, |A y - A x| ≤ 1 * |y - x|) :
    Integrable (fun ω => A (H ω)) μ := by
  refine ((integrable_const |A 0|).add hH.abs).mono'
    ((lipschitzWith_toNNReal_of_abs_sub_le hLip).continuous.measurable.comp
      hHm).aestronglyMeasurable (.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  have hl := hLip 0 (H ω)
  have ha := abs_sub_abs_le_abs_sub (A (H ω)) (A 0)
  simp only [Pi.add_apply, one_mul, sub_zero] at hl ⊢
  linarith

/-- The actual root mass functional has a uniform quadratic remainder.
The coefficient depends only on ξ, through its total variance ceiling.
It is independent of k, all masses and overlaps, u, and the field law.
Only a finite first field moment is needed for this component of (14.264). -/
theorem exists_uniform_splitParisiRoot_mass_taylor_bound
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) :
    ∃ M : ℝ, 0 < M ∧ ∀ {μh : Measure ℝ} [IsProbabilityMeasure μh],
      Integrable id μh → ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      qs ∈ parisiOverlapDomain k → ∀ u : ℝ, 0 ≤ u ∧ u ≤ qs 0 →
      ∀ b ∈ Icc (0 : ℝ) 1,
        |closedRandomFieldParisiFunctional μh ξ
            (splitParisiRootMass ms b) (splitParisiRootOverlap qs u) -
          closedRandomFieldParisiFunctional μh ξ
            (splitParisiRootMass ms 0) (splitParisiRootOverlap qs u) -
          b * ((1 / 2) * parisiRootf μh ξ ms qs u)| ≤ M * b ^ 2 := by
  let V : ℝ≥0 := (deriv ξ 1 - deriv ξ 0).toNNReal
  obtain ⟨M, hM, hTaylor⟩ := exists_uniform_integral_coleHopf_mass_taylor_bound V
  refine ⟨M, hM, ?_⟩
  intro μh _ hμ k ms qs hq u hu b hb
  obtain ⟨hmono, hq0, hq1⟩ := mem_parisiOverlapDomain_iff.1 hq
  have hqmem : qs 0 ∈ Icc (0 : ℝ) 1 :=
    ⟨hq0, (hmono (Fin.zero_le _)).trans hq1⟩
  have humem : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans hqmem.2⟩
  let v : ℝ≥0 := (deriv ξ (qs 0) - deriv ξ u).toNNReal
  let v₀ : ℝ≥0 := (deriv ξ u - deriv ξ 0).toNNReal
  have hv : v ≤ V := Real.toNNReal_le_toNNReal (sub_le_sub
    (hξ.strictMonoOn_deriv.monotoneOn hqmem ⟨zero_le_one, le_rfl⟩ hqmem.2)
    (hξ.strictMonoOn_deriv.monotoneOn ⟨le_rfl, zero_le_one⟩ humem hu.1))
  let μ := μh.prod (gaussianReal 0 v₀)
  let H : ℝ × ℝ → ℝ := fun p => p.1 + p.2
  let A := parisiRootSuffix ξ ms qs
  have hHm : Measurable H := measurable_fst.add measurable_snd
  have hzg : HasLinearGrowth id := ⟨0, 1, zero_le_one, by simp⟩
  have hz : Integrable id (gaussianReal 0 v₀) :=
    hzg.toHasExpGrowth.integrable_gaussianReal measurable_id.aestronglyMeasurable
  have hH : Integrable H μ := (hμ.comp_fst _).add (hz.comp_snd _)
  have hLip : ∀ x y, |A y - A x| ≤ |y - x| := abs_parisiRootSuffix_sub_le ξ ms qs
  have hLip' : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  have hAm := (lipschitzWith_toNNReal_of_abs_sub_le hLip').continuous.measurable
  have hF : ∀ c, Integrable (fun p => coleHopf c v A (H p)) μ :=
    fun c => integrable_one_lipschitz_comp hHm hH
      (abs_coleHopf_sub_le_of_lipschitz c hAm hLip' v)
  let sqs := splitParisiRootOverlap qs u
  let sms := splitParisiRootMass ms 0
  let C := ∑ p ∈ (Finset.range (k + 2)).erase 0, mExt sms (p + 1) *
    (parisiTheta ξ (qExt sqs (p + 2)) - parisiTheta ξ (qExt sqs (p + 1)))
  let d := parisiTheta ξ (qs 0) - parisiTheta ξ u
  have hupdate : ∀ c, Function.update sms 0 c = splitParisiRootMass ms c := by
    intro c
    simp only [sms, splitParisiRootMass_eq_left, update_splitParisiMassLeft]
  have hqL : qExt sqs 1 = u := by simp [sqs, qExt, splitParisiRootOverlap]
  have hqR : qExt sqs 2 = qs 0 := by
    rw [qExt_succ_of_lt _ (by omega : 1 < k + 2)]
    rfl
  have hpenalty : ∀ c,
      (∑ p ∈ Finset.range (k + 2), mExt (splitParisiRootMass ms c) (p + 1) *
        (parisiTheta ξ (qExt sqs (p + 2)) - parisiTheta ξ (qExt sqs (p + 1)))) =
      C + c * d := by
    intro c
    have hh := parisiMassPenalty_mass_update_eq ξ sms sqs 0 c
    rw [hupdate] at hh
    simpa only [Fin.val_zero, zero_add, hqL, hqR, C, d] using hh
  let Φ : ℝ → ℝ := fun c => closedRandomFieldParisiFunctional μh ξ
    (splitParisiRootMass ms c) sqs
  have hΦ : Φ = fun c => Real.log 2 + (∫ p, coleHopf c v A (H p) ∂μ) -
      (1 / 2) * (C + c * d) := by
    funext c
    unfold Φ closedRandomFieldParisiFunctional
    rw [hpenalty]
    simp only [sqs, closedParisiX₀_split_root_eq, coleHopf_zero]
    congr 2
    exact (integral_prod _ (hF c)).symm
  have hdG : HasDerivAt (fun c => ∫ p, coleHopf c v A (H p) ∂μ)
      (∫ p, coleHopfMassDeriv 0 v A (H p) ∂μ) 0 := by
    simpa only [add_zero] using hasDerivAt_integral_coleHopf_mass_comp
      hHm hH hAm hLip v 0 (m := 0) ⟨le_rfl, zero_le_one⟩
  have hdlin : HasDerivAt (fun c => (1 / 2) * (C + c * d)) ((1 / 2) * d) 0 := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const d).const_add C).const_mul (1 / 2)
  have hdΦ : HasDerivAt Φ
      ((∫ p, coleHopfMassDeriv 0 v A (H p) ∂μ) - (1 / 2) * d) 0 := by
    rw [hΦ]
    exact (hdG.const_add (Real.log 2)).sub hdlin
  have hdold : HasDerivWithinAt Φ ((1 / 2) * parisiRootf μh ξ ms qs u)
      (Icc (0 : ℝ) 1) 0 :=
    hasDerivWithinAt_closedRandomFieldParisiFunctional_split_root_mass_zero_eq_U
      hμ ξ ms qs u
  have hcoef := (hdΦ.hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc_zero_one 0 ⟨le_rfl, zero_le_one⟩)).symm.trans
      (hdold.derivWithin (uniqueDiffOn_Icc_zero_one 0 ⟨le_rfl, zero_le_one⟩))
  have hh := hTaylor μ hHm hH A hAm hLip v hv 0 ⟨le_rfl, zero_le_one⟩ b hb
  simp only [sub_zero] at hh
  change |Φ b - Φ 0 - b * ((1 / 2) * parisiRootf μh ξ ms qs u)| ≤ M * b ^ 2
  rw [hΦ]
  rw [← hcoef]
  convert hh using 1
  congr 1
  ring

/-- The root part of (14.264) for a near-infimum overlap minimizer.
The same M works for every later choice of MIN tolerance and parameters;
no lower bound on the first positive mass is assumed. -/
theorem exists_uniform_parisiRootf_lower_bound
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) :
    ∃ M : ℝ, 0 < M ∧ ∀ {μh : Measure ℝ} [IsProbabilityMeasure μh],
      Integrable id μh → ∀ {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ},
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      ∀ {ε : ℝ}, 0 ≤ ε →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ u : ℝ, 0 ≤ u ∧ u ≤ qs 0 →
        -(4 * Real.sqrt (M * ε)) ≤ parisiRootf μh ξ ms qs u := by
  obtain ⟨M, hM, hTaylor⟩ := exists_uniform_splitParisiRoot_mass_taylor_bound hξ
  refine ⟨M, hM, ?_⟩
  intro μh _ hμ k ms qs hm hmin ε hε hnear u hu
  have hmd : ms ∈ parisiMassDomain k := mem_parisiMassDomain_iff.2
    ⟨hm.1.monotone, fun p => (hm.2.1 p).le, fun p => (hm.2.2 p).le⟩
  have hqd : qs ∈ parisiOverlapDomain k := mem_parisiOverlapDomain_iff.2
    ⟨hmin.1.1.monotone, hmin.1.2.1, hmin.1.2.2⟩
  let Φ : ℝ → ℝ := fun c => closedRandomFieldParisiFunctional μh ξ
    (splitParisiRootMass ms c) (splitParisiRootOverlap qs u)
  have hzero : Φ 0 = randomFieldParisiFunctional μh ξ ms qs := by
    dsimp only [Φ]
    rw [closedRandomFieldParisiFunctional_split_root_zero_mass μh hξ ms qs hqd hu,
      closedRandomFieldParisiFunctional_eq μh ξ ms qs hm]
  have hupper : mExt ms 1 ≤ 1 := mExt_le_one (fun p => (hm.2.2 p).le) _
  have hh := Aristotle.split_slope_ge_neg_sqrt
    (Φ := Φ) (a := 0) (b := mExt ms 1) (M := M)
    (s := (1 / 2) * parisiRootf μh ξ ms qs u)
    (hm.mExt_pos (by norm_num)) hM hε
    (closedRandomFieldParisiFunctional_split_root_zero_le_upper_of_isMin hξ hm hmin hu)
    (fun c hc => by
      rw [hzero]
      exact (randomFieldParisiFunctional_sub_lt_split_root_of_near_inf
        hμ hξ hmd hqd hnear hc hu).le)
    (fun c hc => by
      have ht := (le_abs_self _).trans
        (hTaylor hμ k ms qs hqd u hu c ⟨hc.1, hc.2.trans hupper⟩)
      simp only [sub_zero]
      change Φ c - Φ 0 - c * ((1 / 2) * parisiRootf μh ξ ms qs u) ≤ M * c ^ 2 at ht
      linarith)
  linarith

/-- Taylor control for any actual mass coordinate, including inserted zero
or matching masses. Only the preceding fixed masses must be positive; their
order and upper bound prevent dependence on their number. The constant
depends only on V, not on the field law or the other recursion parameters. -/
theorem exists_uniform_closedRandomFieldParisiFunctional_mass_update_taylor_bound (V : ℝ≥0) :
    ∃ M : ℝ, 0 < M ∧ ∀ {μh : Measure ℝ} [IsProbabilityMeasure μh],
      Integrable id μh → ∀ (ξ : ℝ → ℝ) (k : ℕ) (ms : Fin k → ℝ)
      (qs : Fin (k + 1) → ℝ) (r : Fin k), Monotone ms →
      (∀ p : Fin r.val, 0 < ms ⟨p.val, by omega⟩) →
      (∀ p : Fin r.val, ms ⟨p.val, by omega⟩ ≤ 1) →
      parisiVar ξ qs (r.val + 1) ≤ V →
      ∀ m ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        |closedRandomFieldParisiFunctional μh ξ (Function.update ms r b) qs -
          closedRandomFieldParisiFunctional μh ξ (Function.update ms r m) qs -
          (randomFieldParisiMassMoment μh ξ ms qs r m - (1 / 2) *
            (parisiTheta ξ (qExt qs (r.val + 2)) - parisiTheta ξ (qExt qs (r.val + 1)))) *
            (b - m)| ≤ M * (b - m) ^ 2 := by
  obtain ⟨M, hM, hTaylor⟩ := exists_uniform_integral_coleHopfIterate_mass_taylor_bound V
  refine ⟨M, hM, ?_⟩
  intro μh _ hμ ξ k ms qs r hmono hpos hle hv m hm b hb
  let pm := parisiMassPrefixMasses ms r
  let pv := parisiMassPrefixVars ξ qs r
  let v := parisiVar ξ qs (r.val + 1)
  let v₀ := parisiVar ξ qs 0
  let A := parisiQSuffix ξ 0 ms qs r.castSucc
  let μ := μh.prod (gaussianReal 0 v₀)
  let H : ℝ × ℝ → ℝ := fun p => p.1 + p.2
  have hHm : Measurable H := measurable_fst.add measurable_snd
  have hzg : HasLinearGrowth id := ⟨0, 1, zero_le_one, by simp⟩
  have hz : Integrable id (gaussianReal 0 v₀) :=
    hzg.toHasExpGrowth.integrable_gaussianReal measurable_id.aestronglyMeasurable
  have hH : Integrable H μ := (hμ.comp_fst _).add (hz.comp_snd _)
  have hLip : ∀ x y, |A y - A x| ≤ |y - x| := abs_parisiQSuffix_sub_le ξ 0 ms qs r.castSucc
  have hLip' : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using hLip
  have hAm := (lipschitzWith_toNNReal_of_abs_sub_le hLip').continuous.measurable
  have hpm : Monotone pm := fun p q hpq => hmono (by exact hpq)
  have hF : ∀ c, Integrable (fun p => coleHopfIterate r.val pm pv (coleHopf c v A) (H p)) μ := by
    intro c
    have hGlip := abs_coleHopf_sub_le_of_lipschitz c hAm hLip' v
    exact integrable_one_lipschitz_comp hHm hH
      (abs_coleHopfIterate_sub_le r.val pm pv
        (lipschitzWith_toNNReal_of_abs_sub_le hGlip).continuous.measurable hGlip)
  let C := ∑ p ∈ (Finset.range (k + 1)).erase r.val, mExt ms (p + 1) *
    (parisiTheta ξ (qExt qs (p + 2)) - parisiTheta ξ (qExt qs (p + 1)))
  let d := parisiTheta ξ (qExt qs (r.val + 2)) - parisiTheta ξ (qExt qs (r.val + 1))
  let Φ : ℝ → ℝ := fun c => closedRandomFieldParisiFunctional μh ξ (Function.update ms r c) qs
  have hΦ : Φ = fun c => Real.log 2 +
      (∫ p, coleHopfIterate r.val pm pv (coleHopf c v A) (H p) ∂μ) -
      (1 / 2) * (C + c * d) := by
    funext c
    unfold Φ closedRandomFieldParisiFunctional
    rw [parisiMassPenalty_mass_update_eq]
    simp only [closedParisiX₀_mass_update_eq]
    congr 2
    exact (integral_prod _ (hF c)).symm
  have hdG : HasDerivAt
      (fun c => ∫ p, coleHopfIterate r.val pm pv (coleHopf c v A) (H p) ∂μ)
      (∫ p, coleHopfIterateMassDeriv pm pv v A m (H p) ∂μ) m := by
    simpa only [add_zero] using hasDerivAt_integral_coleHopfIterate_mass_layer_comp
      hHm hH pm pv hpos hle hAm hLip v 0 hm
  have hdlin : HasDerivAt (fun c => (1 / 2) * (C + c * d)) ((1 / 2) * d) m := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id m).mul_const d).const_add C).const_mul (1 / 2)
  have hdΦ : HasDerivAt Φ
      ((∫ p, coleHopfIterateMassDeriv pm pv v A m (H p) ∂μ) - (1 / 2) * d) m := by
    rw [hΦ]
    exact (hdG.const_add (Real.log 2)).sub hdlin
  have hdold := hasDerivWithinAt_closedRandomFieldParisiFunctional_mass_update
    hμ ξ ms qs r hpos hle hm
  have hcoef := (hdΦ.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one m hm)).symm.trans
    (hdold.derivWithin (uniqueDiffOn_Icc_zero_one m hm))
  have hh := hTaylor r.val pm pv hpm hpos hle μ hHm hH A hAm hLip v hv m hm b hb
  change |Φ b - Φ m - (randomFieldParisiMassMoment μh ξ ms qs r m - (1 / 2) * d) *
    (b - m)| ≤ M * (b - m) ^ 2
  rw [hΦ, ← hcoef]
  convert hh using 1
  congr 1
  ring

/-- Every admissible Gaussian interval is bounded by the total profile
variance. Strict positivity of ξ'' at zero is not needed. -/
theorem parisiVar_le_total_variance {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} {qs : Fin (k + 1) → ℝ} (hq : qs ∈ parisiOverlapDomain k) (n : ℕ) :
    parisiVar ξ qs n ≤ (deriv ξ 1 - deriv ξ 0).toNNReal := by
  have hL := qExt_mem_Icc_of_mem_cube hq.1 n
  have hR := qExt_mem_Icc_of_mem_cube hq.1 (n + 1)
  exact Real.toNNReal_le_toNNReal (sub_le_sub
    (hξ.strictMonoOn_deriv.monotoneOn hR ⟨zero_le_one, le_rfl⟩ hR.2)
    (hξ.strictMonoOn_deriv.monotoneOn ⟨le_rfl, zero_le_one⟩ hL hL.1))

/-- At the upper mass endpoint of the nonroot inner-mass split, matching
adjacent layers produce the original functional with its right overlap
moved to u. The last old free mass is included, with upper endpoint 1. -/
theorem closedRandomFieldParisiFunctional_split_right_upper_mass
    (μh : Measure ℝ) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hq : qs ∈ parisiOverlapDomain k)
    (p : Fin k) {u : ℝ} (hu : qs p.castSucc ≤ u ∧ u ≤ qs p.succ) :
    closedRandomFieldParisiFunctional μh ξ
        (splitParisiMassRight ms p (mExt ms (p.val + 2)))
        (splitParisiOverlap qs p.castSucc u) =
      closedRandomFieldParisiFunctional μh ξ ms (qUpdate qs p.succ u) := by
  let r : Fin (k + 2) := p.succ.succ
  have hmass : mExt (splitParisiMassRight ms p (mExt ms (p.val + 2))) r.val =
      mExt (splitParisiMassRight ms p (mExt ms (p.val + 2))) (r.val + 1) := by
    change mExt (splitParisiMassRight ms p (mExt ms (p.val + 2))) (p.val + 2) =
      mExt (splitParisiMassRight ms p (mExt ms (p.val + 2))) ((p.val + 2) + 1)
    rw [mExt_splitParisiMassRight_inserted,
      mExt_splitParisiMassRight_after ms p _ (by omega : p.val + 1 < p.val + 2)]
  have hu' : qExt qs (p.castSucc.val + 1) ≤ u ∧ u ≤ qExt qs (p.castSucc.val + 2) := by
    have hL : qExt qs (p.val + 1) = qs p.castSucc := qExt_succ_of_lt qs p.castSucc.isLt
    have hR : qExt qs (p.val + 2) = qs p.succ := qExt_succ_of_lt qs p.succ.isLt
    change qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2)
    rw [hL, hR]
    exact hu
  have hbounds : qExt (splitParisiOverlap qs p.castSucc u) r.val ≤ u ∧
      u ≤ qExt (splitParisiOverlap qs p.castSucc u) (r.val + 2) := by
    change qExt (splitParisiOverlap qs p.castSucc u) (p.val + 2) ≤ u ∧
      u ≤ qExt (splitParisiOverlap qs p.castSucc u) ((p.val + 3) + 1)
    have hL : qExt (splitParisiOverlap qs p.castSucc u) (p.val + 2) = u :=
      qExt_splitParisiOverlap_inserted qs p.castSucc u
    rw [hL,
      qExt_splitParisiOverlap_after qs p.castSucc u (by change p.val + 1 < p.val + 3; omega)]
    have hq' := mem_parisiOverlapDomain_iff.1 hq
    have hnext : qExt qs (p.val + 2) ≤ qExt qs ((p.val + 2) + 1) :=
      qExt_le_succ hq'.1 hq'.2.1 hq'.2.2 (by omega)
    exact ⟨le_rfl, hu'.2.trans hnext⟩
  have he := closedRandomFieldParisiFunctional_qUpdate_eq_of_equal_mass μh hξ
    (splitParisiMassRight ms p (mExt ms (p.val + 2))) (splitParisiOverlap qs p.castSucc u)
    (splitParisiOverlap_mem_domain hq p.castSucc hu') r u hmass hbounds
  have hr : r = p.castSucc.succ.succAbove p.succ := by
    apply Fin.ext
    simp [r, Fin.succAbove]
  have hqs : qUpdate (splitParisiOverlap qs p.castSucc u) r u =
      splitParisiOverlap (qUpdate qs p.succ u) p.castSucc u := by
    unfold qUpdate splitParisiOverlap
    rw [hr]
    exact (Fin.insertNth_update (α := fun _ => ℝ) p.castSucc.succ u p.succ u qs).symm
  rw [hqs] at he
  have hend := closedRandomFieldParisiFunctional_split_right_endpoint_any_mass
    μh (ξ := ξ) ms (qUpdate qs p.succ u) p (mExt ms (p.val + 2))
  rw [qUpdate_self] at hend
  exact he.symm.trans hend

private lemma qUpdate_mem_domain_of_bounds {k : ℕ} {qs : Fin (k + 1) → ℝ}
    (hq : qs ∈ parisiOverlapDomain k) (r : Fin (k + 1)) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1)
    (hleft : ∀ i, i < r → qs i ≤ u) (hright : ∀ i, r < i → u ≤ qs i) :
    qUpdate qs r u ∈ parisiOverlapDomain k := by
  refine ⟨mem_parisiOverlapCube_iff.2 (fun i => ?_), ?_⟩
  · by_cases hi : i = r
    · subst i
      simpa only [qUpdate_self] using hu
    · rw [qUpdate_of_ne _ _ hi]
      exact mem_parisiOverlapCube_iff.1 hq.1 i
  · intro i j hij
    by_cases hir : i = r
    · subst i
      by_cases hjr : j = r
      · subst j
        exact le_rfl
      · rw [qUpdate_self, qUpdate_of_ne _ _ hjr]
        exact hright j (lt_of_le_of_ne hij (Ne.symm hjr))
    · by_cases hjr : j = r
      · subst j
        rw [qUpdate_of_ne _ _ hir, qUpdate_self]
        exact hleft i (lt_of_le_of_ne hij hir)
      · rw [qUpdate_of_ne _ _ hir, qUpdate_of_ne _ _ hjr]
        exact hq.2 hij

/-- Fixed-level closed minimality gives the endpoint comparison for every
nonroot overlap, including the closed left endpoint of its interval. -/
theorem closedRandomFieldParisiFunctional_split_right_matching_le_upper_of_isMinOn
    {μh : Measure ℝ} {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hmin : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain k) (ms, qs)) (p : Fin k) {u : ℝ}
    (hu : u ∈ Icc (qs p.castSucc) (qs p.succ)) :
    closedRandomFieldParisiFunctional μh ξ
        (splitParisiMassRight ms p (ms p)) (splitParisiOverlap qs p.castSucc u) ≤
      closedRandomFieldParisiFunctional μh ξ
        (splitParisiMassRight ms p (mExt ms (p.val + 2))) (splitParisiOverlap qs p.castSucc u) := by
  have hqd : qs ∈ parisiOverlapDomain k := mem_parisiOverlapDomain_iff.2
    ⟨hq.1.monotone, hq.2.1, hq.2.2⟩
  have hu' : qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2) := by
    have hL : qExt qs (p.val + 1) = qs p.castSucc := qExt_succ_of_lt qs p.castSucc.isLt
    have hR : qExt qs (p.val + 2) = qs p.succ := qExt_succ_of_lt qs p.succ.isLt
    rw [hL, hR]
    exact hu
  rw [closedRandomFieldParisiFunctional_split_right_matching_mass μh hξ ms qs hqd p u hu',
    closedRandomFieldParisiFunctional_split_right_upper_mass μh hξ ms qs hqd p hu]
  have hmd : ms ∈ parisiMassDomain k := mem_parisiMassDomain_iff.2
    ⟨hm.1.monotone, fun i => (hm.2.1 i).le, fun i => (hm.2.2 i).le⟩
  refine hmin (a := (ms, qUpdate qs p.succ u)) ⟨hmd, ?_⟩
  refine qUpdate_mem_domain_of_bounds hqd p.succ
    ⟨(hq.mem_Icc p.castSucc).1.trans hu.1, hu.2.trans (hq.mem_Icc p.succ).2⟩ ?_ ?_
  · intro i hi
    exact (hq.1.monotone (by
      change i.val ≤ p.val
      change i.val < p.val + 1 at hi
      omega)).trans hu.1
  · intro i hi
    exact hu.2.trans (hq.1.monotone hi.le)

/-- The nonroot inner-mass split has the same uniform quadratic control,
with its derivative identified as half of the concrete f in (14.239).
The coefficient is selected from ξ before every MIN parameter. -/
theorem exists_uniform_splitParisiRight_mass_taylor_bound
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) :
    ∃ M : ℝ, 0 < M ∧ ∀ {μh : Measure ℝ} [IsProbabilityMeasure μh],
      Integrable id μh → ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → ParisiQAdmissible qs → ∀ p : Fin k, ∀ u : ℝ,
      u ∈ Icc (qs p.castSucc) (qs p.succ) → ∀ b ∈ Icc (0 : ℝ) 1,
        |closedRandomFieldParisiFunctional μh ξ
            (splitParisiMassRight ms p b) (splitParisiOverlap qs p.castSucc u) -
          closedRandomFieldParisiFunctional μh ξ
            (splitParisiMassRight ms p (ms p)) (splitParisiOverlap qs p.castSucc u) -
          ((1 / 2) * parisiRightf μh ξ ms qs p u) * (b - ms p)| ≤ M * (b - ms p) ^ 2 := by
  let V : ℝ≥0 := (deriv ξ 1 - deriv ξ 0).toNNReal
  obtain ⟨M, hM, hTaylor⟩ :=
    exists_uniform_closedRandomFieldParisiFunctional_mass_update_taylor_bound V
  refine ⟨M, hM, ?_⟩
  intro μh _ hμ k ms qs hm hq p u hu b hb
  have hmd : ms ∈ parisiMassDomain k := mem_parisiMassDomain_iff.2
    ⟨hm.1.monotone, fun i => (hm.2.1 i).le, fun i => (hm.2.2 i).le⟩
  have hqd : qs ∈ parisiOverlapDomain k := mem_parisiOverlapDomain_iff.2
    ⟨hq.1.monotone, hq.2.1, hq.2.2⟩
  have hu' : qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2) := by
    have hL : qExt qs (p.val + 1) = qs p.castSucc := qExt_succ_of_lt qs p.castSucc.isLt
    have hR : qExt qs (p.val + 2) = qs p.succ := qExt_succ_of_lt qs p.succ.isLt
    rw [hL, hR]
    exact hu
  have hmass : ms p ≤ mExt ms (p.val + 2) := by
    have hh := (sub_pos.1 (hm.mExt_gap_pos p.succ)).le
    simpa only [Fin.val_succ, mExt_val_succ] using hh
  let sms := splitParisiMassRight ms p (ms p)
  let sqs := splitParisiOverlap qs p.castSucc u
  have hsms : sms ∈ parisiMassDomain (k + 1) :=
    splitParisiMassRight_mem_domain hmd p ⟨by rw [mExt_val_succ], hmass⟩
  have hsqs : sqs ∈ parisiOverlapDomain (k + 1) :=
    splitParisiOverlap_mem_domain hqd p.castSucc hu'
  have hpref : ∀ i : Fin p.succ.val, sms ⟨i.val, by omega⟩ = ms ⟨i.val, by omega⟩ :=
    fun i => splitParisiMassLeft_apply_of_lt ms p.succ (ms p) (by exact i.isLt)
  have hpos : ∀ i : Fin p.succ.val, 0 < sms ⟨i.val, by omega⟩ := by
    intro i
    rw [hpref i]
    exact hm.2.1 _
  have hle : ∀ i : Fin p.succ.val, sms ⟨i.val, by omega⟩ ≤ 1 := by
    intro i
    rw [hpref i]
    exact (hm.2.2 _).le
  have hv : parisiVar ξ sqs (p.succ.val + 1) ≤ V := parisiVar_le_total_variance hξ hsqs _
  have hmp : ms p ∈ Icc (0 : ℝ) 1 := ⟨(hm.2.1 p).le, (hm.2.2 p).le⟩
  have hh := hTaylor hμ ξ (k + 1) sms sqs p.succ
    (mem_parisiMassDomain_iff.1 hsms).1 hpos hle hv (ms p) hmp b hb
  have hd := hasDerivWithinAt_closedRandomFieldParisiFunctional_mass_update
    hμ ξ sms sqs p.succ hpos hle hmp
  simp only [sms, update_splitParisiMassRight] at hd hh
  have hdU := hasDerivWithinAt_closedRandomFieldParisiFunctional_split_right_mass_eq_U
    hμ hξ ms qs p hm hq hu
  have hcoef := (hd.derivWithin (uniqueDiffOn_Icc_zero_one _ hmp)).symm.trans
    (hdU.derivWithin (uniqueDiffOn_Icc_zero_one _ hmp))
  rw [hcoef] at hh
  exact hh

/-- The nonroot part of (14.264), including both closed overlap endpoints.
The bound is uniform in every later MIN choice and in the number of levels;
the fixed-level minimum is used only for the upper mass endpoint comparison. -/
theorem exists_uniform_parisiRightf_lower_bound
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) :
    ∃ M : ℝ, 0 < M ∧ ∀ {μh : Measure ℝ} [IsProbabilityMeasure μh],
      Integrable id μh → ∀ {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ},
      ParisiMAdmissible ms → ParisiQAdmissible qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) → ∀ {ε : ℝ}, 0 ≤ ε →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ p : Fin k, ∀ u : ℝ, u ∈ Icc (qs p.castSucc) (qs p.succ) →
        -(4 * Real.sqrt (M * ε)) ≤ parisiRightf μh ξ ms qs p u := by
  obtain ⟨M, hM, hTaylor⟩ := exists_uniform_splitParisiRight_mass_taylor_bound hξ
  refine ⟨M, hM, ?_⟩
  intro μh _ hμ k ms qs hm hq hmin ε hε hnear p u hu
  have hmd : ms ∈ parisiMassDomain k := mem_parisiMassDomain_iff.2
    ⟨hm.1.monotone, fun i => (hm.2.1 i).le, fun i => (hm.2.2 i).le⟩
  have hqd : qs ∈ parisiOverlapDomain k := mem_parisiOverlapDomain_iff.2
    ⟨hq.1.monotone, hq.2.1, hq.2.2⟩
  have hu' : qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2) := by
    have hL : qExt qs (p.val + 1) = qs p.castSucc := qExt_succ_of_lt qs p.castSucc.isLt
    have hR : qExt qs (p.val + 2) = qs p.succ := qExt_succ_of_lt qs p.succ.isLt
    rw [hL, hR]
    exact hu
  let Φ : ℝ → ℝ := fun c => closedRandomFieldParisiFunctional μh ξ
    (splitParisiMassRight ms p c) (splitParisiOverlap qs p.castSucc u)
  have hzero : Φ (ms p) = randomFieldParisiFunctional μh ξ ms qs := by
    dsimp only [Φ]
    rw [closedRandomFieldParisiFunctional_split_right_matching_mass μh hξ ms qs hqd p u hu',
      closedRandomFieldParisiFunctional_eq μh ξ ms qs hm]
  have hinterval : ms p < mExt ms (p.val + 2) := by
    have hh := sub_pos.1 (hm.mExt_gap_pos p.succ)
    simpa only [Fin.val_succ, mExt_val_succ] using hh
  have hupper : mExt ms (p.val + 2) ≤ 1 := mExt_le_one (fun i => (hm.2.2 i).le) _
  have hh := Aristotle.split_slope_ge_neg_sqrt
    (Φ := Φ) (a := ms p) (b := mExt ms (p.val + 2)) (M := M)
    (s := (1 / 2) * parisiRightf μh ξ ms qs p u) hinterval hM hε
    (closedRandomFieldParisiFunctional_split_right_matching_le_upper_of_isMinOn
      hξ ms qs hm hq hmin p hu)
    (fun c hc => by
      rw [hzero]
      exact (randomFieldParisiFunctional_sub_lt_split_right_of_near_inf
        hμ hξ hmd hqd hnear p ⟨by simpa only [mExt_val_succ] using hc.1, hc.2⟩ hu').le)
    (fun c hc => by
      have ht := (le_abs_self _).trans (hTaylor hμ k ms qs hm hq p u hu c
        ⟨(hm.2.1 p).le.trans hc.1, hc.2.trans hupper⟩)
      change Φ c - Φ (ms p) - ((1 / 2) * parisiRightf μh ξ ms qs p u) * (c - ms p) ≤
        M * (c - ms p) ^ 2 at ht
      linarith)
  linarith

/-- The outer-mass orientation used for the mirror cases in Section 14.9
has the same parameter-independent quadratic Taylor bound. The expansion is
at the matching old mass, including the terminal old mass one and k=0. -/
theorem exists_uniform_splitParisiLeft_mass_taylor_bound
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) :
    ∃ M : ℝ, 0 < M ∧ ∀ {μh : Measure ℝ} [IsProbabilityMeasure μh],
      Integrable id μh → ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → ParisiQAdmissible qs → ∀ p : Fin (k + 1), ∀ u : ℝ,
      qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2) → ∀ b ∈ Icc (0 : ℝ) 1,
        |closedRandomFieldParisiFunctional μh ξ
            (splitParisiMassLeft ms p b) (splitParisiOverlap qs p u) -
          closedRandomFieldParisiFunctional μh ξ
            (splitParisiMassLeft ms p (mExt ms (p.val + 1))) (splitParisiOverlap qs p u) -
          splitParisiLeftMassDeriv μh ξ ms qs p u (mExt ms (p.val + 1)) *
            (b - mExt ms (p.val + 1))| ≤ M * (b - mExt ms (p.val + 1)) ^ 2 := by
  let V : ℝ≥0 := (deriv ξ 1 - deriv ξ 0).toNNReal
  obtain ⟨M, hM, hTaylor⟩ :=
    exists_uniform_closedRandomFieldParisiFunctional_mass_update_taylor_bound V
  refine ⟨M, hM, ?_⟩
  intro μh _ hμ k ms qs hm hq p u hu b hb
  have hmd : ms ∈ parisiMassDomain k := mem_parisiMassDomain_iff.2
    ⟨hm.1.monotone, fun i => (hm.2.1 i).le, fun i => (hm.2.2 i).le⟩
  have hqd : qs ∈ parisiOverlapDomain k := mem_parisiOverlapDomain_iff.2
    ⟨hq.1.monotone, hq.2.1, hq.2.2⟩
  let sms := splitParisiMassLeft ms p (mExt ms (p.val + 1))
  let sqs := splitParisiOverlap qs p u
  have hsms : sms ∈ parisiMassDomain (k + 1) :=
    splitParisiMassLeft_mem_domain hmd p ⟨(sub_pos.1 (hm.mExt_gap_pos p)).le, le_rfl⟩
  have hsqs : sqs ∈ parisiOverlapDomain (k + 1) := splitParisiOverlap_mem_domain hqd p hu
  have hpref : ∀ i : Fin p.val, sms ⟨i.val, by omega⟩ = ms ⟨i.val, by omega⟩ :=
    fun i => splitParisiMassLeft_apply_of_lt ms p _ i.isLt
  have hpos : ∀ i : Fin p.val, 0 < sms ⟨i.val, by omega⟩ := by
    intro i
    rw [hpref i]
    exact hm.2.1 _
  have hle : ∀ i : Fin p.val, sms ⟨i.val, by omega⟩ ≤ 1 := by
    intro i
    rw [hpref i]
    exact (hm.2.2 _).le
  have hv : parisiVar ξ sqs (p.val + 1) ≤ V := parisiVar_le_total_variance hξ hsqs _
  have hmp : mExt ms (p.val + 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨mExt_nonneg (fun i => (hm.2.1 i).le) _, mExt_le_one (fun i => (hm.2.2 i).le) _⟩
  have hh := hTaylor hμ ξ (k + 1) sms sqs p
    (mem_parisiMassDomain_iff.1 hsms).1 hpos hle hv _ hmp b hb
  have hd := hasDerivWithinAt_closedRandomFieldParisiFunctional_mass_update
    hμ ξ sms sqs p hpos hle hmp
  simp only [sms, update_splitParisiMassLeft] at hd hh
  have hdleft := hasDerivWithinAt_closedRandomFieldParisiFunctional_split_left_mass
    hμ ξ ms qs (fun i => hm.2.1 i) (fun i => (hm.2.2 i).le) p u hmp
  have hcoef := (hd.derivWithin (uniqueDiffOn_Icc_zero_one _ hmp)).symm.trans
    (hdleft.derivWithin (uniqueDiffOn_Icc_zero_one _ hmp))
  rw [hcoef] at hh
  exact hh

/-- At the lower mass endpoint of the outer-mass split, the preceding two
layers merge and the old left overlap moves to u. This is the endpoint input
for the mirror of (14.264), including the initial and terminal intervals. -/
theorem closedRandomFieldParisiFunctional_split_left_lower_mass
    (μh : Measure ℝ) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hq : qs ∈ parisiOverlapDomain k)
    (p : Fin (k + 1)) {u : ℝ}
    (hu : qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2)) :
    closedRandomFieldParisiFunctional μh ξ
        (splitParisiMassLeft ms p (mExt ms p.val)) (splitParisiOverlap qs p u) =
      closedRandomFieldParisiFunctional μh ξ ms (qUpdate qs p u) := by
  let sms := splitParisiMassLeft ms p (mExt ms p.val)
  have hprev : mExt ms p.val = mExt sms p.val := by
    have he := mExt_eraseParisiMass sms p p.val
    simpa only [sms, erase_splitParisiMassLeft, ite_eq_left le_rfl] using he
  have hmass : mExt sms p.castSucc.val = mExt sms (p.castSucc.val + 1) := by
    change mExt sms p.val = mExt sms (p.val + 1)
    rw [← hprev, mExt_val_succ sms p]
    exact (Fin.insertNth_apply_same (α := fun _ => ℝ) p (mExt ms p.val) ms).symm
  have hbounds : qExt (splitParisiOverlap qs p u) p.castSucc.val ≤ u ∧
      u ≤ qExt (splitParisiOverlap qs p u) (p.castSucc.val + 2) := by
    change qExt (splitParisiOverlap qs p u) p.val ≤ u ∧
      u ≤ qExt (splitParisiOverlap qs p u) (p.val + 2)
    rw [qExt_splitParisiOverlap_before qs p u (by omega),
      qExt_splitParisiOverlap_inserted]
    have hb := mem_parisiOverlapDomain_iff.1 hq
    exact ⟨(qExt_le_succ hb.1 hb.2.1 hb.2.2 (by omega)).trans hu.1, le_rfl⟩
  have he := closedRandomFieldParisiFunctional_qUpdate_eq_of_equal_mass μh hξ sms
    (splitParisiOverlap qs p u) (splitParisiOverlap_mem_domain hq p hu)
    p.castSucc u hmass hbounds
  have hqs : qUpdate (splitParisiOverlap qs p u) p.castSucc u =
      splitParisiOverlap (qUpdate qs p u) p u := by
    unfold qUpdate splitParisiOverlap
    rw [← Fin.succAbove_succ_self p]
    exact (Fin.insertNth_update (α := fun _ => ℝ) p.succ u p u qs).symm
  rw [hqs] at he
  have hend := closedRandomFieldParisiFunctional_split_left_endpoint
    μh (ξ := ξ) ms (qUpdate qs p u) p (mExt ms p.val)
  rw [qUpdate_self] at hend
  exact he.symm.trans hend

/-- Full fixed-level minimality compares the old matching-mass value with
the lower mass endpoint of the outer split. The comparison is at the old
dimension, even for the terminal interval and repeated endpoint overlaps. -/
theorem closedRandomFieldParisiFunctional_split_left_matching_le_lower_of_isMinOn
    {μh : Measure ℝ} {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hmin : IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
      (parisiParameterDomain k) (ms, qs)) (p : Fin (k + 1)) {u : ℝ}
    (hu : qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2)) :
    closedRandomFieldParisiFunctional μh ξ
        (splitParisiMassLeft ms p (mExt ms (p.val + 1))) (splitParisiOverlap qs p u) ≤
      closedRandomFieldParisiFunctional μh ξ
        (splitParisiMassLeft ms p (mExt ms p.val)) (splitParisiOverlap qs p u) := by
  have hqd : qs ∈ parisiOverlapDomain k := mem_parisiOverlapDomain_iff.2
    ⟨hq.1.monotone, hq.2.1, hq.2.2⟩
  rw [closedRandomFieldParisiFunctional_split_matching_mass μh hξ ms qs hqd p u hu,
    closedRandomFieldParisiFunctional_split_left_lower_mass μh hξ ms qs hqd p hu]
  have hmd : ms ∈ parisiMassDomain k := mem_parisiMassDomain_iff.2
    ⟨hm.1.monotone, fun i => (hm.2.1 i).le, fun i => (hm.2.2 i).le⟩
  have hleft : qs p ≤ u := by
    simpa only [qExt_succ_of_lt qs p.isLt] using hu.1
  refine hmin (a := (ms, qUpdate qs p u)) ⟨hmd, ?_⟩
  refine qUpdate_mem_domain_of_bounds hqd p
    ⟨(hq.mem_Icc p).1.trans hleft, hu.2.trans (qExt_mem_Icc_of_mem_cube hqd.1 _).2⟩ ?_ ?_
  · intro i hi
    exact (hq.monotone hi.le).trans hleft
  · intro i hi
    have hnext : qExt qs (p.val + 2) ≤ qs i := by
      rw [show p.val + 2 = (p.val + 1) + 1 by omega,
        qExt_succ_of_lt qs (by have hh := i.isLt; change p.val < i.val at hi; omega)]
      apply hq.monotone
      change p.val + 1 ≤ i.val
      change p.val < i.val at hi
      omega
    exact hu.2.trans hnext

/-- The mirror of (14.264) for the actual outer-mass derivative.
Its constant is chosen before all parameters and field laws, including the
terminal old mass one. No lower bound on the admissible mass gap is assumed. -/
theorem exists_uniform_splitParisiLeftMassDeriv_upper_bound
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) :
    ∃ M : ℝ, 0 < M ∧ ∀ {μh : Measure ℝ} [IsProbabilityMeasure μh],
      Integrable id μh → ∀ {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ},
      ParisiMAdmissible ms → ParisiQAdmissible qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) → ∀ {ε : ℝ}, 0 ≤ ε →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ p : Fin (k + 1), ∀ u : ℝ,
      qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2) →
        splitParisiLeftMassDeriv μh ξ ms qs p u (mExt ms (p.val + 1)) ≤
          2 * Real.sqrt (M * ε) := by
  obtain ⟨M, hM, hTaylor⟩ := exists_uniform_splitParisiLeft_mass_taylor_bound hξ
  refine ⟨M, hM, ?_⟩
  intro μh _ hμ k ms qs hm hq hmin ε hε hnear p u hu
  have hmd : ms ∈ parisiMassDomain k := mem_parisiMassDomain_iff.2
    ⟨hm.1.monotone, fun i => (hm.2.1 i).le, fun i => (hm.2.2 i).le⟩
  have hqd : qs ∈ parisiOverlapDomain k := mem_parisiOverlapDomain_iff.2
    ⟨hq.1.monotone, hq.2.1, hq.2.2⟩
  let a := mExt ms p.val
  let b := mExt ms (p.val + 1)
  let D := splitParisiLeftMassDeriv μh ξ ms qs p u b
  let Φ : ℝ → ℝ := fun c => closedRandomFieldParisiFunctional μh ξ
    (splitParisiMassLeft ms p c) (splitParisiOverlap qs p u)
  have hab : a < b := sub_pos.1 (hm.mExt_gap_pos p)
  have ha : 0 ≤ a := mExt_nonneg (fun i => (hm.2.1 i).le) _
  have hb : b ≤ 1 := mExt_le_one (fun i => (hm.2.2 i).le) _
  have hzero : Φ b = randomFieldParisiFunctional μh ξ ms qs := by
    dsimp only [Φ, b]
    rw [closedRandomFieldParisiFunctional_split_matching_mass μh hξ ms qs hqd p u hu,
      closedRandomFieldParisiFunctional_eq μh ξ ms qs hm]
  have hcomp : Φ b ≤ Φ a :=
    closedRandomFieldParisiFunctional_split_left_matching_le_lower_of_isMinOn
      hξ ms qs hm hq hmin p hu
  have hh := Aristotle.split_slope_ge_neg_sqrt
    (Φ := fun c => Φ (a + b - c)) (a := a) (b := b) (M := M) (s := -D) hab hM hε
    (by simpa only [show a + b - a = b by ring, show a + b - b = a by ring] using hcomp)
    (fun c hc => by
      rw [show a + b - a = b by ring, hzero]
      exact (randomFieldParisiFunctional_sub_lt_split_left_of_near_inf hμ hξ hmd hqd
        hnear p ⟨by change a ≤ a + b - c; linarith [hc.2],
          by change a + b - c ≤ b; linarith [hc.1]⟩ hu).le)
    (fun c hc => by
      have ht := (le_abs_self _).trans (hTaylor hμ k ms qs hm hq p u hu (a + b - c)
        ⟨by linarith [hc.2], by linarith [hc.1]⟩)
      change Φ (a + b - c) - Φ b - D * (a + b - c - b) ≤
        M * (a + b - c - b) ^ 2 at ht
      rw [show a + b - c - b = -(c - a) by ring, neg_sq] at ht
      rw [show a + b - a = b by ring]
      linarith)
  linarith

/-- The mirror of (14.264) for the actual outer U/f response. The constant
depends only on the covariance profile, and the terminal old mass one and
k=0 are included. -/
theorem exists_uniform_parisiLeftf_upper_bound
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) :
    ∃ M : ℝ, 0 < M ∧ ∀ {μh : Measure ℝ} [IsProbabilityMeasure μh],
      Integrable id μh → ∀ {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ},
      ParisiMAdmissible ms → ParisiQAdmissible qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) → ∀ {ε : ℝ}, 0 ≤ ε →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ p : Fin (k + 1), ∀ u ∈ Icc (qs p) (qExt qs (p.val + 2)),
        parisiLeftf μh ξ ms qs p u ≤ 4 * Real.sqrt (M * ε) := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_splitParisiLeftMassDeriv_upper_bound hξ
  refine ⟨M, hM, ?_⟩
  intro μh _ hμ k ms qs hm hq hmin ε hε hnear p u hu
  have hh := hbound hμ hm hq hmin hε hnear p u
    ⟨by simpa only [qExt_succ_of_lt qs p.isLt] using hu.1, hu.2⟩
  rw [splitParisiLeftMassDeriv_eq_U hμ hξ ms qs p hm hq hu] at hh
  change (1 / 2) * parisiLeftf μh ξ ms qs p u ≤ 2 * Real.sqrt (M * ε) at hh
  linarith

end SpinGlass
