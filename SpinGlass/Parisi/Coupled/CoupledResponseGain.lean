import SpinGlass.Parisi.Coupled.CoupledResponseMoment
import SpinGlass.Parisi.Coupled.CoupledFieldTaylor
import SpinGlass.Parisi.Variational.ParisiCriticalResponse

/-!
# Concrete coupling gains for the critical response cases

The matched Gaussian split has the original zero-coupling value and the
actual spatial response moment as its slope. Combining these identities
with the coupled Taylor bound gives the explicit gain in (14.330)-(14.331).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- Erasing the matching mass and variance split recovers the actual
unsplit post-root recursion throughout the closed variance interval. -/
theorem coleHopfIterate_parisiResponseSplit_eq_rootSuffix (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) :
    coleHopfIterate ((p.val + 1) + ((k - p.val) + 1))
        (parisiResponseSplitMasses ms p) (parisiResponseSplitVars ξ qs p v)
        (parisiLogCoshTerminal 0) = parisiRootSuffix ξ ms qs := by
  have hL : ∀ y z, |parisiQSuffix ξ 0 ms qs p z - parisiQSuffix ξ 0 ms qs p y| ≤
      1 * |z - y| := by
    simpa only [one_mul] using abs_parisiQSuffix_sub_le ξ 0 ms qs p
  have hAm := (lipschitzWith_toNNReal_of_abs_sub_le hL).continuous.measurable
  unfold parisiResponseSplitMasses parisiResponseSplitVars
  rw [coleHopfIterate_append, coleHopfIterate_snoc_eq, coleHopfIterate_succ]
  change coleHopfIterate p.val (parisiOuterMassPrefixMasses ms p)
      (parisiOuterMassPrefixVars ξ qs p)
      (coleHopf (mExt ms (p.val + 1))
        (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - v).toNNReal
        (coleHopf (mExt ms (p.val + 1)) v.toNNReal (parisiQSuffix ξ 0 ms qs p))) = _
  rw [coleHopfSplit_matching_mass (HasLinearGrowth.of_lipschitz hL) hAm _ hv]
  unfold parisiRootSuffix
  conv_rhs => rw [coleHopfIterate_split_one_of_eq p.val (k - p.val) (by omega)]
  have hvold : parisiVar ξ qs (p.val + 1) =
      (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p)).toNNReal := by
    unfold parisiVar
    rw [qExt_succ_of_lt qs p.isLt]
  simp only [parisiLevelMasses_apply, parisiLevelVars, hvold]
  rfl

/-- The zero-coupling one-copy value in (14.313) is the original
Parisi root value after independent root-Gaussian and site-field averages. -/
theorem integral_logCoshRec_parisiResponseSplit_eq_closedParisiX₀
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) :
    (∫ h, ∫ z, logCoshRec ((p.val + 1) + ((k - p.val) + 1))
      (parisiResponseSplitMasses ms p) (parisiResponseSplitVars ξ qs p v) (h + z)
      ∂gaussianReal 0 (parisiVar ξ qs 0) ∂μh) =
      ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  apply integral_congr_ae (.of_forall fun h => ?_)
  simp_rw [logCoshRec_eq_coleHopfIterate_terminal_zero _ _
    (parisiResponseSplitMasses_pos ms p hm),
    coleHopfIterate_parisiResponseSplit_eq_rootSuffix ξ ms qs p hv]
  rw [closedParisiX₀_translate, coleHopfIterate_succ]
  change _ = coleHopf 0 (parisiVar ξ qs 0) (parisiRootSuffix ξ ms qs) h
  rw [coleHopf_zero]

/-- The actual mirror moment supplies the slope gap in (14.331).
The explicit coupling yields its square divided by two as the gain. -/
theorem randomFieldPairSiteY₀_parisi_outer_split_le_gain {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) {w : ℝ}
    (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) (u : ℝ) :
    let β := parisiLeftUSpatialMoment 1 μh ξ ms qs p w - u
    let vs := parisiResponseSplitVars ξ qs p
      (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w)
    randomFieldPairSiteY₀ μh (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p))
        (parisiVar ξ qs 0) vs (-β) (couplingFactorSgn 1 (p.val + 2) 0)
        (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) + β * u ≤
      2 * (∫ h, closedParisiX₀ ξ ms qs h ∂μh) - β ^ 2 / 2 := by
  have hv : deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w ∈
      Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p)) :=
    ⟨sub_nonneg.2 hw.2, sub_le_self _ hw.1⟩
  have hh := randomFieldPairSiteY₀_coupling_zero_le_gain hμ
    (parisiResponseSplitMasses ms p) (parisiResponseSplitMasses_monotone ms p hm)
    (parisiResponseSplitMasses_pos ms p hm) (parisiResponseSplitMasses_le_one ms p hm)
    (parisiVar ξ qs 0)
    (parisiResponseSplitVars ξ qs p (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - w))
    (τ := p.val + 2) (by omega) u
  dsimp only at hh ⊢
  rw [show p.val + 2 - 1 = p.val + 1 by omega,
    integral_cascadeTiltTanhSq_parisi_split_eq_left_moment ξ ms qs p hm hw,
    integral_logCoshRec_parisiResponseSplit_eq_closedParisiX₀ μh ξ ms qs p hm hv] at hh
  exact hh

/-- The actual coupled one-site value for the time-dependent mirror
split. Both replicas use the same external-field coordinate. -/
noncomputable def parisiOuterCouplingValue (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t u lam : ℝ) : ℝ :=
  randomFieldPairSiteY₀ μh (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p))
    (parisiVar ξ qs 0)
    (parisiResponseSplitVars ξ qs p
      (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - t * (deriv ξ u - deriv ξ (qs p))))
    lam (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))

/-- The time-dependent mirror Gaussian coordinate stays in its
admissible closed variance interval, including terminal splits. -/
theorem parisi_outer_time_variance_mem_Icc {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (hq : ParisiQAdmissible qs)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    t * (deriv ξ u - deriv ξ (qs p)) ∈
      Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p)) := by
  have hR := qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (p.val + 2)
  have hw := mapsTo_parisi_outer_variance_coordinate hξ (hq.mem_Icc p) hR hu
  exact ⟨mul_nonneg ht.1 hw.1, (mul_le_of_le_one_left hw.1 ht.2).trans hw.2⟩

/-- The mirror coupling derivative is the concrete time-dependent U
moment appearing in the critical response gap. -/
theorem hasDerivAt_parisiOuterCouplingValue_zero {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμ : Integrable id μh) {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    HasDerivAt (parisiOuterCouplingValue μh ξ ms qs p t u)
      (parisiLeftUSpatialMoment 1 μh ξ ms qs p (t * (deriv ξ u - deriv ξ (qs p)))) 0 :=
  hasDerivAt_randomFieldPairSiteY₀_parisi_outer_split_zero hμ ξ ms qs p hm
    (parisi_outer_time_variance_mem_Icc hξ qs p hq ht hu)

/-- The time-dependent mirror coupling gives the square of the actual
response gap divided by two as a one-site gain. -/
theorem parisiOuterCouplingValue_le_gain {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2))) :
    let β := parisiLeftResponseGap μh ξ ms qs p t u
    parisiOuterCouplingValue μh ξ ms qs p t u (-β) + β * u ≤
      2 * (∫ h, closedParisiX₀ ξ ms qs h ∂μh) - β ^ 2 / 2 :=
  randomFieldPairSiteY₀_parisi_outer_split_le_gain hμ ξ ms qs p hm
    (parisi_outer_time_variance_mem_Icc hξ qs p hq ht hu) u

/-- The uniform critical mirror response gap gives the explicit
quadratic one-site coupling penalty. Tolerance and radius are selected before
all MIN parameters and times. A finite-volume coupled comparison is still
required to turn this estimate into the main pressure estimate. -/
theorem exists_uniform_parisi_outer_coupling_gain {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
        ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
        IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
          (parisiParameterDomain k) (ms, qs) →
        randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
        ∀ t ∈ Icc (0 : ℝ) t₀, ∀ p : Fin (k + 1),
          ∀ u ∈ Icc (qs p) (qExt qs (p.val + 2)), u - qs p ≤ ρ →
            let β := parisiLeftResponseGap μh ξ ms qs p t u
            parisiOuterCouplingValue μh ξ ms qs p t u (-β) + β * u ≤
              2 * (∫ h, closedParisiX₀ ξ ms qs h ∂μh) -
                (1 - t₀) ^ 2 * (u - qs p) ^ 2 / 32 := by
  obtain ⟨ε, hε, ρ, hρ, hgap⟩ := exists_uniform_parisi_critical_response_gap hξ hμ ht₀
  refine ⟨ε, hε, ρ, hρ, ?_⟩
  intro k ms qs hm hmin hfull hnear t ht p u hu hdist
  have hfirst : Integrable id μh := hμ.integrable_id
  have hg := (hgap k ms qs hm hmin hfull hnear t ht).2.2 p u hu hdist
  have hgain := parisiOuterCouplingValue_le_gain hfirst hξ ms qs p hm hmin.1
    ⟨ht.1, ht.2.trans ht₀.2.le⟩ hu
  dsimp only at hgain ⊢
  have hnonneg : 0 ≤ (1 - t₀) / 4 * (u - qs p) :=
    mul_nonneg (by linarith [ht₀.2]) (sub_nonneg.2 hu.1)
  have hsquare := mul_self_le_mul_self hnonneg (show
      (1 - t₀) / 4 * (u - qs p) ≤ -parisiLeftResponseGap μh ξ ms qs p t u by linarith)
  nlinarith

/-- The original inner-orientation coupled value uses the same actual
matched split, with variance v=t(ξ'(q_R)−ξ'(u)). -/
noncomputable def parisiInnerCouplingValue (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (t u lam : ℝ) : ℝ :=
  randomFieldPairSiteY₀ μh (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p.castSucc))
    (parisiVar ξ qs 0)
    (parisiResponseSplitVars ξ qs p.castSucc (t * (deriv ξ (qs p.succ) - deriv ξ u)))
    lam (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))

/-- The time-dependent inner Gaussian coordinate stays in its closed
admissible variance interval. -/
theorem parisi_inner_time_variance_mem_Icc {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (p : Fin k) (hq : ParisiQAdmissible qs)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p.castSucc) (qs p.succ)) :
    t * (deriv ξ (qs p.succ) - deriv ξ u) ∈
      Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)) := by
  have hv := mapsTo_parisi_variance_coordinate hξ (hq.mem_Icc p.castSucc) (hq.mem_Icc p.succ) hu
  exact ⟨mul_nonneg ht.1 hv.1, (mul_le_of_le_one_left hv.1 ht.2).trans hv.2⟩

/-- The inner coupling derivative is identified with the actual
time-dependent U moment, after differentiation under the site-field law. -/
theorem hasDerivAt_parisiInnerCouplingValue_zero {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμ : Integrable id μh) {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p.castSucc) (qs p.succ)) :
    HasDerivAt (parisiInnerCouplingValue μh ξ ms qs p t u)
      (parisiRightUSpatialMoment 1 μh ξ ms qs p (t * (deriv ξ (qs p.succ) - deriv ξ u))) 0 := by
  have hd := hasDerivAt_randomFieldPairSiteY₀_coupling_zero hμ
    (parisiResponseSplitMasses ms p.castSucc) (parisiResponseSplitMasses_pos ms p.castSucc hm)
    (parisiResponseSplitMasses_le_one ms p.castSucc hm) (parisiVar ξ qs 0)
    (parisiResponseSplitVars ξ qs p.castSucc (t * (deriv ξ (qs p.succ) - deriv ξ u)))
    (τ := p.val + 2) (by omega)
  rw [show p.val + 2 - 1 = p.val + 1 by omega,
    integral_cascadeTiltTanhSq_parisi_split_eq_right_moment ξ ms qs p hm
      (parisi_inner_time_variance_mem_Icc hξ qs p hq ht hu)] at hd
  exact hd

/-- The original inner-orientation coupling gives the square of its
concrete response gap divided by two as the one-site gain. -/
theorem parisiInnerCouplingValue_le_gain {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p.castSucc) (qs p.succ)) :
    let β := parisiRightResponseGap μh ξ ms qs p t u
    parisiInnerCouplingValue μh ξ ms qs p t u (-β) + β * u ≤
      2 * (∫ h, closedParisiX₀ ξ ms qs h ∂μh) - β ^ 2 / 2 := by
  have hR : qExt qs (p.castSucc.val + 2) = qs p.succ :=
    qExt_succ_of_lt qs p.succ.isLt
  have hv := parisi_inner_time_variance_mem_Icc hξ qs p hq ht hu
  have hw : deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) -
      t * (deriv ξ (qs p.succ) - deriv ξ u) ∈
      Icc (0 : ℝ) (deriv ξ (qExt qs (p.castSucc.val + 2)) - deriv ξ (qs p.castSucc)) := by
    rw [hR]
    exact ⟨sub_nonneg.2 hv.2, sub_le_self _ hv.1⟩
  have hh := randomFieldPairSiteY₀_parisi_outer_split_le_gain hμ ξ ms qs p.castSucc hm hw u
  dsimp only at hh ⊢
  rw [parisiLeftUSpatialMoment_castSucc_complement_eq_right, hR, sub_sub_cancel] at hh
  exact hh

/-- The inner critical response estimate supplies a uniform explicit
quadratic one-site coupling penalty. The constants precede all MIN parameters
and times; a finite-volume coupled comparison remains a separate theorem. -/
theorem exists_uniform_parisi_inner_coupling_gain {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
        ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
        IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
          (parisiParameterDomain k) (ms, qs) →
        randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
        ∀ t ∈ Icc (0 : ℝ) t₀, ∀ p : Fin k,
          ∀ u ∈ Icc (qs p.castSucc) (qs p.succ), qs p.succ - u ≤ ρ →
            let β := parisiRightResponseGap μh ξ ms qs p t u
            parisiInnerCouplingValue μh ξ ms qs p t u (-β) + β * u ≤
              2 * (∫ h, closedParisiX₀ ξ ms qs h ∂μh) -
                (1 - t₀) ^ 2 * (u - qs p.succ) ^ 2 / 32 := by
  obtain ⟨ε, hε, ρ, hρ, hgap⟩ := exists_uniform_parisi_critical_response_gap hξ hμ ht₀
  refine ⟨ε, hε, ρ, hρ, ?_⟩
  intro k ms qs hm hmin hfull hnear t ht p u hu hdist
  have hg := (hgap k ms qs hm hmin hfull hnear t ht).2.1 p u hu hdist
  have hgain := parisiInnerCouplingValue_le_gain hμ.integrable_id hξ ms qs p hm hmin.1
    ⟨ht.1, ht.2.trans ht₀.2.le⟩ hu
  dsimp only at hgain ⊢
  have hnonneg : 0 ≤ (1 - t₀) / 4 * (qs p.succ - u) :=
    mul_nonneg (by linarith [ht₀.2]) (sub_nonneg.2 hu.2)
  have hsquare := mul_self_le_mul_self hnonneg hg
  nlinarith

end SpinGlass
