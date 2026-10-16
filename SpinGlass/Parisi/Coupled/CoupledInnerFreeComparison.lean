import SpinGlass.Parisi.Coupled.CoupledInnerFreeBound

/-!
# The physical pressure comparison at a free inner mass

The auxiliary pressure is independent of the inserted positive mass.
The coupled mass list permits variation on both sides of the old mass,
even when the scalar split mass list is no longer monotone.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable def parisiInnerFreePressure {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (t u b : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec (k + 2) (parisiInnerFreeCoupledMasses ms p b)
    (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) _ (fun i =>
      parisiDrivenSplitVars ξ qs p.castSucc t u (parisiSplitIndex p.castSucc i) +
        parisiInnerAuxSplitVars ξ qs p.castSucc t (parisiSplitIndex p.castSucc i)))
    (coupledG N u a
      (coupledDrivenVarianceFactor (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
        (couplingFactorSgn 1 (p.val + 2) 0))
      (coupledAuxVarianceFactor (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
        (couplingFactorSgn 1 (p.val + 2) 0))
      (fun i => coupledDrivenVarianceFactor
        (parisiDrivenSplitVars ξ qs p.castSucc t u (parisiSplitIndex p.castSucc i))
        (parisiInnerAuxSplitVars ξ qs p.castSucc t (parisiSplitIndex p.castSucc i))
        (couplingFactorSgn 1 (p.val + 2) (i.val + 1)))
      (fun i => coupledAuxVarianceFactor
        (parisiDrivenSplitVars ξ qs p.castSucc t u (parisiSplitIndex p.castSucc i))
        (parisiInnerAuxSplitVars ξ qs p.castSucc t (parisiSplitIndex p.castSucc i))
        (couplingFactorSgn 1 (p.val + 2) (i.val + 1))) (parisiTimeProfile ξ t) G₀ 1 θ)).toReal
    ∂Pm.prod (rootMarksLaw N (parisiDrivenRootVar ξ qs t + parisiAuxRootVar ξ qs t))

/-- The actual physical pressure at a free positive mass is the
original constrained auxiliary pressure plus its terminal normalization. -/
theorem parisiInnerFreePressure_eq_original {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (t u : ℝ)
    (hm : ParisiMAdmissible ms) {b : ℝ} (hb : 0 < b)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiInnerFreePressure ξ ms qs p t u b G₀ a =
      parisiAuxPairPressure ξ ms qs (p.val + 2) t u G₀ a + parisiAuxTerminalVar ξ qs t := by
  have hi := integral_log_cascadeRec_pairHamG_auxVarianceShare_eq Pm
    (parisiInnerFreeCoupledMasses ms p b) (constraintR N u) G₀.U G₀.measU 0 a
    (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
    (fun i => parisiDrivenSplitVars ξ qs p.castSucc t u (parisiSplitIndex p.castSucc i))
    (fun i => parisiInnerAuxSplitVars ξ qs p.castSucc t (parisiSplitIndex p.castSucc i))
    (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))
  unfold parisiInnerFreePressure coupledG parisiAuxPairPressure
  simp only [sub_self, Real.sqrt_zero, Real.sqrt_one, zero_smul, one_smul, zero_add]
  rw [hi]
  have hrec (θ : Ω × (Fin N × Fin 2 → ℝ)) :=
    cascadeRec_parisi_inner_free_aux_eq ξ ms qs p t hb.ne' (constraintR N u) (G₀.U θ.1) 0 a θ.2
  simp_rw [hrec]
  have hcpos : ∃ σ, 0 < constraintR N u σ :=
    hreach.elim fun σ hσ => ⟨σ, constraintR_pos_of_overlap_eq N hσ⟩
  have hlog (θ : Ω × (Fin N × Fin 2 → ℝ)) :=
    log_cascadeRec_parisi_aux_eq (τ := p.val + 2) ξ ms qs t hm (by omega) (by omega)
      (constraintR_nonneg N u) hcpos (G₀.U θ.1) 0 a θ.2
  have hint := integrable_log_cascadeRec_parisi_aux ξ ms qs (p.val + 2) t u hm G₀ a hreach
  simp only [show p.val + 2 - 1 = p.val + 1 by omega] at hlog hint ⊢
  simp_rw [hlog]
  rw [integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- The finite-volume coupled bound uses the freely varied physical
mass list and its exact correction, without scalar mass monotonicity. -/
theorem parisiInnerFreePressure_le_siteValue {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u b : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p.castSucc) (qs p.succ))
    (hbL : ms p / 2 ≤ b) (hbR : b ≤ mExt ms (p.val + 2))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiInnerFreePressure ξ ms qs p t u b G₀ a ≤
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ j, pairSiteY₀
        (parisiInnerFreeCoupledMasses ms p b) (parisiVar ξ qs 0)
        (parisiInnerFreeTotalVars ξ qs p (t * (deriv ξ (qs p.succ) - deriv ξ u)))
        lam (fun l => a (j, l)) (couplingFactorSgn 1 (p.val + 2) 0)
        (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) - lam * u -
          t * (parisiCorrection ξ ms qs + (b - ms p) * (parisiTheta ξ (qs p.succ) - parisiTheta ξ u)) := by
  have hR : qExt qs (p.castSucc.val + 2) = qs p.succ := qExt_succ_of_lt qs p.succ.isLt
  have huExt : u ∈ Icc (qs p.castSucc) (qExt qs (p.castSucc.val + 2)) := by
    rw [hR]
    exact hu
  have hb0 : 0 < b := by linarith [hm.2.1 p]
  have hb1 : b ≤ 1 := hbR.trans (mExt_le_one (fun i => (hm.2.2 i).le) _)
  have hC (i : Fin (k + 2)) (l l' : Fin 2) :=
    parisiDrivenSplitVars_mul_gram hξ qs p.castSucc hq ht.1 huExt (parisiSplitIndex p.castSucc i) l l'
  simp only [parisiSplitIndex_val, Fin.val_castSucc] at hC
  have hb := coupled_bound_varianceShare_sameFactors_siteField hN (parisiTimeProfile ξ t)
    (parisiSplitCouplingRho qs p.castSucc u) u (parisiSplitCouplingRho_zero qs p.castSucc u)
    (S := Icc (0 : ℝ) 1) (parisiSplitCouplingRho_mem_Icc qs p.castSucc hq huExt)
    (fun x _ q hq' => parisiTimeProfile_tangent_line_le hξ ht.1 hq' x)
    (deriv_parisiTimeProfile_zero hξ t) G₀
    (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
    (fun i => parisiDrivenSplitVars ξ qs p.castSucc t u (parisiSplitIndex p.castSucc i))
    (fun i => parisiInnerAuxSplitVars ξ qs p.castSucc t (parisiSplitIndex p.castSucc i))
    (couplingFactorSgn 1 (p.val + 2) 0) (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))
    (parisiDrivenRootVar_mul_gram hξ qs p.castSucc hq ht.1 huExt) hC a lam
    (parisiInnerFreeCoupledMasses ms p b) (parisiInnerFreeCoupledMasses_monotone ms p hm hbL hbR)
    (parisiInnerFreeCoupledMasses_pos ms p hm hb0) (parisiInnerFreeCoupledMasses_le_one ms p hm hb1) hreach
  have htop := pairDiagDefect_parisiSplitCouplingRho_top (parisiTimeProfile ξ t) qs p.castSucc u
  rw [parisiSplitSize_eq p.castSucc] at htop
  have hv : (fun i : Fin (k + 2) =>
      parisiDrivenSplitVars ξ qs p.castSucc t u (parisiSplitIndex p.castSucc i) +
        parisiInnerAuxSplitVars ξ qs p.castSucc t (parisiSplitIndex p.castSucc i)) =
      parisiInnerFreeTotalVars ξ qs p (t * (deriv ξ (qs p.succ) - deriv ξ u)) := by
    funext i
    have he := congrFun (parisiDrivenSplitVars_add_innerAux_eq hξ qs p.castSucc hq ht huExt)
      (parisiSplitIndex p.castSucc i)
    simpa only [parisiInnerFreeTotalVars, hR] using he
  rw [htop, coupledLevelSum_parisiInnerFree_eq_correction, add_zero,
    parisiDrivenRootVar_add_aux_eq ξ qs ht, hv] at hb
  simpa only [parisiInnerFreePressure, parisiDrivenRootVar_add_aux_eq ξ qs ht, hv] using hb

/-- Finite first field moment suffices for the actual free-mass
one-site value at every coupling parameter. -/
theorem integrable_pairSiteY₀_parisiInnerFree_externalField {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμ : Integrable id μh) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1)
    (ξ : ℝ → ℝ) (vs : Fin (k + 2) → ℝ≥0) (lam : ℝ) :
    Integrable (fun h : ℝ => pairSiteY₀ (parisiInnerFreeCoupledMasses ms p b)
      (parisiVar ξ qs 0) vs lam (fun _ => h) (couplingFactorSgn 1 (p.val + 2) 0)
      (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))) μh := by
  have hpos := parisiLevelMasses_splitParisiMassRight_pos ms p hm hb0
  have hle := parisiLevelMasses_splitParisiMassRight_le_one ms p hm hb1
  have hY : Integrable (fun h : ℝ => pairSiteY₀ (parisiInnerFreeCoupledMasses ms p b)
      (parisiVar ξ qs 0) vs 0 (fun _ => h) (couplingFactorSgn 1 (p.val + 2) 0)
      (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))) μh := by
    have hi := (integrable_integral_logCoshRec_externalField hμ
      (parisiLevelMasses (splitParisiMassRight ms p b)) vs hpos hle (parisiVar ξ qs 0)).const_mul 2
    apply hi.congr (.of_forall fun h => ?_)
    have hh := pairSiteY₀_coupling_zero (parisiLevelMasses (splitParisiMassRight ms p b)) hpos
      (parisiVar ξ qs 0) vs h (τ := p.val + 2) (by omega)
    simpa only [parisiInnerFreeCoupledMasses, show p.val + 2 - 1 = p.val + 1 by omega] using hh.symm
  exact integrable_pairSiteY₀_commonField_of_integrable_at_zero
    (parisiInnerFreeCoupledMasses ms p b) (parisiInnerFreeCoupledMasses_pos ms p hm hb0)
    (parisiInnerFreeCoupledMasses_le_one ms p hm hb1) (parisiVar ξ qs 0) vs
    (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) hY lam

/-- The free-mass comparison after averaging independent site fields
and removing the actual terminal auxiliary variance. -/
theorem randomFieldParisiAuxPairPressure_inner_free_le_siteValue {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u b : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p.castSucc) (qs p.succ))
    (hbL : ms p / 2 ≤ b) (hbR : b ≤ mExt ms (p.val + 2))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (lam : ℝ) (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 2) t u G₀ ≤
      2 * Real.log 2 + parisiInnerFreeCouplingValue μh ξ ms qs p
        (t * (deriv ξ (qs p.succ) - deriv ξ u)) b lam - lam * u -
        t * (parisiCorrection ξ ms qs + (b - ms p) * (parisiTheta ξ (qs p.succ) - parisiTheta ξ u)) -
        parisiAuxTerminalVar ξ qs t := by
  let v := t * (deriv ξ (qs p.succ) - deriv ξ u)
  let C := t * (parisiCorrection ξ ms qs + (b - ms p) * (parisiTheta ξ (qs p.succ) - parisiTheta ξ u))
  let F := fun h : ℝ => pairSiteY₀ (parisiInnerFreeCoupledMasses ms p b)
    (parisiVar ξ qs 0) (parisiInnerFreeTotalVars ξ qs p v) lam (fun _ => h)
    (couplingFactorSgn 1 (p.val + 2) 0) (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))
  have hb0 : 0 < b := by linarith [hm.2.1 p]
  have hb1 : b ≤ 1 := hbR.trans (mExt_le_one (fun i => (hm.2.2 i).le) _)
  have hF : Integrable F μh := integrable_pairSiteY₀_parisiInnerFree_externalField hμ
    ms qs p hm hb0 hb1 ξ (parisiInnerFreeTotalVars ξ qs p v) lam
  have hAvg := integrable_externalFieldVec_siteAverage hF N
  have hLeft := integrable_parisiSplitPressure_externalField hμ ξ ms qs p.castSucc t u hm G₀
    (parisiInnerAuxSplitVars ξ qs p.castSucc t) hreach
  have hRhs : Integrable (fun hVec : Fin N → ℝ =>
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) - lam * u - C)
      (externalFieldVecLaw N μh) :=
    (((integrable_const (2 * Real.log 2)).add hAvg).sub (integrable_const (lam * u))).sub (integrable_const C)
  have hpoint (hVec : Fin N → ℝ) :
      parisiSplitPressure ξ ms qs p.castSucc t u G₀ (parisiInnerAuxSplitVars ξ qs p.castSucc t)
        (sharedReplicaSiteField hVec) ≤
        2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) - lam * u - C := by
    have hh := parisiInnerFreePressure_le_siteValue hN hξ ms qs p hm hq ht hu hbL hbR
      G₀ (sharedReplicaSiteField hVec) lam hreach
    rw [parisiInnerFreePressure_eq_original hN ξ ms qs p t u hm hb0 G₀
      (sharedReplicaSiteField hVec) hreach] at hh
    rw [parisiSplitPressure_inner_eq_original hN ξ ms qs p u hm ht G₀
      (sharedReplicaSiteField hVec) hreach]
    exact hh
  have hb := integral_mono hLeft hRhs hpoint
  have hmean : (∫ hVec : Fin N → ℝ,
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) - lam * u - C
      ∂externalFieldVecLaw N μh) = 2 * Real.log 2 + (∫ h, F h ∂μh) - lam * u - C := by
    have ha := integral_add (integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)) hAvg
    have hs := integral_sub ((integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)).add hAvg)
      (integrable_const (lam * u))
    have hc := integral_sub
      (((integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)).add hAvg).sub
        (integrable_const (lam * u))) (integrable_const C)
    simp only [Pi.add_apply, Pi.sub_apply] at ha hs hc
    rw [hc, hs, ha, integral_externalFieldVec_siteAverage hF hN]
    simp only [integral_const, probReal_univ, one_smul]
  rw [hmean] at hb
  change randomFieldParisiSplitPressure μh ξ ms qs p.castSucc t u G₀
    (parisiInnerAuxSplitVars ξ qs p.castSucc t) ≤
      2 * Real.log 2 + parisiInnerFreeCouplingValue μh ξ ms qs p v b lam - lam * u - C at hb
  rw [randomFieldParisiAuxPairPressure_inner_eq hμ hN ξ ms qs p u hm ht G₀ hreach]
  dsimp only [v, C] at hb
  linarith

/-- The actual pressure is bounded by the differentiable scalar
mass family for every admissible free inner mass. -/
theorem randomFieldParisiAuxPairPressure_inner_free_le_scalarBound {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u b : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p.castSucc) (qs p.succ))
    (hbL : ms p / 2 ≤ b) (hbR : b ≤ mExt ms (p.val + 2))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 2) t u G₀ ≤
      parisiInnerFreeScalarBound μh ξ ms qs p t u b := by
  have hb0 : 0 < b := by linarith [hm.2.1 p]
  have hb := randomFieldParisiAuxPairPressure_inner_free_le_siteValue hμ hN hξ ms qs p
    hm hq ht hu hbL hbR G₀ 0 hreach
  rw [parisiInnerFreeCouplingValue_zero hμ ξ ms qs p hm hb0] at hb
  simpa only [zero_mul, sub_zero, parisiInnerFreeScalarBound] using hb

end SpinGlass
