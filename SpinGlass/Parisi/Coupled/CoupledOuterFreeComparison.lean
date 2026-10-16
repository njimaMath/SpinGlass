import SpinGlass.Parisi.Coupled.CoupledOuterFreeBound

/-!
# The physical pressure comparison at a free outer mass

The auxiliary pressure is independent of the inserted positive mass.
The coupled mass list permits variation on both sides of the old mass,
even when the scalar split mass list is no longer monotone.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable def parisiOuterFreePressure {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t u b : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec (k + 2) (parisiOuterFreeCoupledMasses ms p b)
    (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) _ (fun i =>
      parisiDrivenSplitVars ξ qs p t u (parisiSplitIndex p i) +
        parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i)))
    (coupledG N u a
      (coupledDrivenVarianceFactor (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
        (couplingFactorSgn 1 (p.val + 2) 0))
      (coupledAuxVarianceFactor (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
        (couplingFactorSgn 1 (p.val + 2) 0))
      (fun i => coupledDrivenVarianceFactor
        (parisiDrivenSplitVars ξ qs p t u (parisiSplitIndex p i))
        (parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i))
        (couplingFactorSgn 1 (p.val + 2) (i.val + 1)))
      (fun i => coupledAuxVarianceFactor
        (parisiDrivenSplitVars ξ qs p t u (parisiSplitIndex p i))
        (parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i))
        (couplingFactorSgn 1 (p.val + 2) (i.val + 1))) (parisiTimeProfile ξ t) G₀ 1 θ)).toReal
    ∂Pm.prod (rootMarksLaw N (parisiDrivenRootVar ξ qs t + parisiAuxRootVar ξ qs t))

/-- The actual physical pressure at a free positive mass is the
original constrained auxiliary pressure plus its terminal normalization. -/
theorem parisiOuterFreePressure_eq_original {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t u : ℝ)
    (hm : ParisiMAdmissible ms) {b : ℝ} (hb : 0 < b)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiOuterFreePressure ξ ms qs p t u b G₀ a =
      parisiAuxPairPressure ξ ms qs (p.val + 1) t u G₀ a + parisiAuxTerminalVar ξ qs t := by
  have hi := integral_log_cascadeRec_pairHamG_auxVarianceShare_eq Pm
    (parisiOuterFreeCoupledMasses ms p b) (constraintR N u) G₀.U G₀.measU 0 a
    (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
    (fun i => parisiDrivenSplitVars ξ qs p t u (parisiSplitIndex p i))
    (fun i => parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i))
    (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))
  unfold parisiOuterFreePressure coupledG parisiAuxPairPressure
  simp only [sub_self, Real.sqrt_zero, Real.sqrt_one, zero_smul, one_smul, zero_add]
  rw [hi]
  have hrec (θ : Ω × (Fin N × Fin 2 → ℝ)) :=
    cascadeRec_parisi_outer_free_aux_eq ξ ms qs p t hb.ne' (constraintR N u) (G₀.U θ.1) 0 a θ.2
  simp_rw [hrec]
  have hcpos : ∃ σ, 0 < constraintR N u σ :=
    hreach.elim fun σ hσ => ⟨σ, constraintR_pos_of_overlap_eq N hσ⟩
  have hlog (θ : Ω × (Fin N × Fin 2 → ℝ)) :=
    log_cascadeRec_parisi_aux_eq (τ := p.val + 1) ξ ms qs t hm (by omega) (by omega)
      (constraintR_nonneg N u) hcpos (G₀.U θ.1) 0 a θ.2
  have hint := integrable_log_cascadeRec_parisi_aux ξ ms qs (p.val + 1) t u hm G₀ a hreach
  simp only [Nat.add_sub_cancel] at hlog hint ⊢
  simp_rw [hlog]
  rw [integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- The finite-volume coupled bound uses the freely varied physical
mass list and its exact correction, without scalar mass monotonicity. -/
theorem parisiOuterFreePressure_le_siteValue {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u b : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (hb0 : 0 < b) (hbL : mExt ms p.val ≤ b) (hbR : b ≤ 2 * mExt ms (p.val + 1))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiOuterFreePressure ξ ms qs p t u b G₀ a ≤
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ j, pairSiteY₀
        (parisiOuterFreeCoupledMasses ms p b) (parisiVar ξ qs 0)
        (parisiOuterFreeTotalVars ξ qs p (t * (deriv ξ u - deriv ξ (qs p))))
        lam (fun l => a (j, l)) (couplingFactorSgn 1 (p.val + 2) 0)
        (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) - lam * u -
          t * (parisiCorrection ξ ms qs + (b - mExt ms (p.val + 1)) * (parisiTheta ξ u - parisiTheta ξ (qs p))) := by
  have huExt := hu
  have hb2 : b ≤ 2 := by nlinarith [mExt_le_one (fun i => (hm.2.2 i).le) (p.val + 1)]
  have hC (i : Fin (k + 2)) (l l' : Fin 2) :=
    parisiDrivenSplitVars_mul_gram hξ qs p hq ht.1 huExt (parisiSplitIndex p i) l l'
  simp only [parisiSplitIndex_val] at hC
  have hb := coupled_bound_varianceShare_sameFactors_siteField hN (parisiTimeProfile ξ t)
    (parisiSplitCouplingRho qs p u) u (parisiSplitCouplingRho_zero qs p u)
    (S := Icc (0 : ℝ) 1) (parisiSplitCouplingRho_mem_Icc qs p hq huExt)
    (fun x _ q hq' => parisiTimeProfile_tangent_line_le hξ ht.1 hq' x)
    (deriv_parisiTimeProfile_zero hξ t) G₀
    (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
    (fun i => parisiDrivenSplitVars ξ qs p t u (parisiSplitIndex p i))
    (fun i => parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i))
    (couplingFactorSgn 1 (p.val + 2) 0) (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))
    (parisiDrivenRootVar_mul_gram hξ qs p hq ht.1 huExt) hC a lam
    (parisiOuterFreeCoupledMasses ms p b) (parisiOuterFreeCoupledMasses_monotone ms p hm hbL hbR)
    (parisiOuterFreeCoupledMasses_pos ms p hm hb0) (parisiOuterFreeCoupledMasses_le_one ms p hm hb2) hreach
  have htop := pairDiagDefect_parisiSplitCouplingRho_top (parisiTimeProfile ξ t) qs p u
  rw [parisiSplitSize_eq p] at htop
  have hv : (fun i : Fin (k + 2) =>
      parisiDrivenSplitVars ξ qs p t u (parisiSplitIndex p i) +
        parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i)) =
      parisiOuterFreeTotalVars ξ qs p (t * (deriv ξ u - deriv ξ (qs p))) := by
    funext i
    have he := congrFun (parisiDrivenSplitVars_add_outerAux_eq hξ qs p hq ht huExt)
      (parisiSplitIndex p i)
    simpa only [parisiOuterFreeTotalVars] using he
  rw [htop, coupledLevelSum_parisiOuterFree_eq_correction, add_zero,
    parisiDrivenRootVar_add_aux_eq ξ qs ht, hv] at hb
  simpa only [parisiOuterFreePressure, parisiDrivenRootVar_add_aux_eq ξ qs ht, hv] using hb

/-- Finite first field moment suffices for the actual free-mass
one-site value at every coupling parameter. -/
theorem integrable_pairSiteY₀_parisiOuterFree_externalField {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμ : Integrable id μh) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) {b : ℝ} (hb0 : 0 < b) (hb2 : b ≤ 2)
    (ξ : ℝ → ℝ) (w lam : ℝ) :
    Integrable (fun h : ℝ => pairSiteY₀ (parisiOuterFreeCoupledMasses ms p b)
      (parisiVar ξ qs 0) (parisiOuterFreeTotalVars ξ qs p w) lam (fun _ => h) (couplingFactorSgn 1 (p.val + 2) 0)
      (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))) μh := by
  have hpos := parisiLevelMasses_splitParisiMassLeft_pos ms p hm hb0
  have hY : Integrable (fun h : ℝ => pairSiteY₀ (parisiOuterFreeCoupledMasses ms p b)
      (parisiVar ξ qs 0) (parisiOuterFreeTotalVars ξ qs p w) 0 (fun _ => h) (couplingFactorSgn 1 (p.val + 2) 0)
      (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))) μh := by
    have hi := (integrable_parisiOuterFreeSplit_externalField hμ ξ ms qs p w b).integral_prod_left.const_mul 2
    apply hi.congr (.of_forall fun h => ?_)
    rw [parisiOuterFreeCoupledMasses_eq_halveBelow]
    have hh := pairSiteY₀_coupling_zero (parisiLevelMasses (splitParisiMassLeft ms p b)) hpos
      (parisiVar ξ qs 0) (parisiOuterFreeTotalVars ξ qs p w) h (τ := p.val + 2) (by omega)
    simp only [show p.val + 2 - 1 = p.val + 1 by omega,
      logCoshRec_eq_coleHopfIterate_terminal_zero _ _ hpos,
      coleHopfIterate_parisiOuterFree_eq_split ξ ms qs p w b] at hh
    exact hh.symm
  exact integrable_pairSiteY₀_commonField_of_integrable_at_zero
    (parisiOuterFreeCoupledMasses ms p b) (parisiOuterFreeCoupledMasses_pos ms p hm hb0)
    (parisiOuterFreeCoupledMasses_le_one ms p hm hb2) (parisiVar ξ qs 0) (parisiOuterFreeTotalVars ξ qs p w)
    (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) hY lam

/-- The free-mass comparison after averaging independent site fields
and removing the actual terminal auxiliary variance. -/
theorem randomFieldParisiAuxPairPressure_outer_free_le_siteValue {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u b : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (hb0 : 0 < b) (hbL : mExt ms p.val ≤ b) (hbR : b ≤ 2 * mExt ms (p.val + 1))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (lam : ℝ) (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 1) t u G₀ ≤
      2 * Real.log 2 + parisiOuterFreeCouplingValue μh ξ ms qs p
        (t * (deriv ξ u - deriv ξ (qs p))) b lam - lam * u -
        t * (parisiCorrection ξ ms qs + (b - mExt ms (p.val + 1)) * (parisiTheta ξ u - parisiTheta ξ (qs p))) -
        parisiAuxTerminalVar ξ qs t := by
  let v := t * (deriv ξ u - deriv ξ (qs p))
  let C := t * (parisiCorrection ξ ms qs + (b - mExt ms (p.val + 1)) * (parisiTheta ξ u - parisiTheta ξ (qs p)))
  let F := fun h : ℝ => pairSiteY₀ (parisiOuterFreeCoupledMasses ms p b)
    (parisiVar ξ qs 0) (parisiOuterFreeTotalVars ξ qs p v) lam (fun _ => h)
    (couplingFactorSgn 1 (p.val + 2) 0) (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))
  have hb2 : b ≤ 2 := by nlinarith [mExt_le_one (fun i => (hm.2.2 i).le) (p.val + 1)]
  have hF : Integrable F μh := integrable_pairSiteY₀_parisiOuterFree_externalField hμ
    ms qs p hm hb0 hb2 ξ v lam
  have hAvg := integrable_externalFieldVec_siteAverage hF N
  have hLeft := integrable_parisiSplitPressure_externalField hμ ξ ms qs p t u hm G₀
    (parisiOuterAuxSplitVars ξ qs p t) hreach
  have hRhs : Integrable (fun hVec : Fin N → ℝ =>
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) - lam * u - C)
      (externalFieldVecLaw N μh) :=
    (((integrable_const (2 * Real.log 2)).add hAvg).sub (integrable_const (lam * u))).sub (integrable_const C)
  have hpoint (hVec : Fin N → ℝ) :
      parisiSplitPressure ξ ms qs p t u G₀ (parisiOuterAuxSplitVars ξ qs p t)
        (sharedReplicaSiteField hVec) ≤
        2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) - lam * u - C := by
    have hh := parisiOuterFreePressure_le_siteValue hN hξ ms qs p hm hq ht hu hb0 hbL hbR
      G₀ (sharedReplicaSiteField hVec) lam hreach
    rw [parisiOuterFreePressure_eq_original hN ξ ms qs p t u hm hb0 G₀
      (sharedReplicaSiteField hVec) hreach] at hh
    rw [parisiSplitPressure_outer_eq_original hN ξ ms qs p u hm ht G₀
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
  change randomFieldParisiSplitPressure μh ξ ms qs p t u G₀
    (parisiOuterAuxSplitVars ξ qs p t) ≤
      2 * Real.log 2 + parisiOuterFreeCouplingValue μh ξ ms qs p v b lam - lam * u - C at hb
  rw [randomFieldParisiAuxPairPressure_outer_eq hμ hN ξ ms qs p u hm ht G₀ hreach]
  dsimp only [v, C] at hb
  linarith

/-- The actual pressure is bounded by the differentiable scalar
mass family for every admissible free outer mass. -/
theorem randomFieldParisiAuxPairPressure_outer_free_le_scalarBound {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u b : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (hb0 : 0 < b) (hbL : mExt ms p.val ≤ b) (hbR : b ≤ 2 * mExt ms (p.val + 1))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 1) t u G₀ ≤
      parisiOuterFreeScalarBound μh ξ ms qs p t u b := by
  have hb := randomFieldParisiAuxPairPressure_outer_free_le_siteValue hμ hN hξ ms qs p
    hm hq ht hu hb0 hbL hbR G₀ 0 hreach
  rw [parisiOuterFreeCouplingValue_zero hμ ξ ms qs p hm hb0] at hb
  simpa only [zero_mul, sub_zero, parisiOuterFreeScalarBound] using hb

end SpinGlass
