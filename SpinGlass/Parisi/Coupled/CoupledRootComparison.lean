import SpinGlass.Parisi.Coupled.CoupledRootVariance
import SpinGlass.Parisi.Coupled.CoupledRootGain

/-!
# Finite-volume comparison for a positive root insertion

Every positive inserted mass has the same original physical auxiliary
pressure. Its driven covariance witnesses, one-site total laws and theta
correction are explicit. The inserted-mass limit therefore concerns only
the right side of the finite-volume comparison.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable def parisiRootSplitPressure {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u m : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec (k + 2) (parisiRootResponseMasses ms m)
    (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) _
      (fun i => parisiRootDrivenVars ξ qs t u i + parisiRootAuxVars ξ qs t i))
    (coupledG N u a
      (coupledDrivenVarianceFactor (parisiRootDrivenRootVar ξ qs t u) (parisiAuxRootVar ξ qs t)
        (couplingFactorSgn 1 1 0))
      (coupledAuxVarianceFactor (parisiRootDrivenRootVar ξ qs t u) (parisiAuxRootVar ξ qs t)
        (couplingFactorSgn 1 1 0))
      (fun i => coupledDrivenVarianceFactor (parisiRootDrivenVars ξ qs t u i) (parisiRootAuxVars ξ qs t i)
        (couplingFactorSgn 1 1 (i.val + 1)))
      (fun i => coupledAuxVarianceFactor (parisiRootDrivenVars ξ qs t u i) (parisiRootAuxVars ξ qs t i)
        (couplingFactorSgn 1 1 (i.val + 1))) (parisiTimeProfile ξ t) G₀ 1 θ)).toReal
    ∂Pm.prod (rootMarksLaw N (J := Fin 2 ⊕ Fin 2)
      (parisiRootDrivenRootVar ξ qs t u + parisiAuxRootVar ξ qs t))

/-- The positive root insertion is a deterministic auxiliary mark.
Transport and deletion identify its physical pressure with the original
cascade, including the proved terminal mass-one correction. -/
theorem parisiRootSplitPressure_eq_original {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u : ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiRootSplitPressure ξ ms qs t u m G₀ a =
      parisiAuxPairPressure ξ ms qs 1 t u G₀ a + parisiAuxTerminalVar ξ qs t := by
  have hi := integral_log_cascadeRec_pairHamG_auxVarianceShare_eq Pm
    (parisiRootResponseMasses ms m) (constraintR N u) G₀.U G₀.measU 0 a
    (parisiRootDrivenRootVar ξ qs t u) (parisiAuxRootVar ξ qs t)
    (parisiRootDrivenVars ξ qs t u) (parisiRootAuxVars ξ qs t)
    (couplingFactorSgn 1 1 0) (fun i => couplingFactorSgn 1 1 (i.val + 1))
  unfold parisiRootSplitPressure coupledG parisiAuxPairPressure
  simp only [sub_self, Real.sqrt_zero, Real.sqrt_one, zero_smul, one_smul, zero_add]
  rw [hi]
  have hrec (θ : Ω × (Fin N × Fin 2 → ℝ)) :=
    cascadeRec_parisi_root_aux_eq ξ ms qs t hm0 (constraintR N u) (G₀.U θ.1) 0 a θ.2
  simp_rw [hrec]
  have hcpos : ∃ σ, 0 < constraintR N u σ :=
    hreach.elim fun σ hσ => ⟨σ, constraintR_pos_of_overlap_eq N hσ⟩
  have hlog (θ : Ω × (Fin N × Fin 2 → ℝ)) :=
    log_cascadeRec_parisi_aux_eq (τ := 1) ξ ms qs t hm (by norm_num) (by omega)
      (constraintR_nonneg N u) hcpos (G₀.U θ.1) 0 a θ.2
  have hint := integrable_log_cascadeRec_parisi_aux ξ ms qs 1 t u hm G₀ a hreach
  simp only [Nat.sub_self, halveBelow_zero] at hlog hint ⊢
  simp_rw [hlog]
  rw [integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- The actual finite-volume initial-interval comparison at every
positive inserted mass. Its covariance and correction hypotheses are
discharged from the preserved profile and admissible original parameters. -/
theorem parisiRootSplitPressure_le_siteValue {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t u m : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) (qs 0)) (hm0 : 0 < m) (hmr : m ≤ mExt ms 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiRootSplitPressure ξ ms qs t u m G₀ a ≤
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ j, pairSiteY₀ (parisiRootResponseMasses ms m)
        (deriv ξ (qs 0) - deriv ξ 0 - t * (deriv ξ (qs 0) - deriv ξ u)).toNNReal
        (parisiRootResponseVars ξ qs (t * (deriv ξ (qs 0) - deriv ξ u))) lam (fun l => a (j, l))
        (couplingFactorSgn 1 1 0) (fun i => couplingFactorSgn 1 1 (i.val + 1)) - lam * u -
          t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ u)) := by
  have hm1 : m ≤ 1 := hmr.trans (mExt_le_one (fun i => (hm.2.2 i).le) _)
  have hb := coupled_bound_varianceShare_sameFactors_siteField hN (parisiTimeProfile ξ t)
    (parisiRootCouplingRho qs u) u (parisiRootCouplingRho_zero qs u)
    (S := Icc (0 : ℝ) 1) (parisiRootCouplingRho_mem_Icc qs hq hu)
    (fun x _ q hq' => parisiTimeProfile_tangent_line_le hξ ht.1 hq' x)
    (deriv_parisiTimeProfile_zero hξ t) G₀
    (parisiRootDrivenRootVar ξ qs t u) (parisiAuxRootVar ξ qs t)
    (parisiRootDrivenVars ξ qs t u) (parisiRootAuxVars ξ qs t)
    (couplingFactorSgn 1 1 0) (fun i => couplingFactorSgn 1 1 (i.val + 1))
    (parisiRootDrivenRootVar_mul_gram hξ qs hq ht.1 hu)
    (parisiRootDrivenVars_mul_gram hξ qs hq ht.1 hu) a lam (parisiRootResponseMasses ms m)
    (parisiRootResponseMasses_monotone ms hm hmr) (parisiRootResponseMasses_pos ms hm hm0)
    (parisiRootResponseMasses_le_one ms hm hm1) hreach
  change parisiRootSplitPressure ξ ms qs t u m G₀ a ≤
    2 * Real.log 2 + (1 / (N : ℝ)) * ∑ j, pairSiteY₀ (parisiRootResponseMasses ms m)
      (parisiRootDrivenRootVar ξ qs t u + parisiAuxRootVar ξ qs t)
      (fun i => parisiRootDrivenVars ξ qs t u i + parisiRootAuxVars ξ qs t i)
      lam (fun l => a (j, l)) (couplingFactorSgn 1 1 0)
      (fun i => couplingFactorSgn 1 1 (i.val + 1)) - lam * u -
      (1 / 2) * coupledLevelSum (parisiTimeProfile ξ t) (parisiRootCouplingRho qs u)
        (parisiRootResponseMasses ms m) +
      pairDiagDefect (parisiTimeProfile ξ t) u (fun l l' => parisiRootCouplingRho qs u l l' (k + 3)) at hb
  rw [parisiRootDrivenRootVar_add_aux_eq hξ qs hq ht hu, parisiRootDrivenVars_add_aux_eq ξ qs ht u,
    coupledLevelSum_parisiRoot_eq_correction, pairDiagDefect_parisiRootCouplingRho_top, add_zero] at hb
  exact hb

theorem integrable_pairSiteY₀_parisiRoot_externalField {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (v lam : ℝ) :
    Integrable (fun h => pairSiteY₀ (parisiRootResponseMasses ms m)
      (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal (parisiRootResponseVars ξ qs v)
      lam (fun _ => h) (couplingFactorSgn 1 1 0) (fun i => couplingFactorSgn 1 1 (i.val + 1))) μh := by
  have hpos := parisiRootResponseMasses_pos ms hm hm0
  have hle := parisiRootResponseMasses_le_one ms hm hm1
  have hY : Integrable (fun h => pairSiteY₀ (parisiRootResponseMasses ms m)
      (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal (parisiRootResponseVars ξ qs v)
      0 (fun _ => h) (couplingFactorSgn 1 1 0) (fun i => couplingFactorSgn 1 1 (i.val + 1))) μh := by
    have hi := (integrable_integral_logCoshRec_externalField hμ
      (parisiRootResponseMasses ms m) (parisiRootResponseVars ξ qs v) hpos hle
      (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal).const_mul 2
    apply hi.congr (.of_forall fun h => ?_)
    have hh := pairSiteY₀_coupling_zero (parisiRootResponseMasses ms m) hpos
      (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal (parisiRootResponseVars ξ qs v) h (τ := 1) (by norm_num)
    simpa only [Nat.sub_self, halveBelow_zero] using hh.symm
  exact integrable_pairSiteY₀_commonField_of_integrable_at_zero _ hpos hle _ _ _ _ hY lam

/-- The root comparison under the i.i.d. field law, expressed in the
original pressure normalization. The positive inserted mass is still free. -/
theorem randomFieldParisiAuxPairPressure_root_le_siteValue {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t u m : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) (qs 0)) (hm0 : 0 < m) (hmr : m ≤ mExt ms 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ)) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
      2 * Real.log 2 + parisiRootCouplingValue μh ξ ms qs
        (t * (deriv ξ (qs 0) - deriv ξ u)) m lam - lam * u -
        t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ u)) -
        parisiAuxTerminalVar ξ qs t := by
  let v := t * (deriv ξ (qs 0) - deriv ξ u)
  let C := t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ u))
  let F := fun h : ℝ => pairSiteY₀ (parisiRootResponseMasses ms m)
    (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal (parisiRootResponseVars ξ qs v)
    lam (fun _ => h) (couplingFactorSgn 1 1 0) (fun i => couplingFactorSgn 1 1 (i.val + 1))
  have hm1 : m ≤ 1 := hmr.trans (mExt_le_one (fun i => (hm.2.2 i).le) _)
  have hF : Integrable F μh := integrable_pairSiteY₀_parisiRoot_externalField hμ ξ ms qs hm hm0 hm1 v lam
  have hAvg := integrable_externalFieldVec_siteAverage hF N
  have hLeft := integrable_parisiSplitPressure_externalField hμ ξ ms qs 0 t u hm G₀
    (parisiOuterAuxSplitVars ξ qs 0 t) hreach
  have hRhs : Integrable (fun hVec : Fin N → ℝ =>
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) - lam * u - C)
      (externalFieldVecLaw N μh) :=
    (((integrable_const (2 * Real.log 2)).add hAvg).sub (integrable_const (lam * u))).sub (integrable_const C)
  have hpoint (hVec : Fin N → ℝ) :
      parisiSplitPressure ξ ms qs 0 t u G₀ (parisiOuterAuxSplitVars ξ qs 0 t)
        (sharedReplicaSiteField hVec) ≤
        2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) - lam * u - C := by
    have hh := parisiRootSplitPressure_le_siteValue hN hξ ms qs hm hq ht hu hm0 hmr G₀
      (sharedReplicaSiteField hVec) lam hreach
    rw [parisiRootSplitPressure_eq_original hN ξ ms qs t u hm hm0 G₀ (sharedReplicaSiteField hVec) hreach] at hh
    rw [parisiSplitPressure_outer_eq_original hN ξ ms qs 0 u hm ht G₀ (sharedReplicaSiteField hVec) hreach]
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
  change randomFieldParisiSplitPressure μh ξ ms qs 0 t u G₀ (parisiOuterAuxSplitVars ξ qs 0 t) ≤
    2 * Real.log 2 + parisiRootCouplingValue μh ξ ms qs v m lam - lam * u - C at hb
  have ho := randomFieldParisiAuxPairPressure_outer_eq hμ hN ξ ms qs 0 u hm ht G₀ hreach
  simp only [Fin.val_zero, zero_add] at ho
  rw [ho]
  dsimp only [v, C] at hb
  linarith

/-- Combining the actual finite-volume root comparison with its
positive inserted-mass coupling gain leaves only the proved scalar limits. -/
theorem randomFieldParisiAuxPairPressure_root_le_mass_gain {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t u m : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) (qs 0)) (hm0 : 0 < m) (hmr : m ≤ mExt ms 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    let v := t * (deriv ξ (qs 0) - deriv ξ u)
    randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
      2 * Real.log 2 + 2 * parisiRootCouplingZeroValue μh ξ ms qs v m -
        (parisiRootCouplingMoment μh ξ ms qs v m - u) ^ 2 / 2 -
        t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ u)) -
        parisiAuxTerminalVar ξ qs t := by
  let v := t * (deriv ξ (qs 0) - deriv ξ u)
  let β := parisiRootCouplingMoment μh ξ ms qs v m - u
  have hb := randomFieldParisiAuxPairPressure_root_le_siteValue hμ hN hξ ms qs hm hq ht hu hm0 hmr G₀ (-β) hreach
  have hg := parisiRootCouplingValue_le_gain hμ ξ ms qs hm hm0 hmr v u
  dsimp only at hg ⊢
  dsimp only [β, v] at hb hg
  linarith

end SpinGlass
