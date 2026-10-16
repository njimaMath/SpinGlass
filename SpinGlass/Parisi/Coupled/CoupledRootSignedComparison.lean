import SpinGlass.Parisi.Coupled.CoupledRootSignedVariance

/-!
# The negative initial-interval physical pressure comparison

The separate signed driven and common auxiliary factors satisfy the
concrete profile covariance identities. At the physical endpoint only
the original auxiliary field remains, including its terminal correction.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable def parisiRootSignedRawSiteValue (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u m lam h : ℝ) : ℝ :=
  parisiRootSignedRawCouplingValue (Measure.dirac h) ξ ms qs t u m lam

theorem integral_parisiRootSignedRawSiteValue {μh : Measure ℝ} (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u m lam : ℝ) :
    (∫ h, parisiRootSignedRawSiteValue ξ ms qs t u m lam h ∂μh) =
      parisiRootSignedRawCouplingValue μh ξ ms qs t u m lam := by
  simp only [parisiRootSignedRawSiteValue, parisiRootSignedRawCouplingValue,
    randomFieldPairSiteY₀, integral_dirac]

noncomputable def parisiRootSignedSplitPressure {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u m : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec (k + 2) (parisiRootResponseMasses ms m)
    (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) _
      (fun i => parisiRootDrivenVars ξ qs t |u| i + parisiRootAuxVars ξ qs t i))
    (coupledG N u a
      (coupledDrivenVarianceFactor (parisiRootDrivenRootVar ξ qs t |u|) (parisiAuxRootVar ξ qs t)
        (couplingFactorSgn (-1) 1 0))
      (coupledAuxVarianceFactor (parisiRootDrivenRootVar ξ qs t |u|) (parisiAuxRootVar ξ qs t)
        (couplingFactorSgn 1 1 0))
      (fun i => coupledDrivenVarianceFactor (parisiRootDrivenVars ξ qs t |u| i) (parisiRootAuxVars ξ qs t i)
        (couplingFactorSgn (-1) 1 (i.val + 1)))
      (fun i => coupledAuxVarianceFactor (parisiRootDrivenVars ξ qs t |u| i) (parisiRootAuxVars ξ qs t i)
        (couplingFactorSgn 1 1 (i.val + 1))) (parisiTimeProfile ξ t) G₀ 1 θ)).toReal
    ∂Pm.prod (rootMarksLaw N (J := Fin 2 ⊕ Fin 2)
      (parisiRootDrivenRootVar ξ qs t |u| + parisiAuxRootVar ξ qs t))

/-- The actual signed physical pressure is the original pressure plus
the terminal variance, independently of every positive inserted mass. -/
theorem parisiRootSignedSplitPressure_eq_original {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u : ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiRootSignedSplitPressure ξ ms qs t u m G₀ a =
      parisiAuxPairPressure ξ ms qs 1 t u G₀ a + parisiAuxTerminalVar ξ qs t := by
  have hi := integral_log_cascadeRec_pairHamG_auxVarianceShare_eq Pm
    (parisiRootResponseMasses ms m) (constraintR N u) G₀.U G₀.measU 0 a
    (parisiRootDrivenRootVar ξ qs t |u|) (parisiAuxRootVar ξ qs t)
    (parisiRootDrivenVars ξ qs t |u|) (parisiRootAuxVars ξ qs t)
    (couplingFactorSgn 1 1 0) (fun i => couplingFactorSgn 1 1 (i.val + 1))
  unfold parisiRootSignedSplitPressure coupledG parisiAuxPairPressure
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

/-- Every signed covariance, tangent and correction input of the
finite-volume separate-factor comparison is concretely discharged. -/
theorem parisiRootSignedSplitPressure_le_siteValue {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t u m : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : |u| ≤ qs 0) (hu0 : u ≤ 0) (hm0 : 0 < m) (hmr : m ≤ mExt ms 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hVec : Fin N → ℝ) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiRootSignedSplitPressure ξ ms qs t u m G₀ (sharedReplicaSiteField hVec) ≤
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, parisiRootSignedRawSiteValue ξ ms qs t u m lam (hVec i) -
        lam * u - t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ |u|)) := by
  have hm1 : m ≤ 1 := hmr.trans (mExt_le_one (fun i => (hm.2.2 i).le) _)
  have hb := coupled_bound_varianceShare_siteField hN (parisiTimeProfile ξ t)
    (parisiRootSignedCouplingRho qs u) u (parisiRootSignedCouplingRho_zero qs u)
    (S := Icc (-1 : ℝ) 1) (parisiRootSignedCouplingRho_mem_Icc qs hq hu)
    (fun x _ q hq' => parisiTimeProfile_tangent_line_le_signed hξ ht.1 hq' x)
    (deriv_parisiTimeProfile_zero hξ t) G₀
    (parisiRootDrivenRootVar ξ qs t |u|) (parisiAuxRootVar ξ qs t)
    (parisiRootDrivenVars ξ qs t |u|) (parisiRootAuxVars ξ qs t)
    (couplingFactorSgn (-1) 1 0) (couplingFactorSgn 1 1 0)
    (fun i => couplingFactorSgn (-1) 1 (i.val + 1)) (fun i => couplingFactorSgn 1 1 (i.val + 1))
    (parisiRootSignedDrivenRootVar_mul_gram hξ qs hq ht.1 hu)
    (parisiRootSignedDrivenVars_mul_gram hξ qs hq ht.1 hu)
    (sharedReplicaSiteField hVec) lam (parisiRootResponseMasses ms m)
    (parisiRootResponseMasses_monotone ms hm hmr) (parisiRootResponseMasses_pos ms hm hm0)
    (parisiRootResponseMasses_le_one ms hm hm1) hreach
  rw [coupledLevelSum_parisiRootSigned_eq_correction hξ,
    pairDiagDefect_parisiRootSignedCouplingRho_top _ _ hu0, add_zero] at hb
  simpa only [parisiRootSignedSplitPressure, parisiRootSignedRawSiteValue,
    parisiRootSignedRawCouplingValue, randomFieldPairSiteY₀, integral_dirac, sharedReplicaSiteField] using hb

/-- The signed one-site average remains integrable under the
original finite-first-moment field law. -/
theorem integrable_parisiRootSignedRawSiteValue {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t u m : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : |u| ≤ qs 0) (hm0 : 0 < m) (hm1 : m ≤ 1) (lam : ℝ) :
    Integrable (parisiRootSignedRawSiteValue ξ ms qs t u m lam) μh := by
  let v := t * (deriv ξ (qs 0) - deriv ξ |u|)
  have he (h : ℝ) : parisiRootSignedRawSiteValue ξ ms qs t u m 0 h =
      pairSiteY₀ (parisiRootResponseMasses ms m) (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal
        (parisiRootResponseVars ξ qs v) 0 (fun _ => h) (couplingFactorSgn 1 1 0)
        (fun i => couplingFactorSgn 1 1 (i.val + 1)) := by
    have hD : Integrable id (Measure.dirac h) := by apply integrable_dirac; finiteness
    have hh : parisiRootSignedRawCouplingValue (Measure.dirac h) ξ ms qs t u m 0 =
        parisiRootCouplingValue (Measure.dirac h) ξ ms qs v m 0 := by
      rw [parisiRootSignedRawCouplingValue_eq hD ξ ms qs hm ht hm0 hm1,
        parisiRootSignedCouplingValue_zero hD hξ ms qs hm hq ht hu hm0 hm1,
        parisiRootCouplingValue_zero hD ξ ms qs hm hm0 v]
    simpa only [parisiRootSignedRawSiteValue, parisiRootCouplingValue,
      randomFieldPairSiteY₀, integral_dirac] using hh
  have hi0 : Integrable (parisiRootSignedRawSiteValue ξ ms qs t u m 0) μh :=
    (integrable_pairSiteY₀_parisiRoot_externalField hμ ξ ms qs hm hm0 hm1 v 0).congr
      (.of_forall fun h => (he h).symm)
  unfold parisiRootSignedRawSiteValue parisiRootSignedRawCouplingValue randomFieldPairSiteY₀ at hi0 ⊢
  simp only [integral_dirac] at hi0 ⊢
  exact integrable_pairSiteY₀_commonField_of_integrable_at_zero _
    (parisiRootResponseMasses_pos ms hm hm0) (parisiRootResponseMasses_le_one ms hm hm1)
    _ _ _ _ hi0 lam

/-- Averaging the signed finite-volume comparison over the actual
i.i.d. product-coordinate external field gives the original pressure bound. -/
theorem randomFieldParisiAuxPairPressure_root_signed_le_siteValue {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t u m : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (-(qs 0)) (0 : ℝ)) (hm0 : 0 < m) (hmr : m ≤ mExt ms 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ)) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
      2 * Real.log 2 + parisiRootSignedCouplingValue μh ξ ms qs t u m lam - lam * u -
        t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ |u|)) -
        parisiAuxTerminalVar ξ qs t := by
  let C := t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ |u|))
  let F := parisiRootSignedRawSiteValue ξ ms qs t u m lam
  have huabs : |u| ≤ qs 0 := by rw [abs_of_nonpos hu.2]; linarith [hu.1]
  have hm1 : m ≤ 1 := hmr.trans (mExt_le_one (fun i => (hm.2.2 i).le) _)
  have hF : Integrable F μh := integrable_parisiRootSignedRawSiteValue hμ hξ ms qs hm hq ht huabs hm0 hm1 lam
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
    have hh := parisiRootSignedSplitPressure_le_siteValue hN hξ ms qs hm hq ht huabs hu.2 hm0 hmr G₀
      hVec lam hreach
    rw [parisiRootSignedSplitPressure_eq_original hN ξ ms qs t u hm hm0 G₀
      (sharedReplicaSiteField hVec) hreach] at hh
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
  rw [show (∫ h, F h ∂μh) = parisiRootSignedRawCouplingValue μh ξ ms qs t u m lam from
    integral_parisiRootSignedRawSiteValue ξ ms qs t u m lam] at hb
  change randomFieldParisiSplitPressure μh ξ ms qs 0 t u G₀ (parisiOuterAuxSplitVars ξ qs 0 t) ≤
    2 * Real.log 2 + parisiRootSignedRawCouplingValue μh ξ ms qs t u m lam - lam * u - C at hb
  rw [parisiRootSignedRawCouplingValue_eq hμ ξ ms qs hm ht hm0 hm1 lam] at hb
  have ho := randomFieldParisiAuxPairPressure_outer_eq hμ hN ξ ms qs 0 u hm ht G₀ hreach
  simp only [Fin.val_zero, zero_add] at ho
  rw [ho]
  dsimp only [C] at hb
  linarith

/-- The actual signed finite-volume comparison and its concrete
one-site gain leave only the proved positive inserted-mass limits. -/
theorem randomFieldParisiAuxPairPressure_root_signed_le_mass_gain {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t u m : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (-(qs 0)) (0 : ℝ)) (hm0 : 0 < m) (hmr : m ≤ mExt ms 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    let v := t * (deriv ξ (qs 0) - deriv ξ |u|)
    randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
      2 * Real.log 2 + 2 * parisiRootCouplingZeroValue μh ξ ms qs v m -
        (parisiRootSignedCouplingMassMoment μh ξ ms qs t u m - u) ^ 2 / 2 -
        t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ |u|)) -
        parisiAuxTerminalVar ξ qs t := by
  let β := parisiRootSignedCouplingMassMoment μh ξ ms qs t u m - u
  have huabs : |u| ≤ qs 0 := by rw [abs_of_nonpos hu.2]; linarith [hu.1]
  have hc := randomFieldParisiAuxPairPressure_root_signed_le_siteValue hμ hN hξ ms qs hm hq ht hu hm0 hmr G₀ (-β) hreach
  have hg := parisiRootSignedCouplingValue_le_gain hμ hξ ms qs hm hq ht huabs hm0 hmr
  dsimp only at hg ⊢
  dsimp only [β] at hc
  linarith

end SpinGlass
