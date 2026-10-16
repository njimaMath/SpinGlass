import SpinGlass.Parisi.Coupled.CoupledRootSignedComparison
import SpinGlass.Parisi.Coupled.CoupledRootSignedContinuity
import SpinGlass.Parisi.Coupled.CoupledOverlapTangentDefect

/-!
# Signed initial-interval comparison at a fixed trial overlap

A positive inserted root mass defines the actual admissible cascade.
The realized constraint may vary independently of its signed trial
covariance, with the exact terminal tangent defect of (14.147).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The signed trial covariance has the same exact tangent defect
at every realized overlap, including positive constraints. -/
theorem pairDiagDefect_parisiRootSignedCouplingRho_trial (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (s u : ℝ) (hs : s ≤ 0) :
    pairDiagDefect ξ u (fun l l' => parisiRootSignedCouplingRho qs s l l' (k + 3)) =
      parisiOverlapTangentDefect ξ s u := by
  have he : (fun l l' => parisiRootSignedCouplingRho qs s l l' (k + 3)) =
      fun l l' => if l = l' then (1 : ℝ) else s := by
    funext l l'
    rw [parisiRootSignedCouplingRho_top, abs_of_nonpos hs, neg_neg]
  rw [he, pairDiagDefect_overlapMatrix_eq]

noncomputable def parisiRootSignedTrialPressure {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t s u m : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec (k + 2) (parisiRootResponseMasses ms m)
    (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) _
      (fun i => parisiRootDrivenVars ξ qs t |s| i + parisiRootAuxVars ξ qs t i))
    (coupledG N u a
      (coupledDrivenVarianceFactor (parisiRootDrivenRootVar ξ qs t |s|) (parisiAuxRootVar ξ qs t)
        (couplingFactorSgn (-1) 1 0))
      (coupledAuxVarianceFactor (parisiRootDrivenRootVar ξ qs t |s|) (parisiAuxRootVar ξ qs t)
        (couplingFactorSgn 1 1 0))
      (fun i => coupledDrivenVarianceFactor
        (parisiRootDrivenVars ξ qs t |s| i) (parisiRootAuxVars ξ qs t i)
        (couplingFactorSgn (-1) 1 (i.val + 1)))
      (fun i => coupledAuxVarianceFactor
        (parisiRootDrivenVars ξ qs t |s| i) (parisiRootAuxVars ξ qs t i)
        (couplingFactorSgn 1 1 (i.val + 1))) (parisiTimeProfile ξ t) G₀ 1 θ)).toReal
    ∂Pm.prod (rootMarksLaw N (J := Fin 2 ⊕ Fin 2)
      (parisiRootDrivenRootVar ξ qs t |s| + parisiAuxRootVar ξ qs t))

/-- The actual signed physical pressure is the original pressure plus
the terminal variance, independently of every positive inserted mass. -/
theorem parisiRootSignedTrialPressure_eq_original {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t s u : ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiRootSignedTrialPressure ξ ms qs t s u m G₀ a =
      parisiAuxPairPressure ξ ms qs 1 t u G₀ a + parisiAuxTerminalVar ξ qs t := by
  have hi := integral_log_cascadeRec_pairHamG_auxVarianceShare_eq Pm
    (parisiRootResponseMasses ms m) (constraintR N u) G₀.U G₀.measU 0 a
    (parisiRootDrivenRootVar ξ qs t |s|) (parisiAuxRootVar ξ qs t)
    (parisiRootDrivenVars ξ qs t |s|) (parisiRootAuxVars ξ qs t)
    (couplingFactorSgn 1 1 0) (fun i => couplingFactorSgn 1 1 (i.val + 1))
  unfold parisiRootSignedTrialPressure coupledG parisiAuxPairPressure
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
theorem parisiRootSignedTrialPressure_le_siteValue {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t s m : ℝ} (u : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : |s| ≤ qs 0) (hu0 : s ≤ 0) (hm0 : 0 < m) (hmr : m ≤ mExt ms 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hVec : Fin N → ℝ) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiRootSignedTrialPressure ξ ms qs t s u m G₀ (sharedReplicaSiteField hVec) ≤
      2 * Real.log 2 + (1 / (N : ℝ)) *
        ∑ i, parisiRootSignedRawSiteValue ξ ms qs t s m lam (hVec i) -
        lam * u - t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ |s|)) +
          t * parisiOverlapTangentDefect ξ s u := by
  have hm1 : m ≤ 1 := hmr.trans (mExt_le_one (fun i => (hm.2.2 i).le) _)
  have hb := coupled_bound_varianceShare_siteField hN (parisiTimeProfile ξ t)
    (parisiRootSignedCouplingRho qs s) u (parisiRootSignedCouplingRho_zero qs s)
    (S := Icc (-1 : ℝ) 1) (parisiRootSignedCouplingRho_mem_Icc qs hq hu)
    (fun x _ q hq' => parisiTimeProfile_tangent_line_le_signed hξ ht.1 hq' x)
    (deriv_parisiTimeProfile_zero hξ t) G₀
    (parisiRootDrivenRootVar ξ qs t |s|) (parisiAuxRootVar ξ qs t)
    (parisiRootDrivenVars ξ qs t |s|) (parisiRootAuxVars ξ qs t)
    (couplingFactorSgn (-1) 1 0) (couplingFactorSgn 1 1 0)
    (fun i => couplingFactorSgn (-1) 1 (i.val + 1)) (fun i => couplingFactorSgn 1 1 (i.val + 1))
    (parisiRootSignedDrivenRootVar_mul_gram hξ qs hq ht.1 hu)
    (parisiRootSignedDrivenVars_mul_gram hξ qs hq ht.1 hu)
    (sharedReplicaSiteField hVec) lam (parisiRootResponseMasses ms m)
    (parisiRootResponseMasses_monotone ms hm hmr) (parisiRootResponseMasses_pos ms hm hm0)
    (parisiRootResponseMasses_le_one ms hm hm1) hreach
  rw [coupledLevelSum_parisiRootSigned_eq_correction hξ,
    pairDiagDefect_parisiRootSignedCouplingRho_trial _ _ s u hu0,
    parisiOverlapTangentDefect_timeProfile] at hb
  simpa only [parisiRootSignedTrialPressure, parisiRootSignedRawSiteValue,
    parisiRootSignedRawCouplingValue, randomFieldPairSiteY₀, integral_dirac,
    sharedReplicaSiteField] using hb

/-- Averaging the signed finite-volume comparison over the actual
i.i.d. product-coordinate external field gives the original pressure bound. -/
theorem randomFieldParisiAuxPairPressure_root_signed_trial_le_siteValue {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t s m : ℝ} (u : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : s ∈ Icc (-(qs 0)) (0 : ℝ)) (hm0 : 0 < m) (hmr : m ≤ mExt ms 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ)) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
      2 * Real.log 2 + parisiRootSignedCouplingValue μh ξ ms qs t s m lam - lam * u -
        (t * (parisiCorrection ξ ms qs +
          m * (parisiTheta ξ (qs 0) - parisiTheta ξ |s|)) -
            t * parisiOverlapTangentDefect ξ s u) -
        parisiAuxTerminalVar ξ qs t := by
  let C := t * (parisiCorrection ξ ms qs +
    m * (parisiTheta ξ (qs 0) - parisiTheta ξ |s|)) - t * parisiOverlapTangentDefect ξ s u
  let F := parisiRootSignedRawSiteValue ξ ms qs t s m lam
  have huabs : |s| ≤ qs 0 := by rw [abs_of_nonpos hu.2]; linarith [hu.1]
  have hm1 : m ≤ 1 := hmr.trans (mExt_le_one (fun i => (hm.2.2 i).le) _)
  have hF : Integrable F μh :=
    integrable_parisiRootSignedRawSiteValue hμ hξ ms qs hm hq ht huabs hm0 hm1 lam
  have hAvg := integrable_externalFieldVec_siteAverage hF N
  have hLeft := integrable_parisiSplitPressure_externalField hμ ξ ms qs 0 t u hm G₀
    (parisiOuterAuxSplitVars ξ qs 0 t) hreach
  have hRhs : Integrable (fun hVec : Fin N → ℝ =>
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) - lam * u - C)
      (externalFieldVecLaw N μh) :=
    (((integrable_const (2 * Real.log 2)).add hAvg).sub
      (integrable_const (lam * u))).sub (integrable_const C)
  have hpoint (hVec : Fin N → ℝ) :
      parisiSplitPressure ξ ms qs 0 t u G₀ (parisiOuterAuxSplitVars ξ qs 0 t)
        (sharedReplicaSiteField hVec) ≤
        2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) - lam * u - C := by
    have hh := parisiRootSignedTrialPressure_le_siteValue hN hξ ms qs hm hq u ht
      huabs hu.2 hm0 hmr G₀ hVec lam hreach
    rw [parisiRootSignedTrialPressure_eq_original hN ξ ms qs t s u hm hm0 G₀
      (sharedReplicaSiteField hVec) hreach] at hh
    rw [parisiSplitPressure_outer_eq_original hN ξ ms qs 0 u hm ht G₀
      (sharedReplicaSiteField hVec) hreach]
    dsimp only [C, F] at hh ⊢
    simp only [Fin.val_zero, zero_add]
    linarith
  have hb := integral_mono hLeft hRhs hpoint
  have hmean : (∫ hVec : Fin N → ℝ,
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) - lam * u - C
      ∂externalFieldVecLaw N μh) = 2 * Real.log 2 + (∫ h, F h ∂μh) - lam * u - C := by
    have ha := integral_add (integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)) hAvg
    have hs := integral_sub
      ((integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)).add hAvg)
      (integrable_const (lam * u))
    have hc := integral_sub
      (((integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)).add hAvg).sub
        (integrable_const (lam * u))) (integrable_const C)
    simp only [Pi.add_apply, Pi.sub_apply] at ha hs hc
    rw [hc, hs, ha, integral_externalFieldVec_siteAverage hF hN]
    simp only [integral_const, probReal_univ, one_smul]
  rw [hmean] at hb
  rw [show (∫ h, F h ∂μh) = parisiRootSignedRawCouplingValue μh ξ ms qs t s m lam from
    integral_parisiRootSignedRawSiteValue ξ ms qs t s m lam] at hb
  change randomFieldParisiSplitPressure μh ξ ms qs 0 t u G₀ (parisiOuterAuxSplitVars ξ qs 0 t) ≤
    2 * Real.log 2 + parisiRootSignedRawCouplingValue μh ξ ms qs t s m lam - lam * u - C at hb
  rw [parisiRootSignedRawCouplingValue_eq hμ ξ ms qs hm ht hm0 hm1 lam] at hb
  have ho := randomFieldParisiAuxPairPressure_outer_eq hμ hN ξ ms qs 0 u hm ht G₀ hreach
  simp only [Fin.val_zero, zero_add] at ho
  rw [ho]
  dsimp only [C] at hb
  linarith

noncomputable def parisiRootSignedTrialGap (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (s m lam t u : ℝ) : ℝ :=
  2 * (∫ h, closedParisiX₀ ξ ms qs h ∂μh) + lam * u -
    parisiRootSignedCouplingValue μh ξ ms qs t s m lam +
      t * m * (parisiTheta ξ (qs 0) - parisiTheta ξ |s|) -
        t * parisiOverlapTangentDefect ξ s u

/-- The actual signed-root scalar witness is continuous in time
and the realized constraint at every admissible positive inserted mass. -/
theorem continuous_parisiRootSignedTrialGap_time_overlap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (s lam : ℝ) :
    Continuous (fun x : ℝ × ℝ => parisiRootSignedTrialGap μh ξ ms qs s m lam x.1 x.2) := by
  have hsite := (continuous_parisiRootSignedCouplingValue_time hμ ξ ms qs hm
    hm0 hm1 s lam).comp (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))
  unfold parisiRootSignedTrialGap
  exact (((continuous_const.add (continuous_snd.const_mul lam)).sub hsite).add
    ((continuous_fst.mul continuous_const).mul continuous_const)).sub
      (continuous_fst.mul ((continuous_parisiOverlapTangentDefect hξ s).comp continuous_snd))

/-- The signed trial controls every realizable constraint under the
actual i.i.d. field law. The trial itself stays in the initial negative interval. -/
theorem randomFieldParisiAuxPairPressure_le_rootSignedTrialGap {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t s m : ℝ} (u : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (-(qs 0)) (0 : ℝ)) (hm0 : 0 < m) (hmr : m ≤ mExt ms 1)
    (lam : ℝ) (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
      2 * parisiInterpolationBracket μh ξ ms qs t -
        parisiRootSignedTrialGap μh ξ ms qs s m lam t u := by
  have hh := randomFieldParisiAuxPairPressure_root_signed_trial_le_siteValue hμ hN hξ
    ms qs hm hq u ht hs hm0 hmr G₀ lam hreach
  unfold parisiRootSignedTrialGap parisiInterpolationBracket parisiSplitBracket
  nlinarith

/-- A nonzero actual zero-mass response yields a strictly positive
continuous trial with positive inserted mass. The zero-mass limit is
used only to choose this admissible trial, as in Proposition 14.8.3. -/
theorem exists_parisiRootSignedTrialGap_pos_of_response_ne_zero
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (-(qs 0)) (0 : ℝ))
    (hresponse : parisiRootSignedResponseGap μh ξ ms qs t s ≠ 0) :
    ∃ m ∈ Ioc (0 : ℝ) (mExt ms 1), ∃ lam : ℝ,
      0 < parisiRootSignedTrialGap μh ξ ms qs s m lam t s := by
  let v := t * (deriv ξ (qs 0) - deriv ξ |s|)
  let H := fun m : ℝ => 2 * (∫ h, closedParisiX₀ ξ ms qs h ∂μh) -
    2 * parisiRootCouplingZeroValue μh ξ ms qs v m +
      (parisiRootSignedCouplingMassMoment μh ξ ms qs t s m - s) ^ 2 / 2 +
        t * m * (parisiTheta ξ (qs 0) - parisiTheta ξ |s|)
  have hVal := continuousAt_parisiRootCouplingZeroValue_zero hμ ξ ms qs v
  have hMom := continuousAt_parisiRootSignedCouplingMassMoment_zero (μh := μh) ξ ms qs t s
  have hHc : ContinuousAt H 0 := by dsimp only [H]; fun_prop
  have hsabs : |s| ≤ qs 0 := by rw [abs_of_nonpos hs.2]; linarith [hs.1]
  have hv := parisi_root_time_variance_mem_Icc hξ qs hq ht ⟨abs_nonneg _, hsabs⟩
  have hH0 : 0 < H 0 := by
    dsimp only [H]
    rw [parisiRootCouplingZeroValue_zero hμ ξ ms qs hv,
      parisiRootSignedCouplingMassMoment_zero hξ ms qs hq ht hsabs]
    simpa only [sub_self, zero_add, mul_zero, zero_mul, add_zero,
      parisiRootSignedResponseGap] using
      div_pos (sq_pos_of_ne_zero hresponse) (by norm_num : (0 : ℝ) < 2)
  have hsmall0 : ∀ᶠ m : ℝ in 𝓝 0, m < mExt ms 1 :=
    Iio_mem_nhds (hm.mExt_pos (by norm_num : 0 < 1))
  have hsmall : ∀ᶠ m : ℝ in 𝓝[>] 0, m < mExt ms 1 :=
    hsmall0.filter_mono nhdsWithin_le_nhds
  have hpositive : ∀ᶠ m : ℝ in 𝓝[>] 0, 0 < H m :=
    (hHc.tendsto.eventually (Ioi_mem_nhds hH0)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ m : ℝ in 𝓝[>] 0, 0 < m := self_mem_nhdsWithin
  obtain ⟨m, hm0, hmr, hHm⟩ := (hpos.and (hsmall.and hpositive)).exists
  let β := parisiRootSignedCouplingMassMoment μh ξ ms qs t s m - s
  refine ⟨m, ⟨hm0, hmr.le⟩, -β, ?_⟩
  have hg := parisiRootSignedCouplingValue_le_gain hμ hξ ms qs hm hq ht hsabs hm0 hmr.le
  dsimp only at hg
  unfold parisiRootSignedTrialGap parisiOverlapTangentDefect
  dsimp only [H, v, β] at hHm ⊢
  nlinarith

structure ParisiRootSignedTrial {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) where
  overlap : ℝ
  overlap_mem : overlap ∈ Icc (-(qs 0)) (0 : ℝ)
  mass : ℝ
  mass_mem : mass ∈ Ioc (0 : ℝ) (mExt ms 1)
  coupling : ℝ

/-- The MIN tolerance is chosen before all parameters. Every point
of the closed negative initial interval then has a positive continuous
trial, chosen before the volume and the Gaussian Hamiltonian law. -/
theorem exists_uniform_parisiRootSignedTrial_positive_gap {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (-(qs 0)) (0 : ℝ),
        ∃ w : ParisiRootSignedTrial ms qs,
          0 < parisiRootSignedTrialGap μh ξ ms qs w.overlap w.mass w.coupling t u := by
  obtain ⟨ε, hε, hgap⟩ := exists_uniform_parisi_root_signed_response_gap hξ hμ ht₀
  refine ⟨ε, hε, ?_⟩
  intro k ms qs hm hmin hfull hnear t ht u hu
  have hqpos := randomFieldParisiQ_first_pos_of_isMin ms qs hμ.integrable_id hm hξ hμ hmin
  have hresponse := hgap k ms qs hm hmin hfull hnear t ht u hu
  have hpositive : 0 < parisiRootSignedResponseGap μh ξ ms qs t u :=
    (mul_pos (div_pos (sub_pos.2 ht₀.2) (by norm_num))
      (by linarith [hu.2] : 0 < qs 0 - u)).trans_le hresponse
  obtain ⟨m, hmrange, lam, hw⟩ :=
    exists_parisiRootSignedTrialGap_pos_of_response_ne_zero hμ.integrable_id hξ ms qs hm hmin.1
      ⟨ht.1, ht.2.trans ht₀.2.le⟩ hu hpositive.ne'
  exact ⟨⟨u, hu, m, hmrange, lam⟩, hw⟩

end SpinGlass
