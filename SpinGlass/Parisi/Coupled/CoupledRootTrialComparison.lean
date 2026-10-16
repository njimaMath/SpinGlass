import SpinGlass.Parisi.Coupled.CoupledRootComparison
import SpinGlass.Parisi.Coupled.CoupledGaussianSiteContinuity
import SpinGlass.Parisi.Coupled.CoupledInnerFreeContinuity
import SpinGlass.Parisi.Coupled.CoupledOverlapTangentDefect
import SpinGlass.Parisi.Coupled.CoupledCanonicalFieldComparison

/-!
# Fixed positive-root trial comparisons

The positive inserted mass supplies a continuous scalar bound at a
fixed root overlap. Its concrete zero-mass limit selects an actual
positive-mass witness before finite volume, including root boundaries.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable def parisiRootTrialPressure {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t v u m : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec (k + 2) (parisiRootResponseMasses ms m)
    (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) _
      (fun i => parisiRootDrivenVars ξ qs t v i + parisiRootAuxVars ξ qs t i))
    (coupledG N u a
      (coupledDrivenVarianceFactor (parisiRootDrivenRootVar ξ qs t v) (parisiAuxRootVar ξ qs t)
        (couplingFactorSgn 1 1 0))
      (coupledAuxVarianceFactor (parisiRootDrivenRootVar ξ qs t v) (parisiAuxRootVar ξ qs t)
        (couplingFactorSgn 1 1 0))
      (fun i => coupledDrivenVarianceFactor (parisiRootDrivenVars ξ qs t v i) (parisiRootAuxVars ξ qs t i)
        (couplingFactorSgn 1 1 (i.val + 1)))
      (fun i => coupledAuxVarianceFactor (parisiRootDrivenVars ξ qs t v i) (parisiRootAuxVars ξ qs t i)
        (couplingFactorSgn 1 1 (i.val + 1))) (parisiTimeProfile ξ t) G₀ 1 θ)).toReal
    ∂Pm.prod (rootMarksLaw N (J := Fin 2 ⊕ Fin 2)
      (parisiRootDrivenRootVar ξ qs t v + parisiAuxRootVar ξ qs t))

/-- The positive root insertion is a deterministic auxiliary mark.
Transport and deletion identify its physical pressure with the original
cascade, including the proved terminal mass-one correction. -/
theorem parisiRootTrialPressure_eq_original {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t v u : ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiRootTrialPressure ξ ms qs t v u m G₀ a =
      parisiAuxPairPressure ξ ms qs 1 t u G₀ a + parisiAuxTerminalVar ξ qs t := by
  have hi := integral_log_cascadeRec_pairHamG_auxVarianceShare_eq Pm
    (parisiRootResponseMasses ms m) (constraintR N u) G₀.U G₀.measU 0 a
    (parisiRootDrivenRootVar ξ qs t v) (parisiAuxRootVar ξ qs t)
    (parisiRootDrivenVars ξ qs t v) (parisiRootAuxVars ξ qs t)
    (couplingFactorSgn 1 1 0) (fun i => couplingFactorSgn 1 1 (i.val + 1))
  unfold parisiRootTrialPressure coupledG parisiAuxPairPressure
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
theorem parisiRootTrialPressure_le_siteValue {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t v m : ℝ} (u : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) (qs 0)) (hm0 : 0 < m) (hmr : m ≤ mExt ms 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiRootTrialPressure ξ ms qs t v u m G₀ a ≤
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ j, pairSiteY₀ (parisiRootResponseMasses ms m)
        (deriv ξ (qs 0) - deriv ξ 0 - t * (deriv ξ (qs 0) - deriv ξ v)).toNNReal
        (parisiRootResponseVars ξ qs (t * (deriv ξ (qs 0) - deriv ξ v))) lam (fun l => a (j, l))
        (couplingFactorSgn 1 1 0) (fun i => couplingFactorSgn 1 1 (i.val + 1)) - lam * u -
          t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ v)) +
          t * parisiOverlapTangentDefect ξ v u := by
  have hm1 : m ≤ 1 := hmr.trans (mExt_le_one (fun i => (hm.2.2 i).le) _)
  have hb := coupled_bound_varianceShare_sameFactors_siteField hN (parisiTimeProfile ξ t)
    (parisiRootCouplingRho qs v) u (parisiRootCouplingRho_zero qs v)
    (S := Icc (0 : ℝ) 1) (parisiRootCouplingRho_mem_Icc qs hq hv)
    (fun x _ q hq' => parisiTimeProfile_tangent_line_le hξ ht.1 hq' x)
    (deriv_parisiTimeProfile_zero hξ t) G₀
    (parisiRootDrivenRootVar ξ qs t v) (parisiAuxRootVar ξ qs t)
    (parisiRootDrivenVars ξ qs t v) (parisiRootAuxVars ξ qs t)
    (couplingFactorSgn 1 1 0) (fun i => couplingFactorSgn 1 1 (i.val + 1))
    (parisiRootDrivenRootVar_mul_gram hξ qs hq ht.1 hv)
    (parisiRootDrivenVars_mul_gram hξ qs hq ht.1 hv) a lam (parisiRootResponseMasses ms m)
    (parisiRootResponseMasses_monotone ms hm hmr) (parisiRootResponseMasses_pos ms hm hm0)
    (parisiRootResponseMasses_le_one ms hm hm1) hreach
  change parisiRootTrialPressure ξ ms qs t v u m G₀ a ≤
    2 * Real.log 2 + (1 / (N : ℝ)) * ∑ j, pairSiteY₀ (parisiRootResponseMasses ms m)
      (parisiRootDrivenRootVar ξ qs t v + parisiAuxRootVar ξ qs t)
      (fun i => parisiRootDrivenVars ξ qs t v i + parisiRootAuxVars ξ qs t i)
      lam (fun l => a (j, l)) (couplingFactorSgn 1 1 0)
      (fun i => couplingFactorSgn 1 1 (i.val + 1)) - lam * u -
      (1 / 2) * coupledLevelSum (parisiTimeProfile ξ t) (parisiRootCouplingRho qs v)
        (parisiRootResponseMasses ms m) +
      pairDiagDefect (parisiTimeProfile ξ t) u (fun l l' => parisiRootCouplingRho qs v l l' (k + 3)) at hb
  have htop : pairDiagDefect (parisiTimeProfile ξ t) u
      (fun l l' => parisiRootCouplingRho qs v l l' (k + 3)) =
        t * parisiOverlapTangentDefect ξ v u := by
    simp_rw [parisiRootCouplingRho_top]
    rw [pairDiagDefect_overlapMatrix_eq, parisiOverlapTangentDefect_timeProfile]
  rw [parisiRootDrivenRootVar_add_aux_eq hξ qs hq ht hv, parisiRootDrivenVars_add_aux_eq ξ qs ht v,
    coupledLevelSum_parisiRoot_eq_correction, htop] at hb
  exact hb


/-- The fixed root Gaussian trial bounds every realized constraint under
its actual independent site-field law, with the exact terminal defect. -/
theorem randomFieldParisiAuxPairPressure_root_trial_le_siteValue {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t v m : ℝ} (u : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) (qs 0)) (hm0 : 0 < m) (hmr : m ≤ mExt ms 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ)) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
      2 * Real.log 2 + parisiRootCouplingValue μh ξ ms qs
        (t * (deriv ξ (qs 0) - deriv ξ v)) m lam - lam * u -
        t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ v)) -
        parisiAuxTerminalVar ξ qs t + t * parisiOverlapTangentDefect ξ v u := by
  let w := t * (deriv ξ (qs 0) - deriv ξ v)
  let F := fun h : ℝ => pairSiteY₀ (parisiRootResponseMasses ms m)
    (deriv ξ (qs 0) - deriv ξ 0 - w).toNNReal (parisiRootResponseVars ξ qs w)
    lam (fun _ => h) (couplingFactorSgn 1 1 0) (fun i => couplingFactorSgn 1 1 (i.val + 1))
  let C := 2 * Real.log 2 - lam * u -
    t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ v)) -
    parisiAuxTerminalVar ξ qs t + t * parisiOverlapTangentDefect ξ v u
  have hm1 : m ≤ 1 := hmr.trans (mExt_le_one (fun i => (hm.2.2 i).le) _)
  have hF : Integrable F μh :=
    integrable_pairSiteY₀_parisiRoot_externalField hμ ξ ms qs hm hm0 hm1 w lam
  have hAvg := integrable_externalFieldVec_siteAverage hF N
  have hLeft := integrable_parisiAuxPairPressure_externalField hμ hN ξ ms qs hm 0 ht u G₀ hreach
  simp only [Fin.val_zero, zero_add] at hLeft
  have hRhs : Integrable (fun hVec : Fin N → ℝ => C + (1 / (N : ℝ)) * ∑ i, F (hVec i))
      (externalFieldVecLaw N μh) := (integrable_const C).add hAvg
  have hb := integral_mono hLeft hRhs (fun hVec => by
    have hh := parisiRootTrialPressure_le_siteValue hN hξ ms qs hm hq u ht hv hm0 hmr G₀
      (sharedReplicaSiteField hVec) lam hreach
    rw [parisiRootTrialPressure_eq_original hN ξ ms qs t v u hm hm0 G₀
      (sharedReplicaSiteField hVec) hreach] at hh
    dsimp only [C, F, w, sharedReplicaSiteField] at hh ⊢
    linarith)
  have hmean : (∫ hVec : Fin N → ℝ, C + (1 / (N : ℝ)) * ∑ i, F (hVec i)
      ∂externalFieldVecLaw N μh) = C + ∫ h, F h ∂μh := by
    rw [integral_add (integrable_const C) hAvg, integral_externalFieldVec_siteAverage hF hN]
    simp only [integral_const, probReal_univ, one_smul]
  rw [hmean] at hb
  change randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
    C + parisiRootCouplingValue μh ξ ms qs w m lam at hb
  dsimp only [C, w] at hb
  linarith

noncomputable def parisiRootTrialGap (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (v m lam t u : ℝ) : ℝ :=
  2 * parisiInterpolationBracket μh ξ ms qs t -
    (2 * Real.log 2 + parisiRootCouplingValue μh ξ ms qs (t * (deriv ξ (qs 0) - deriv ξ v)) m lam -
      lam * u - t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ v)) -
      parisiAuxTerminalVar ξ qs t + t * parisiOverlapTangentDefect ξ v u)

/-- The actual root response variance array is continuous at every
split variance, including the clamped zero-variance endpoint. -/
theorem continuous_parisiRootResponseVars (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ) :
    Continuous (parisiRootResponseVars ξ qs) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [parisiRootResponseVars, Fin.cons_zero] using continuous_real_toNNReal
  · simpa only [parisiRootResponseVars, Fin.cons_succ] using
      (continuous_const : Continuous (fun _ : ℝ => parisiLevelVars ξ qs j))

/-- A fixed positive root insertion gives a globally continuous scalar
witness in time and realized constraint, under a finite first field moment. -/
theorem continuous_parisiRootTrialGap_time_overlap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m) (v lam : ℝ) :
    Continuous (fun x : ℝ × ℝ => parisiRootTrialGap μh ξ ms qs v m lam x.1 x.2) := by
  have hw : Continuous (fun x : ℝ × ℝ => x.1 * (deriv ξ (qs 0) - deriv ξ v)) :=
    continuous_fst.mul continuous_const
  have hc := continuous_randomFieldPairSiteY₀_of_continuous_variance hμ
    (parisiRootResponseMasses ms m) (parisiRootResponseMasses_pos ms hm hm0) 1 lam
    (fun x : ℝ × ℝ => (deriv ξ (qs 0) - deriv ξ 0 -
      x.1 * (deriv ξ (qs 0) - deriv ξ v)).toNNReal)
    (fun x : ℝ × ℝ => parisiRootResponseVars ξ qs (x.1 * (deriv ξ (qs 0) - deriv ξ v)))
    (continuous_real_toNNReal.comp (continuous_const.sub hw))
    (fun i => (continuous_apply i).comp ((continuous_parisiRootResponseVars ξ qs).comp hw))
  have hsite : Continuous (fun x : ℝ × ℝ => parisiRootCouplingValue μh ξ ms qs
      (x.1 * (deriv ξ (qs 0) - deriv ξ v)) m lam) := hc
  have hterminal : Continuous (fun x : ℝ × ℝ => (parisiAuxTerminalVar ξ qs x.1 : ℝ)) :=
    (continuous_parisiAuxTerminalVar_time ξ qs).comp continuous_fst
  have hbracket : Continuous (fun x : ℝ × ℝ => parisiInterpolationBracket μh ξ ms qs x.1) :=
    (continuous_parisiInterpolationBracket_time μh ξ ms qs).comp continuous_fst
  have hdefect : Continuous (fun x : ℝ × ℝ => parisiOverlapTangentDefect ξ v x.2) :=
    (continuous_parisiOverlapTangentDefect hξ v).comp continuous_snd
  unfold parisiRootTrialGap
  exact (hbracket.const_mul 2).sub
    (((((continuous_const.add hsite).sub (continuous_snd.const_mul lam)).sub
      (continuous_fst.mul continuous_const)).sub hterminal).add (continuous_fst.mul hdefect))

/-- A fixed admissible positive root trial bounds the original pressure
at any realizable constraint; its Gaussian overlap remains fixed. -/
theorem randomFieldParisiAuxPairPressure_le_rootTrialGap {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t v m : ℝ} (u : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) (qs 0)) (hm0 : 0 < m) (hmr : m ≤ mExt ms 1) (lam : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
      2 * parisiInterpolationBracket μh ξ ms qs t - parisiRootTrialGap μh ξ ms qs v m lam t u := by
  have hb := randomFieldParisiAuxPairPressure_root_trial_le_siteValue hμ hN hξ ms qs hm hq
    u ht hv hm0 hmr G₀ lam hreach
  unfold parisiRootTrialGap
  linarith

/-- A nonzero concrete zero-mass root response selects a positive-mass
trial witness. The physical cascade is evaluated only at positive mass. -/
theorem exists_parisiRootTrialGap_pos_of_response_ne_zero
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t v : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) (qs 0))
    (hresponse : parisiRootResponseGap μh ξ ms qs t v ≠ 0) :
    ∃ m ∈ Ioc (0 : ℝ) (mExt ms 1), ∃ lam : ℝ,
      0 < parisiRootTrialGap μh ξ ms qs v m lam t v := by
  let w := t * (deriv ξ (qs 0) - deriv ξ v)
  let H := fun m : ℝ => 2 * (∫ h, closedParisiX₀ ξ ms qs h ∂μh) -
    2 * parisiRootCouplingZeroValue μh ξ ms qs w m +
      (parisiRootCouplingMoment μh ξ ms qs w m - v) ^ 2 / 2 +
        t * m * (parisiTheta ξ (qs 0) - parisiTheta ξ v)
  have hVal := continuousAt_parisiRootCouplingZeroValue_zero hμ ξ ms qs w
  have hMom := continuousAt_parisiRootCouplingMoment_zero (μh := μh) ξ ms qs w
  have hHc : ContinuousAt H 0 := by dsimp only [H]; fun_prop
  have hw := parisi_root_time_variance_mem_Icc hξ qs hq ht hv
  have hH0 : 0 < H 0 := by
    dsimp only [H]
    rw [parisiRootCouplingZeroValue_zero hμ ξ ms qs hw, parisiRootCouplingMoment_zero]
    simpa only [sub_self, zero_add, mul_zero, zero_mul, add_zero, parisiRootResponseGap, w] using
      div_pos (sq_pos_of_ne_zero hresponse) (by norm_num : (0 : ℝ) < 2)
  have hsmall0 : ∀ᶠ m : ℝ in 𝓝 0, m < mExt ms 1 :=
    Iio_mem_nhds (hm.mExt_pos (by norm_num : 0 < 1))
  have hsmall : ∀ᶠ m : ℝ in 𝓝[>] 0, m < mExt ms 1 :=
    hsmall0.filter_mono nhdsWithin_le_nhds
  have hpositive : ∀ᶠ m : ℝ in 𝓝[>] 0, 0 < H m :=
    (hHc.tendsto.eventually (Ioi_mem_nhds hH0)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ m : ℝ in 𝓝[>] 0, 0 < m := self_mem_nhdsWithin
  obtain ⟨m, hm0, hmr, hHm⟩ := (hpos.and (hsmall.and hpositive)).exists
  let β := parisiRootCouplingMoment μh ξ ms qs w m - v
  refine ⟨m, ⟨hm0, hmr.le⟩, -β, ?_⟩
  have hg := parisiRootCouplingValue_le_gain hμ ξ ms qs hm hm0 hmr.le w v
  dsimp only at hg
  unfold parisiRootTrialGap parisiInterpolationBracket parisiSplitBracket parisiOverlapTangentDefect
  dsimp only [H, w, β] at hHm ⊢
  nlinarith

end SpinGlass
