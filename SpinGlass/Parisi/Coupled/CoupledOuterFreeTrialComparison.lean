import SpinGlass.Parisi.Coupled.CoupledOuterFreeComparison
import SpinGlass.Parisi.Coupled.CoupledOuterFreeContinuity
import SpinGlass.Parisi.Coupled.CoupledGaussianSiteContinuity
import SpinGlass.Parisi.Coupled.CoupledOverlapTangentDefect
import SpinGlass.Parisi.Coupled.CoupledCanonicalFieldComparison

/-!
# Fixed-trial comparison for a free outer mass

The Gaussian split is fixed at a trial overlap while the physical
constraint varies. The exact tangent defect in (14.147) gives a
continuous scalar witness across neighboring interval boundaries.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable def parisiOuterFreeTrialPressure {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t v u b : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec (k + 2) (parisiOuterFreeCoupledMasses ms p b)
    (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) _ (fun i =>
      parisiDrivenSplitVars ξ qs p t v (parisiSplitIndex p i) +
        parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i)))
    (coupledG N u a
      (coupledDrivenVarianceFactor (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
        (couplingFactorSgn 1 (p.val + 2) 0))
      (coupledAuxVarianceFactor (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
        (couplingFactorSgn 1 (p.val + 2) 0))
      (fun i => coupledDrivenVarianceFactor
        (parisiDrivenSplitVars ξ qs p t v (parisiSplitIndex p i))
        (parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i))
        (couplingFactorSgn 1 (p.val + 2) (i.val + 1)))
      (fun i => coupledAuxVarianceFactor
        (parisiDrivenSplitVars ξ qs p t v (parisiSplitIndex p i))
        (parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i))
        (couplingFactorSgn 1 (p.val + 2) (i.val + 1))) (parisiTimeProfile ξ t) G₀ 1 θ)).toReal
    ∂Pm.prod (rootMarksLaw N (parisiDrivenRootVar ξ qs t + parisiAuxRootVar ξ qs t))

/-- The actual physical pressure at a free positive mass is the
original constrained auxiliary pressure plus its terminal normalization. -/
theorem parisiOuterFreeTrialPressure_eq_original {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t v u : ℝ)
    (hm : ParisiMAdmissible ms) {b : ℝ} (hb : 0 < b)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiOuterFreeTrialPressure ξ ms qs p t v u b G₀ a =
      parisiAuxPairPressure ξ ms qs (p.val + 1) t u G₀ a + parisiAuxTerminalVar ξ qs t := by
  have hi := integral_log_cascadeRec_pairHamG_auxVarianceShare_eq Pm
    (parisiOuterFreeCoupledMasses ms p b) (constraintR N u) G₀.U G₀.measU 0 a
    (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
    (fun i => parisiDrivenSplitVars ξ qs p t v (parisiSplitIndex p i))
    (fun i => parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i))
    (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))
  unfold parisiOuterFreeTrialPressure coupledG parisiAuxPairPressure
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
theorem parisiOuterFreeTrialPressure_le_siteValue {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t v b : ℝ} (u : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (hb0 : 0 < b) (hbL : mExt ms p.val ≤ b) (hbR : b ≤ 2 * mExt ms (p.val + 1))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiOuterFreeTrialPressure ξ ms qs p t v u b G₀ a ≤
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ j, pairSiteY₀
        (parisiOuterFreeCoupledMasses ms p b) (parisiVar ξ qs 0)
        (parisiOuterFreeTotalVars ξ qs p (t * (deriv ξ v - deriv ξ (qs p))))
        lam (fun l => a (j, l)) (couplingFactorSgn 1 (p.val + 2) 0)
        (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) - lam * u -
          t * (parisiCorrection ξ ms qs + (b - mExt ms (p.val + 1)) * (parisiTheta ξ v - parisiTheta ξ (qs p))) +
          t * parisiOverlapTangentDefect ξ v u := by
  have hvExt := hv
  have hb2 : b ≤ 2 := by nlinarith [mExt_le_one (fun i => (hm.2.2 i).le) (p.val + 1)]
  have hC (i : Fin (k + 2)) (l l' : Fin 2) :=
    parisiDrivenSplitVars_mul_gram hξ qs p hq ht.1 hvExt (parisiSplitIndex p i) l l'
  simp only [parisiSplitIndex_val] at hC
  have hb := coupled_bound_varianceShare_sameFactors_siteField hN (parisiTimeProfile ξ t)
    (parisiSplitCouplingRho qs p v) u (parisiSplitCouplingRho_zero qs p v)
    (S := Icc (0 : ℝ) 1) (parisiSplitCouplingRho_mem_Icc qs p hq hvExt)
    (fun x _ q hq' => parisiTimeProfile_tangent_line_le hξ ht.1 hq' x)
    (deriv_parisiTimeProfile_zero hξ t) G₀
    (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
    (fun i => parisiDrivenSplitVars ξ qs p t v (parisiSplitIndex p i))
    (fun i => parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i))
    (couplingFactorSgn 1 (p.val + 2) 0) (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))
    (parisiDrivenRootVar_mul_gram hξ qs p hq ht.1 hvExt) hC a lam
    (parisiOuterFreeCoupledMasses ms p b) (parisiOuterFreeCoupledMasses_monotone ms p hm hbL hbR)
    (parisiOuterFreeCoupledMasses_pos ms p hm hb0) (parisiOuterFreeCoupledMasses_le_one ms p hm hb2) hreach
  have htop : pairDiagDefect (parisiTimeProfile ξ t) u
      (fun l l' => parisiSplitCouplingRho qs p v l l' ((k + 2) + 1)) =
        t * parisiOverlapTangentDefect ξ v u := by
    have he (l l' : Fin 2) := parisiSplitCouplingRho_top qs p v l l'
    rw [parisiSplitSize_eq p] at he
    simp_rw [he]
    rw [pairDiagDefect_overlapMatrix_eq, parisiOverlapTangentDefect_timeProfile]
  have hv : (fun i : Fin (k + 2) =>
      parisiDrivenSplitVars ξ qs p t v (parisiSplitIndex p i) +
        parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i)) =
      parisiOuterFreeTotalVars ξ qs p (t * (deriv ξ v - deriv ξ (qs p))) := by
    funext i
    have he := congrFun (parisiDrivenSplitVars_add_outerAux_eq hξ qs p hq ht hvExt)
      (parisiSplitIndex p i)
    simpa only [parisiOuterFreeTotalVars] using he
  rw [htop, coupledLevelSum_parisiOuterFree_eq_correction,
    parisiDrivenRootVar_add_aux_eq ξ qs ht, hv] at hb
  simpa only [parisiOuterFreeTrialPressure, parisiDrivenRootVar_add_aux_eq ξ qs ht, hv] using hb


/-- The fixed Gaussian trial bounds every realizable constraint after
averaging the actual independent site fields. -/
theorem randomFieldParisiAuxPairPressure_outer_free_trial_le_siteValue {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t v b : ℝ} (u : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (hb0 : 0 < b) (hbL : mExt ms p.val ≤ b) (hbR : b ≤ 2 * mExt ms (p.val + 1))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (lam : ℝ) (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 1) t u G₀ ≤
      2 * Real.log 2 + parisiOuterFreeCouplingValue μh ξ ms qs p
        (t * (deriv ξ v - deriv ξ (qs p))) b lam - lam * u -
        t * (parisiCorrection ξ ms qs + (b - mExt ms (p.val + 1)) * (parisiTheta ξ v - parisiTheta ξ (qs p))) -
        parisiAuxTerminalVar ξ qs t + t * parisiOverlapTangentDefect ξ v u := by
  let w := t * (deriv ξ v - deriv ξ (qs p))
  let F := fun h : ℝ => pairSiteY₀ (parisiOuterFreeCoupledMasses ms p b)
    (parisiVar ξ qs 0) (parisiOuterFreeTotalVars ξ qs p w) lam (fun _ => h)
    (couplingFactorSgn 1 (p.val + 2) 0) (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))
  let C := 2 * Real.log 2 - lam * u -
    t * (parisiCorrection ξ ms qs + (b - mExt ms (p.val + 1)) * (parisiTheta ξ v - parisiTheta ξ (qs p))) -
    parisiAuxTerminalVar ξ qs t + t * parisiOverlapTangentDefect ξ v u
  have hb2 : b ≤ 2 := by nlinarith [mExt_le_one (fun i => (hm.2.2 i).le) (p.val + 1)]
  have hF : Integrable F μh := integrable_pairSiteY₀_parisiOuterFree_externalField hμ
    ms qs p hm hb0 hb2 ξ w lam
  have hAvg := integrable_externalFieldVec_siteAverage hF N
  have hLeft := integrable_parisiAuxPairPressure_externalField hμ hN ξ ms qs hm p ht u G₀ hreach
  have hRhs : Integrable (fun hVec : Fin N → ℝ => C + (1 / (N : ℝ)) * ∑ i, F (hVec i))
      (externalFieldVecLaw N μh) := (integrable_const C).add hAvg
  have hb := integral_mono hLeft hRhs (fun hVec => by
    have hh := parisiOuterFreeTrialPressure_le_siteValue hN hξ ms qs p hm hq u ht hv
      hb0 hbL hbR G₀ (sharedReplicaSiteField hVec) lam hreach
    rw [parisiOuterFreeTrialPressure_eq_original hN ξ ms qs p t v u hm hb0 G₀
      (sharedReplicaSiteField hVec) hreach] at hh
    dsimp only [C, F, w, sharedReplicaSiteField] at hh ⊢
    linarith)
  have hmean : (∫ hVec : Fin N → ℝ, C + (1 / (N : ℝ)) * ∑ i, F (hVec i)
      ∂externalFieldVecLaw N μh) = C + ∫ h, F h ∂μh := by
    rw [integral_add (integrable_const C) hAvg, integral_externalFieldVec_siteAverage hF hN]
    simp only [integral_const, probReal_univ, one_smul]
  rw [hmean] at hb
  change randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 1) t u G₀ ≤
    C + parisiOuterFreeCouplingValue μh ξ ms qs p w b lam at hb
  dsimp only [C, w] at hb
  linarith

noncomputable def parisiOuterFreeTrialGap (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (v b lam t u : ℝ) : ℝ :=
  2 * parisiInterpolationBracket μh ξ ms qs t -
    (2 * Real.log 2 + parisiOuterFreeCouplingValue μh ξ ms qs p (t * (deriv ξ v - deriv ξ (qs p))) b lam -
      lam * u - t * (parisiCorrection ξ ms qs + (b - mExt ms (p.val + 1)) * (parisiTheta ξ v - parisiTheta ξ (qs p))) -
      parisiAuxTerminalVar ξ qs t + t * parisiOverlapTangentDefect ξ v u)

/-- At the trial constraint and zero coupling the new witness is the
proved free-mass scalar improvement, with no tangent defect. -/
theorem parisiOuterFreeTrialGap_at_trial_zero {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) {b : ℝ} (hb0 : 0 < b) (v t : ℝ) :
    parisiOuterFreeTrialGap μh ξ ms qs p v b 0 t v =
      2 * parisiInterpolationBracket μh ξ ms qs t -
        parisiOuterFreeScalarBound μh ξ ms qs p t v b := by
  unfold parisiOuterFreeTrialGap parisiOuterFreeScalarBound
  rw [parisiOuterFreeCouplingValue_zero hμ ξ ms qs p hm hb0]
  simp only [parisiOverlapTangentDefect, sub_self, zero_mul, sub_zero, mul_zero, add_zero]

/-- A fixed trial, free positive mass and coupling give a globally
continuous scalar gap in time and the realized constraint. -/
theorem continuous_parisiOuterFreeTrialGap_time_overlap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) {b : ℝ} (hb0 : 0 < b) (v lam : ℝ) :
    Continuous (fun x : ℝ × ℝ => parisiOuterFreeTrialGap μh ξ ms qs p v b lam x.1 x.2) := by
  have hc := continuous_randomFieldPairSiteY₀_of_continuous_variance hμ
    (parisiOuterFreeCoupledMasses ms p b) (parisiOuterFreeCoupledMasses_pos ms p hm hb0)
    (p.val + 2) lam (fun _ : ℝ × ℝ => parisiVar ξ qs 0)
    (fun x : ℝ × ℝ => parisiOuterFreeTotalVars ξ qs p (x.1 * (deriv ξ v - deriv ξ (qs p)))) continuous_const
    (fun i => (continuous_apply i).comp ((continuous_parisiOuterFreeTotalVars ξ qs p).comp
      (continuous_fst.mul continuous_const)))
  have hsite : Continuous (fun x : ℝ × ℝ => parisiOuterFreeCouplingValue μh ξ ms qs p
      (x.1 * (deriv ξ v - deriv ξ (qs p))) b lam) := hc
  have hterminal : Continuous (fun x : ℝ × ℝ => (parisiAuxTerminalVar ξ qs x.1 : ℝ)) := (continuous_parisiAuxTerminalVar_time ξ qs).comp continuous_fst
  have hbracket : Continuous (fun x : ℝ × ℝ => parisiInterpolationBracket μh ξ ms qs x.1) := (continuous_parisiInterpolationBracket_time μh ξ ms qs).comp continuous_fst
  have hdefect : Continuous (fun x : ℝ × ℝ => parisiOverlapTangentDefect ξ v x.2) := (continuous_parisiOverlapTangentDefect hξ v).comp continuous_snd
  unfold parisiOuterFreeTrialGap
  exact (hbracket.const_mul 2).sub
    (((((continuous_const.add hsite).sub (continuous_snd.const_mul lam)).sub
      (continuous_fst.mul continuous_const)).sub hterminal).add (continuous_fst.mul hdefect))

/-- Each fixed admissible free-mass trial bounds every realizable
physical overlap, including those outside its own Gaussian split interval. -/
theorem randomFieldParisiAuxPairPressure_le_outerFreeTrialGap {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t v b : ℝ} (u : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (hb0 : 0 < b) (hbL : mExt ms p.val ≤ b) (hbR : b ≤ 2 * mExt ms (p.val + 1)) (lam : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 1) t u G₀ ≤
      2 * parisiInterpolationBracket μh ξ ms qs t -
        parisiOuterFreeTrialGap μh ξ ms qs p v b lam t u := by
  have hb := randomFieldParisiAuxPairPressure_outer_free_trial_le_siteValue hμ hN hξ ms qs p
    hm hq u ht hv hb0 hbL hbR G₀ lam hreach
  unfold parisiOuterFreeTrialGap
  linarith

end SpinGlass
