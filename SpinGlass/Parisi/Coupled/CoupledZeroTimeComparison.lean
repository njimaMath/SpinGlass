import SpinGlass.Parisi.Coupled.CoupledMainOuterUniform

/-!
# Zero-time comparison at every realizable overlap

At zero time every driven covariance increment vanishes. The coupled
comparison then holds without restricting the overlap to either
neighboring interval. The actual auxiliary pressure is retained.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

theorem parisiSplitPressure_zero_le_siteValue {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ 0) σ τ))
    (es : Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0)
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiSplitPressure ξ ms qs p 0 u G₀ es a ≤
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ j, pairSiteY₀
        (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)) (parisiVar ξ qs 0)
        (fun i => parisiDrivenSplitVars ξ qs p 0 u i + es i) lam (fun l => a (j, l))
        (couplingFactorSgn 1 (p.val + 2) 0) (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) - lam * u := by
  have hpos := parisiResponseSplitMasses_pos ms p hm
  have hle := parisiResponseSplitMasses_le_one ms p hm
  have hmono := parisiResponseSplitMasses_monotone ms p hm
  have hb := coupled_bound_varianceShare_sameFactors_siteField hN (parisiTimeProfile ξ 0)
    (parisiSplitCouplingRho qs p u) u (parisiSplitCouplingRho_zero qs p u)
    (S := univ) (fun _ _ _ => mem_univ _)
    (fun x _ q _ => by simp only [parisiTimeProfile, deriv_parisiTimeProfile, zero_mul, mul_zero, zero_add, le_refl])
    (by simp only [deriv_parisiTimeProfile, zero_mul]) G₀
    (parisiDrivenRootVar ξ qs 0) (parisiAuxRootVar ξ qs 0)
    (parisiDrivenSplitVars ξ qs p 0 u) es (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))
    (fun _ _ => by simp only [parisiDrivenRootVar, Real.toNNReal_zero, zero_mul,
      NNReal.coe_zero, deriv_parisiTimeProfile, sub_self])
    (fun _ _ _ => by simp only [parisiDrivenSplitVars, Real.toNNReal_zero, zero_mul,
      NNReal.coe_zero, deriv_parisiTimeProfile, sub_self])
    a lam (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p))
    (halveBelow_monotone hmono hpos _) (halveBelow_pos hpos _) (halveBelow_le_one hle _) hreach
  rw [pairDiagDefect_parisiSplitCouplingRho_top, coupledLevelSum_parisiSplit_eq_correction,
    zero_mul, sub_zero, add_zero] at hb
  simpa only [parisiDrivenRootVar_add_aux_eq ξ qs (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num),
    parisiSplitPressure] using hb

theorem randomFieldParisiSplitPressure_zero_le_siteValue {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ 0) σ τ))
    (es : Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiSplitPressure μh ξ ms qs p 0 u G₀ es ≤
      2 * Real.log 2 + randomFieldPairSiteY₀ μh
        (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)) (parisiVar ξ qs 0)
        (fun i => parisiDrivenSplitVars ξ qs p 0 u i + es i) lam
        (couplingFactorSgn 1 (p.val + 2) 0)
        (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) - lam * u := by
  let F := fun h : ℝ => pairSiteY₀
    (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)) (parisiVar ξ qs 0)
    (fun i => parisiDrivenSplitVars ξ qs p 0 u i + es i) lam (fun _ => h)
    (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))
  have hF : Integrable F μh := integrable_pairSiteY₀_parisiSplit_externalField hμ ms qs p hm ξ _ lam
  have hAvg := integrable_externalFieldVec_siteAverage hF N
  have hLeft := integrable_parisiSplitPressure_externalField hμ ξ ms qs p 0 u hm G₀ es hreach
  have hRhs : Integrable (fun hVec : Fin N → ℝ =>
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) - lam * u - (0 : ℝ) * parisiCorrection ξ ms qs)
      (externalFieldVecLaw N μh) :=
    (((integrable_const (2 * Real.log 2)).add hAvg).sub (integrable_const (lam * u))).sub
      (integrable_const ((0 : ℝ) * parisiCorrection ξ ms qs))
  have hb := integral_mono hLeft hRhs fun hVec => by
    simp only [zero_mul, sub_zero]
    exact parisiSplitPressure_zero_le_siteValue hN ξ ms qs p hm u G₀ es
      (sharedReplicaSiteField hVec) lam hreach
  have hmean : (∫ hVec : Fin N → ℝ,
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) - lam * u - (0 : ℝ) * parisiCorrection ξ ms qs
      ∂externalFieldVecLaw N μh) =
      2 * Real.log 2 + (∫ h, F h ∂μh) - lam * u - (0 : ℝ) * parisiCorrection ξ ms qs := by
    have ha := integral_add (integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)) hAvg
    have hs := integral_sub ((integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)).add hAvg)
      (integrable_const (lam * u))
    have ht' := integral_sub
      (((integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)).add hAvg).sub
        (integrable_const (lam * u))) (integrable_const ((0 : ℝ) * parisiCorrection ξ ms qs))
    simp only [Pi.add_apply, Pi.sub_apply] at ha hs ht'
    rw [ht', hs, ha, integral_externalFieldVec_siteAverage hF hN]
    simp only [integral_const, probReal_univ, one_smul]
  rw [hmean] at hb
  simp only [zero_mul, sub_zero] at hb
  exact hb

end SpinGlass
