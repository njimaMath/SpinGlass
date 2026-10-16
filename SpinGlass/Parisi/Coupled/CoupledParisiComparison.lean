import SpinGlass.Parisi.Coupled.CoupledParisiCorrection

/-!
# The finite-volume coupled comparison for the actual Parisi split

The covariance, overlap-domain and correction hypotheses of the general
coupled theorem are discharged from the preserved profile contract and the
actual split arrays. The remaining pressure is explicit in the auxiliary
Gaussian marks, so its identification with the original interpolation
cascade is a separate obligation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The concrete finite-volume constrained pressure of the matching
Parisi split, for a specified auxiliary Gaussian variance list. -/
noncomputable def parisiSplitPressure {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (es : Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0)
    (a : Fin N × Fin 2 → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec ((p.val + 1) + ((k - p.val) + 1))
      (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p))
      (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) ((p.val + 1) + ((k - p.val) + 1))
        (fun i => parisiDrivenSplitVars ξ qs p t u i + es i))
      (coupledG N u a
        (coupledDrivenVarianceFactor (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
          (couplingFactorSgn 1 (p.val + 2) 0))
        (coupledAuxVarianceFactor (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
          (couplingFactorSgn 1 (p.val + 2) 0))
        (fun i => coupledDrivenVarianceFactor (parisiDrivenSplitVars ξ qs p t u i) (es i)
          (couplingFactorSgn 1 (p.val + 2) (i.val + 1)))
        (fun i => coupledAuxVarianceFactor (parisiDrivenSplitVars ξ qs p t u i) (es i)
          (couplingFactorSgn 1 (p.val + 2) (i.val + 1))) (parisiTimeProfile ξ t) G₀ 1 θ)).toReal
    ∂Pm.prod (rootMarksLaw N (parisiVar ξ qs 0))

/-- The finite-volume comparison for the actual parameters. Covariance
increments, tangent support, admissibility and the terminal defect are
proved inputs, and the correction is exactly t times the old correction. -/
theorem parisiSplitPressure_le_siteValue {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (es : Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0)
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiSplitPressure ξ ms qs p t u G₀ es a ≤
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ j, pairSiteY₀
        (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)) (parisiVar ξ qs 0)
        (fun i => parisiDrivenSplitVars ξ qs p t u i + es i) lam (fun l => a (j, l))
        (couplingFactorSgn 1 (p.val + 2) 0)
        (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) - lam * u -
          t * parisiCorrection ξ ms qs := by
  have hpos := parisiResponseSplitMasses_pos ms p hm
  have hle := parisiResponseSplitMasses_le_one ms p hm
  have hmono := parisiResponseSplitMasses_monotone ms p hm
  have hb := coupled_bound_varianceShare_sameFactors_siteField hN (parisiTimeProfile ξ t)
    (parisiSplitCouplingRho qs p u) u (parisiSplitCouplingRho_zero qs p u)
    (S := Icc (0 : ℝ) 1) (parisiSplitCouplingRho_mem_Icc qs p hq hu)
    (fun x _ q hq' => parisiTimeProfile_tangent_line_le hξ ht.1 hq' x)
    (deriv_parisiTimeProfile_zero hξ t) G₀
    (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
    (parisiDrivenSplitVars ξ qs p t u) es (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))
    (parisiDrivenRootVar_mul_gram hξ qs p hq ht.1 hu)
    (parisiDrivenSplitVars_mul_gram hξ qs p hq ht.1 hu)
    a lam (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p))
    (halveBelow_monotone hmono hpos _) (halveBelow_pos hpos _) (halveBelow_le_one hle _) hreach
  rw [pairDiagDefect_parisiSplitCouplingRho_top,
    coupledLevelSum_parisiSplit_eq_correction, add_zero] at hb
  simpa only [parisiDrivenRootVar_add_aux_eq ξ qs ht, parisiSplitPressure] using hb

/-- Actual inner-oriented auxiliary fields give the concrete response
variance array on the right side of the finite-volume comparison. -/
theorem parisiSplitPressure_inner_le_siteValue {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiSplitPressure ξ ms qs p t u G₀ (parisiInnerAuxSplitVars ξ qs p t) a ≤
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ j, pairSiteY₀
        (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)) (parisiVar ξ qs 0)
        (parisiResponseSplitVars ξ qs p (t * (deriv ξ (qExt qs (p.val + 2)) - deriv ξ u)))
        lam (fun l => a (j, l)) (couplingFactorSgn 1 (p.val + 2) 0)
        (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) - lam * u -
          t * parisiCorrection ξ ms qs := by
  have hb := parisiSplitPressure_le_siteValue hN hξ ms qs p hm hq ht hu G₀
    (parisiInnerAuxSplitVars ξ qs p t) a lam hreach
  simpa only [parisiDrivenSplitVars_add_innerAux_eq hξ qs p hq ht hu] using hb

/-- The mirror auxiliary construction gives the other concrete
response variance array, including the terminal old interval. -/
theorem parisiSplitPressure_outer_le_siteValue {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiSplitPressure ξ ms qs p t u G₀ (parisiOuterAuxSplitVars ξ qs p t) a ≤
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ j, pairSiteY₀
        (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)) (parisiVar ξ qs 0)
        (parisiResponseSplitVars ξ qs p
          (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) - t * (deriv ξ u - deriv ξ (qs p))))
        lam (fun l => a (j, l)) (couplingFactorSgn 1 (p.val + 2) 0)
        (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) - lam * u -
          t * parisiCorrection ξ ms qs := by
  have hb := parisiSplitPressure_le_siteValue hN hξ ms qs p hm hq ht hu G₀
    (parisiOuterAuxSplitVars ξ qs p t) a lam hreach
  simpa only [parisiDrivenSplitVars_add_outerAux_eq hξ qs p hq ht hu] using hb

end SpinGlass
