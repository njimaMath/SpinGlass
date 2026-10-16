import SpinGlass.Parisi.Coupled.CoupledCanonicalFieldComparison
import SpinGlass.Parisi.Coupled.CoupledCanonicalCoupling

/-!
# Continuous canonical coupling witnesses for the physical pressure

The actual finite-volume comparison is averaged over the i.i.d. field law
at any coupling. Its physical-pressure normalization cancels the explicit
correction terms, leaving a continuous one-site gap independent of volume.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable def parisiCanonicalCouplingGap (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t v lam : ℝ) : ℝ :=
  2 * (∫ h, closedParisiX₀ ξ ms qs h ∂μh) + lam * (if negative then -v else v) -
    parisiCanonicalSiteValue μh ξ ms qs negative r p t v lam

theorem parisiCanonicalCouplingGap_zero_eq (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t v : ℝ) :
    parisiCanonicalCouplingGap μh ξ ms qs negative r p t v 0 =
      2 * (∫ h, closedParisiX₀ ξ ms qs h ∂μh) - randomFieldPairColeHopfListValue μh
        (parisiCanonicalPairLevels ξ ms qs negative r p t v) := by
  simp only [parisiCanonicalCouplingGap, zero_mul, add_zero, parisiCanonicalSiteValue_zero_eq]

theorem continuousOn_parisiCanonicalCouplingGap_time_overlap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (lam : ℝ) :
    ContinuousOn (fun x : ℝ × ℝ => parisiCanonicalCouplingGap μh ξ ms qs negative r p x.1 x.2 lam)
      (univ ×ˢ Icc (0 : ℝ) 1) := by
  have hs : Continuous (fun x : ℝ × ℝ => if negative then -x.2 else x.2) := by
    cases negative <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  unfold parisiCanonicalCouplingGap
  exact (continuousOn_const.add (hs.const_mul lam).continuousOn).sub
    (continuousOn_parisiCanonicalSiteValue_time_overlap hμ hξ ms qs negative r p lam)

/-- Every actual canonical coupling gap bounds the original physical
pressure at every positive volume. The field law has only a finite first
moment; no physical-pressure or Gaussian-law identity is assumed. -/
theorem randomFieldParisiAuxPairPressure_le_canonicalCouplingGap {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {t v : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) (lam : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = if negative then -v else v) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t
        (if negative then -v else v) G₀ ≤
      2 * parisiInterpolationBracket μh ξ ms qs t -
        parisiCanonicalCouplingGap μh ξ ms qs negative r p t v lam := by
  let F := fun h => pairColeHopfIterate (parisiCanonicalPairLevels ξ ms qs negative r p t v)
    (pairSiteY lam) h h
  let C : ℝ := 2 * Real.log 2 - lam * (if negative then -v else v) -
    t * parisiCorrection ξ ms qs - parisiAuxTerminalVar ξ qs t
  have hF : Integrable F μh := integrable_pairColeHopfIterate_terminal_externalField hμ _
    (pairUnitLipschitz_pairSiteY lam)
  have hAvg := integrable_externalFieldVec_siteAverage hF N
  have hLeft := integrable_parisiAuxPairPressure_externalField hμ hN ξ ms qs hm r ht
    (if negative then -v else v) G₀ hreach
  have hRhs : Integrable (fun hVec : Fin N → ℝ => C + (1 / (N : ℝ)) * ∑ i, F (hVec i))
      (externalFieldVecLaw N μh) := (integrable_const C).add hAvg
  have hb := integral_mono hLeft hRhs (fun hVec => by
    have hp := parisiCanonicalPressure_le_siteValue hN hξ ms qs hm hq negative r p ht hv G₀
      (sharedReplicaSiteField hVec) lam hreach
    have hsite (i : Fin N) : pairSiteY₀ (parisiCanonicalPositiveMasses ms r p) 1 (fun _ => 1) lam
        (fun l => sharedReplicaSiteField hVec (i, l))
        (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t v +
          parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t v)
        (fun j => parisiCanonicalDrivenFactor ξ ms qs negative r p t v j +
          parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t v j) = F (hVec i) :=
      pairSiteY₀_parisiCanonical_eq ξ ms qs hm negative r p t v lam (fun _ => hVec i)
    simp_rw [hsite] at hp
    rw [parisiCanonicalPressure_eq_original hN ξ ms qs hm negative r p t v G₀
      (sharedReplicaSiteField hVec) hreach] at hp
    dsimp only [C]
    linarith)
  have hmean : (∫ hVec : Fin N → ℝ, C + (1 / (N : ℝ)) * ∑ i, F (hVec i)
      ∂externalFieldVecLaw N μh) = C + ∫ h, F h ∂μh := by
    have ha := integral_add (integrable_const (μ := externalFieldVecLaw N μh) C) hAvg
    rw [ha, integral_externalFieldVec_siteAverage hF hN]
    simp only [integral_const, probReal_univ, one_smul]
  rw [hmean] at hb
  change randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t
    (if negative then -v else v) G₀ ≤ _ at hb
  unfold parisiInterpolationBracket parisiSplitBracket parisiCanonicalCouplingGap
    parisiCanonicalSiteValue randomFieldPairColeHopfTerminalValue
  dsimp only [C, F] at hb
  linarith

end SpinGlass
