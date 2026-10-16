import SpinGlass.Parisi.Coupled.CoupledCanonicalPressure
import SpinGlass.Parisi.Coupled.CoupledCanonicalRootRecursion

/-!
# Canonical comparison averaged over the actual i.i.d. site law

The physical pressure and the complete canonical one-site recursion have
proved identifications. Their field average uses the independent coordinate
law and a finite first moment, with the same realized field in both replicas.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The original auxiliary pressure is integrable under the actual
i.i.d. field law with finite first moment. -/
theorem integrable_parisiAuxPairPressure_externalField {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    Integrable (fun hVec => parisiAuxPairPressure ξ ms qs (r.val + 1) t u G₀
      (sharedReplicaSiteField hVec)) (externalFieldVecLaw N μh) := by
  have hi := (integrable_parisiSplitPressure_externalField hμ ξ ms qs r t u hm G₀
    (parisiOuterAuxSplitVars ξ qs r t) hreach).sub
      (integrable_const (parisiAuxTerminalVar ξ qs t : ℝ))
  apply hi.congr (.of_forall fun hVec => ?_)
  have he := parisiSplitPressure_outer_eq_original hN ξ ms qs r u hm ht G₀
    (sharedReplicaSiteField hVec) hreach
  dsimp only [Pi.sub_apply]
  linarith

/-- The actual original pressure is bounded by the complete canonical
paired one-site list after i.i.d. field averaging. Its terminal variance
is included explicitly, as required by (14.312). -/
theorem randomFieldParisiAuxPairPressure_le_parisiCanonical {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = if negative then -u else u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t
        (if negative then -u else u) G₀ + parisiAuxTerminalVar ξ qs t ≤
      2 * Real.log 2 + randomFieldPairColeHopfListValue μh
        (parisiCanonicalPairLevels ξ ms qs negative r p t u) - t * parisiCorrection ξ ms qs := by
  let F := fun h => pairColeHopfIterate (parisiCanonicalPairLevels ξ ms qs negative r p t u)
    (fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b) h h
  have hF : Integrable F μh := integrable_pairColeHopfIterate_externalField hμ _
  have hAvg := integrable_externalFieldVec_siteAverage hF N
  have hLeft := integrable_parisiAuxPairPressure_externalField hμ hN ξ ms qs hm r ht
    (if negative then -u else u) G₀ hreach
  have hRhs : Integrable (fun hVec : Fin N → ℝ =>
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) -
        t * parisiCorrection ξ ms qs - parisiAuxTerminalVar ξ qs t) (externalFieldVecLaw N μh) :=
    (((integrable_const (2 * Real.log 2)).add hAvg).sub
      (integrable_const (t * parisiCorrection ξ ms qs))).sub
      (integrable_const (parisiAuxTerminalVar ξ qs t : ℝ))
  have hb := integral_mono hLeft hRhs (fun hVec => by
    have hp := parisiCanonicalPressure_le_siteValue hN hξ ms qs hm hq negative r p ht hu G₀
      (sharedReplicaSiteField hVec) 0 hreach
    have hsite (i : Fin N) : pairSiteY₀ (parisiCanonicalPositiveMasses ms r p) 1 (fun _ => 1) 0
        (fun l => sharedReplicaSiteField hVec (i, l))
        (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t u +
          parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t u)
        (fun j => parisiCanonicalDrivenFactor ξ ms qs negative r p t u j +
          parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t u j) = F (hVec i) :=
      pairSiteY₀_parisiCanonical_zero_eq ξ ms qs hm negative r p t u (hVec i)
    simp only [zero_mul, sub_zero, hsite] at hp
    rw [parisiCanonicalPressure_eq_original hN ξ ms qs hm negative r p t u G₀
      (sharedReplicaSiteField hVec) hreach] at hp
    linarith)
  have hmean : (∫ hVec : Fin N → ℝ,
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) -
        t * parisiCorrection ξ ms qs - parisiAuxTerminalVar ξ qs t ∂externalFieldVecLaw N μh) =
      2 * Real.log 2 + (∫ h, F h ∂μh) -
        t * parisiCorrection ξ ms qs - parisiAuxTerminalVar ξ qs t := by
    have ha := integral_add (integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)) hAvg
    have hs := integral_sub
      ((integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)).add hAvg)
      (integrable_const (t * parisiCorrection ξ ms qs))
    have hv := integral_sub
      (((integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)).add hAvg).sub
        (integrable_const (t * parisiCorrection ξ ms qs)))
      (integrable_const (parisiAuxTerminalVar ξ qs t : ℝ))
    simp only [Pi.add_apply, Pi.sub_apply] at ha hs hv
    rw [hv, hs, ha, integral_externalFieldVec_siteAverage hF hN]
    simp only [integral_const, probReal_univ, one_smul]
  rw [hmean] at hb
  change randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t
    (if negative then -u else u) G₀ ≤ _ at hb
  change _ ≤ 2 * Real.log 2 + (∫ h, F h ∂μh) - t * parisiCorrection ξ ms qs
  linarith

end SpinGlass
