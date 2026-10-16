import SpinGlass.Parisi.Interpolation.PressureLaw

/-!
# Integrability of the single-copy interpolation

The exact unconstrained-pair factorization transfers the proved joint
logarithmic integrability to the single-copy pressure. Only a finite first
moment of the site field is required.
-/

open MeasureTheory ProbabilityTheory Set

namespace SpinGlass

variable {N k : ℕ}

theorem integrable_parisiInterpolationLogPartition
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (t : ℝ)
    (hS : (overlapCovMatrix N (parisiTimeProfile ξ t)).PosSemidef) :
    Integrable (parisiInterpolationLogPartition N ξ ms qs t)
      (parisiInterpolationFieldLaw N μh ξ qs t) := by
  have hpair := integrable_pairHamRandomFieldLogPressure hμ hS (halveBelow 0 ms)
    (parisiAuxLevelVars ξ qs t) (parisiAuxRootVar ξ qs t)
    (fun _ => zero_le_one) (fun _ => le_rfl) ⟨fun _ _ => true, rfl⟩
    (halveBelow_pos hpos 0) (halveBelow_le_one hle 0) 0
    (couplingFactorSgn 1 1 0) (fun p => couplingFactorSgn 1 1 (p.val + 1))
  have hT := measurePreserving_parisiAuxRootProjection (N := N) μh ξ qs t
  apply (hT.integrable_comp
    (measurable_parisiInterpolationLogPartition ξ ms qs t).aestronglyMeasurable).1
  refine (hpair.const_mul (1 / 2 : ℝ)).congr (.of_forall fun z => ?_)
  change (1 / 2 : ℝ) * Real.log (cascadeRec k (halveBelow 0 ms)
    (siteGaussianMarks (Fin N × Fin 2) k (parisiAuxLevelVars ξ qs t))
    (pairHamG N k (fun _ => 1) z.1.1 0 (sharedReplicaSiteField z.2)
      (couplingFactorSgn 1 1 0) (fun p => couplingFactorSgn 1 1 (p.val + 1)) z.1.2)).toReal = _
  rw [log_cascadeRec_pairHamG_original_one_eq_two_mul 0 ms _ hpos]
  dsimp only [parisiInterpolationLogPartition, Function.comp_apply]
  ring

/-- The same integrability after transporting every time to one fixed law. -/
theorem integrable_parisiBaseLogPartition
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hS : (overlapCovMatrix N ξ).PosSemidef) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun z : (EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ) =>
      Real.log (cascadeRec k ms (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1)))
        (hamG N k t z.2 z.1.1 z.1.2)).toReal)
      (parisiBaseDisorderFieldLaw N μh ξ qs) := by
  have hT := measurePreserving_parisiInterpolationScaling μh ξ qs hS ht
  have hi := (hT.integrable_comp
    (measurable_parisiInterpolationLogPartition ξ ms qs t).aestronglyMeasurable).2
      (integrable_parisiInterpolationLogPartition hμ ξ ms qs hpos hle t
        (posSemidef_overlapCovMatrix_parisiTimeProfile hS ht.1))
  exact hi.congr (.of_forall fun z => parisiInterpolationLogPartition_scaling_eq ξ ms qs ht.2 z)

end SpinGlass
