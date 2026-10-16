import SpinGlass.Parisi.Concentration.PairPressureIntegrability
import SpinGlass.Parisi.Concentration.PairBranchFactorization

/-!
# Identifying the physical pressure gap

The unconstrained original pair pressure is twice the actual single-copy
interpolation pressure. The constrained pressure is the existing
`randomFieldParisiAuxPairPressure`. Their difference therefore has the
normalization needed by the tilted-mass estimate.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ}

/-- The physical single-copy disorder, root marks and i.i.d. site law. -/
noncomputable def parisiInterpolationFieldLaw (N : ℕ) (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (t : ℝ) :=
  ((multivariateGaussian 0 (overlapCovMatrix N (parisiTimeProfile ξ t))).prod
    (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiAuxRootVar ξ qs t)))).prod
      (externalFieldVecLaw N μh)

/-- The actual single-copy recursion, before division by the volume. -/
noncomputable def parisiInterpolationLogPartition (N : ℕ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ)
    (z : (EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ)) : ℝ :=
  Real.log (cascadeRec k ms (gaussianMarks N k (parisiAuxLevelVars ξ qs t))
    (unscaledHamG N k z.1.1 z.2 z.1.2)).toReal

/-- The finite-volume interpolation pressure with the original i.i.d.
site law, using the actual single-copy cascade recursion. -/
noncomputable def parisiInterpolationPressure (N : ℕ) (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ z, parisiInterpolationLogPartition N ξ ms qs t z
    ∂parisiInterpolationFieldLaw N μh ξ qs t

theorem measurable_parisiInterpolationLogPartition (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ) :
    Measurable (parisiInterpolationLogPartition N ξ ms qs t) := by
  apply (measurable_cascadeRec_prod k ms (gaussianMarks N k (parisiAuxLevelVars ξ qs t))
    ?_).ennreal_toReal.log
  unfold Function.uncurry unscaledHamG
  fun_prop

/-- The unused second root column can be discarded exactly. -/
theorem measurePreserving_parisiAuxRootProjection (μh : Measure ℝ)
    [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ) :
    MeasurePreserving
      (fun z : (EnergySpace N × (Fin N × Fin 2 → ℝ)) × (Fin N → ℝ) =>
        ((z.1.1, fun i => z.1.2 (i, 0)), z.2))
      (parisiAuxDisorderFieldLaw N μh ξ qs t) (parisiInterpolationFieldLaw N μh ξ qs t) := by
  have hroot : MeasurePreserving (fun z : Fin N × Fin 2 → ℝ => fun i => z (i, 0))
      (rootMarksLaw N (J := Fin 2) (parisiAuxRootVar ξ qs t))
      (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiAuxRootVar ξ qs t))) := by
    refine ⟨by fun_prop, ?_⟩
    change (Measure.pi (fun _ : Fin N × Fin 2 => gaussianReal 0 (parisiAuxRootVar ξ qs t))).map
      (Prod.fst ∘ splitSitePair) = _
    rw [← Measure.map_map measurable_fst measurable_splitSitePair, map_gaussian_splitSitePair,
      Measure.map_fst_prod, measure_univ, one_smul]
  exact ((MeasurePreserving.id _).prod hroot).prod (MeasurePreserving.id _)

/-- The original unconstrained pair recursion has precisely twice the
single-copy averaged value; all root and field laws are identified. -/
theorem integral_parisiAuxLogPressure_one_eq
    (hN : 0 < N) (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hpos : ∀ i, 0 < ms i)
    (r : Fin (k + 1)) (t : ℝ) :
    (∫ z, parisiAuxLogPressure N ξ ms qs r t (fun _ => 1) z
      ∂parisiAuxDisorderFieldLaw N μh ξ qs t) =
        2 * (N : ℝ) * parisiInterpolationPressure N μh ξ ms qs t := by
  let T := fun z : (EnergySpace N × (Fin N × Fin 2 → ℝ)) × (Fin N → ℝ) =>
    ((z.1.1, fun i => z.1.2 (i, 0)), z.2)
  have hT := measurePreserving_parisiAuxRootProjection (N := N) μh ξ qs t
  have hpoint (z) : parisiAuxLogPressure N ξ ms qs r t (fun _ => 1) z =
      2 * parisiInterpolationLogPartition N ξ ms qs t (T z) :=
    log_cascadeRec_pairHamG_original_one_eq_two_mul r.val ms (parisiAuxLevelVars ξ qs t)
      hpos z.1.1 z.2 z.1.2
  simp_rw [hpoint]
  rw [integral_const_mul]
  have he : (∫ z, parisiInterpolationLogPartition N ξ ms qs t (T z)
      ∂parisiAuxDisorderFieldLaw N μh ξ qs t) =
      ∫ z, parisiInterpolationLogPartition N ξ ms qs t z
        ∂parisiInterpolationFieldLaw N μh ξ qs t := by
    rw [← hT.map_eq, integral_map hT.measurable.aemeasurable
      (measurable_parisiInterpolationLogPartition ξ ms qs t).aestronglyMeasurable]
  rw [he]
  unfold parisiInterpolationPressure
  field_simp

/-- The averaged unnormalized constrained recursion equals volume times
the existing physical constrained auxiliary pressure. -/
theorem integral_parisiAuxLogPressure_constraint_eq
    (hN : 0 < N) {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (r : Fin (k + 1)) (t u : ℝ)
    (hS : (overlapCovMatrix N (parisiTimeProfile ξ t)).PosSemidef)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    (∫ z, parisiAuxLogPressure N ξ ms qs r t (constraintR N u) z
      ∂parisiAuxDisorderFieldLaw N μh ξ qs t) =
      (N : ℝ) * randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u
        (GaussianField.ofMultivariateGaussian hS) := by
  have hcpos : ∃ σ, constraintR N u σ = 1 := by
    obtain ⟨σ, hσ⟩ := hreach
    exact ⟨σ, by simp [constraintR, hσ]⟩
  have hi := integrable_pairHamRandomFieldLogPressure hμ hS (halveBelow r.val ms)
    (parisiAuxLevelVars ξ qs t) (parisiAuxRootVar ξ qs t)
    (constraintR_nonneg N u) (constraintR_le_one N u) hcpos
    (halveBelow_pos hm.2.1 _) (halveBelow_le_one (fun i => (hm.2.2 i).le) _)
    0 (couplingFactorSgn 1 (r.val + 1) 0)
    (fun i => couplingFactorSgn 1 (r.val + 1) (i.val + 1))
  change (∫ z, pairHamRandomFieldLogPressure (halveBelow r.val ms)
    (parisiAuxLevelVars ξ qs t) (constraintR N u) 0
    (couplingFactorSgn 1 (r.val + 1) 0)
    (fun i => couplingFactorSgn 1 (r.val + 1) (i.val + 1)) z
    ∂((multivariateGaussian 0 (overlapCovMatrix N (parisiTimeProfile ξ t))).prod
      (rootMarksLaw N (J := Fin 2) (parisiAuxRootVar ξ qs t))).prod
      (externalFieldVecLaw N μh)) = _
  rw [integral_prod_symm _ hi]
  unfold randomFieldParisiAuxPairPressure parisiAuxPairPressure
  rw [integral_const_mul]
  simp only [Nat.add_sub_cancel, GaussianField.ofMultivariateGaussian, id_eq]
  change _ = (N : ℝ) * ((1 / (N : ℝ)) * _)
  rw [← mul_assoc, mul_one_div_cancel (by exact_mod_cast hN.ne'), one_mul]
  rfl

/-- The exact pressure-gap normalization consumed by concentration.
The integrability of both pressures is proved from a first field moment. -/
theorem integral_parisiAuxLogPressure_gap_eq
    (hN : 0 < N) {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (r : Fin (k + 1)) (t u : ℝ)
    (hS : (overlapCovMatrix N (parisiTimeProfile ξ t)).PosSemidef)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    (∫ z, (parisiAuxLogPressure N ξ ms qs r t (constraintR N u) z -
      parisiAuxLogPressure N ξ ms qs r t (fun _ => 1) z)
      ∂parisiAuxDisorderFieldLaw N μh ξ qs t) =
      (N : ℝ) * (randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u
        (GaussianField.ofMultivariateGaussian hS) -
          2 * parisiInterpolationPressure N μh ξ ms qs t) := by
  have hi (c : (Fin 2 → Config N) → ℝ) (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
      (hcpos : ∃ σ, c σ = 1) : Integrable (parisiAuxLogPressure N ξ ms qs r t c)
        (parisiAuxDisorderFieldLaw N μh ξ qs t) :=
    integrable_pairHamRandomFieldLogPressure hμ hS (halveBelow r.val ms)
      (parisiAuxLevelVars ξ qs t) (parisiAuxRootVar ξ qs t) hc0 hc1 hcpos
      (halveBelow_pos hm.2.1 _) (halveBelow_le_one (fun i => (hm.2.2 i).le) _)
      0 (couplingFactorSgn 1 (r.val + 1) 0)
      (fun i => couplingFactorSgn 1 (r.val + 1) (i.val + 1))
  have hcpos : ∃ σ, constraintR N u σ = 1 := by
    obtain ⟨σ, hσ⟩ := hreach
    exact ⟨σ, by simp [constraintR, hσ]⟩
  rw [integral_sub (hi _ (constraintR_nonneg N u) (constraintR_le_one N u) hcpos)
    (hi _ (fun _ => zero_le_one) (fun _ => le_rfl) ⟨fun _ _ => true, rfl⟩),
    integral_parisiAuxLogPressure_constraint_eq hN hμ ξ ms qs hm r t u hS hreach,
    integral_parisiAuxLogPressure_one_eq hN μh ξ ms qs hm.2.1 r t]
  ring

end SpinGlass
