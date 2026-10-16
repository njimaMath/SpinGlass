import SpinGlass.Parisi.Concentration.ParisiTiltParameters

/-!
# Concentration for the original auxiliary pair cascade

All masses, Gaussian variances, root factors and level factors here are the
ones defining `parisiAuxPairPressure`. Constants are uniform in time,
volume, meeting level and the constrained overlap.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- Canonical interaction disorder, independent original root marks and
the i.i.d. site field for the auxiliary pair cascade. -/
noncomputable def parisiAuxDisorderFieldLaw (N : ℕ) (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) (t : ℝ) :=
  ((multivariateGaussian 0 (overlapCovMatrix N (parisiTimeProfile ξ t))).prod
    (rootMarksLaw N (J := Fin 2) (parisiAuxRootVar ξ qs t))).prod (externalFieldVecLaw N μh)

instance isProbabilityMeasure_parisiAuxDisorderFieldLaw (N : ℕ) (μh : Measure ℝ)
    [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ) (t : ℝ) :
    IsProbabilityMeasure (parisiAuxDisorderFieldLaw N μh ξ qs t) := by
  unfold parisiAuxDisorderFieldLaw
  infer_instance

/-- The actual constrained tilted mass at an original meeting level. -/
noncomputable def parisiAuxTiltMass (N : ℕ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (t u : ℝ)
    (z : (EnergySpace N × (Fin N × Fin 2 → ℝ)) × (Fin N → ℝ)) : ℝ≥0∞ :=
  pairHamConstrainedTiltMass (halveBelow r.val ms) (parisiAuxLevelVars ξ qs t)
    (constraintR N u) z.1.1 0 (sharedReplicaSiteField z.2)
    (couplingFactorSgn 1 (r.val + 1) 0)
    (fun i => couplingFactorSgn 1 (r.val + 1) (i.val + 1)) z.1.2

/-- Its logarithm after all positive-level marks have been averaged. -/
noncomputable def parisiAuxLogTiltMass (N : ℕ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (t u : ℝ)
    (z : (EnergySpace N × (Fin N × Fin 2 → ℝ)) × (Fin N → ℝ)) : ℝ :=
  Real.log (parisiAuxTiltMass N ξ ms qs r t u z).toReal

/-- The original unnormalized log pressure, allowing either an overlap
constraint or the unconstrained pair partition function. -/
noncomputable def parisiAuxLogPressure (N : ℕ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (t : ℝ)
    (c : (Fin 2 → Config N) → ℝ) :=
  pairHamRandomFieldLogPressure (halveBelow r.val ms) (parisiAuxLevelVars ξ qs t) c 0
    (couplingFactorSgn 1 (r.val + 1) 0)
    (fun i => couplingFactorSgn 1 (r.val + 1) (i.val + 1))

/-- Full disorder/root/field concentration for the original auxiliary
cascade, with no residual coefficient or covariance-norm hypotheses. -/
theorem integrable_and_hasSubgaussianMGF_parisiAuxLogTiltMass
    {N k : ℕ} (μh : Measure ℝ) [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : qs ∈ parisiOverlapDomain k)
    (r : Fin (k + 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ᵐ h ∂μh, |h| ≤ R) :
    let P := parisiAuxDisorderFieldLaw N μh ξ qs t
    let F := parisiAuxLogTiltMass N ξ ms qs r t u
    Integrable F P ∧ HasSubgaussianMGF (fun z => F z - ∫ w, F w ∂P)
      ((N : ℝ) * parisiTiltVarianceBound ξ R).toNNReal P := by
  have hcpos : ∃ σ, 0 < constraintR N u σ := by
    obtain ⟨σ, hσ⟩ := hreach
    exact ⟨σ, by simp [constraintR, hσ]⟩
  obtain ⟨hi, hh⟩ := integrable_and_hasSubgaussianMGF_pairHamRandomFieldLogTiltMass μh
    (posSemidef_overlapCovMatrix_parisiTimeProfile hS ht.1) (halveBelow r.val ms)
    (parisiAuxLevelVars ξ qs t) (parisiAuxRootVar ξ qs t)
    (constraintR_nonneg N u) (constraintR_le_one N u) hcpos
    (strictMono_halveBelow hm.1 hm.2.1 _) (halveBelow_pos hm.2.1 _) (halveBelow_lt_one hm.2.2 _)
    0 (couplingFactorSgn 1 (r.val + 1) 0)
    (fun i => couplingFactorSgn 1 (r.val + 1) (i.val + 1)) (abs_nonneg (ξ 1))
    (show (0 : ℝ) ≤ 1 by norm_num) hR hbound
    (overlapCovMatrix_parisiTimeProfile_diag_le N ξ ht)
    (fun l => (sum_sq_couplingFactorSgn_one (r.val + 1) 0 l).le)
  refine ⟨hi, hasSubgaussianMGF_mono hh ?_⟩
  apply Real.toNNReal_mono
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  have hv : (parisiAuxRootVar ξ qs t : ℝ) ≤ (deriv ξ 1 - deriv ξ 0).toNNReal :=
    parisiAuxRootVar_le_total_variance hξ hq ht
  dsimp only [parisiTiltVarianceBound]
  nlinarith only [hv]

/-- A pressure gap for the original explicit auxiliary cascade implies
exponentially small tilted mass, uniformly over time and meeting level. -/
theorem integral_parisiAuxTiltMass_le_of_pressure_gap
    {N k : ℕ} (hN : 0 < N) (μh : Measure ℝ) [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : qs ∈ parisiOverlapDomain k)
    (r : Fin (k + 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ᵐ h ∂μh, |h| ≤ R)
    {b ε : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hblower : ∀ i, b ≤ halveBelow r.val ms i) (hε : 0 < ε) :
    let P := parisiAuxDisorderFieldLaw N μh ξ qs t
    (∫ z, (parisiAuxLogPressure N ξ ms qs r t (constraintR N u) z -
      parisiAuxLogPressure N ξ ms qs r t (fun _ => 1) z) ∂P) ≤ -ε * N →
    (∫ z, (parisiAuxTiltMass N ξ ms qs r t u z).toReal ∂P) ≤
      Real.exp (-(b * ε) * N / 2) +
        Real.exp (-((b * ε) ^ 2 * N) / (8 * (1 + parisiTiltVarianceBound ξ R))) := by
  dsimp only
  intro hgap
  have hcpos : ∃ σ, 0 < constraintR N u σ := by
    obtain ⟨σ, hσ⟩ := hreach
    exact ⟨σ, by simp [constraintR, hσ]⟩
  have hh := integral_pairHamConstrainedTiltMass_bounded_field_le_of_pressure_gap hN μh
    (posSemidef_overlapCovMatrix_parisiTimeProfile hS ht.1) (halveBelow r.val ms)
    (parisiAuxLevelVars ξ qs t) (parisiAuxRootVar ξ qs t)
    (constraintR_nonneg N u) (constraintR_le_one N u) hcpos
    (strictMono_halveBelow hm.1 hm.2.1 _) (halveBelow_pos hm.2.1 _) (halveBelow_lt_one hm.2.2 _)
    0 (couplingFactorSgn 1 (r.val + 1) 0)
    (fun i => couplingFactorSgn 1 (r.val + 1) (i.val + 1)) (abs_nonneg (ξ 1))
    (show (0 : ℝ) ≤ 1 by norm_num) hR hbound
    (overlapCovMatrix_parisiTimeProfile_diag_le N ξ ht)
    (fun l => (sum_sq_couplingFactorSgn_one (r.val + 1) 0 l).le) hb hb1 hblower hε hgap
  refine hh.trans (add_le_add le_rfl (Real.exp_le_exp.2 ?_))
  have hv : (parisiAuxRootVar ξ qs t : ℝ) ≤ (deriv ξ 1 - deriv ξ 0).toNNReal :=
    parisiAuxRootVar_le_total_variance hξ hq ht
  rw [neg_div, neg_div, neg_le_neg_iff]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  dsimp only [parisiTiltVarianceBound]
  nlinarith only [hv]

end SpinGlass
