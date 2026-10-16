import SpinGlass.Parisi.Concentration.ParisiPressureConcentration
import SpinGlass.Parisi.Concentration.PairBranchMeeting

/-!
# Pressure-gap decay of the physical branch-meeting mass

The joint constrained tree mass is averaged under the original interaction,
root and i.i.d. field laws. Its exact tilt identity transfers concentration
with a rate uniform in volume, time, level and constrained overlap.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The actual averaged constrained mass of a pair of tree branches
meeting at the specified original level. -/
noncomputable def parisiBranchMeetingMass (N : ℕ) (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (t u : ℝ) : ℝ :=
  ∫ z, unscaledBranchMeetingMass ms (parisiAuxLevelVars ξ qs t) r.val
    (constraintR N u) z.1.1 z.2 z.1.2 ∂parisiInterpolationFieldLaw N μh ξ qs t

/-- Exact disorder, root and field averaging of the tree-meeting
identity. The mass increment stays as a factor, without division. -/
theorem parisiBranchMeetingMass_eq_integral_tilt
    {N k : ℕ} (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (t u : ℝ) :
    parisiBranchMeetingMass N μh ξ ms qs r t u =
      (mExt ms (r.val + 1) - mExt ms r.val) *
        ∫ z, (parisiAuxTiltMass N ξ ms qs r t u z).toReal
          ∂parisiAuxDisorderFieldLaw N μh ξ qs t := by
  have hT := measurePreserving_parisiAuxRootProjection (N := N) μh ξ qs t
  have hF := measurable_unscaledBranchMeetingMass ms (parisiAuxLevelVars ξ qs t)
    hm r (constraintR_le_one N u)
  unfold parisiBranchMeetingMass
  rw [← hT.map_eq, integral_map hT.measurable.aemeasurable hF.aestronglyMeasurable]
  simp_rw [unscaledBranchMeetingMass_eq_tilt ms (parisiAuxLevelVars ξ qs t)
    hm r (constraintR_le_one N u)]
  exact integral_const_mul _ _

/-- An unrealizable overlap has zero tilted mass, including before
averaging any interaction disorder, root marks or site fields. -/
theorem parisiAuxTiltMass_eq_zero_of_unrealizable
    {N k : ℕ} (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (t u : ℝ)
    (habsent : ¬ ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u)
    (z : (EnergySpace N × (Fin N × Fin 2 → ℝ)) × (Fin N → ℝ)) :
    parisiAuxTiltMass N ξ ms qs r t u z = 0 := by
  have hc : constraintR N u = fun _ => 0 := by
    funext σ
    exact ite_eq_right (fun hh => habsent ⟨σ, hh⟩)
  have hzero (x : Fin k → Fin N × Fin 2 → ℝ) :
      pairHamG N k (constraintR N u) z.1.1 0 (sharedReplicaSiteField z.2)
        (couplingFactorSgn 1 (r.val + 1) 0)
        (fun p => couplingFactorSgn 1 (r.val + 1) (p.val + 1)) z.1.2 x = 0 := by
    simp only [hc, pairHamG, pairBranchZX, zero_mul, Finset.sum_const_zero, ENNReal.ofReal_zero]
  unfold parisiAuxTiltMass pairHamConstrainedTiltMass
  simp only [hzero, ENNReal.zero_div]
  rw [cascadeTilt_eq_lintegral_density k _ _
    (measurable_pairHamG' N k _ _ _ _ _ _ _) measurable_const]
  simp only [mul_zero, lintegral_zero]

theorem parisiBranchMeetingMass_eq_zero_of_unrealizable
    {N k : ℕ} (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (t u : ℝ)
    (habsent : ¬ ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiBranchMeetingMass N μh ξ ms qs r t u = 0 := by
  rw [parisiBranchMeetingMass_eq_integral_tilt μh ξ ms qs hm r t u]
  simp only [parisiAuxTiltMass_eq_zero_of_unrealizable ξ ms qs r t u habsent,
    ENNReal.toReal_zero, integral_zero, mul_zero]

theorem parisiBranchMeetingMass_nonneg
    {N k : ℕ} (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (t u : ℝ) :
    0 ≤ parisiBranchMeetingMass N μh ξ ms qs r t u := by
  rw [parisiBranchMeetingMass_eq_integral_tilt μh ξ ms qs hm r t u]
  exact mul_nonneg (hm.mExt_gap_pos r).le (integral_nonneg fun _ => ENNReal.toReal_nonneg)

/-- The pressure-gap estimate for the actual joint branch-meeting mass.
The positive rate is chosen before volume, time, level and overlap. -/
theorem exists_uniform_parisiBranchMeetingMass_exponential_bound
    {k : ℕ} (μh : Measure ℝ) [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : qs ∈ parisiOverlapDomain k)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ᵐ h ∂μh, |h| ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 0 < N →
      ∀ hS : (overlapCovMatrix N ξ).PosSemidef,
      ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1), ∀ r : Fin (k + 1), ∀ u : ℝ,
      (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
      randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u
        (GaussianField.ofMultivariateGaussian
          (posSemidef_overlapCovMatrix_parisiTimeProfile hS ht.1)) ≤
          2 * parisiInterpolationPressure N μh ξ ms qs t - ε →
      parisiBranchMeetingMass N μh ξ ms qs r t u ≤ 2 * Real.exp (-c * N) := by
  obtain ⟨c, hc, hmass⟩ := exists_uniform_parisiAuxTiltMass_exponential_bound μh hξ
    ms qs hm hq hR hbound hε
  refine ⟨c, hc, ?_⟩
  intro N hN hS t ht r u hreach hgap
  rw [parisiBranchMeetingMass_eq_integral_tilt μh ξ ms qs hm r t u]
  have hδ : mExt ms (r.val + 1) - mExt ms r.val ≤ 1 := by
    have h0 := mExt_nonneg (fun i => (hm.2.1 i).le) r.val
    have h1 := mExt_le_one (fun i => (hm.2.2 i).le) (r.val + 1)
    linarith only [h0, h1]
  calc
    _ ≤ 1 * ∫ z, (parisiAuxTiltMass N ξ ms qs r t u z).toReal
        ∂parisiAuxDisorderFieldLaw N μh ξ qs t :=
      mul_le_mul_of_nonneg_right hδ (integral_nonneg fun _ => ENNReal.toReal_nonneg)
    _ ≤ 2 * Real.exp (-c * N) := by
      simpa only [one_mul] using hmass N hN hS t ht r u hreach hgap

end SpinGlass
