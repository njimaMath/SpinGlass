import SpinGlass.Parisi.Concentration.ParisiPressureIdentification

/-!
# Concentration from the physical pressure gap

The actual auxiliary tilted mass has exponential decay whenever the
existing constrained pressure is below twice the single-copy pressure.
The decay constant is selected before volume, time, meeting level and
overlap. The only field restriction here is bounded support.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The physical pressure gap implies the explicit two-term exponential
bound for the original auxiliary tilted mass. -/
theorem integral_parisiAuxTiltMass_le_of_physical_pressure_gap
    {N k : ℕ} (hN : 0 < N) (μh : Measure ℝ) [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : qs ∈ parisiOverlapDomain k)
    (r : Fin (k + 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ᵐ h ∂μh, |h| ≤ R)
    {b ε : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hblower : ∀ i, b ≤ halveBelow r.val ms i) (hε : 0 < ε)
    (hgap : randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u
      (GaussianField.ofMultivariateGaussian
        (posSemidef_overlapCovMatrix_parisiTimeProfile hS ht.1)) ≤
        2 * parisiInterpolationPressure N μh ξ ms qs t - ε) :
    (∫ z, (parisiAuxTiltMass N ξ ms qs r t u z).toReal
      ∂parisiAuxDisorderFieldLaw N μh ξ qs t) ≤
      Real.exp (-(b * ε) * N / 2) +
        Real.exp (-((b * ε) ^ 2 * N) / (8 * (1 + parisiTiltVarianceBound ξ R))) := by
  apply integral_parisiAuxTiltMass_le_of_pressure_gap hN μh hξ hS ms qs hm hq r ht u
    hreach hR hbound hb hb1 hblower hε
  have hμ : Integrable id μh := (integrable_const R).mono'
    measurable_id.aestronglyMeasurable (by simpa only [id_eq, Real.norm_eq_abs] using hbound)
  rw [integral_parisiAuxLogPressure_gap_eq hN hμ ξ ms qs hm r t u
    (posSemidef_overlapCovMatrix_parisiTimeProfile hS ht.1) hreach]
  have hh := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg (α := ℝ) N)
  nlinarith only [hh]

/-- One positive rate, uniform in volume, time, meeting level and overlap,
for the actual pressure-gap concentration estimate. -/
theorem exists_uniform_parisiAuxTiltMass_exponential_bound
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
      (∫ z, (parisiAuxTiltMass N ξ ms qs r t u z).toReal
        ∂parisiAuxDisorderFieldLaw N μh ξ qs t) ≤ 2 * Real.exp (-c * N) := by
  obtain ⟨b, hb, hb1, hblower⟩ := exists_uniform_halveBelow_lower_mass ms hm
  let a := b * ε / 2
  let d := (b * ε) ^ 2 / (8 * (1 + parisiTiltVarianceBound ξ R))
  have ha : 0 < a := div_pos (mul_pos hb hε) (by norm_num)
  have hd : 0 < d := div_pos (sq_pos_of_pos (mul_pos hb hε)) (by
    have := parisiTiltVarianceBound_nonneg ξ R
    positivity)
  refine ⟨min a d, lt_min ha hd, ?_⟩
  intro N hN hS t ht r u hreach hgap
  have hh := integral_parisiAuxTiltMass_le_of_physical_pressure_gap hN μh hξ hS
    ms qs hm hq r ht u hreach hR hbound hb hb1 (hblower r.val) hε hgap
  have hfirst : -(b * ε) * N / 2 ≤ -(min a d) * N := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left a d) (Nat.cast_nonneg (α := ℝ) N)
    dsimp only [a] at hh
    nlinarith only [hh]
  have hsecond : -((b * ε) ^ 2 * N) / (8 * (1 + parisiTiltVarianceBound ξ R)) ≤
      -(min a d) * N := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right a d) (Nat.cast_nonneg (α := ℝ) N)
    dsimp only [d] at hh
    calc
      -((b * ε) ^ 2 * N) / (8 * (1 + parisiTiltVarianceBound ξ R)) =
          -((b * ε) ^ 2 / (8 * (1 + parisiTiltVarianceBound ξ R)) * N) := by ring
      _ ≤ -(min a d * N) := neg_le_neg hh
      _ = -(min a d) * N := (neg_mul _ _).symm
  refine hh.trans ?_
  have hsum := add_le_add (Real.exp_le_exp.2 hfirst) (Real.exp_le_exp.2 hsecond)
  linarith only [hsum]

end SpinGlass
