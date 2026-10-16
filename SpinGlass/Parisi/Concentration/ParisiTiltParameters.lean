import SpinGlass.Parisi.Concentration.PairTiltBoundedField
import SpinGlass.Parisi.Coupled.CoupledOriginalPressure
import SpinGlass.Parisi.Variational.ParisiQuantitativeMass

/-!
# Uniform concentration parameters for the original interpolation

The original halved masses, covariance and common-prefix Gaussian factors
satisfy the concrete concentration hypotheses uniformly in time and level.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- Time scaling preserves the required covariance positivity. -/
theorem posSemidef_overlapCovMatrix_parisiTimeProfile {N : ℕ} {ξ : ℝ → ℝ}
    (hS : (overlapCovMatrix N ξ).PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    (overlapCovMatrix N (parisiTimeProfile ξ t)).PosSemidef := by
  have he : overlapCovMatrix N (parisiTimeProfile ξ t) = t • overlapCovMatrix N ξ := by
    ext σ τ
    simp only [overlapCovMatrix_apply, parisiTimeProfile, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact hS.smul ht

/-- A profile-only bound for the interpolation covariance diagonal,
valid also at zero volume and zero time. -/
theorem overlapCovMatrix_parisiTimeProfile_diag_le (N : ℕ) (ξ : ℝ → ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (σ : Config N) :
    overlapCovMatrix N (parisiTimeProfile ξ t) σ σ ≤ (N : ℝ) * |ξ 1| := by
  rw [overlapCovMatrix_diag]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  change t * ξ 1 ≤ |ξ 1|
  calc t * ξ 1 ≤ t * |ξ 1| := mul_le_mul_of_nonneg_left (le_abs_self _) ht.1
    _ ≤ |ξ 1| := mul_le_of_le_one_left (abs_nonneg _) ht.2

/-- Every replica row of the original common-prefix factor has norm one. -/
theorem sum_sq_couplingFactorSgn_one (τ p : ℕ) (l : Fin 2) :
    ∑ j, couplingFactorSgn 1 τ p l j ^ 2 = 1 := by
  have hh : gram (couplingFactorSgn 1 τ p) l l = 1 := by
    rcases lt_or_ge p τ with h | h
    · simpa using gram_couplingFactorSgn_of_lt (η := 1) (by norm_num) h l l
    · simpa using gram_couplingFactorSgn_of_le (η := 1) h l l
  simpa only [gram, pow_two] using hh

/-- The root variance is uniformly bounded by the total profile variance. -/
theorem parisiAuxRootVar_le_total_variance {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} {qs : Fin (k + 1) → ℝ} (hq : qs ∈ parisiOverlapDomain k)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiAuxRootVar ξ qs t ≤ (deriv ξ 1 - deriv ξ 0).toNNReal := by
  have ht' : (1 - t).toNNReal ≤ (1 : ℝ≥0) := by
    rw [Real.toNNReal_le_iff_le_coe]
    simpa using sub_le_self (1 : ℝ) ht.1
  exact (mul_le_of_le_one_left (by positivity) ht').trans (parisiVar_le_total_variance hξ hq 0)

/-- One positive lower mass works for every meeting level, including
the empty positive cascade. It is selected before time and volume. -/
theorem exists_uniform_halveBelow_lower_mass {k : ℕ} (ms : Fin k → ℝ)
    (hm : ParisiMAdmissible ms) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧ ∀ r : ℕ, ∀ i, b ≤ halveBelow r ms i := by
  cases k with
  | zero => exact ⟨1, one_pos, le_rfl, fun _ i => Fin.elim0 i⟩
  | succ k =>
    refine ⟨ms 0 / 2, half_pos (hm.2.1 0), by linarith [hm.2.2 0], ?_⟩
    intro r i
    have hi := hm.1.monotone (Fin.zero_le i)
    unfold halveBelow
    split_ifs <;> linarith [hm.2.1 i]

/-- The covariance and root part of the variance bound depends only on
the profile. This expression avoids any positivity assumption on ξ at zero. -/
noncomputable def parisiTiltVarianceBound (ξ : ℝ → ℝ) (R : ℝ) : ℝ :=
  32 * (|ξ 1| + ((deriv ξ 1 - deriv ξ 0).toNNReal : ℝ)) + 16 * R ^ 2

theorem parisiTiltVarianceBound_nonneg (ξ : ℝ → ℝ) (R : ℝ) :
    0 ≤ parisiTiltVarianceBound ξ R := by
  unfold parisiTiltVarianceBound
  positivity

end SpinGlass
