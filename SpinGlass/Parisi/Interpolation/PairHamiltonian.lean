import SpinGlass.Parisi.Interpolation.PairFractionFinite
import SpinGlass.Parisi.Concentration.PairTiltBranchIdentity

/-!
# The actual interpolating two-branch numerator

The numerator uses the same square-root scaling and site field as
`truncHam`. Its finite constrained prefix fractions are exactly the
physical Gibbs pair averages, before any disorder averaging.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

def pairHamGt (t : ℝ) (c : (Fin 2 → Config N) → ℝ)
    (h : Fin N → ℝ) (H : EnergySpace N) (z : Fin N → ℝ)
    (x : Fin k → (Fin N → ℝ) × (Fin N → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (∑ σ : Config N, ∑ τ : Config N, c ![σ, τ] * Real.exp (
    -branchHamX N k t h H z (fun p => (x p).1) σ -
      branchHamX N k t h H z (fun p => (x p).2) τ))

theorem measurable_pairHamGt (c : (Fin 2 → Config N) → ℝ) (h : Fin N → ℝ) :
    Measurable (fun q : (ℝ × EnergySpace N × (Fin N → ℝ)) ×
      (Fin k → (Fin N → ℝ) × (Fin N → ℝ)) =>
        pairHamGt N k q.1.1 c h q.1.2.1 q.1.2.2 q.2) := by
  unfold pairHamGt branchHamX
  fun_prop

theorem pairHamGt_le_prod (t : ℝ) {c : (Fin 2 → Config N) → ℝ}
    (hc : ∀ σ, c σ ≤ 1) (h : Fin N → ℝ) (H : EnergySpace N) (z : Fin N → ℝ)
    (x : Fin k → (Fin N → ℝ) × (Fin N → ℝ)) :
    pairHamGt N k t c h H z x ≤
      hamG N k t h H z (fun p => (x p).1) * hamG N k t h H z (fun p => (x p).2) := by
  unfold pairHamGt hamG branchZX
  rw [← ENNReal.ofReal_mul (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)]
  apply ENNReal.ofReal_le_ofReal
  rw [Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  apply Finset.sum_le_sum
  intro τ _
  rw [← Real.exp_add]
  convert mul_le_mul_of_nonneg_right (hc ![σ, τ]) (Real.exp_nonneg _) using 1
  simp only [one_mul, sub_eq_add_neg]

/-- Restoring the interpolation coefficients gives the original
unscaled pair numerator, including both closed time endpoints. -/
theorem pairHamGt_eq_unscaled (t : ℝ) (c : (Fin 2 → Config N) → ℝ)
    (h : Fin N → ℝ) (H : EnergySpace N) (z : Fin N → ℝ)
    (x : Fin k → (Fin N → ℝ) × (Fin N → ℝ)) :
    pairHamGt N k t c h H z x =
      unscaledPairHamG N k c (Real.sqrt t • H) h
        (fun i => Real.sqrt (1 - t) * z i)
        (fun p => ((fun i => Real.sqrt (1 - t) * (x p).1 i),
          (fun i => Real.sqrt (1 - t) * (x p).2 i))) := by
  have he (y : Fin k → Fin N → ℝ) (σ : Config N) :
      branchHamX N k t h H z y σ = Real.sqrt t * H σ +
        ∑ i, isingSpin (σ i) * (h i + Real.sqrt (1 - t) * z i +
          ∑ p, Real.sqrt (1 - t) * y p i) := by
    have hi (i : Fin N) : isingSpin (σ i) *
        (h i + Real.sqrt (1 - t) * z i + ∑ p, Real.sqrt (1 - t) * y p i) =
        Real.sqrt (1 - t) * (isingSpin (σ i) * (z i + ∑ p, y p i)) +
          h i * isingSpin (σ i) := by
      rw [← Finset.mul_sum]
      ring
    unfold branchHamX
    simp_rw [hi, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  unfold pairHamGt unscaledPairHamG
  congr 1
  rw [← (finTwoArrowEquiv (Config N)).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  change c ![σ, τ] * _ = c ![σ, τ] * _
  congr 2
  rw [he, he]
  change _ = -(Real.sqrt t * H σ + Real.sqrt t * H τ +
    (∑ i, isingSpin (σ i) * (h i + Real.sqrt (1 - t) * z i +
      ∑ p, Real.sqrt (1 - t) * (x p).1 i)) +
    (∑ i, isingSpin (τ i) * (h i + Real.sqrt (1 - t) * z i +
      ∑ p, Real.sqrt (1 - t) * (x p).2 i)))
  ring

theorem truncPairObservable_pairHamGt_eq_gibbs (M r : ℕ)
    (t : ℝ) (c : (Fin 2 → Config N) → ℝ) (hc : ∀ σ, 0 ≤ c σ)
    (h : Fin N → ℝ) (H : EnergySpace N) (z : MarksSpace N k)
    (w : CascadeWeights k) (hw : ∀ α, branchWeight k w α ≠ ∞) :
    truncPairObservable k M r (pairHamGt N k t c h H z.1) (hamG N k t h H z.1) w z.2 =
      ∑ p : Config N × TruncBranch k M, ∑ q : Config N × TruncBranch k M,
        wGibbs (branchWt (N := N) (truncWt k M w)) (truncHam N k M t h (H, z)) p *
          wGibbs (branchWt (N := N) (truncWt k M w)) (truncHam N k M t h (H, z)) q *
            c ![p.1, q.1] * (if r ≤ branchLevel p.2 q.2 then (1 : ℝ) else 0) := by
  apply truncPairObservable_eq_gibbs k M r _ _ w z.2 hw
    (truncHam N k M t h (H, z)) (fun σ τ => c ![σ, τ]) (fun σ τ => hc ![σ, τ])
  · intro α γ
    unfold pairHamGt
    simp only [truncHam_apply, branchHam_eq]
  · intro α
    unfold hamG branchZX
    simp only [truncHam_apply, branchHam_eq]

end

end SpinGlass
