import SpinGlass.Parisi.Interpolation.PairFractionLimit
import SpinGlass.FiniteGibbs.WeightedInterpolation

/-!
# Constrained prefix fractions as finite Gibbs averages

The joint branch numerator is retained when the two spin configurations
are summed. This gives the finite identity needed before passing the
constrained overlap remainder to the cascade limit.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable {T X : Type*} [Fintype X] (k M : ℕ)

/-- Real-valued form of the joint prefix numerator and its normalization.
All weights may vanish; finiteness suffices for this algebraic identity. -/
theorem truncPairObservable_eq_real_sum (r : ℕ)
    (U : (Fin k → T × T) → ℝ≥0∞) (G : (Fin k → T) → ℝ≥0∞)
    (w : CascadeWeights k) (z : CascadeMarks T k)
    (hw : ∀ α, branchWeight k w α ≠ ∞)
    (V : TruncBranch k M → TruncBranch k M → ℝ) (Z : TruncBranch k M → ℝ)
    (hV : ∀ α γ, 0 ≤ V α γ) (hZ : ∀ α, 0 ≤ Z α)
    (hU : ∀ α γ, U (fun p => (branchMarks k z (truncBranchCoe k M α) p,
      branchMarks k z (truncBranchCoe k M γ) p)) = ENNReal.ofReal (V α γ))
    (hG : ∀ α, G (branchMarks k z (truncBranchCoe k M α)) = ENNReal.ofReal (Z α)) :
    truncPairObservable k M r U G w z =
      (∑ α, ∑ γ, (if r ≤ branchLevel α γ then (1 : ℝ) else 0) *
        (truncWt k M w α * truncWt k M w γ * V α γ)) /
        (∑ α, truncWt k M w α * Z α) ^ 2 := by
  classical
  have hfin (α γ : TruncBranch k M) :
      (if r ≤ branchLevel α γ then (1 : ℝ≥0∞) else 0) *
        (branchWeight k w (truncBranchCoe k M α) *
          branchWeight k w (truncBranchCoe k M γ) * ENNReal.ofReal (V α γ)) ≠ ∞ :=
    ENNReal.mul_ne_top (by split_ifs <;> simp)
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (hw _) (hw _)) ENNReal.ofReal_ne_top)
  unfold truncPairObservable truncPairNumerator
  simp_rw [hU, hG, prefixEq_truncBranchCoe]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_sum (fun α _ => ENNReal.sum_ne_top.2 fun γ _ => hfin α γ),
    ENNReal.toReal_sum (fun α _ => ENNReal.mul_ne_top (hw _) ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_sum (fun γ _ => hfin _ γ), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (hZ _), ENNReal.toReal_ofReal (hV _ _)]
  have hp (α γ : TruncBranch k M) :
      (if r ≤ branchLevel α γ then (1 : ℝ≥0∞) else 0).toReal =
        (if r ≤ branchLevel α γ then (1 : ℝ) else 0) := by split_ifs <;> simp
  simp only [hp, truncWt, div_eq_mul_inv, inv_pow]

/-- The finite constrained prefix fraction is the Gibbs pair average
with the spin constraint and prefix indicator both still present. -/
theorem truncPairObservable_eq_gibbs (r : ℕ)
    (U : (Fin k → T × T) → ℝ≥0∞) (G : (Fin k → T) → ℝ≥0∞)
    (w : CascadeWeights k) (z : CascadeMarks T k)
    (hw : ∀ α, branchWeight k w α ≠ ∞)
    (H : FiniteGibbs.EnergySpace (X × TruncBranch k M)) (c : X → X → ℝ)
    (hc : ∀ σ τ, 0 ≤ c σ τ)
    (hU : ∀ α γ, U (fun p => (branchMarks k z (truncBranchCoe k M α) p,
      branchMarks k z (truncBranchCoe k M γ) p)) =
        ENNReal.ofReal (∑ σ, ∑ τ, c σ τ * Real.exp (-H (σ, α) - H (τ, γ))))
    (hG : ∀ α, G (branchMarks k z (truncBranchCoe k M α)) =
      ENNReal.ofReal (∑ σ, Real.exp (-H (σ, α)))) :
    truncPairObservable k M r U G w z =
      ∑ p : X × TruncBranch k M, ∑ q : X × TruncBranch k M,
        wGibbs (fun p => truncWt k M w p.2) H p *
          wGibbs (fun p => truncWt k M w p.2) H q * c p.1 q.1 *
            (if r ≤ branchLevel p.2 q.2 then (1 : ℝ) else 0) := by
  classical
  rw [truncPairObservable_eq_real_sum k M r U G w z hw
    (fun α γ => ∑ σ, ∑ τ, c σ τ * Real.exp (-H (σ, α) - H (τ, γ)))
    (fun α => ∑ σ, Real.exp (-H (σ, α)))
    (fun α γ => Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun τ _ =>
      mul_nonneg (hc σ τ) (Real.exp_pos _).le)
    (fun α => Finset.sum_nonneg fun σ _ => (Real.exp_pos _).le) hU hG]
  have hden : wZ (fun p : X × TruncBranch k M => truncWt k M w p.2) H =
      ∑ α, truncWt k M w α * ∑ σ, Real.exp (-H (σ, α)) := by
    unfold wZ
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  have hsplit (f : X × TruncBranch k M → ℝ) :
      (∑ p, f p) = ∑ α, ∑ σ, f (σ, α) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [hsplit, wGibbs, hden]
  simp only [div_eq_mul_inv, ← inv_pow, Real.exp_sub, Real.exp_neg]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

/-- Decomposing a constrained Gibbs pair average by its exact meeting
level produces differences of the joint prefix fractions. -/
theorem gibbs_pair_level_eq_truncPairObservable
    (U : (Fin k → T × T) → ℝ≥0∞) (G : (Fin k → T) → ℝ≥0∞)
    (w : CascadeWeights k) (z : CascadeMarks T k)
    (hw : ∀ α, branchWeight k w α ≠ ∞)
    (H : FiniteGibbs.EnergySpace (X × TruncBranch k M)) (c : X → X → ℝ)
    (hc : ∀ σ τ, 0 ≤ c σ τ)
    (hU : ∀ α γ, U (fun p => (branchMarks k z (truncBranchCoe k M α) p,
      branchMarks k z (truncBranchCoe k M γ) p)) =
        ENNReal.ofReal (∑ σ, ∑ τ, c σ τ * Real.exp (-H (σ, α) - H (τ, γ))))
    (hG : ∀ α, G (branchMarks k z (truncBranchCoe k M α)) =
      ENNReal.ofReal (∑ σ, Real.exp (-H (σ, α)))) (θ : ℕ → ℝ) :
    (∑ p : X × TruncBranch k M, ∑ q : X × TruncBranch k M,
      wGibbs (fun p => truncWt k M w p.2) H p *
        wGibbs (fun p => truncWt k M w p.2) H q * c p.1 q.1 * θ (branchLevel p.2 q.2)) =
      ∑ r ∈ Finset.range (k + 1), θ r *
        (truncPairObservable k M r U G w z - truncPairObservable k M (r + 1) U G w z) := by
  classical
  let V := fun p q : X × TruncBranch k M =>
    wGibbs (fun p => truncWt k M w p.2) H p *
      wGibbs (fun p => truncWt k M w p.2) H q * c p.1 q.1
  have hp (r) : (∑ p, ∑ q,
      (if r ≤ branchLevel p.2 q.2 then (1 : ℝ) else 0) * V p q) =
        truncPairObservable k M r U G w z := by
    rw [truncPairObservable_eq_gibbs k M r U G w z hw H c hc hU hG]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    exact mul_comm _ _
  have hh := sum_pair_levels_div k V (fun p q => branchLevel p.2 q.2)
    (fun p q => branchLevel_le p.2 q.2) θ 1
  simp only [one_pow, div_one] at hh
  simp_rw [hp] at hh
  exact hh

end

end SpinGlass
