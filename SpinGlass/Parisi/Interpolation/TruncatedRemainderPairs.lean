import SpinGlass.Parisi.Interpolation.PairHamiltonian
import SpinGlass.Parisi.Interpolation.TreeRemainder
import SpinGlass.Parisi.Localization.OverlapValues

/-!
# The finite Guerra remainder by overlap and meeting level

The actual finite-tree remainder is a finite sum of constrained prefix
differences. This identifies the observables to which the proved
constrained branch limits apply.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k M : ℕ)

theorem gibbs_pair_level_pairHamGt_eq
    (t : ℝ) (c : (Fin 2 → Config N) → ℝ) (hc : ∀ σ, 0 ≤ c σ)
    (h : Fin N → ℝ) (H : EnergySpace N) (z : MarksSpace N k)
    (w : CascadeWeights k) (hw : ∀ α, branchWeight k w α ≠ ∞) (θ : ℕ → ℝ) :
    (∑ p : Config N × TruncBranch k M, ∑ q : Config N × TruncBranch k M,
      wGibbs (branchWt (N := N) (truncWt k M w)) (truncHam N k M t h (H, z)) p *
        wGibbs (branchWt (N := N) (truncWt k M w)) (truncHam N k M t h (H, z)) q *
          c ![p.1, q.1] * θ (branchLevel p.2 q.2)) =
      ∑ r ∈ Finset.range (k + 1), θ r *
        (truncPairObservable k M r (pairHamGt N k t c h H z.1)
            (hamG N k t h H z.1) w z.2 -
          truncPairObservable k M (r + 1) (pairHamGt N k t c h H z.1)
            (hamG N k t h H z.1) w z.2) := by
  apply gibbs_pair_level_eq_truncPairObservable k M _ _ w z.2 hw
    (truncHam N k M t h (H, z)) (fun σ τ => c ![σ, τ]) (fun σ τ => hc ![σ, τ])
  · intro α γ
    unfold pairHamGt
    simp only [truncHam_apply, branchHam_eq]
  · intro α
    unfold hamG branchZX
    simp only [truncHam_apply, branchHam_eq]

/-- The exact finite remainder is a sum of the original overlap
constraints times their meeting masses; no averaging or limiting
identification is assumed. -/
theorem weightedTreeProfileRemainder_eq_pairFractions
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ)
    (h : Fin N → ℝ) (H : EnergySpace N) (z : MarksSpace N k)
    (w : CascadeWeights k) (hw : ∀ α, branchWeight k w α ≠ ∞) :
    weightedTreeProfileRemainder ξ (treeOverlap qs)
      (branchWt (N := N) (truncWt k M w)) (truncHam N k M t h (H, z)) =
      (1 / 2 : ℝ) * ∑ r ∈ Finset.range (k + 1), ∑ u ∈ parisiOverlapValues N,
        parisiProfileRemainder ξ u (qExt qs (r + 1)) *
          (truncPairObservable k M r (pairHamGt N k t (constraintR N u) h H z.1)
              (hamG N k t h H z.1) w z.2 -
            truncPairObservable k M (r + 1) (pairHamGt N k t (constraintR N u) h H z.1)
              (hamG N k t h H z.1) w z.2) := by
  classical
  let g := wGibbs (branchWt (N := N) (truncWt k M w)) (truncHam N k M t h (H, z))
  have hp (p q : Config N × TruncBranch k M) :
      g p * g q * parisiProfileRemainder ξ (overlap N p.1 q.1) (treeOverlap qs p.2 q.2) =
        ∑ u ∈ parisiOverlapValues N, g p * g q * constraintR N u ![p.1, q.1] *
          parisiProfileRemainder ξ u (qExt qs (branchLevel p.2 q.2 + 1)) := by
    have hmem : overlap N p.1 q.1 ∈ parisiOverlapValues N := by
      simpa using overlap_mem_parisiOverlapValues ![p.1, q.1]
    simp [constraintR, eq_comm, hmem, treeOverlap, mul_ite, ite_mul]
  unfold weightedTreeProfileRemainder
  change (1 / 2 : ℝ) * (∑ p, ∑ q, g p * g q *
    parisiProfileRemainder ξ (overlap N p.1 q.1) (treeOverlap qs p.2 q.2)) = _
  congr 1
  simp_rw [hp]
  conv_lhs => enter [2, p]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have he (u : ℝ) := gibbs_pair_level_pairHamGt_eq N k M t (constraintR N u)
    (constraintR_nonneg N u) h H z w hw (fun r => parisiProfileRemainder ξ u (qExt qs (r + 1)))
  simp_rw [show g = wGibbs (branchWt (N := N) (truncWt k M w))
    (truncHam N k M t h (H, z)) from rfl, he]
  exact Finset.sum_comm

end

end SpinGlass
