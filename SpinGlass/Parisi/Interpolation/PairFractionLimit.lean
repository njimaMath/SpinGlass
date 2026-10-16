import SpinGlass.Parisi.Interpolation.CascadePairExpansion
import SpinGlass.Parisi.Tree.PairLevels

/-!
# Limits of constrained finite-tree prefix masses

The numerator retains an arbitrary joint observable bounded by the product
partition. Its normalized finite-tree value converges to the actual
recursive cascade pair observable whenever the limiting partition is
positive and finite.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace SpinGlass

noncomputable section

variable {T : Type*} [MeasurableSpace T] (k : ℕ)

def truncPairNumerator (M r : ℕ) (U : (Fin k → T × T) → ℝ≥0∞)
    (w : CascadeWeights k) (z : CascadeMarks T k) : ℝ≥0∞ :=
  ∑ α : TruncBranch k M, ∑ γ : TruncBranch k M,
    prefixEq k r (truncBranchCoe k M α) (truncBranchCoe k M γ) *
      (branchWeight k w (truncBranchCoe k M α) * branchWeight k w (truncBranchCoe k M γ) *
        U (fun p => (branchMarks k z (truncBranchCoe k M α) p,
          branchMarks k z (truncBranchCoe k M γ) p)))

def truncPairObservable (M r : ℕ) (U : (Fin k → T × T) → ℝ≥0∞)
    (G : (Fin k → T) → ℝ≥0∞) (w : CascadeWeights k) (z : CascadeMarks T k) : ℝ :=
  (truncPairNumerator k M r U w z *
    (∑ α : TruncBranch k M, branchWeight k w (truncBranchCoe k M α) *
      G (branchMarks k z (truncBranchCoe k M α)))⁻¹ ^ 2).toReal

def cascadePairObservable (r : ℕ) (U : (Fin k → T × T) → ℝ≥0∞)
    (G : (Fin k → T) → ℝ≥0∞) (w : CascadeWeights k) (z : CascadeMarks T k) : ℝ :=
  (cascadeSqPair k r U (cascadeZip k (w, z)) *
    (cascadeSum k G (cascadeZip k (w, z)))⁻¹ ^ 2).toReal

omit [MeasurableSpace T] in
theorem truncPairNumerator_le_partition_sq (M r : ℕ)
    {U : (Fin k → T × T) → ℝ≥0∞} {G : (Fin k → T) → ℝ≥0∞}
    (hUG : ∀ x, U x ≤ G (fun p => (x p).1) * G (fun p => (x p).2))
    (w : CascadeWeights k) (z : CascadeMarks T k) :
    truncPairNumerator k M r U w z ≤
      (∑ α : TruncBranch k M, branchWeight k w (truncBranchCoe k M α) *
        G (branchMarks k z (truncBranchCoe k M α))) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  apply Finset.sum_le_sum
  intro α _
  apply Finset.sum_le_sum
  intro γ _
  calc
    _ ≤ 1 * (branchWeight k w (truncBranchCoe k M α) *
        branchWeight k w (truncBranchCoe k M γ) *
        (G (branchMarks k z (truncBranchCoe k M α)) *
          G (branchMarks k z (truncBranchCoe k M γ)))) :=
      mul_le_mul' (prefixEq_le_one k r _ _) (mul_le_mul' le_rfl (hUG _))
    _ = _ := by ring

omit [MeasurableSpace T] in
theorem truncPairObservable_nonneg (M r : ℕ) (U : (Fin k → T × T) → ℝ≥0∞)
    (G : (Fin k → T) → ℝ≥0∞) (w : CascadeWeights k) (z : CascadeMarks T k) :
    0 ≤ truncPairObservable k M r U G w z := ENNReal.toReal_nonneg

omit [MeasurableSpace T] in
theorem truncPairObservable_le_one (M r : ℕ)
    {U : (Fin k → T × T) → ℝ≥0∞} {G : (Fin k → T) → ℝ≥0∞}
    (hUG : ∀ x, U x ≤ G (fun p => (x p).1) * G (fun p => (x p).2))
    (w : CascadeWeights k) (z : CascadeMarks T k) :
    truncPairObservable k M r U G w z ≤ 1 := by
  let S := ∑ α : TruncBranch k M, branchWeight k w (truncBranchCoe k M α) *
    G (branchMarks k z (truncBranchCoe k M α))
  have hn : truncPairNumerator k M r U w z * S⁻¹ ^ 2 ≤ 1 := by
    calc
      _ ≤ S ^ 2 * S⁻¹ ^ 2 :=
        mul_le_mul' (truncPairNumerator_le_partition_sq k M r hUG w z) le_rfl
      _ = (S * S⁻¹) * (S * S⁻¹) := by ring
      _ ≤ 1 * 1 := mul_le_mul' (ENNReal.mul_inv_le_one _) (ENNReal.mul_inv_le_one _)
      _ = 1 := one_mul 1
  exact (ENNReal.toReal_mono ENNReal.one_ne_top hn).trans_eq ENNReal.toReal_one

theorem cascadePairObservable_nonneg (r : ℕ) (U : (Fin k → T × T) → ℝ≥0∞)
    (G : (Fin k → T) → ℝ≥0∞) (w : CascadeWeights k) (z : CascadeMarks T k) :
    0 ≤ cascadePairObservable k r U G w z := ENNReal.toReal_nonneg

theorem cascadePairObservable_le_one (r : ℕ)
    {U : (Fin k → T × T) → ℝ≥0∞} {G : (Fin k → T) → ℝ≥0∞}
    (hG : Measurable G)
    (hUG : ∀ x, U x ≤ G (fun p => (x p).1) * G (fun p => (x p).2))
    (w : CascadeWeights k) (z : CascadeMarks T k) :
    cascadePairObservable k r U G w z ≤ 1 :=
  (ENNReal.toReal_mono ENNReal.one_ne_top
    (cascadeSqPair_mul_inv_sq_le_one k r hG hUG _)).trans_eq ENNReal.toReal_one

theorem tendsto_truncPairNumerator (r : ℕ)
    {U : (Fin k → T × T) → ℝ≥0∞} (hU : Measurable U)
    (w : CascadeWeights k) (z : CascadeMarks T k) :
    Tendsto (fun M => truncPairNumerator k M r U w z) atTop
      (𝓝 (cascadeSqPair k r U (cascadeZip k (w, z)))) := by
  rw [cascadeSqPair_cascadeZip k r hU]
  exact tendsto_sum_sum_truncBranch k (fun α γ => prefixEq k r α γ *
    (branchWeight k w α * branchWeight k w γ *
      U (fun p => (branchMarks k z α p, branchMarks k z γ p))))

/-- The constrained prefix fraction converges, including empty constraints
and every prefix level, without strict positivity of individual weights. -/
theorem tendsto_truncPairObservable (r : ℕ)
    {U : (Fin k → T × T) → ℝ≥0∞} {G : (Fin k → T) → ℝ≥0∞}
    (hU : Measurable U) (hG : Measurable G)
    (hUG : ∀ x, U x ≤ G (fun p => (x p).1) * G (fun p => (x p).2))
    (w : CascadeWeights k) (z : CascadeMarks T k)
    (hS0 : cascadeSum k G (cascadeZip k (w, z)) ≠ 0)
    (hS : cascadeSum k G (cascadeZip k (w, z)) ≠ ∞) :
    Tendsto (fun M => truncPairObservable k M r U G w z) atTop
      (𝓝 (cascadePairObservable k r U G w z)) := by
  have hQ := tendsto_truncPairNumerator k r hU w z
  have hSM := tendsto_sum_truncBranch k (fun α => branchWeight k w α * G (branchMarks k z α))
  rw [← cascadeSum_cascadeZip k hG] at hSM
  have hQfin : cascadeSqPair k r U (cascadeZip k (w, z)) ≠ ∞ := by
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hS hS)
    calc
      _ ≤ cascadeSqPair k r
          (fun x => G (fun p => (x p).1) * G (fun p => (x p).2)) (cascadeZip k (w, z)) :=
        cascadeSqPair_mono k r hUG _
      _ = cascadeSq k r G (cascadeZip k (w, z)) := cascadeSqPair_prod k r hG _
      _ ≤ _ := cascadeSq_le_sq k r hG _
  have hinv : (cascadeSum k G (cascadeZip k (w, z)))⁻¹ ^ 2 ≠ ∞ :=
    ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hS0)
  have hmul := ENNReal.Tendsto.mul hQ (Or.inr hinv)
    (ENNReal.Tendsto.pow (tendsto_inv_iff.2 hSM)) (Or.inr hQfin)
  exact (ENNReal.tendsto_toReal (ENNReal.mul_ne_top hQfin hinv)).comp hmul

/-- Subtracting successive constrained prefix fractions commutes with
the finite-tree limit. -/
theorem tendsto_truncPairObservable_meeting (r : ℕ)
    {U : (Fin k → T × T) → ℝ≥0∞} {G : (Fin k → T) → ℝ≥0∞}
    (hU : Measurable U) (hG : Measurable G)
    (hUG : ∀ x, U x ≤ G (fun p => (x p).1) * G (fun p => (x p).2))
    (w : CascadeWeights k) (z : CascadeMarks T k)
    (hS0 : cascadeSum k G (cascadeZip k (w, z)) ≠ 0)
    (hS : cascadeSum k G (cascadeZip k (w, z)) ≠ ∞) :
    Tendsto (fun M => truncPairObservable k M r U G w z -
      truncPairObservable k M (r + 1) U G w z) atTop
      (𝓝 (cascadePairObservable k r U G w z - cascadePairObservable k (r + 1) U G w z)) :=
  (tendsto_truncPairObservable k r hU hG hUG w z hS0 hS).sub
    (tendsto_truncPairObservable k (r + 1) hU hG hUG w z hS0 hS)

end

end SpinGlass
