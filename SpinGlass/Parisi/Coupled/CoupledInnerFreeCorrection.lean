import SpinGlass.Parisi.Coupled.CoupledInnerFreeAuxiliary

/-!
# Exact correction for the free inner mass

Only the independent inner level changes. Its correction is the old
Parisi correction plus (b-m) times the actual inner theta increment.
The common-prefix normalization and every other level are unchanged.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- Reindexing the finite mass array preserves the full coupled
theta sum, since each cast preserves its natural level coordinate. -/
theorem coupledLevelSum_cast {n m : ℕ} (h : n = m) (ξ : ℝ → ℝ)
    (ρ : Fin 2 → Fin 2 → ℕ → ℝ) (ns : Fin n → ℝ) :
    coupledLevelSum ξ ρ ns = coupledLevelSum ξ ρ (fun i => ns (Fin.cast h.symm i)) := by
  subst m
  rfl

/-- Updating a single actual mass changes only its linear theta
coefficient in the complete coupled correction. -/
theorem coupledLevelSum_update {n : ℕ} (ξ : ℝ → ℝ) (ρ : Fin 2 → Fin 2 → ℕ → ℝ)
    (ns : Fin n → ℝ) (i : Fin n) (b : ℝ) :
    coupledLevelSum ξ ρ (Function.update ns i b) = coupledLevelSum ξ ρ ns +
      (b - ns i) * ∑ l : Fin 2, ∑ l' : Fin 2,
        (parisiTheta ξ (ρ l l' (i.val + 2)) - parisiTheta ξ (ρ l l' (i.val + 1))) := by
  have hs (l l' : Fin 2) :
      (∑ r : Fin n, Function.update ns i b r *
        (parisiTheta ξ (ρ l l' (r.val + 2)) - parisiTheta ξ (ρ l l' (r.val + 1)))) =
        (∑ r : Fin n, ns r * (parisiTheta ξ (ρ l l' (r.val + 2)) - parisiTheta ξ (ρ l l' (r.val + 1)))) +
          (b - ns i) * (parisiTheta ξ (ρ l l' (i.val + 2)) - parisiTheta ξ (ρ l l' (i.val + 1))) := by
    calc
      _ = ∑ r : Fin n, (ns r * (parisiTheta ξ (ρ l l' (r.val + 2)) -
          parisiTheta ξ (ρ l l' (r.val + 1))) + if r = i then
            (b - ns i) * (parisiTheta ξ (ρ l l' (i.val + 2)) - parisiTheta ξ (ρ l l' (i.val + 1))) else 0) := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases hr : r = i
        · subst r
          rw [Function.update_self, ite_eq_left rfl]
          ring
        · rw [Function.update_of_ne hr, ite_eq_right hr, add_zero]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  unfold coupledLevelSum
  simp_rw [hs]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- The baseline mass at the inserted independent level is exactly
the original matching mass of this nonroot interval. -/
theorem parisiSplitPhysicalMasses_inner_matching {k : ℕ} (ms : Fin k → ℝ) (p : Fin k) :
    parisiSplitPhysicalMasses ms p.castSucc (parisiInnerFreeMassIndex p) = ms p := by
  rw [parisiSplitPhysicalMasses_apply]
  simp only [parisiInnerFreeMassIndex, Fin.val_succ, Fin.val_castSucc, lt_self_iff_false, ite_false]
  exact mExt_val_succ ms p

/-- The common-root off-diagonal theta terms cancel at the new
independent level; the two diagonal terms give the actual inner increment. -/
theorem parisiInnerFreeThetaCoefficient (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin k) (u : ℝ) :
    (∑ l : Fin 2, ∑ l' : Fin 2,
      (parisiTheta ξ (parisiSplitCouplingRho qs p.castSucc u l l' ((parisiInnerFreeMassIndex p).val + 2)) -
        parisiTheta ξ (parisiSplitCouplingRho qs p.castSucc u l l' ((parisiInnerFreeMassIndex p).val + 1)))) =
      2 * (parisiTheta ξ (qs p.succ) - parisiTheta ξ u) := by
  have hleft : qExt (splitParisiOverlap qs p.castSucc u) (p.val + 2) = u :=
    qExt_splitParisiOverlap_inserted qs p.castSucc u
  have hright : qExt (splitParisiOverlap qs p.castSucc u) (p.val + 3) = qs p.succ := by
    rw [qExt_splitParisiOverlap_after qs p.castSucc u (r := p.val + 2) (by
      simp only [Fin.val_castSucc]
      omega)]
    exact qExt_succ_of_lt qs p.succ.isLt
  have hmin : min (p.val + 3) (p.val + 2) = p.val + 2 := min_eq_right (by omega)
  simp only [parisiInnerFreeMassIndex, Fin.val_succ, Fin.val_castSucc, Fin.sum_univ_two,
    parisiSplitCouplingRho, couplingRhoSgn, Fin.isValue, reduceIte, Fin.zero_eq_one_iff,
    OfNat.ofNat_ne_one, one_ne_zero, one_mul]
  rw [hleft, hright, hmin, min_self]
  ring

/-- The exact correction for any free inner mass; its derivative
is the inner theta increment used in the far-case mass variation. -/
theorem coupledLevelSum_parisiInnerFree_eq_correction (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (t u b : ℝ) :
    (1 / 2) * coupledLevelSum (parisiTimeProfile ξ t) (parisiSplitCouplingRho qs p.castSucc u)
      (parisiInnerFreeCoupledMasses ms p b) =
      t * (parisiCorrection ξ ms qs + (b - ms p) * (parisiTheta ξ (qs p.succ) - parisiTheta ξ u)) := by
  have hbase := coupledLevelSum_parisiSplit_eq_correction ξ ms qs p.castSucc t u
  rw [coupledLevelSum_cast (parisiSplitSize_eq p.castSucc)] at hbase
  change (1 / 2) * coupledLevelSum (parisiTimeProfile ξ t) (parisiSplitCouplingRho qs p.castSucc u)
    (parisiSplitPhysicalMasses ms p.castSucc) = t * parisiCorrection ξ ms qs at hbase
  rw [parisiInnerFreeCoupledMasses_eq_update, coupledLevelSum_update,
    parisiSplitPhysicalMasses_inner_matching, parisiInnerFreeThetaCoefficient]
  simp only [parisiTheta_timeProfile]
  nlinarith

end SpinGlass
