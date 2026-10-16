import SpinGlass.Parisi.Coupled.CoupledOuterFreeAuxiliary

/-!
# Exact correction for the free outer mass

The shared new level has twice as many theta terms and half the scalar
mass. Its free correction is the old correction plus the actual outer
theta increment times the scalar mass change.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

theorem parisiSplitPhysicalMasses_outer_matching {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1)) :
    parisiSplitPhysicalMasses ms p p.castSucc = mExt ms (p.val + 1) / 2 := by
  rw [parisiSplitPhysicalMasses_apply]
  simp only [Fin.val_castSucc, Nat.lt_succ_self, ite_true]

theorem parisiOuterFreeThetaCoefficient (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (u : ℝ) :
    (∑ l : Fin 2, ∑ l' : Fin 2,
      (parisiTheta ξ (parisiSplitCouplingRho qs p u l l' (p.castSucc.val + 2)) -
        parisiTheta ξ (parisiSplitCouplingRho qs p u l l' (p.castSucc.val + 1)))) =
      4 * (parisiTheta ξ u - parisiTheta ξ (qs p)) := by
  have hleft : qExt (splitParisiOverlap qs p u) (p.val + 1) = qs p := by
    rw [qExt_splitParisiOverlap_before qs p u (r := p.val + 1) (by omega)]
    exact qExt_succ_of_lt qs p.isLt
  have hright := qExt_splitParisiOverlap_inserted qs p u
  simp only [Fin.val_castSucc, Fin.sum_univ_two, parisiSplitCouplingRho, couplingRhoSgn,
    Fin.isValue, reduceIte, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, one_ne_zero, one_mul,
    min_self, show min (p.val + 1) (p.val + 2) = p.val + 1 by omega]
  rw [hleft, hright]
  ring

theorem coupledLevelSum_parisiOuterFree_eq_correction (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t u b : ℝ) :
    (1 / 2) * coupledLevelSum (parisiTimeProfile ξ t) (parisiSplitCouplingRho qs p u)
      (parisiOuterFreeCoupledMasses ms p b) =
      t * (parisiCorrection ξ ms qs + (b - mExt ms (p.val + 1)) * (parisiTheta ξ u - parisiTheta ξ (qs p))) := by
  have hbase := coupledLevelSum_parisiSplit_eq_correction ξ ms qs p t u
  rw [coupledLevelSum_cast (parisiSplitSize_eq p)] at hbase
  change (1 / 2) * coupledLevelSum (parisiTimeProfile ξ t) (parisiSplitCouplingRho qs p u)
    (parisiSplitPhysicalMasses ms p) = t * parisiCorrection ξ ms qs at hbase
  unfold parisiOuterFreeCoupledMasses
  rw [coupledLevelSum_update, parisiSplitPhysicalMasses_outer_matching, parisiOuterFreeThetaCoefficient]
  simp only [parisiTheta_timeProfile]
  nlinarith

end SpinGlass
