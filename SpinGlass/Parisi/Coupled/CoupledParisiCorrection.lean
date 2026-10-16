import SpinGlass.Parisi.Coupled.CoupledParisiSplitVariance

/-!
# The actual correction of the matched coupled split

The adjacent split pieces carry the same original mass. Their correction
therefore equals the old Parisi correction. Halving the common-prefix masses
exactly cancels the doubling in the coupled correction, as in (14.312).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The deterministic correction in the original Parisi functional. -/
noncomputable def parisiCorrection (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) : ℝ :=
  ∑ r : Fin (k + 1), mExt ms (r.val + 1) *
    (parisiTheta ξ (qExt qs (r.val + 2)) - parisiTheta ξ (qExt qs (r.val + 1)))

/-- Abel summation writes the correction using the actual mass jumps. -/
theorem parisiCorrection_eq_theta_fin_sum (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    parisiCorrection ξ ms qs = parisiTheta ξ 1 -
      ∑ r : Fin (k + 1), parisiTheta ξ (qs r) * (mExt ms (r.val + 1) - mExt ms r.val) := by
  have hh := parisiFunctional_eq_theta_sum ξ 0 ms qs
  unfold parisiFunctional at hh
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at hh
  have he : (∑ r : Fin (k + 1), parisiTheta ξ (qExt qs (r.val + 1)) *
      (mExt ms (r.val + 1) - mExt ms r.val)) =
      ∑ r : Fin (k + 1), parisiTheta ξ (qs r) * (mExt ms (r.val + 1) - mExt ms r.val) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [qExt_succ_of_lt qs r.isLt]
  rw [he] at hh
  change Real.log 2 + _ - (1 / 2) * parisiCorrection ξ ms qs = _ at hh
  linarith

/-- A free overlap between equal masses makes no contribution to the
correction, independently of all profile regularity and overlap ordering. -/
theorem parisiCorrection_qUpdate_eq_of_equal_mass (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (u : ℝ)
    (hm : mExt ms r.val = mExt ms (r.val + 1)) :
    parisiCorrection ξ ms (qUpdate qs r u) = parisiCorrection ξ ms qs := by
  rw [parisiCorrection_eq_theta_fin_sum, parisiCorrection_eq_theta_fin_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p = r
  · subst p
    simp only [qUpdate_self, hm, sub_self, mul_zero]
  · rw [qUpdate_of_ne qs u hp]

/-- Inserting the old matching mass preserves the complete actual
correction for any inserted overlap, including the terminal mass one. -/
theorem parisiCorrection_split_matching_mass (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (u : ℝ) :
    parisiCorrection ξ (splitParisiMassLeft ms p (mExt ms (p.val + 1)))
      (splitParisiOverlap qs p u) = parisiCorrection ξ ms qs := by
  rw [splitParisiOverlap_eq_qUpdate_left,
    parisiCorrection_qUpdate_eq_of_equal_mass ξ _ _ p.succ u
      (splitParisiMassLeft_matching_mass ms p)]
  have hh := parisiCorrection_erase_adjacent_eq (ξ := ξ)
    (splitParisiMassLeft ms p (mExt ms (p.val + 1))) (splitParisiOverlap qs p (qs p))
    p (splitParisiOverlap_left_adjacent_eq qs p)
  simpa only [erase_splitParisiMassLeft, erase_splitParisiOverlap, parisiCorrection] using hh.symm

/-- The concrete response mass array is the actual extended mass list
of the matching left insertion. -/
theorem parisiResponseSplitMasses_eq_matching_mExt {k : ℕ}
    (ms : Fin k → ℝ) (p : Fin (k + 1))
    (i : Fin ((p.val + 1) + ((k - p.val) + 1))) :
    parisiResponseSplitMasses ms p i =
      mExt (splitParisiMassLeft ms p (mExt ms (p.val + 1))) (i.val + 1) := by
  rw [parisiResponseSplitMasses_eq_mExt]
  by_cases hi : i.val ≤ p.val
  · rw [ite_eq_left hi]
    rcases lt_or_eq_of_le hi with hi | hi
    · rw [mExt_splitParisiMassLeft_before ms p _ (by omega)]
    · rw [hi, mExt_splitParisiMassLeft_inserted]
  · rw [ite_eq_right hi, mExt_splitParisiMassLeft_after ms p _ (by omega)]

/-- The correction written in the concrete response-array dimension
is exactly the original Parisi correction. -/
theorem parisiResponseSplitMasses_correction_eq (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (u : ℝ) :
    (∑ i : Fin ((p.val + 1) + ((k - p.val) + 1)), parisiResponseSplitMasses ms p i *
      (parisiTheta ξ (qExt (splitParisiOverlap qs p u) (i.val + 2)) -
        parisiTheta ξ (qExt (splitParisiOverlap qs p u) (i.val + 1)))) =
      parisiCorrection ξ ms qs := by
  rw [← parisiCorrection_split_matching_mass ξ ms qs p u]
  unfold parisiCorrection
  simp_rw [parisiResponseSplitMasses_eq_matching_mExt]
  let f := fun r : ℕ => mExt (splitParisiMassLeft ms p (mExt ms (p.val + 1))) (r + 1) *
    (parisiTheta ξ (qExt (splitParisiOverlap qs p u) (r + 2)) -
      parisiTheta ξ (qExt (splitParisiOverlap qs p u) (r + 1)))
  change (∑ i : Fin ((p.val + 1) + ((k - p.val) + 1)), f i.val) =
    ∑ i : Fin (k + 2), f i.val
  rw [show (p.val + 1) + ((k - p.val) + 1) = k + 2 by omega]

/-- Scaling the driven profile scales its complete theta correction. -/
theorem parisiTheta_timeProfile (ξ : ℝ → ℝ) (t x : ℝ) :
    parisiTheta (parisiTimeProfile ξ t) x = t * parisiTheta ξ x := by
  unfold parisiTheta
  rw [deriv_parisiTimeProfile]
  dsimp only [parisiTimeProfile]
  ring

theorem parisiCorrection_timeProfile (ξ : ℝ → ℝ) (t : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    parisiCorrection (parisiTimeProfile ξ t) ms qs = t * parisiCorrection ξ ms qs := by
  unfold parisiCorrection
  simp_rw [parisiTheta_timeProfile]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The original coupled correction after both normalization and the
actual matched split is precisely t times the old Parisi correction. -/
theorem coupledLevelSum_parisiSplit_eq_correction (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t u : ℝ) :
    (1 / 2) * coupledLevelSum (parisiTimeProfile ξ t) (parisiSplitCouplingRho qs p u)
        (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)) =
      t * parisiCorrection ξ ms qs := by
  unfold parisiSplitCouplingRho
  rw [coupledLevelSum_couplingRhoSgn (fun x => by simp only [one_mul])]
  have hh := couplingLevelSum_halveBelow (parisiTimeProfile ξ t)
    (qExt (splitParisiOverlap qs p u)) (τ := p.val + 2) (by omega)
    (parisiResponseSplitMasses ms p)
  rw [show p.val + 2 - 1 = p.val + 1 by omega] at hh
  rw [hh, parisiResponseSplitMasses_correction_eq, parisiCorrection_timeProfile]
  ring

end SpinGlass
