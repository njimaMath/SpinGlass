import SpinGlass.Parisi.Coupled.CoupledCanonicalScalar

/-!
# The correction sum of the canonical labelled pieces

Only driven pieces change the overlap coordinate. The half physical
mass at shared pieces cancels the doubled coupled correction. Both
pieces of the split interval have the same original effective mass,
so their actual profile increments telescope as in (14.356)-(14.360).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

noncomputable def ParisiCanonicalPiece.profileIncrement {k : ℕ} (θ : ℝ → ℝ)
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 2)) (u : ℝ) : ParisiCanonicalPiece k → ℝ
  | .auxiliary _ => 0
  | .driven i => if i = p then θ u - θ (qExt qs i.val)
      else θ (qExt qs (i.val + 1)) - θ (qExt qs i.val)
  | .splitRight => θ (qExt qs (p.val + 1)) - θ u

noncomputable def ParisiCanonicalPiece.correction {k : ℕ} (θ : ℝ → ℝ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ)
    (e : ParisiCanonicalPiece k) : ℝ :=
  (if e.shared r p then 2 * e.physicalMass ms r p else e.physicalMass ms r p) *
    e.profileIncrement θ qs p u

theorem ParisiCanonicalPiece.correction_eq {k : ℕ} (θ : ℝ → ℝ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ)
    (e : ParisiCanonicalPiece k) :
    e.correction θ ms qs r p u = mExt ms (e.oldLevel p).val * e.profileIncrement θ qs p u := by
  unfold correction physicalMass
  split_ifs <;> ring

theorem parisiCanonicalCorrectionBlock_sum {k : ℕ} (θ : ℝ → ℝ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (p i : Fin (k + 2)) (u : ℝ) :
    ((ParisiCanonicalPiece.auxiliary i :: parisiCanonicalDrivenBlock p i).map
      (ParisiCanonicalPiece.correction θ ms qs r p u)).sum =
        mExt ms i.val * (θ (qExt qs (i.val + 1)) - θ (qExt qs i.val)) := by
  by_cases hi : i = p
  · subst i
    simp only [parisiCanonicalDrivenBlock, ite_true, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, ParisiCanonicalPiece.correction_eq,
      ParisiCanonicalPiece.profileIncrement, ParisiCanonicalPiece.oldLevel, mul_zero, zero_add]
    ring
  · simp only [parisiCanonicalDrivenBlock, hi, ite_false, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, ParisiCanonicalPiece.correction_eq,
      ParisiCanonicalPiece.profileIncrement, ParisiCanonicalPiece.oldLevel, mul_zero, zero_add]

/-- The full old correction, with the zero root term displayed
explicitly, equals the existing positive-level correction definition. -/
theorem parisiCorrection_eq_all_level_sum {k : ℕ} (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    parisiCorrection ξ ms qs = ∑ i : Fin (k + 2), mExt ms i.val *
      (parisiTheta ξ (qExt qs (i.val + 1)) - parisiTheta ξ (qExt qs i.val)) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, mExt_zero, zero_mul, zero_add, Fin.val_succ]
  rfl

/-- Physical sorting preserves exactly the correction sum of the
original Parisi functional. No correction identity is assumed. -/
theorem sum_parisiCanonicalMerged_correction_eq {k : ℕ} (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) :
    ((parisiCanonicalMergedPieces ms r p).map
      (ParisiCanonicalPiece.correction (parisiTheta ξ) ms qs r p u)).sum = parisiCorrection ξ ms qs := by
  have hp := ((parisiCanonicalMergedPieces_perm ms r p).trans (parisiCanonicalPieces_perm_grouped p)).map
    (ParisiCanonicalPiece.correction (parisiTheta ξ) ms qs r p u)
  rw [hp.sum_eq]
  have hsum (l : List (Fin (k + 2))) :
      (l.flatMap (fun i => (ParisiCanonicalPiece.auxiliary i :: parisiCanonicalDrivenBlock p i).map
        (ParisiCanonicalPiece.correction (parisiTheta ξ) ms qs r p u))).sum =
      (l.map (fun i => ((ParisiCanonicalPiece.auxiliary i :: parisiCanonicalDrivenBlock p i).map
        (ParisiCanonicalPiece.correction (parisiTheta ξ) ms qs r p u)).sum)).sum := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.flatMap_cons, List.sum_append]
      exact congrArg (fun z => ((ParisiCanonicalPiece.auxiliary i :: parisiCanonicalDrivenBlock p i).map
        (ParisiCanonicalPiece.correction (parisiTheta ξ) ms qs r p u)).sum + z) ih
  simp only [parisiCanonicalGroupedPieces, List.map_flatMap]
  rw [hsum]
  simp_rw [parisiCanonicalCorrectionBlock_sum]
  rw [parisiCorrection_eq_all_level_sum]
  simp only [parisiCanonicalIndices, List.map_ofFn, List.sum_ofFn, Function.comp_apply, id_eq]

end SpinGlass
