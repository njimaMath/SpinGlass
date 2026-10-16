import SpinGlass.Parisi.Coupled.CoupledCanonicalCovariance
import SpinGlass.Parisi.Coupled.CoupledCanonicalRootPrefix

/-!
# The matrix correction of the canonical physical path

Each actual matrix-path increment gives the labelled shared/independent
correction. Summing yields the original time-scaled Parisi correction.
The raw positive-index array still contains zero-mass root expectations;
its algebraic level-sum identity does not apply the positive-mass cascade API.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

theorem parisiCanonicalCouplingRho_even_profile_step {k : ℕ}
    {θ : ℝ → ℝ} (hθ : Function.Even θ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {u : ℝ}
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (n : Fin (2 * k + 5)) (l l' : Fin 2) :
    θ (parisiCanonicalCouplingRho ms qs negative r p u l l' (n.val + 1)) -
        θ (parisiCanonicalCouplingRho ms qs negative r p u l l' n.val) =
      if l = l' then
        ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).profileIncrement θ qs p u
      else if ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).shared r p then
        ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).profileIncrement θ qs p u
      else 0 := by
  by_cases hll : l = l'
  · simp only [parisiCanonicalCouplingRho, hll, ite_true]
    exact parisiCanonicalOverlapPath_profile_step θ ms qs hm r p u n
  · simp only [parisiCanonicalCouplingRho, hll, ite_false]
    have hneg (x : ℝ) : θ (-x) = θ x := hθ x
    cases negative <;> simp only [Bool.false_eq_true, ite_false, ite_true, hneg]
    all_goals exact parisiCanonicalOverlapPath_clamped_profile_step θ ms qs hm hq r p hu n

/-- The four concrete matrix entries give exactly the labelled
correction, including auxiliary marks and either overlap sign. -/
theorem parisiCanonicalMatrixCorrection_step {k : ℕ}
    {θ : ℝ → ℝ} (hθ : Function.Even θ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {u : ℝ}
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) (n : Fin (2 * k + 5)) :
    (1 / 2) * ∑ l : Fin 2, ∑ l' : Fin 2,
      ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).physicalMass ms r p *
        (θ (parisiCanonicalCouplingRho ms qs negative r p u l l' (n.val + 1)) -
          θ (parisiCanonicalCouplingRho ms qs negative r p u l l' n.val)) =
      ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).correction θ ms qs r p u := by
  simp_rw [parisiCanonicalCouplingRho_even_profile_step hθ ms qs hm hq negative r p hu]
  let e := (parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)
  change (1 / 2) * ∑ l : Fin 2, ∑ l' : Fin 2, e.physicalMass ms r p *
    (if l = l' then e.profileIncrement θ qs p u
      else if e.shared r p then e.profileIncrement θ qs p u else 0) =
      e.correction θ ms qs r p u
  by_cases hs : e.shared r p = true <;>
    simp [ParisiCanonicalPiece.correction, hs, Fin.sum_univ_two] <;> ring

theorem ParisiCanonicalPiece.correction_timeProfile {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) (e : ParisiCanonicalPiece k) :
    e.correction (parisiTheta (parisiTimeProfile ξ t)) ms qs r p u =
      t * e.correction (parisiTheta ξ) ms qs r p u := by
  unfold correction
  cases e with
  | auxiliary i => simp [profileIncrement]
  | driven i =>
    simp only [profileIncrement, parisiTheta_timeProfile]
    split_ifs <;> ring
  | splitRight =>
    simp only [profileIncrement, parisiTheta_timeProfile]
    ring

theorem sum_parisiCanonicalMerged_correction_fin {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) :
    (∑ n : Fin (2 * k + 5),
      ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).correction
        (parisiTheta ξ) ms qs r p u) = parisiCorrection ξ ms qs := by
  have he : List.ofFn (fun n : Fin (2 * k + 5) =>
      ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).correction
        (parisiTheta ξ) ms qs r p u) =
      (parisiCanonicalMergedPieces ms r p).map
        (ParisiCanonicalPiece.correction (parisiTheta ξ) ms qs r p u) := by
    simpa only [parisiCanonicalMergedPieces_length, Fin.val_cast] using
      List.ofFn_getElem_eq_map (parisiCanonicalMergedPieces ms r p)
        (ParisiCanonicalPiece.correction (parisiTheta ξ) ms qs r p u)
  rw [← List.sum_ofFn, he]
  exact sum_parisiCanonicalMerged_correction_eq ξ ms qs r p u

/-- The actual matrix correction, summed over all merged pieces,
is t times the original Parisi correction, equation (14.356). -/
theorem parisiCanonicalFullLevelSum_eq_correction {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) (t : ℝ) {u : ℝ}
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) :
    (1 / 2) * ∑ l : Fin 2, ∑ l' : Fin 2, ∑ n : Fin (2 * k + 5),
      ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).physicalMass ms r p *
        (parisiTheta (parisiTimeProfile ξ t)
            (parisiCanonicalCouplingRho ms qs negative r p u l l' (n.val + 1)) -
          parisiTheta (parisiTimeProfile ξ t)
            (parisiCanonicalCouplingRho ms qs negative r p u l l' n.val)) =
      t * parisiCorrection ξ ms qs := by
  have hθ : Function.Even (parisiTheta (parisiTimeProfile ξ t)) := by
    intro x
    rw [parisiTheta_timeProfile, parisiTheta_timeProfile]
    have he := parisiTheta_sgn_mul_of_even hξ.even (η := -1) (Or.inr rfl) x
    simpa only [neg_one_mul] using congrArg (fun y : ℝ => t * y) he
  let F (n : Fin (2 * k + 5)) (l l' : Fin 2) : ℝ :=
    ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).physicalMass ms r p *
      (parisiTheta (parisiTimeProfile ξ t)
          (parisiCanonicalCouplingRho ms qs negative r p u l l' (n.val + 1)) -
        parisiTheta (parisiTimeProfile ξ t)
          (parisiCanonicalCouplingRho ms qs negative r p u l l' n.val))
  have hc : (∑ l : Fin 2, ∑ l' : Fin 2, ∑ n, F n l l') =
      ∑ n, ∑ l : Fin 2, ∑ l' : Fin 2, F n l l' := by
    calc
      _ = ∑ l : Fin 2, ∑ n, ∑ l' : Fin 2, F n l l' :=
        Finset.sum_congr rfl (fun l _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  change (1 / 2) * (∑ l : Fin 2, ∑ l' : Fin 2, ∑ n, F n l l') = _
  rw [hc, Finset.mul_sum]
  dsimp only [F]
  simp_rw [parisiCanonicalMatrixCorrection_step hθ ms qs hm hq negative r p hu,
    ParisiCanonicalPiece.correction_timeProfile]
  rw [← Finset.mul_sum, sum_parisiCanonicalMerged_correction_fin]

/-- Raw positive-index masses retain the zero-mass driven root.
They are used here only for the algebraic coupled level sum. -/
noncomputable def parisiCanonicalRawMasses {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) : Fin (2 * k + 4) → ℝ :=
  fun n => ((parisiCanonicalMergedPieces ms r p)[n.val + 1]'(by
    rw [parisiCanonicalMergedPieces_length]; omega)).physicalMass ms r p

/-- The existing coupled level-sum API agrees with the actual labelled
correction before root compression. Zero masses are never supplied to
a positive-mass cascade comparison by this identity. -/
theorem coupledLevelSum_parisiCanonical_raw_eq_correction {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) (t : ℝ) {u : ℝ}
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) :
    (1 / 2) * coupledLevelSum (parisiTimeProfile ξ t)
      (parisiCanonicalCouplingRho ms qs negative r p u) (parisiCanonicalRawMasses ms r p) =
      t * parisiCorrection ξ ms qs := by
  have hs := parisiCanonicalFullLevelSum_eq_correction hξ ms qs hm hq negative r p t hu
  obtain ⟨tail, hroot⟩ := parisiCanonicalMergedPieces_root_prefix ms hm r p
  have hzero : ((parisiCanonicalMergedPieces ms r p)[0]'(by
      rw [parisiCanonicalMergedPieces_length]; omega)).physicalMass ms r p = 0 := by
    simpa only [hroot, List.getElem_cons_zero] using parisiCanonicalAuxiliaryRoot_mass_zero ms r p
  have hinner (l l' : Fin 2) :
      (∑ n : Fin (2 * k + 5),
        ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).physicalMass ms r p *
          (parisiTheta (parisiTimeProfile ξ t)
              (parisiCanonicalCouplingRho ms qs negative r p u l l' (n.val + 1)) -
            parisiTheta (parisiTimeProfile ξ t)
              (parisiCanonicalCouplingRho ms qs negative r p u l l' n.val))) =
      ∑ n : Fin (2 * k + 4),
        ((parisiCanonicalMergedPieces ms r p)[n.val + 1]'(by
          rw [parisiCanonicalMergedPieces_length]; omega)).physicalMass ms r p *
          (parisiTheta (parisiTimeProfile ξ t)
              (parisiCanonicalCouplingRho ms qs negative r p u l l' (n.val + 2)) -
            parisiTheta (parisiTimeProfile ξ t)
              (parisiCanonicalCouplingRho ms qs negative r p u l l' (n.val + 1))) := by
    rw [Fin.sum_univ_succ (n := 2 * k + 4)]
    simp only [Fin.val_zero, Fin.val_succ, hzero, zero_mul, zero_add,
      show ∀ n : ℕ, n + 1 + 1 = n + 2 by omega]
  simp_rw [hinner] at hs
  exact hs

end SpinGlass
