import SpinGlass.Parisi.Coupled.CoupledCanonicalRootCompression

/-!
# The root-compressed canonical matrix path

All zero-mass expectations form a single product-Gaussian root. The
remaining matrix path uses exactly the positive suffix. Its concrete
indices transfer the driven covariance, terminal defect and correction
identities to the positive-mass coupled comparison API.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

theorem parisiCanonicalRoot_length_add_positive_length {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) :
    (parisiCanonicalRootPieces ms r p).length +
      (parisiCanonicalPositivePieces ms r p).length = 2 * k + 5 := by
  have he := congrArg List.length (parisiCanonicalRoot_append_positive ms r p)
  simpa only [List.length_append, parisiCanonicalMergedPieces_length] using he

noncomputable def parisiCanonicalRootIndex {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2))
    (i : Fin (parisiCanonicalRootPieces ms r p).length) : Fin (2 * k + 5) :=
  ⟨i.val, by have hl := parisiCanonicalRoot_length_add_positive_length ms r p; omega⟩

noncomputable def parisiCanonicalPositiveIndex {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2))
    (i : Fin (parisiCanonicalPositivePieces ms r p).length) : Fin (2 * k + 5) :=
  ⟨(parisiCanonicalRootPieces ms r p).length + i.val,
    by have hl := parisiCanonicalRoot_length_add_positive_length ms r p; omega⟩

theorem parisiCanonicalMerged_get_rootIndex {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2))
    (i : Fin (parisiCanonicalRootPieces ms r p).length) :
    (parisiCanonicalMergedPieces ms r p)[(parisiCanonicalRootIndex ms r p i).val]'(by
      rw [parisiCanonicalMergedPieces_length]; exact (parisiCanonicalRootIndex ms r p i).isLt) =
      (parisiCanonicalRootPieces ms r p)[i.val] := by
  simp only [parisiCanonicalRootIndex]
  calc
    _ = (parisiCanonicalRootPieces ms r p ++ parisiCanonicalPositivePieces ms r p)[i.val]'(by
      simp only [List.length_append]; omega) :=
      List.getElem_of_eq (parisiCanonicalRoot_append_positive ms r p).symm _
    _ = _ := List.getElem_append_left i.isLt

theorem parisiCanonicalMerged_get_positiveIndex {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2))
    (i : Fin (parisiCanonicalPositivePieces ms r p).length) :
    (parisiCanonicalMergedPieces ms r p)[(parisiCanonicalPositiveIndex ms r p i).val]'(by
      rw [parisiCanonicalMergedPieces_length]; exact (parisiCanonicalPositiveIndex ms r p i).isLt) =
      (parisiCanonicalPositivePieces ms r p)[i.val] := by
  simp only [parisiCanonicalPositiveIndex]
  calc
    _ = (parisiCanonicalRootPieces ms r p ++ parisiCanonicalPositivePieces ms r p)[
        (parisiCanonicalRootPieces ms r p).length + i.val]'(by
          simp only [List.length_append]; omega) :=
      List.getElem_of_eq (parisiCanonicalRoot_append_positive ms r p).symm _
    _ = _ := by
      simpa only [Nat.add_comm] using
        (List.getElem_append_right' (parisiCanonicalRootPieces ms r p) i.isLt).symm

/-- Coordinate one is the aggregate of the entire zero-mass root;
each subsequent coordinate advances one actual positive suffix piece. -/
noncomputable def parisiCanonicalCompressedRho {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) (l l' : Fin 2) : ℕ → ℝ
  | 0 => 0
  | n + 1 => parisiCanonicalCouplingRho ms qs negative r p u l l'
      ((parisiCanonicalRootPieces ms r p).length + n)

@[simp] theorem parisiCanonicalCompressedRho_zero {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) (l l' : Fin 2) :
    parisiCanonicalCompressedRho ms qs negative r p u l l' 0 = 0 := rfl

theorem parisiCanonicalCompressedRho_mem_Icc {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {u : ℝ}
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) (l l' : Fin 2) (n : ℕ) :
    parisiCanonicalCompressedRho ms qs negative r p u l l' n ∈ Icc (-1 : ℝ) 1 := by
  cases n with
  | zero => norm_num
  | succ n => exact parisiCanonicalCouplingRho_mem_Icc ms qs hq negative r p hu l l' _

theorem parisiCanonicalCompressedRho_terminal {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {u : ℝ} (hu : u ≤ 1) (l l' : Fin 2) :
    parisiCanonicalCompressedRho ms qs negative r p u l l'
        ((parisiCanonicalPositivePieces ms r p).length + 1) =
      if l = l' then 1 else if negative then -u else u := by
  simp only [parisiCanonicalCompressedRho, parisiCanonicalRoot_length_add_positive_length]
  exact parisiCanonicalCouplingRho_terminal ms qs negative r p hu l l' le_rfl

theorem pairDiagDefect_parisiCanonicalCompressedRho_terminal {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {u : ℝ} (hu : u ≤ 1) :
    pairDiagDefect ξ (if negative then -u else u)
      (fun l l' => parisiCanonicalCompressedRho ms qs negative r p u l l'
        ((parisiCanonicalPositivePieces ms r p).length + 1)) = 0 := by
  simp only [pairDiagDefect, parisiCanonicalCompressedRho_terminal ms qs negative r p hu,
    sub_self, zero_mul, Finset.sum_const_zero, mul_zero]

/-- The covariance columns of every positive suffix piece satisfy
the root-compressed path increments, with no root mass in the suffix API. -/
theorem parisiCanonicalPositiveDrivenVariance_mul_gram {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ} (ht : 0 ≤ t)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (i : Fin (parisiCanonicalPositivePieces ms r p).length) (l l' : Fin 2) :
    (((parisiCanonicalPositivePieces ms r p)[i.val]).drivenVariance ξ qs p t u : ℝ) *
      gram (((parisiCanonicalPositivePieces ms r p)[i.val]).gaussianFactor negative r p) l l' =
      deriv (parisiTimeProfile ξ t)
          (parisiCanonicalCompressedRho ms qs negative r p u l l' (i.val + 2)) -
        deriv (parisiTimeProfile ξ t)
          (parisiCanonicalCompressedRho ms qs negative r p u l l' (i.val + 1)) := by
  have hc := parisiCanonicalDrivenVariance_mul_gram hξ ms qs hm hq negative r p ht hu
    (parisiCanonicalPositiveIndex ms r p i) l l'
  rw [parisiCanonicalMerged_get_positiveIndex] at hc
  simpa only [parisiCanonicalPositiveIndex, parisiCanonicalCompressedRho, Nat.add_assoc] using hc

theorem parisiCanonicalPositiveMatrixCorrection_step {k : ℕ}
    {θ : ℝ → ℝ} (hθ : Function.Even θ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {u : ℝ}
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (i : Fin (parisiCanonicalPositivePieces ms r p).length) :
    (1 / 2) * ∑ l : Fin 2, ∑ l' : Fin 2,
      parisiCanonicalPositiveMasses ms r p i *
        (θ (parisiCanonicalCompressedRho ms qs negative r p u l l' (i.val + 2)) -
          θ (parisiCanonicalCompressedRho ms qs negative r p u l l' (i.val + 1))) =
      ((parisiCanonicalPositivePieces ms r p)[i.val]).correction θ ms qs r p u := by
  have hs := parisiCanonicalMatrixCorrection_step hθ ms qs hm hq negative r p hu
    (parisiCanonicalPositiveIndex ms r p i)
  rw [parisiCanonicalMerged_get_positiveIndex] at hs
  simpa only [parisiCanonicalPositiveMasses, parisiCanonicalPositiveIndex,
    parisiCanonicalCompressedRho, Nat.add_assoc] using hs

theorem sum_parisiCanonicalPositivePieces_correction_fin {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) :
    (∑ i : Fin (parisiCanonicalPositivePieces ms r p).length,
      ((parisiCanonicalPositivePieces ms r p)[i.val]).correction
        (parisiTheta ξ) ms qs r p u) = parisiCorrection ξ ms qs := by
  rw [← List.sum_ofFn, List.ofFn_getElem_eq_map]
  exact sum_parisiCanonicalPositivePieces_correction_eq ξ ms qs r p u

/-- The existing coupled level-sum API now uses the actual strictly
positive suffix masses and the aggregated root coordinate. -/
theorem coupledLevelSum_parisiCanonical_compressed_eq_correction {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) (t : ℝ) {u : ℝ}
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) :
    (1 / 2) * coupledLevelSum (parisiTimeProfile ξ t)
      (parisiCanonicalCompressedRho ms qs negative r p u)
      (parisiCanonicalPositiveMasses ms r p) = t * parisiCorrection ξ ms qs := by
  have hθ : Function.Even (parisiTheta (parisiTimeProfile ξ t)) := by
    intro x
    rw [parisiTheta_timeProfile, parisiTheta_timeProfile]
    have he := parisiTheta_sgn_mul_of_even hξ.even (η := -1) (Or.inr rfl) x
    simpa only [neg_one_mul] using congrArg (fun y : ℝ => t * y) he
  let F (i : Fin (parisiCanonicalPositivePieces ms r p).length) (l l' : Fin 2) : ℝ :=
    parisiCanonicalPositiveMasses ms r p i *
      (parisiTheta (parisiTimeProfile ξ t)
          (parisiCanonicalCompressedRho ms qs negative r p u l l' (i.val + 2)) -
        parisiTheta (parisiTimeProfile ξ t)
          (parisiCanonicalCompressedRho ms qs negative r p u l l' (i.val + 1)))
  have hc : (∑ l : Fin 2, ∑ l' : Fin 2, ∑ i, F i l l') =
      ∑ i, ∑ l : Fin 2, ∑ l' : Fin 2, F i l l' := by
    calc
      _ = ∑ l : Fin 2, ∑ i, ∑ l' : Fin 2, F i l l' :=
        Finset.sum_congr rfl (fun l _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  change (1 / 2) * (∑ l : Fin 2, ∑ l' : Fin 2, ∑ i, F i l l') = _
  rw [hc, Finset.mul_sum]
  dsimp only [F]
  simp_rw [parisiCanonicalPositiveMatrixCorrection_step hθ ms qs hm hq negative r p hu,
    ParisiCanonicalPiece.correction_timeProfile]
  rw [← Finset.mul_sum, sum_parisiCanonicalPositivePieces_correction_fin]

/-- The actual product root covariance telescopes to the first
compressed matrix increment, including the third split-root expectation. -/
theorem sum_parisiCanonicalRootDrivenVariance_mul_gram {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ} (ht : 0 ≤ t)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) (l l' : Fin 2) :
    (∑ i : Fin (parisiCanonicalRootPieces ms r p).length,
      (((parisiCanonicalRootPieces ms r p)[i.val]).drivenVariance ξ qs p t u : ℝ) *
        gram (((parisiCanonicalRootPieces ms r p)[i.val]).gaussianFactor negative r p) l l') =
      deriv (parisiTimeProfile ξ t) (parisiCanonicalCompressedRho ms qs negative r p u l l' 1) -
        deriv (parisiTimeProfile ξ t) (parisiCanonicalCompressedRho ms qs negative r p u l l' 0) := by
  have hc (i : Fin (parisiCanonicalRootPieces ms r p).length) :
      (((parisiCanonicalRootPieces ms r p)[i.val]).drivenVariance ξ qs p t u : ℝ) *
          gram (((parisiCanonicalRootPieces ms r p)[i.val]).gaussianFactor negative r p) l l' =
        deriv (parisiTimeProfile ξ t) (parisiCanonicalCouplingRho ms qs negative r p u l l' (i.val + 1)) -
          deriv (parisiTimeProfile ξ t) (parisiCanonicalCouplingRho ms qs negative r p u l l' i.val) := by
    have hh := parisiCanonicalDrivenVariance_mul_gram hξ ms qs hm hq negative r p ht hu
      (parisiCanonicalRootIndex ms r p i) l l'
    rw [parisiCanonicalMerged_get_rootIndex] at hh
    simpa only [parisiCanonicalRootIndex] using hh
  simp_rw [hc]
  let F (n : ℕ) : ℝ := deriv (parisiTimeProfile ξ t)
    (parisiCanonicalCouplingRho ms qs negative r p u l l' n)
  change (∑ i : Fin (parisiCanonicalRootPieces ms r p).length,
    (F (i.val + 1) - F i.val)) = _
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => F (n + 1) - F n)]
  have htel : ∀ n : ℕ, (∑ i ∈ Finset.range n, (F (i + 1) - F i)) = F n - F 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  rw [htel]
  have hu0 := (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 p.val).1.trans hu.1
  simp only [F, parisiCanonicalCompressedRho, Nat.add_zero,
    parisiCanonicalCouplingRho_zero ms qs negative r p hu0]

end SpinGlass
