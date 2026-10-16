import SpinGlass.Parisi.Coupled.CoupledCanonicalCorrection
import SpinGlass.Parisi.Coupled.CoupledCanonicalWitness

/-!
# The overlap path of the physical canonical merge

Auxiliary pieces leave the overlap unchanged. Driven pieces traverse
the original overlap intervals, with the chosen interval split at the
absolute overlap. Their nonnegative increments define the concrete path
in (14.363), including repeated coordinates at auxiliary pieces.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

def ParisiCanonicalPiece.isDriven {k : ℕ} : ParisiCanonicalPiece k → Bool
  | .auxiliary _ => false
  | _ => true

theorem parisiCanonicalAuxiliaryPieces_filter_driven (k : ℕ) :
    (parisiCanonicalAuxiliaryPieces k).filter ParisiCanonicalPiece.isDriven = [] := by
  apply List.filter_eq_nil_iff.2
  intro e he
  obtain ⟨i, _hi, rfl⟩ := List.mem_map.1 he
  simp [ParisiCanonicalPiece.isDriven]

theorem parisiCanonicalDrivenPieces_filter_driven {k : ℕ} (p : Fin (k + 2)) :
    (parisiCanonicalDrivenPieces p).filter ParisiCanonicalPiece.isDriven =
      parisiCanonicalDrivenPieces p := by
  apply List.filter_eq_self.2
  intro e he
  obtain ⟨i, _hi, he⟩ := List.mem_flatMap.1 he
  by_cases hi : i = p
  · simp only [parisiCanonicalDrivenBlock, hi, ite_true, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl
  · simp only [parisiCanonicalDrivenBlock, hi, ite_false, List.mem_singleton] at he
    subst e
    rfl

/-- Filtering the physical merge recovers the exact driven source
list, rather than just a permutation of its overlap intervals. -/
theorem parisiCanonicalMergedPieces_filter_driven {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    (parisiCanonicalMergedPieces ms r p).filter ParisiCanonicalPiece.isDriven =
      parisiCanonicalDrivenPieces p := by
  have hs := (parisiCanonicalDrivenPieces_sublist_merged ms hm r p).filter
    ParisiCanonicalPiece.isDriven
  rw [parisiCanonicalDrivenPieces_filter_driven] at hs
  have hp := (parisiCanonicalMergedPieces_perm ms r p).filter ParisiCanonicalPiece.isDriven
  rw [List.filter_append, parisiCanonicalAuxiliaryPieces_filter_driven,
    parisiCanonicalDrivenPieces_filter_driven, List.nil_append] at hp
  exact (hs.eq_of_length hp.length_eq.symm).symm

theorem parisiCanonicalDrivenBlock_overlap_sum {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p i : Fin (k + 2)) (u : ℝ) :
    ((parisiCanonicalDrivenBlock p i).map
      (ParisiCanonicalPiece.profileIncrement id qs p u)).sum =
        qExt qs (i.val + 1) - qExt qs i.val := by
  by_cases hi : i = p
  · subst i
    simp only [parisiCanonicalDrivenBlock, ite_true, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, ParisiCanonicalPiece.profileIncrement, id_eq]
    ring
  · simp [parisiCanonicalDrivenBlock, hi, ParisiCanonicalPiece.profileIncrement]

/-- The sum of the actual driven overlap increments is one,
including both pieces of a root or terminal split. -/
theorem sum_parisiCanonicalMerged_overlap_increment {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) :
    ((parisiCanonicalMergedPieces ms r p).map
      (ParisiCanonicalPiece.profileIncrement id qs p u)).sum = 1 := by
  have hp := (parisiCanonicalMergedPieces_perm ms r p).map
    (ParisiCanonicalPiece.profileIncrement id qs p u)
  rw [hp.sum_eq, List.map_append, List.sum_append]
  have haux : ((parisiCanonicalAuxiliaryPieces k).map
      (ParisiCanonicalPiece.profileIncrement id qs p u)).sum = 0 := by
    simp [parisiCanonicalAuxiliaryPieces, List.map_map,
      ParisiCanonicalPiece.profileIncrement, Function.comp_def]
  rw [haux, zero_add]
  have hsum (l : List (Fin (k + 2))) :
      ((l.flatMap (parisiCanonicalDrivenBlock p)).map
        (ParisiCanonicalPiece.profileIncrement id qs p u)).sum =
      (l.map (fun i => qExt qs (i.val + 1) - qExt qs i.val)).sum := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, parisiCanonicalDrivenBlock_overlap_sum, ih]
  rw [parisiCanonicalDrivenPieces, hsum]
  simp only [parisiCanonicalIndices, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply, id_eq]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => qExt qs (i + 1) - qExt qs i)]
  have htel : ∀ n : ℕ, (∑ i ∈ Finset.range n,
      (qExt qs (i + 1) - qExt qs i)) = qExt qs n - qExt qs 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  rw [htel, qExt_zero, qExt_add_two]
  norm_num

theorem ParisiCanonicalPiece.overlapIncrement_nonneg {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) (p : Fin (k + 2))
    {u : ℝ} (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (e : ParisiCanonicalPiece k) : 0 ≤ e.profileIncrement id qs p u := by
  cases e with
  | auxiliary i => exact le_rfl
  | driven i =>
    simp only [profileIncrement, id_eq]
    split_ifs with hi
    · subst i
      exact sub_nonneg.2 hu.1
    · exact sub_nonneg.2 (hq.monotone_qExt (by omega))
  | splitRight => exact sub_nonneg.2 hu.2

noncomputable def parisiCanonicalOverlapPath {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) (n : ℕ) : ℝ :=
  (((parisiCanonicalMergedPieces ms r p).take n).map
    (ParisiCanonicalPiece.profileIncrement id qs p u)).sum

@[simp] theorem parisiCanonicalOverlapPath_zero {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) :
    parisiCanonicalOverlapPath ms qs r p u 0 = 0 := by
  simp [parisiCanonicalOverlapPath]

/-- The full merged path has the correct terminal overlap one. -/
theorem parisiCanonicalOverlapPath_terminal {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) {n : ℕ}
    (hn : 2 * k + 5 ≤ n) : parisiCanonicalOverlapPath ms qs r p u n = 1 := by
  unfold parisiCanonicalOverlapPath
  rw [List.take_of_length_le (by simpa using hn)]
  exact sum_parisiCanonicalMerged_overlap_increment ms qs r p u

theorem parisiCanonicalOverlapPath_monotone {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {u : ℝ}
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) :
    Monotone (parisiCanonicalOverlapPath ms qs r p u) := by
  intro n m hnm
  apply List.Sublist.sum_le_sum
  · exact List.Sublist.map _ (List.take_sublist_take_left hnm)
  · intro x hx
    obtain ⟨e, _he, rfl⟩ := List.mem_map.1 hx
    exact e.overlapIncrement_nonneg qs hq p hu

/-- Every coordinate of the physical overlap path is admissible. -/
theorem parisiCanonicalOverlapPath_mem_Icc {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {u : ℝ}
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) (n : ℕ) :
    parisiCanonicalOverlapPath ms qs r p u n ∈ Icc (0 : ℝ) 1 := by
  have hmono := parisiCanonicalOverlapPath_monotone ms qs hq r p hu
  constructor
  · simpa only [parisiCanonicalOverlapPath_zero] using hmono (Nat.zero_le n)
  · have hn := hmono (show n ≤ max n (2 * k + 5) from le_max_left _ _)
    rw [parisiCanonicalOverlapPath_terminal ms qs r p u (le_max_right _ _)] at hn
    exact hn

/-- Each merged piece advances the physical path by its actual
driven overlap increment, with zero advance at auxiliary pieces. -/
theorem parisiCanonicalOverlapPath_step {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) (n : Fin (2 * k + 5)) :
    parisiCanonicalOverlapPath ms qs r p u (n.val + 1) =
      parisiCanonicalOverlapPath ms qs r p u n.val +
        ((parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt)).profileIncrement
          id qs p u := by
  unfold parisiCanonicalOverlapPath
  rw [List.take_succ_eq_append_getElem (by simpa using n.isLt)]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

theorem parisiCanonicalOverlapPath_auxiliary_step {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (p i : Fin (k + 2)) (u : ℝ) (n : Fin (2 * k + 5))
    (he : (parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt) =
      .auxiliary i) :
    parisiCanonicalOverlapPath ms qs r p u (n.val + 1) =
      parisiCanonicalOverlapPath ms qs r p u n.val := by
  rw [parisiCanonicalOverlapPath_step, he]
  simp only [ParisiCanonicalPiece.profileIncrement, add_zero]

/-- The concrete matrix path uses signed shared overlaps up to
the chosen absolute overlap and constant off-diagonal overlaps thereafter. -/
noncomputable def parisiCanonicalCouplingRho {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ)
    (l l' : Fin 2) (n : ℕ) : ℝ :=
  if l = l' then parisiCanonicalOverlapPath ms qs r p u n
  else if negative then -min u (parisiCanonicalOverlapPath ms qs r p u n)
    else min u (parisiCanonicalOverlapPath ms qs r p u n)

theorem parisiCanonicalCouplingRho_zero {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {u : ℝ} (hu : 0 ≤ u) (l l' : Fin 2) :
    parisiCanonicalCouplingRho ms qs negative r p u l l' 0 = 0 := by
  simp [parisiCanonicalCouplingRho, min_eq_right hu]

theorem parisiCanonicalCouplingRho_mem_Icc {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {u : ℝ}
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) (l l' : Fin 2) (n : ℕ) :
    parisiCanonicalCouplingRho ms qs negative r p u l l' n ∈ Icc (-1 : ℝ) 1 := by
  have hp := parisiCanonicalOverlapPath_mem_Icc ms qs hq r p hu n
  have hu0 := (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 p.val).1.trans hu.1
  have hmin0 := le_min hu0 hp.1
  have hmin1 := (min_le_right u (parisiCanonicalOverlapPath ms qs r p u n)).trans hp.2
  rcases hp with ⟨hp0, hp1⟩
  unfold parisiCanonicalCouplingRho
  split_ifs <;> constructor <;> linarith

/-- The terminal matrix is the prescribed two-replica overlap.
This discharges the diagonal defect independently of Gaussian transport. -/
theorem parisiCanonicalCouplingRho_terminal {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {u : ℝ} (hu : u ≤ 1)
    (l l' : Fin 2) {n : ℕ} (hn : 2 * k + 5 ≤ n) :
    parisiCanonicalCouplingRho ms qs negative r p u l l' n =
      if l = l' then 1 else if negative then -u else u := by
  simp only [parisiCanonicalCouplingRho,
    parisiCanonicalOverlapPath_terminal ms qs r p u hn, min_eq_left hu]

theorem pairDiagDefect_parisiCanonicalCouplingRho_terminal {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {u : ℝ} (hu : u ≤ 1) :
    pairDiagDefect ξ (if negative then -u else u)
      (fun l l' => parisiCanonicalCouplingRho ms qs negative r p u l l' (2 * k + 5)) = 0 := by
  have hρ : (fun l l' => parisiCanonicalCouplingRho ms qs negative r p u l l' (2 * k + 5)) =
      (fun l l' => if l = l' then 1 else if negative then -u else u) := by
    funext l l'
    exact parisiCanonicalCouplingRho_terminal ms qs negative r p hu l l' le_rfl
  rw [hρ]
  simp only [pairDiagDefect, sub_self, zero_mul, Finset.sum_const_zero, mul_zero]

theorem parisiCanonicalCouplingRho_auxiliary_step {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p i : Fin (k + 2)) (u : ℝ) (n : Fin (2 * k + 5))
    (he : (parisiCanonicalMergedPieces ms r p)[n.val]'(by simpa using n.isLt) =
      .auxiliary i) (l l' : Fin 2) :
    parisiCanonicalCouplingRho ms qs negative r p u l l' (n.val + 1) =
      parisiCanonicalCouplingRho ms qs negative r p u l l' n.val := by
  simp only [parisiCanonicalCouplingRho,
    parisiCanonicalOverlapPath_auxiliary_step ms qs r p i u n he]

end SpinGlass
