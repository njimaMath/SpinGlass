import SpinGlass.Parisi.Coupled.CoupledCanonicalScalar

/-!
# Canonical physical order and preserved source lists

The auxiliary and driven lists are separately ordered by their actual
physical masses. Stable sorting retains each as an unchanged sublist,
including tied zero masses from a root split. These are the index-order
bridges needed to delete deterministic marks in the physical cascade.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

theorem parisiCanonicalAuxiliaryMass_monotone {k : ℕ} (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    Monotone (fun i : Fin (k + 2) => (ParisiCanonicalPiece.auxiliary i).physicalMass ms r p) := by
  intro i j hij
  have hmass := hm.monotone_mExt (Fin.le_iff_val_le_val.1 hij)
  have h0 := mExt_nonneg (fun q => (hm.2.1 q).le) i.val
  simp only [ParisiCanonicalPiece.physicalMass, ParisiCanonicalPiece.shared,
    ParisiCanonicalPiece.oldLevel, decide_eq_true_eq]
  split_ifs with hi hj hj
  · linarith
  · linarith
  · omega
  · exact hmass

theorem parisiCanonicalDrivenMass_monotone {k : ℕ} (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    Monotone (fun i : Fin (k + 2) => (ParisiCanonicalPiece.driven i).physicalMass ms r p) := by
  intro i j hij
  have hmass := hm.monotone_mExt (Fin.le_iff_val_le_val.1 hij)
  have h0 := mExt_nonneg (fun q => (hm.2.1 q).le) i.val
  simp only [ParisiCanonicalPiece.physicalMass, ParisiCanonicalPiece.shared,
    ParisiCanonicalPiece.oldLevel, decide_eq_true_eq]
  split_ifs with hi hj hj
  · linarith
  · linarith
  · exact (hi (hij.trans hj)).elim
  · exact hmass

theorem parisiCanonicalDrivenBlock_mass_bounds {k : ℕ} (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p i : Fin (k + 2)) (e : ParisiCanonicalPiece k)
    (he : e ∈ parisiCanonicalDrivenBlock p i) :
    mExt ms i.val / 2 ≤ e.physicalMass ms r p ∧ e.physicalMass ms r p ≤ mExt ms i.val := by
  have h0 := mExt_nonneg (fun q => (hm.2.1 q).le) i.val
  by_cases hi : i = p
  · subst i
    simp [parisiCanonicalDrivenBlock] at he
    rcases he with rfl | rfl
    · simpa [ParisiCanonicalPiece.physicalMass, ParisiCanonicalPiece.shared,
        ParisiCanonicalPiece.oldLevel] using (show mExt ms p.val / 2 ≤ mExt ms p.val by linarith)
    · simpa [ParisiCanonicalPiece.physicalMass, ParisiCanonicalPiece.shared,
        ParisiCanonicalPiece.oldLevel] using (show mExt ms p.val / 2 ≤ mExt ms p.val by linarith)
  · simp [parisiCanonicalDrivenBlock, hi] at he
    subst e
    simp only [ParisiCanonicalPiece.physicalMass, ParisiCanonicalPiece.shared, ParisiCanonicalPiece.oldLevel,
      decide_eq_true_eq]
    split_ifs <;> constructor <;> linarith

theorem parisiCanonicalAuxiliaryPieces_sorted {k : ℕ} (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    List.Pairwise (parisiCanonicalPhysicalOrder ms r p) (parisiCanonicalAuxiliaryPieces k) := by
  simp only [parisiCanonicalAuxiliaryPieces, parisiCanonicalIndices, List.map_ofFn]
  apply List.pairwise_ofFn.2
  intro i j hij
  exact parisiCanonicalAuxiliaryMass_monotone ms hm r p hij.le

theorem parisiCanonicalDrivenPieces_sorted {k : ℕ} (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    List.Pairwise (parisiCanonicalPhysicalOrder ms r p) (parisiCanonicalDrivenPieces p) := by
  unfold parisiCanonicalDrivenPieces
  apply List.pairwise_flatMap.2
  refine ⟨fun i _hi => ?_, ?_⟩
  · by_cases hi : i = p
    · subst i
      have h0 := mExt_nonneg (fun q => (hm.2.1 q).le) p.val
      simpa [parisiCanonicalDrivenBlock, parisiCanonicalPhysicalOrder,
        ParisiCanonicalPiece.physicalMass, ParisiCanonicalPiece.shared,
        ParisiCanonicalPiece.oldLevel] using (show mExt ms p.val / 2 ≤ mExt ms p.val by linarith)
    · simp only [parisiCanonicalDrivenBlock, hi, ite_false, List.pairwise_singleton]
  · unfold parisiCanonicalIndices
    apply List.pairwise_ofFn.2
    intro i j hij a ha b hb
    change a.physicalMass ms r p ≤ b.physicalMass ms r p
    have hmass := hm.monotone_mExt (Fin.le_iff_val_le_val.1 hij.le)
    by_cases hj : j ≤ p
    · have hi : i ≠ p := by intro he; subst i; exact (not_lt_of_ge hj) hij
      have hip : i ≤ p := hij.le.trans hj
      simp [parisiCanonicalDrivenBlock, hi] at ha
      subst a
      have hmin := (parisiCanonicalDrivenBlock_mass_bounds ms hm r p j b hb).1
      have himass : (ParisiCanonicalPiece.driven i).physicalMass ms r p = mExt ms i.val / 2 := by
        simp [ParisiCanonicalPiece.physicalMass, ParisiCanonicalPiece.shared, ParisiCanonicalPiece.oldLevel, hip]
      rw [himass]
      exact (div_le_div_of_nonneg_right hmass (by norm_num : (0 : ℝ) ≤ 2)).trans hmin
    · have hjne : j ≠ p := by intro he; subst j; exact hj le_rfl
      simp [parisiCanonicalDrivenBlock, hjne] at hb
      subst b
      have hmax := (parisiCanonicalDrivenBlock_mass_bounds ms hm r p i a ha).2
      simp only [ParisiCanonicalPiece.physicalMass, ParisiCanonicalPiece.shared,
        ParisiCanonicalPiece.oldLevel, hj, decide_false, Bool.false_eq_true, ite_false]
      exact hmax.trans hmass

/-- The canonical auxiliary list occurs unchanged in physical
order inside the merged list, even at tied masses. -/
theorem parisiCanonicalAuxiliaryPieces_sublist_merged {k : ℕ} (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    (parisiCanonicalAuxiliaryPieces k).Sublist (parisiCanonicalMergedPieces ms r p) :=
  List.sublist_insertionSort (parisiCanonicalAuxiliaryPieces_sorted ms hm r p) (List.sublist_append_left _ _)

/-- The driven split list occurs unchanged in physical order.
This includes the extra expectation at a split root. -/
theorem parisiCanonicalDrivenPieces_sublist_merged {k : ℕ} (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    (parisiCanonicalDrivenPieces p).Sublist (parisiCanonicalMergedPieces ms r p) :=
  List.sublist_insertionSort (parisiCanonicalDrivenPieces_sorted ms hm r p) (List.sublist_append_right _ _)

theorem parisiCanonicalPairLevels_sorted {k : ℕ} (ξ : ℝ → ℝ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) :
    List.Pairwise (fun a b : PairColeHopfLevel => a.mass ≤ b.mass)
      (parisiCanonicalPairLevels ξ ms qs negative r p t u) := by
  apply List.pairwise_map.2
  exact parisiCanonicalMergedPieces_sorted ms r p

@[simp] theorem parisiCanonicalAuxiliaryPieces_length (k : ℕ) :
    (parisiCanonicalAuxiliaryPieces k).length = k + 2 := by
  simp [parisiCanonicalAuxiliaryPieces, parisiCanonicalIndices]

@[simp] theorem parisiCanonicalDrivenPieces_length {k : ℕ} (p : Fin (k + 2)) :
    (parisiCanonicalDrivenPieces p).length = k + 3 := by
  have hblock (i : Fin (k + 2)) : (parisiCanonicalDrivenBlock p i).length = 1 + if i = p then 1 else 0 := by
    by_cases hi : i = p <;> simp [parisiCanonicalDrivenBlock, hi]
  simp only [parisiCanonicalDrivenPieces, List.length_flatMap, parisiCanonicalIndices,
    List.map_ofFn, List.sum_ofFn, Function.comp_apply, id_eq]
  simp_rw [hblock]
  rw [Finset.sum_add_distrib]
  simp

@[simp] theorem parisiCanonicalMergedPieces_length {k : ℕ} (ms : Fin k → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    (parisiCanonicalMergedPieces ms r p).length = 2 * k + 5 := by
  rw [(parisiCanonicalMergedPieces_perm ms r p).length_eq, List.length_append,
    parisiCanonicalAuxiliaryPieces_length, parisiCanonicalDrivenPieces_length]
  omega

@[simp] theorem parisiCanonicalPairLevels_length {k : ℕ} (ξ : ℝ → ℝ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) :
    (parisiCanonicalPairLevels ξ ms qs negative r p t u).length = 2 * k + 5 := by
  simp only [parisiCanonicalPairLevels, List.length_map, parisiCanonicalMergedPieces_length]

/-- Every labelled piece occurs in the actual merged list. This
supplies concrete witnesses for its strict-gap and covariance consumers. -/
theorem parisiCanonicalPiece_mem_merged {k : ℕ} (ms : Fin k → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (e : ParisiCanonicalPiece k) :
    e ∈ parisiCanonicalMergedPieces ms r p := by
  apply (parisiCanonicalMergedPieces_perm ms r p).mem_iff.2
  have hmem (i : Fin (k + 2)) : i ∈ parisiCanonicalIndices k :=
    List.mem_ofFn.2 ⟨i, rfl⟩
  cases e with
  | auxiliary i =>
    apply List.mem_append_left
    exact List.mem_map.2 ⟨i, hmem i, rfl⟩
  | driven i =>
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨i, hmem i, by by_cases hi : i = p <;> simp [parisiCanonicalDrivenBlock, hi]⟩
  | splitRight =>
    apply List.mem_append_right
    exact List.mem_flatMap.2 ⟨p, hmem p, by simp [parisiCanonicalDrivenBlock]⟩

end SpinGlass
