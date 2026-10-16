import SpinGlass.Parisi.Coupled.CoupledCanonicalWitness

/-!
# The actual signed root prefix of the canonical merge

Stable physical sorting places the original common auxiliary root and
the signed driven root first, in that order. A split-root independent
expectation follows them. This identifies the consecutive opposite
Gaussian directions required by the signed equality argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

theorem insertionSort_min_after_strict_prefix {α : Type*} (R : α → α → Prop) [DecidableRel R]
    (pre : List α) (q : α) (tail : List α) (hpre : ∀ a ∈ pre, ¬R a q) (htail : ∀ a ∈ tail, R q a) :
    List.insertionSort R (pre ++ q :: tail) = q :: List.insertionSort R (pre ++ tail) := by
  induction pre with
  | nil => exact List.insertionSort_cons_of_forall_rel R htail
  | cons a pre ih =>
    rw [List.cons_append, List.insertionSort_cons,
      ih (fun b hb => hpre b (List.mem_cons_of_mem _ hb)),
      List.orderedInsert_of_not_le R _ (hpre a (List.mem_cons_self)),
      List.cons_append, List.insertionSort_cons]

theorem parisiCanonicalAuxiliaryRoot_mass_zero {k : ℕ} (ms : Fin k → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    (ParisiCanonicalPiece.auxiliary (0 : Fin (k + 2))).physicalMass ms r p = 0 := by
  simp [ParisiCanonicalPiece.physicalMass, ParisiCanonicalPiece.shared, ParisiCanonicalPiece.oldLevel]

theorem parisiCanonicalDrivenRoot_mass_zero {k : ℕ} (ms : Fin k → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    (ParisiCanonicalPiece.driven (0 : Fin (k + 2))).physicalMass ms r p = 0 := by
  simp [ParisiCanonicalPiece.physicalMass, ParisiCanonicalPiece.shared, ParisiCanonicalPiece.oldLevel]

theorem ParisiCanonicalPiece.physicalMass_pos_of_oldLevel_pos {k : ℕ} (ms : Fin k → ℝ)
    (hm : ParisiMAdmissible ms) (r : Fin (k + 1)) (p : Fin (k + 2)) (e : ParisiCanonicalPiece k)
    (he : 0 < (e.oldLevel p).val) : 0 < e.physicalMass ms r p := by
  have hmass := hm.mExt_pos he
  unfold physicalMass
  split_ifs <;> positivity

/-- The two signed root pieces are consecutive at the beginning
of the actual stable merge, including a split root with a third
zero-mass expectation. No root-order hypothesis is supplied. -/
theorem parisiCanonicalMergedPieces_root_prefix {k : ℕ} (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    ∃ tail : List (ParisiCanonicalPiece k), parisiCanonicalMergedPieces ms r p =
      .auxiliary 0 :: .driven 0 :: tail := by
  let pre : List (ParisiCanonicalPiece k) := List.ofFn (fun j : Fin (k + 1) => .auxiliary j.succ)
  have haux : parisiCanonicalAuxiliaryPieces k = .auxiliary 0 :: pre := by
    simp [parisiCanonicalAuxiliaryPieces, parisiCanonicalIndices, List.map_ofFn,
      List.ofFn_succ, pre, Function.comp_def]
  let rest : List (ParisiCanonicalPiece k) :=
    (List.ofFn (fun j : Fin (k + 1) => j.succ)).flatMap (parisiCanonicalDrivenBlock p)
  have hdrive : ∃ tail, parisiCanonicalDrivenPieces p = .driven 0 :: tail := by
    by_cases hp : (0 : Fin (k + 2)) = p
    · refine ⟨.splitRight :: rest, ?_⟩
      simp [parisiCanonicalDrivenPieces, parisiCanonicalIndices, List.ofFn_succ, List.flatMap_cons,
        parisiCanonicalDrivenBlock, hp, rest]
    · refine ⟨rest, ?_⟩
      simp [parisiCanonicalDrivenPieces, parisiCanonicalIndices, List.ofFn_succ, List.flatMap_cons,
        parisiCanonicalDrivenBlock, hp, rest]
  obtain ⟨tail, htail⟩ := hdrive
  have hmin : ∀ e ∈ pre ++ .driven 0 :: tail,
      parisiCanonicalPhysicalOrder ms r p (.auxiliary 0) e := by
    intro e _he
    change (ParisiCanonicalPiece.auxiliary (0 : Fin (k + 2))).physicalMass ms r p ≤ e.physicalMass ms r p
    rw [parisiCanonicalAuxiliaryRoot_mass_zero]
    exact (e.physicalMass_mem_Icc ms hm r p).1
  have hpre : ∀ e ∈ pre, ¬parisiCanonicalPhysicalOrder ms r p e (.driven 0) := by
    intro e he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 he
    change ¬(ParisiCanonicalPiece.auxiliary j.succ).physicalMass ms r p ≤
      (ParisiCanonicalPiece.driven (0 : Fin (k + 2))).physicalMass ms r p
    rw [parisiCanonicalDrivenRoot_mass_zero]
    exact not_le_of_gt ((ParisiCanonicalPiece.auxiliary j.succ).physicalMass_pos_of_oldLevel_pos
      ms hm r p (by change 0 < j.val + 1; omega))
  have hminDrive : ∀ e ∈ tail, parisiCanonicalPhysicalOrder ms r p (.driven 0) e := by
    intro e _he
    change (ParisiCanonicalPiece.driven (0 : Fin (k + 2))).physicalMass ms r p ≤ e.physicalMass ms r p
    rw [parisiCanonicalDrivenRoot_mass_zero]
    exact (e.physicalMass_mem_Icc ms hm r p).1
  refine ⟨List.insertionSort (parisiCanonicalPhysicalOrder ms r p) (pre ++ tail), ?_⟩
  simp only [parisiCanonicalMergedPieces, haux, htail, List.cons_append]
  rw [List.insertionSort_cons_of_forall_rel _ hmin,
    insertionSort_min_after_strict_prefix _ pre (.driven 0) tail hpre hminDrive]

/-- The actual paired recursion starts with the two signed root
expectations. Any extra split-root expectation remains in the tail. -/
theorem parisiCanonicalPairLevels_root_prefix {k : ℕ} (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) :
    ∃ tail : List PairColeHopfLevel, parisiCanonicalPairLevels ξ ms qs negative r p t u =
      (ParisiCanonicalPiece.auxiliary 0).toPairLevel ξ ms qs negative r p t u ::
      (ParisiCanonicalPiece.driven 0).toPairLevel ξ ms qs negative r p t u :: tail := by
  obtain ⟨tail, htail⟩ := parisiCanonicalMergedPieces_root_prefix ms hm r p
  refine ⟨tail.map (ParisiCanonicalPiece.toPairLevel ξ ms qs negative r p t u), ?_⟩
  simp only [parisiCanonicalPairLevels, htail, List.map_cons]

end SpinGlass
