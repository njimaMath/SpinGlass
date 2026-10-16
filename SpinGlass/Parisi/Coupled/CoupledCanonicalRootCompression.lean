import SpinGlass.Parisi.Coupled.CoupledCanonicalLevelSum

/-!
# Isolating the full zero-mass canonical root prefix

The actual sorted list is decomposed into all zero-mass expectations
and a positive-mass suffix. Its concrete suffix masses are monotone,
positive and at most one, as required by the cascade comparison API.
The additional expectation at a split root belongs to the root prefix.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

theorem canonicalZeroPrefix_mass_zero {α : Type*} (f : α → ℝ) (test : α → Bool)
    (htest : ∀ a, test a = true ↔ f a = 0) (l : List α) :
    ∀ a ∈ l.takeWhile test, f a = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro b hb
    by_cases ha : test a = true
    · simp only [List.takeWhile_cons, ha, ite_true, List.mem_cons] at hb
      rcases hb with hb | hb
      · subst b
        exact (htest a).1 ha
      · exact ih b hb
    · have ha' : test a = false := Bool.eq_false_iff.2 ha
      simp only [List.takeWhile_cons, ha', Bool.false_eq_true, ite_false, List.not_mem_nil] at hb

theorem canonicalPositiveSuffix_mass_pos {α : Type*} (f : α → ℝ) (test : α → Bool)
    (htest : ∀ a, test a = true ↔ f a = 0) (l : List α)
    (hs : l.Pairwise (fun a b => f a ≤ f b)) (hn : ∀ a ∈ l, 0 ≤ f a) :
    ∀ a ∈ l.dropWhile test, 0 < f a := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro b hb
    have hsorted := List.pairwise_cons.1 hs
    by_cases ha : test a = true
    · simp only [List.dropWhile_cons, ha, ite_true] at hb
      exact ih hsorted.2 (fun c hc => hn c (List.mem_cons_of_mem _ hc)) b hb
    · have ha' : test a = false := Bool.eq_false_iff.2 ha
      simp only [List.dropWhile_cons, ha', Bool.false_eq_true, ite_false, List.mem_cons] at hb
      have hapos : 0 < f a := lt_of_le_of_ne (hn a List.mem_cons_self)
        (Ne.symm (fun hz => ha ((htest a).2 hz)))
      rcases hb with rfl | hb
      · exact hapos
      · exact hapos.trans_le (hsorted.1 b hb)

noncomputable def parisiCanonicalRootTest {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) :
    ParisiCanonicalPiece k → Bool := by
  classical
  exact fun e => decide (e.physicalMass ms r p = 0)

@[simp] theorem parisiCanonicalRootTest_eq_true_iff {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) (e : ParisiCanonicalPiece k) :
    parisiCanonicalRootTest ms r p e = true ↔ e.physicalMass ms r p = 0 := by
  classical
  simp [parisiCanonicalRootTest]

noncomputable def parisiCanonicalRootPieces {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) : List (ParisiCanonicalPiece k) :=
  (parisiCanonicalMergedPieces ms r p).takeWhile (parisiCanonicalRootTest ms r p)

noncomputable def parisiCanonicalPositivePieces {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) : List (ParisiCanonicalPiece k) :=
  (parisiCanonicalMergedPieces ms r p).dropWhile (parisiCanonicalRootTest ms r p)

theorem parisiCanonicalRoot_append_positive {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) :
    parisiCanonicalRootPieces ms r p ++ parisiCanonicalPositivePieces ms r p =
      parisiCanonicalMergedPieces ms r p :=
  List.takeWhile_append_dropWhile

theorem parisiCanonicalRootPieces_mass_zero {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) :
    ∀ e ∈ parisiCanonicalRootPieces ms r p, e.physicalMass ms r p = 0 :=
  canonicalZeroPrefix_mass_zero (ParisiCanonicalPiece.physicalMass ms r p)
    (parisiCanonicalRootTest ms r p) (parisiCanonicalRootTest_eq_true_iff ms r p) _

theorem parisiCanonicalPositivePieces_sorted {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) :
    (parisiCanonicalPositivePieces ms r p).Pairwise (parisiCanonicalPhysicalOrder ms r p) :=
  (parisiCanonicalMergedPieces_sorted ms r p).sublist (List.dropWhile_sublist _)

theorem parisiCanonicalPositivePieces_mass_pos {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms) (r : Fin (k + 1)) (p : Fin (k + 2)) :
    ∀ e ∈ parisiCanonicalPositivePieces ms r p, 0 < e.physicalMass ms r p :=
  canonicalPositiveSuffix_mass_pos (ParisiCanonicalPiece.physicalMass ms r p)
    (parisiCanonicalRootTest ms r p) (parisiCanonicalRootTest_eq_true_iff ms r p) _
    (parisiCanonicalMergedPieces_sorted ms r p)
    (fun e _he => (e.physicalMass_mem_Icc ms hm r p).1)

theorem parisiCanonicalPositivePieces_ne_nil {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms) (r : Fin (k + 1)) (p : Fin (k + 2)) :
    parisiCanonicalPositivePieces ms r p ≠ [] := by
  let e : ParisiCanonicalPiece k := .auxiliary (Fin.last (k + 1))
  have he : e ∈ parisiCanonicalMergedPieces ms r p := parisiCanonicalPiece_mem_merged ms r p e
  have hpos : 0 < e.physicalMass ms r p := e.physicalMass_pos_of_oldLevel_pos
    ms hm r p (by simp [e, ParisiCanonicalPiece.oldLevel])
  rw [← parisiCanonicalRoot_append_positive] at he
  rcases List.mem_append.1 he with he | he
  · exact (hpos.ne' (parisiCanonicalRootPieces_mass_zero ms r p e he)).elim
  · intro hnil
    simpa only [hnil, List.not_mem_nil] using he

theorem parisiCanonicalRootPieces_length_ge_two {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms) (r : Fin (k + 1)) (p : Fin (k + 2)) :
    2 ≤ (parisiCanonicalRootPieces ms r p).length := by
  obtain ⟨tail, hroot⟩ := parisiCanonicalMergedPieces_root_prefix ms hm r p
  have haux : parisiCanonicalRootTest ms r p (.auxiliary 0) = true :=
    (parisiCanonicalRootTest_eq_true_iff ms r p _).2 (parisiCanonicalAuxiliaryRoot_mass_zero ms r p)
  have hdriven : parisiCanonicalRootTest ms r p (.driven 0) = true :=
    (parisiCanonicalRootTest_eq_true_iff ms r p _).2 (parisiCanonicalDrivenRoot_mass_zero ms r p)
  simp only [parisiCanonicalRootPieces, hroot, List.takeWhile_cons, haux, hdriven,
    ite_true, List.length_cons]
  omega

/-- The inserted independent mass-zero expectation is part of
the full root prefix when the original root interval is split. -/
theorem parisiCanonicalSplitRight_mem_root_of_root_split {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms) (r : Fin (k + 1)) :
    (ParisiCanonicalPiece.splitRight : ParisiCanonicalPiece k) ∈
      parisiCanonicalRootPieces ms r 0 := by
  have hmem := parisiCanonicalPiece_mem_merged ms r 0
    (ParisiCanonicalPiece.splitRight : ParisiCanonicalPiece k)
  rw [← parisiCanonicalRoot_append_positive] at hmem
  rcases List.mem_append.1 hmem with hmem | hmem
  · exact hmem
  · have hpos := parisiCanonicalPositivePieces_mass_pos ms hm r 0 _ hmem
    have hz : (ParisiCanonicalPiece.splitRight : ParisiCanonicalPiece k).physicalMass ms r 0 = 0 := by
      simp [ParisiCanonicalPiece.physicalMass, ParisiCanonicalPiece.shared,
        ParisiCanonicalPiece.oldLevel]
    exact (hpos.ne' hz).elim

/-- Concrete masses of the actual positive suffix. -/
noncomputable def parisiCanonicalPositiveMasses {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) :
    Fin (parisiCanonicalPositivePieces ms r p).length → ℝ :=
  fun i => ((parisiCanonicalPositivePieces ms r p)[i.val]).physicalMass ms r p

theorem parisiCanonicalPositiveMasses_pos {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms) (r : Fin (k + 1)) (p : Fin (k + 2))
    (i : Fin (parisiCanonicalPositivePieces ms r p).length) :
    0 < parisiCanonicalPositiveMasses ms r p i :=
  parisiCanonicalPositivePieces_mass_pos ms hm r p _ (List.getElem_mem _)

theorem parisiCanonicalPositiveMasses_le_one {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms) (r : Fin (k + 1)) (p : Fin (k + 2))
    (i : Fin (parisiCanonicalPositivePieces ms r p).length) :
    parisiCanonicalPositiveMasses ms r p i ≤ 1 :=
  (((parisiCanonicalPositivePieces ms r p)[i.val]).physicalMass_mem_Icc ms hm r p).2

theorem parisiCanonicalPositiveMasses_monotone {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) :
    Monotone (parisiCanonicalPositiveMasses ms r p) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · exact (List.pairwise_iff_getElem.1 (parisiCanonicalPositivePieces_sorted ms r p))
      i.val j.val i.isLt j.isLt hij
  · exact le_rfl

theorem sum_parisiCanonicalRootPieces_correction_eq_zero {k : ℕ}
    (θ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) :
    ((parisiCanonicalRootPieces ms r p).map
      (ParisiCanonicalPiece.correction θ ms qs r p u)).sum = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  simp [ParisiCanonicalPiece.correction, parisiCanonicalRootPieces_mass_zero ms r p e he]

/-- Removing all zero-mass root pieces preserves the exact old
Parisi correction of the physical list. -/
theorem sum_parisiCanonicalPositivePieces_correction_eq {k : ℕ}
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (u : ℝ) :
    ((parisiCanonicalPositivePieces ms r p).map
      (ParisiCanonicalPiece.correction (parisiTheta ξ) ms qs r p u)).sum =
        parisiCorrection ξ ms qs := by
  have hs := sum_parisiCanonicalMerged_correction_eq ξ ms qs r p u
  rw [← parisiCanonicalRoot_append_positive, List.map_append, List.sum_append,
    sum_parisiCanonicalRootPieces_correction_eq_zero, zero_add] at hs
  exact hs

end SpinGlass
