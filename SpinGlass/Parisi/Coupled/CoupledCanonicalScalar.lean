import SpinGlass.Parisi.Coupled.CoupledCanonicalPieces

/-!
# The original scalar comparator of the merged construction

Physical sorting preserves the labelled pieces. Sorting their effective
scalar masses then groups exactly the Gaussian pieces of each original
interval. Their proved variance sum recovers the original full recursion,
including the mass-zero root and terminal mass one, as in (14.376).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

theorem parisiCanonicalBlock_oldLevel {k : ℕ} (p i : Fin (k + 2))
    (e : ParisiCanonicalPiece k) (he : e ∈ .auxiliary i :: parisiCanonicalDrivenBlock p i) :
    e.oldLevel p = i := by
  rcases List.mem_cons.1 he with rfl | he
  · rfl
  · by_cases hi : i = p
    · subst i
      simp [parisiCanonicalDrivenBlock] at he
      rcases he with rfl | rfl <;> rfl
    · simp [parisiCanonicalDrivenBlock, hi] at he
      subst e
      rfl

theorem parisiCanonicalPieces_perm_grouped {k : ℕ} (p : Fin (k + 2)) :
    (parisiCanonicalAuxiliaryPieces k ++ parisiCanonicalDrivenPieces p).Perm
      (parisiCanonicalGroupedPieces p) := by
  have hperm (l : List (Fin (k + 2))) :
      (l.map ParisiCanonicalPiece.auxiliary ++ l.flatMap (parisiCanonicalDrivenBlock p)).Perm
        (l.flatMap (fun i => .auxiliary i :: parisiCanonicalDrivenBlock p i)) := by
    induction l with
    | nil => exact List.Perm.refl _
    | cons i l ih =>
      simp only [List.map_cons, List.flatMap_cons, List.cons_append]
      apply List.Perm.cons
      have hshuffle : (l.map ParisiCanonicalPiece.auxiliary ++
          (parisiCanonicalDrivenBlock p i ++ l.flatMap (parisiCanonicalDrivenBlock p))).Perm
          (parisiCanonicalDrivenBlock p i ++
            (l.map ParisiCanonicalPiece.auxiliary ++ l.flatMap (parisiCanonicalDrivenBlock p))) := by
        simpa only [List.append_assoc] using
          (List.perm_append_comm : (l.map ParisiCanonicalPiece.auxiliary ++ parisiCanonicalDrivenBlock p i).Perm
            (parisiCanonicalDrivenBlock p i ++ l.map ParisiCanonicalPiece.auxiliary)).append_right
              (l.flatMap (parisiCanonicalDrivenBlock p))
      exact hshuffle.trans (ih.append_left (parisiCanonicalDrivenBlock p i))
  exact hperm (parisiCanonicalIndices k)

noncomputable def parisiCanonicalScalarBlocks {k : ℕ} (ξ : ℝ → ℝ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 2)) (t u : ℝ) : List (ℝ × List ℝ≥0) :=
  (parisiCanonicalIndices k).map (fun i => (mExt ms i.val, parisiCanonicalVarianceBlock ξ qs p i t u))

theorem parisiCanonicalGroupedScalar_eq_blocks {k : ℕ} (ξ : ℝ → ℝ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) :
    (parisiCanonicalGroupedPieces p).map (fun e => (e.toPairLevel ξ ms qs negative r p t u).scalar) =
      (parisiCanonicalScalarBlocks ξ ms qs p t u).flatMap (fun b => b.2.map (fun v => (b.1, v))) := by
  simp only [parisiCanonicalGroupedPieces, parisiCanonicalScalarBlocks, List.map_flatMap, List.flatMap_map]
  congr 1
  funext i
  simp only [parisiCanonicalVarianceBlock, List.map_map]
  apply List.map_congr_left
  intro e he
  rw [e.scalar_eq, parisiCanonicalBlock_oldLevel p i e he]
  rfl

theorem parisiCanonicalGroupedScalar_sorted {k : ℕ} (ξ : ℝ → ℝ) (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t u : ℝ) :
    List.Pairwise parisiLevelMassOrder
      ((parisiCanonicalGroupedPieces p).map (fun e => (e.toPairLevel ξ ms qs negative r p t u).scalar)) := by
  rw [parisiCanonicalGroupedScalar_eq_blocks]
  simp only [parisiCanonicalScalarBlocks, List.flatMap_map]
  apply List.pairwise_flatMap.2
  refine ⟨fun i _hi => ?_, ?_⟩
  · exact List.pairwise_map.2 (List.pairwise_of_forall fun _v _w => (le_rfl : mExt ms i.val ≤ mExt ms i.val))
  · unfold parisiCanonicalIndices
    apply List.pairwise_ofFn.2
    intro i j hij a ha b hb
    obtain ⟨va, _hva, rfl⟩ := List.mem_map.1 ha
    obtain ⟨vb, _hvb, rfl⟩ := List.mem_map.1 hb
    exact hm.monotone_mExt (Fin.le_iff_val_le_val.1 hij.le)

theorem parisiCanonicalScalarBlocks_merge_eq_full {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    (p : Fin (k + 2)) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) :
    (parisiCanonicalScalarBlocks ξ ms qs p t u).map (fun b => (b.1, b.2.sum)) =
      parisiFullColeHopfLevels ξ ms qs := by
  simp only [parisiCanonicalScalarBlocks, parisiCanonicalIndices, List.map_ofFn,
    parisiFullColeHopfLevels]
  congr 1
  funext i
  dsimp only [Function.comp_apply, id_eq]
  rw [parisiCanonicalVarianceBlock_sum hξ qs hq p i ht hu]
  apply Prod.ext
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero, mExt_zero, Fin.cons_zero]
    · simp only [Fin.val_succ, Fin.cons_succ, parisiLevelMasses_apply]
  · rfl

/-- The actual merged scalar comparison is exactly the old full
Parisi recursion after effective-mass sorting and variance regrouping. -/
theorem coleHopfIterateList_parisiCanonical_sorted_eq_full {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2))
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) {A : ℝ → ℝ} {L : ℝ}
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) :
    coleHopfIterateList (List.insertionSort parisiLevelMassOrder
      (pairColeHopfScalarLevels (parisiCanonicalPairLevels ξ ms qs negative r p t u))) A =
        coleHopfIterateList (parisiFullColeHopfLevels ξ ms qs) A := by
  let f := fun e : ParisiCanonicalPiece k => (e.toPairLevel ξ ms qs negative r p t u).scalar
  have hp : (pairColeHopfScalarLevels (parisiCanonicalPairLevels ξ ms qs negative r p t u)).Perm
      ((parisiCanonicalGroupedPieces p).map f) := by
    simpa only [pairColeHopfScalarLevels, parisiCanonicalPairLevels, List.map_map, f, Function.comp_def] using
      ((parisiCanonicalMergedPieces_perm ms r p).trans (parisiCanonicalPieces_perm_grouped p)).map f
  have he := coleHopfIterateList_eq_of_sorted_perm hA
    (List.insertionSort parisiLevelMassOrder
      (pairColeHopfScalarLevels (parisiCanonicalPairLevels ξ ms qs negative r p t u)))
    ((parisiCanonicalGroupedPieces p).map f) (List.pairwise_insertionSort _ _)
    (parisiCanonicalGroupedScalar_sorted ξ ms qs hm negative r p t u)
    ((List.perm_insertionSort _ _).trans hp)
  rw [he, parisiCanonicalGroupedScalar_eq_blocks, coleHopfIterateList_merge_blocks hA,
    parisiCanonicalScalarBlocks_merge_eq_full hξ ms qs hq p ht hu]

theorem randomFieldColeHopfListValue_parisiCanonical_sorted_eq {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (μh : Measure ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2))
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) :
    randomFieldColeHopfListValue μh (List.insertionSort parisiLevelMassOrder
      (pairColeHopfScalarLevels (parisiCanonicalPairLevels ξ ms qs negative r p t u))) =
        ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  have he := coleHopfIterateList_parisiCanonical_sorted_eq_full hξ ms qs hm hq negative r p ht hu
    (L := 1) (fun x y => by simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0 x y)
  unfold randomFieldColeHopfListValue
  rw [he]
  exact randomFieldColeHopfListValue_parisiFull_eq μh ξ ms qs

/-- The non-strict canonical one-site comparison has no supplied
variance-regrouping or scalar equality hypothesis. -/
theorem randomFieldPairColeHopfListValue_parisiCanonical_le {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) :
    randomFieldPairColeHopfListValue μh (parisiCanonicalPairLevels ξ ms qs negative r p t u) ≤
      2 * ∫ h, closedParisiX₀ ξ ms qs h ∂μh := by
  have h := randomFieldPairColeHopfListValue_le_sorted_scalar hμ
    (parisiCanonicalPairLevels ξ ms qs negative r p t u)
    (fun q hq' => (parisiCanonicalPairLevels_mass_mem_Icc ξ ms qs hm negative r p t u q hq').1)
  rw [randomFieldColeHopfListValue_parisiCanonical_sorted_eq hξ μh ms qs hm hq negative r p ht hu] at h
  exact h

end SpinGlass
