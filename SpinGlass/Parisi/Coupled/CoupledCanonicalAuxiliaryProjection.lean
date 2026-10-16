import SpinGlass.Parisi.Coupled.CoupledCanonicalGaussianColumns

/-!
# Exact auxiliary source inside the compressed canonical list

The zero-mass root contains exactly the original auxiliary root mark.
Filtering the positive suffix preserves the original auxiliary order,
including the terminal mass-one mark. These are the deletion indices
for the physical endpoint in (14.363).
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

def ParisiCanonicalPiece.isAuxiliary {k : ℕ} : ParisiCanonicalPiece k → Bool
  | .auxiliary _ => true
  | _ => false

theorem parisiCanonicalAuxiliaryPieces_filter_auxiliary (k : ℕ) :
    (parisiCanonicalAuxiliaryPieces k).filter ParisiCanonicalPiece.isAuxiliary =
      parisiCanonicalAuxiliaryPieces k := by
  apply List.filter_eq_self.2
  intro e he
  obtain ⟨i, _hi, rfl⟩ := List.mem_map.1 he
  rfl

theorem parisiCanonicalDrivenPieces_filter_auxiliary {k : ℕ} (p : Fin (k + 2)) :
    (parisiCanonicalDrivenPieces p).filter ParisiCanonicalPiece.isAuxiliary = [] := by
  apply List.filter_eq_nil_iff.2
  intro e he
  obtain ⟨i, _hi, he⟩ := List.mem_flatMap.1 he
  by_cases hi : i = p
  · simp only [parisiCanonicalDrivenBlock, hi, ite_true, List.mem_cons,
      List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp [ParisiCanonicalPiece.isAuxiliary]
  · simp only [parisiCanonicalDrivenBlock, hi, ite_false, List.mem_singleton] at he
    subst e
    simp [ParisiCanonicalPiece.isAuxiliary]

/-- The physical merge retains the complete auxiliary source in order. -/
theorem parisiCanonicalMergedPieces_filter_auxiliary {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    (parisiCanonicalMergedPieces ms r p).filter ParisiCanonicalPiece.isAuxiliary =
      parisiCanonicalAuxiliaryPieces k := by
  have hs := (parisiCanonicalAuxiliaryPieces_sublist_merged ms hm r p).filter
    ParisiCanonicalPiece.isAuxiliary
  rw [parisiCanonicalAuxiliaryPieces_filter_auxiliary] at hs
  have hp := (parisiCanonicalMergedPieces_perm ms r p).filter
    ParisiCanonicalPiece.isAuxiliary
  rw [List.filter_append, parisiCanonicalAuxiliaryPieces_filter_auxiliary,
    parisiCanonicalDrivenPieces_filter_auxiliary, List.append_nil] at hp
  exact (hs.eq_of_length hp.length_eq.symm).symm

theorem ParisiCanonicalPiece.physicalMass_eq_zero_iff {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (e : ParisiCanonicalPiece k) :
    e.physicalMass ms r p = 0 ↔ (e.oldLevel p).val = 0 := by
  constructor
  · intro hz
    by_contra hn
    exact (e.physicalMass_pos_of_oldLevel_pos ms hm r p (by omega)).ne' hz
  · intro hz
    simp [physicalMass, hz]

theorem parisiCanonicalAuxiliaryPieces_nodup (k : ℕ) :
    (parisiCanonicalAuxiliaryPieces k).Nodup := by
  simp only [parisiCanonicalAuxiliaryPieces, parisiCanonicalIndices, List.map_ofFn]
  exact List.nodup_ofFn_ofInjective (fun _ _ h => ParisiCanonicalPiece.auxiliary.inj h)

/-- The entire zero-mass root prefix has one surviving auxiliary mark,
even if the driven root was split into two zero-mass expectations. -/
theorem parisiCanonicalRootPieces_filter_auxiliary {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    (parisiCanonicalRootPieces ms r p).filter ParisiCanonicalPiece.isAuxiliary =
      [.auxiliary 0] := by
  have hs : ((parisiCanonicalRootPieces ms r p).filter
      ParisiCanonicalPiece.isAuxiliary).Sublist (parisiCanonicalAuxiliaryPieces k) := by
    rw [← parisiCanonicalMergedPieces_filter_auxiliary ms hm r p]
    exact (List.takeWhile_sublist _).filter _
  have hn := (parisiCanonicalAuxiliaryPieces_nodup k).sublist hs
  have hmroot : (ParisiCanonicalPiece.auxiliary 0 : ParisiCanonicalPiece k) ∈
      (parisiCanonicalRootPieces ms r p).filter ParisiCanonicalPiece.isAuxiliary := by
    obtain ⟨tail, htail⟩ := parisiCanonicalMergedPieces_root_prefix ms hm r p
    simp [parisiCanonicalRootPieces, htail, parisiCanonicalAuxiliaryRoot_mass_zero,
      ParisiCanonicalPiece.isAuxiliary]
  have hall : ∀ e ∈ (parisiCanonicalRootPieces ms r p).filter
      ParisiCanonicalPiece.isAuxiliary, e = .auxiliary 0 := by
    intro e he
    obtain ⟨he, ha⟩ := List.mem_filter.1 he
    have hz := (e.physicalMass_eq_zero_iff ms hm r p).1
      (parisiCanonicalRootPieces_mass_zero ms r p e he)
    cases e with
    | auxiliary i =>
      have hi : i = 0 := Fin.ext hz
      simp [hi]
    | driven i => simp [ParisiCanonicalPiece.isAuxiliary] at ha
    | splitRight => simp [ParisiCanonicalPiece.isAuxiliary] at ha
  cases hl : (parisiCanonicalRootPieces ms r p).filter
      ParisiCanonicalPiece.isAuxiliary with
  | nil => simp [hl] at hmroot
  | cons e l =>
    have he : e = .auxiliary 0 := hall e (by simp [hl])
    have hn' := List.nodup_cons.1 (hl ▸ hn)
    have hnil : l = [] := List.eq_nil_iff_forall_not_mem.2 (by
      intro a ha
      have ha' := hall a (by simp [hl, ha])
      exact hn'.1 (by simpa [he, ha'] using ha))
    simp [he, hnil]

/-- Deleting the driven marks from the positive suffix gives exactly
the old positive auxiliary levels, retaining the final mass one. -/
theorem parisiCanonicalPositivePieces_filter_auxiliary {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    (parisiCanonicalPositivePieces ms r p).filter ParisiCanonicalPiece.isAuxiliary =
      List.ofFn (fun i : Fin (k + 1) => .auxiliary i.succ) := by
  have hs := parisiCanonicalMergedPieces_filter_auxiliary ms hm r p
  rw [← parisiCanonicalRoot_append_positive, List.filter_append,
    parisiCanonicalRootPieces_filter_auxiliary ms hm r p] at hs
  have haux : parisiCanonicalAuxiliaryPieces k = .auxiliary 0 ::
      List.ofFn (fun i : Fin (k + 1) => .auxiliary i.succ) := by
    simp [parisiCanonicalAuxiliaryPieces, parisiCanonicalIndices, List.map_ofFn,
      List.ofFn_succ, Function.comp_def]
  rw [haux] at hs
  exact List.cons.inj hs |>.2

/-- The first aggregate root coordinate is the original auxiliary root. -/
theorem parisiCanonicalRootPieces_auxiliary_prefix {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2)) :
    ∃ tail, parisiCanonicalRootPieces ms r p = .auxiliary 0 :: tail := by
  obtain ⟨tail, htail⟩ := parisiCanonicalMergedPieces_root_prefix ms hm r p
  refine ⟨(.driven 0 :: tail).takeWhile (parisiCanonicalRootTest ms r p), ?_⟩
  simp [parisiCanonicalRootPieces, htail, parisiCanonicalAuxiliaryRoot_mass_zero]

/-- Only coordinate zero in the aggregate root can carry auxiliary noise. -/
theorem parisiCanonicalRootPieces_isAuxiliary_iff {k : ℕ}
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (r : Fin (k + 1)) (p : Fin (k + 2))
    (i : Fin (parisiCanonicalRootPieces ms r p).length) :
    ((parisiCanonicalRootPieces ms r p)[i.val]).isAuxiliary = true ↔ i.val = 0 := by
  obtain ⟨tail, htail⟩ := parisiCanonicalRootPieces_auxiliary_prefix ms hm r p
  have hf : tail.filter ParisiCanonicalPiece.isAuxiliary = [] := by
    have hs := parisiCanonicalRootPieces_filter_auxiliary ms hm r p
    rw [htail] at hs
    change .auxiliary 0 :: tail.filter ParisiCanonicalPiece.isAuxiliary = [.auxiliary 0] at hs
    exact List.cons.inj hs |>.2
  by_cases hi : i.val = 0
  · simp [htail, hi, ParisiCanonicalPiece.isAuxiliary]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hi
    have hnlt : n < tail.length := by
      have hil := i.isLt
      have hlen := congrArg List.length htail
      simp only [List.length_cons] at hlen
      omega
    have heq : (parisiCanonicalRootPieces ms r p)[i.val] = tail[n] := by
      simp [htail, hn]
    have hnot := List.filter_eq_nil_iff.1 hf (tail[n]) (List.getElem_mem hnlt)
    simp [heq, hi, hnot]

theorem ParisiCanonicalPiece.auxiliaryVariance_eq_zero_of_not_auxiliary {k : ℕ}
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 2)) (t u : ℝ)
    (e : ParisiCanonicalPiece k) (he : e.isAuxiliary = false) :
    e.auxiliaryVariance ξ qs p t u = 0 := by
  cases e <;> simp [isAuxiliary, auxiliaryVariance, isDriven] at he ⊢

/-- Auxiliary masses after filtering are the original halved-prefix masses. -/
theorem parisiCanonicalAuxiliary_positive_mass {k : ℕ}
    (ms : Fin k → ℝ) (r : Fin (k + 1)) (p : Fin (k + 2)) (i : Fin (k + 1)) :
    (ParisiCanonicalPiece.auxiliary i.succ).physicalMass ms r p =
      halveBelow r.val (parisiLevelMasses ms) i := by
  simp only [ParisiCanonicalPiece.physicalMass, ParisiCanonicalPiece.shared,
    ParisiCanonicalPiece.oldLevel, Fin.val_succ, decide_eq_true_eq,
    halveBelow, parisiLevelMasses_apply]
  simp only [Nat.add_lt_add_iff_right]

theorem parisiCanonicalAuxiliary_gaussianFactor {k : ℕ} (negative : Bool)
    (r : Fin (k + 1)) (p i : Fin (k + 2)) :
    (ParisiCanonicalPiece.auxiliary i).gaussianFactor negative r p =
      couplingFactorSgn 1 (r.val + 1) i.val := by
  unfold ParisiCanonicalPiece.gaussianFactor ParisiCanonicalPiece.kind
  simp only [ParisiCanonicalPiece.shared, decide_eq_true_eq]
  split_ifs with hi
  · simp [couplingFactorSgn, hi]
  · simp [couplingFactorSgn, hi]

end SpinGlass
