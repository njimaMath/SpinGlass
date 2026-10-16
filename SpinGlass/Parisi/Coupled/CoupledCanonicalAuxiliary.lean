import SpinGlass.Parisi.Coupled.CoupledCascadeDeletion
import SpinGlass.Parisi.Coupled.CoupledTerminalNormalization

/-!
# Identifying the physical auxiliary cascade with the original levels

The matching split has one deterministic auxiliary level. Removing it
recovers the original Parisi masses and time-scaled mark variances, with
the common replica prefix at the appropriate endpoint of the old interval.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

theorem parisiSplitSize_eq {k : ℕ} (p : Fin (k + 1)) :
    (p.val + 1) + ((k - p.val) + 1) = k + 2 := by omega

/-- Reindex the split arrays by their actual length k+2. -/
def parisiSplitIndex {k : ℕ} (p : Fin (k + 1)) (i : Fin (k + 2)) :
    Fin ((p.val + 1) + ((k - p.val) + 1)) := Fin.cast (parisiSplitSize_eq p).symm i

@[simp] theorem parisiSplitIndex_val {k : ℕ} (p : Fin (k + 1)) (i : Fin (k + 2)) :
    (parisiSplitIndex p i).val = i.val := rfl

/-- The positive matching split masses at their canonical indices. -/
noncomputable def parisiSplitPhysicalMasses {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1)) :
    Fin (k + 2) → ℝ :=
  fun i => halveBelow (p.val + 1) (parisiResponseSplitMasses ms p) (parisiSplitIndex p i)

theorem parisiSplitPhysicalMasses_apply {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1))
    (i : Fin (k + 2)) :
    parisiSplitPhysicalMasses ms p i =
      if i.val < p.val + 1 then mExt ms (i.val + 1) / 2 else mExt ms i.val := by
  unfold parisiSplitPhysicalMasses halveBelow
  rw [parisiResponseSplitMasses_eq_mExt]
  simp only [parisiSplitIndex_val]
  by_cases hi : i.val < p.val + 1
  · have hi' : i.val ≤ p.val := by omega
    simp only [hi, hi', ite_true]
  · have hi' : ¬i.val ≤ p.val := by omega
    simp only [hi, hi', ite_false]

theorem parisiSplitPhysicalMasses_remove_outer {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) :
    p.castSucc.removeNth (parisiSplitPhysicalMasses ms p) =
      halveBelow p.val (parisiLevelMasses ms) := by
  funext i
  unfold Fin.removeNth
  by_cases hi : i.val < p.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ (show i.castSucc < p.castSucc by exact hi)]
    rw [parisiSplitPhysicalMasses_apply]
    simp only [Fin.val_castSucc, halveBelow, parisiLevelMasses_apply]
    rw [ite_eq_left (by omega), ite_eq_left hi]
  · rw [Fin.succAbove_of_le_castSucc _ _ (show p.castSucc ≤ i.castSucc by exact le_of_not_gt hi)]
    rw [parisiSplitPhysicalMasses_apply]
    simp only [Fin.val_succ, halveBelow, parisiLevelMasses_apply]
    rw [ite_eq_right (by omega), ite_eq_right hi]

theorem parisiSplitPhysicalMasses_remove_inner {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) :
    p.succ.removeNth (parisiSplitPhysicalMasses ms p) =
      halveBelow (p.val + 1) (parisiLevelMasses ms) := by
  funext i
  unfold Fin.removeNth
  by_cases hi : i.val < p.val + 1
  · rw [Fin.succAbove_of_castSucc_lt _ _ (show i.castSucc < p.succ by exact hi)]
    rw [parisiSplitPhysicalMasses_apply]
    simp only [Fin.val_castSucc, halveBelow, parisiLevelMasses_apply]
    rw [ite_eq_left hi, ite_eq_left hi]
  · rw [Fin.succAbove_of_le_castSucc _ _ (show p.succ ≤ i.castSucc by exact le_of_not_gt hi)]
    rw [parisiSplitPhysicalMasses_apply]
    simp only [Fin.val_succ, halveBelow, parisiLevelMasses_apply]
    rw [ite_eq_right (by omega), ite_eq_right hi]

theorem parisiOuterAuxSplitVars_before (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t : ℝ) (i : Fin (k + 2))
    (hi : i.val < p.val) :
    parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i) =
      (1 - t).toNNReal * parisiVar ξ qs (i.val + 1) := by
  let j : Fin p.val := ⟨i.val, hi⟩
  have he : parisiSplitIndex p i = Fin.castAdd ((k - p.val) + 1) j.castSucc := Fin.ext rfl
  rw [he]
  unfold parisiOuterAuxSplitVars
  rw [Fin.append_left, Fin.snoc_castSucc]
  rfl

theorem parisiOuterAuxSplitVars_zero (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t : ℝ) :
    parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p p.castSucc) = 0 := by
  have he : parisiSplitIndex p p.castSucc =
      Fin.castAdd ((k - p.val) + 1) (Fin.last p.val) := Fin.ext rfl
  rw [he]
  unfold parisiOuterAuxSplitVars
  rw [Fin.append_left, Fin.snoc_last]

theorem parisiInnerAuxSplitVars_before (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t : ℝ) (i : Fin (k + 2))
    (hi : i.val < p.val + 1) :
    parisiInnerAuxSplitVars ξ qs p t (parisiSplitIndex p i) =
      (1 - t).toNNReal * parisiVar ξ qs (i.val + 1) := by
  let j : Fin (p.val + 1) := ⟨i.val, hi⟩
  have he : parisiSplitIndex p i = Fin.castAdd ((k - p.val) + 1) j := Fin.ext rfl
  rw [he]
  unfold parisiInnerAuxSplitVars
  rw [Fin.append_left]
  change Fin.snoc (α := fun _ => ℝ≥0)
    (fun r : Fin p.val => (1 - t).toNNReal * parisiVar ξ qs (r.val + 1))
      ((1 - t).toNNReal * parisiVar ξ qs (p.val + 1)) j = _
  have hs (r : Fin (p.val + 1)) :
      Fin.snoc (α := fun _ => ℝ≥0)
        (fun s : Fin p.val => (1 - t).toNNReal * parisiVar ξ qs (s.val + 1))
        ((1 - t).toNNReal * parisiVar ξ qs (p.val + 1)) r =
        (1 - t).toNNReal * parisiVar ξ qs (r.val + 1) := by
    refine Fin.lastCases ?_ (fun s => ?_) r
    · simp only [Fin.snoc_last, Fin.val_last]
    · simp only [Fin.snoc_castSucc, Fin.val_castSucc]
  exact hs j

theorem parisiInnerAuxSplitVars_zero (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t : ℝ) :
    parisiInnerAuxSplitVars ξ qs p t (parisiSplitIndex p p.succ) = 0 := by
  have he : parisiSplitIndex p p.succ =
      Fin.natAdd (p.val + 1) (0 : Fin ((k - p.val) + 1)) := Fin.ext (by simp)
  rw [he]
  unfold parisiInnerAuxSplitVars
  rw [Fin.append_right, Fin.cons_zero]

theorem parisiOuterAuxSplitVars_remove_zero (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t : ℝ) :
    p.castSucc.removeNth (fun i => parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i)) =
      fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i := by
  funext i
  unfold Fin.removeNth
  dsimp only
  by_cases hi : i.val < p.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ (show i.castSucc < p.castSucc by exact hi),
      parisiOuterAuxSplitVars_before ξ qs p t i.castSucc hi]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (show p.castSucc ≤ i.castSucc by exact le_of_not_gt hi)]
    let j : Fin ((k - p.val) + 1) := ⟨i.val - p.val, by omega⟩
    have he : parisiSplitIndex p i.succ = Fin.natAdd (p.val + 1) j := by
      apply Fin.ext
      simp only [parisiSplitIndex_val, Fin.val_succ, Fin.val_natAdd, j]
      omega
    rw [he, parisiOuterAuxSplitVars_natAdd]
    congr 1
    change parisiVar ξ qs (p.val + (i.val - p.val) + 1) = parisiVar ξ qs (i.val + 1)
    congr 1
    omega

theorem parisiInnerAuxSplitVars_remove_zero (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t : ℝ) :
    p.succ.removeNth (fun i => parisiInnerAuxSplitVars ξ qs p t (parisiSplitIndex p i)) =
      fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i := by
  funext i
  unfold Fin.removeNth
  dsimp only
  by_cases hi : i.val < p.val + 1
  · rw [Fin.succAbove_of_castSucc_lt _ _ (show i.castSucc < p.succ by exact hi),
      parisiInnerAuxSplitVars_before ξ qs p t i.castSucc hi]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (show p.succ ≤ i.castSucc by exact le_of_not_gt hi)]
    let j : Fin (k - p.val) := ⟨i.val - p.val - 1, by omega⟩
    have he : parisiSplitIndex p i.succ = Fin.natAdd (p.val + 1) j.succ := by
      apply Fin.ext
      simp only [parisiSplitIndex_val, Fin.val_succ, Fin.val_natAdd, j]
      omega
    rw [he]
    unfold parisiInnerAuxSplitVars
    rw [Fin.append_right, Fin.cons_succ]
    congr 1
    change parisiVar ξ qs (p.val + (i.val - p.val - 1) + 2) = parisiVar ξ qs (i.val + 1)
    congr 1
    omega

theorem parisiSplitFactors_remove_outer {k : ℕ} (p : Fin (k + 1)) :
    p.castSucc.removeNth (fun i : Fin (k + 2) => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) =
      fun i => couplingFactorSgn 1 (p.val + 1) (i.val + 1) := by
  funext i
  unfold Fin.removeNth
  dsimp only
  by_cases hi : i.val < p.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ (show i.castSucc < p.castSucc by exact hi)]
    simp only [Fin.val_castSucc, couplingFactorSgn]
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  · rw [Fin.succAbove_of_le_castSucc _ _ (show p.castSucc ≤ i.castSucc by exact le_of_not_gt hi)]
    simp only [Fin.val_succ, couplingFactorSgn]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem parisiSplitFactors_remove_inner {k : ℕ} (p : Fin (k + 1)) :
    p.succ.removeNth (fun i : Fin (k + 2) => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) =
      fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1) := by
  funext i
  unfold Fin.removeNth
  dsimp only
  by_cases hi : i.val < p.val + 1
  · rw [Fin.succAbove_of_castSucc_lt _ _ (show i.castSucc < p.succ by exact hi)]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (show p.succ ≤ i.castSucc by exact le_of_not_gt hi)]
    simp only [Fin.val_succ, couplingFactorSgn]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- A dimension equality transports the full paired Gaussian cascade,
including its masses, laws and branch factors. -/
theorem cascadeRec_pairHamG_cast {N n m : ℕ} {J : Type*} [Fintype J] (h : n = m)
    (ns : Fin n → ℝ) (vs : Fin n → ℝ≥0) (c : (Fin 2 → Config N) → ℝ)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin n → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    cascadeRec n ns (siteGaussianMarks (Fin N × J) n vs)
        (pairHamG N n c H lam a K₀ K z₀) =
      cascadeRec m (fun i => ns (Fin.cast h.symm i))
        (siteGaussianMarks (Fin N × J) m (fun i => vs (Fin.cast h.symm i)))
        (pairHamG N m c H lam a K₀ (fun i => K (Fin.cast h.symm i)) z₀) := by
  subst m
  rfl

/-- The outer physical split recovers the original Gaussian cascade
with a common prefix below the left endpoint, including k=0 and p=k. -/
theorem cascadeRec_parisi_outer_aux_eq {N k : ℕ} (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t : ℝ)
    (hm : ParisiMAdmissible ms) (c : (Fin 2 → Config N) → ℝ)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (z₀ : Fin N × Fin 2 → ℝ) :
    cascadeRec ((p.val + 1) + ((k - p.val) + 1))
        (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p))
        (siteGaussianMarks (Fin N × Fin 2) _ (parisiOuterAuxSplitVars ξ qs p t))
        (pairHamG N _ c H lam a (couplingFactorSgn 1 (p.val + 2) 0)
          (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) z₀) =
      cascadeRec (k + 1) (halveBelow p.val (parisiLevelMasses ms))
        (siteGaussianMarks (Fin N × Fin 2) _ (fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i))
        (pairHamG N _ c H lam a (couplingFactorSgn 1 (p.val + 1) 0)
          (fun i => couplingFactorSgn 1 (p.val + 1) (i.val + 1)) z₀) := by
  rw [cascadeRec_pairHamG_cast (parisiSplitSize_eq p)]
  change cascadeRec (k + 2) (parisiSplitPhysicalMasses ms p)
    (siteGaussianMarks (Fin N × Fin 2) _ (fun i => parisiOuterAuxSplitVars ξ qs p t (parisiSplitIndex p i)))
    (pairHamG N _ c H lam a (couplingFactorSgn 1 (p.val + 2) 0)
      (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) z₀) = _
  have hmass : parisiSplitPhysicalMasses ms p p.castSucc ≠ 0 :=
    (halveBelow_pos (parisiResponseSplitMasses_pos ms p hm) _ (parisiSplitIndex p p.castSucc)).ne'
  rw [cascadeRec_pairHamG_remove_zero_eq _ _ p.castSucc hmass
    (parisiOuterAuxSplitVars_zero ξ qs p t), parisiSplitPhysicalMasses_remove_outer,
    parisiOuterAuxSplitVars_remove_zero, parisiSplitFactors_remove_outer]
  have hroot : couplingFactorSgn 1 (p.val + 2) 0 = couplingFactorSgn 1 (p.val + 1) 0 := by
    simp only [couplingFactorSgn, ite_eq_left (by omega : 0 < p.val + 2),
      ite_eq_left (by omega : 0 < p.val + 1)]
  rw [hroot]

/-- The inner physical split recovers the original Gaussian cascade
with the common prefix below the right endpoint of the old interval. -/
theorem cascadeRec_parisi_inner_aux_eq {N k : ℕ} (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t : ℝ)
    (hm : ParisiMAdmissible ms) (c : (Fin 2 → Config N) → ℝ)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (z₀ : Fin N × Fin 2 → ℝ) :
    cascadeRec ((p.val + 1) + ((k - p.val) + 1))
        (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p))
        (siteGaussianMarks (Fin N × Fin 2) _ (parisiInnerAuxSplitVars ξ qs p t))
        (pairHamG N _ c H lam a (couplingFactorSgn 1 (p.val + 2) 0)
          (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) z₀) =
      cascadeRec (k + 1) (halveBelow (p.val + 1) (parisiLevelMasses ms))
        (siteGaussianMarks (Fin N × Fin 2) _ (fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i))
        (pairHamG N _ c H lam a (couplingFactorSgn 1 (p.val + 2) 0)
          (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) z₀) := by
  rw [cascadeRec_pairHamG_cast (parisiSplitSize_eq p)]
  change cascadeRec (k + 2) (parisiSplitPhysicalMasses ms p)
    (siteGaussianMarks (Fin N × Fin 2) _ (fun i => parisiInnerAuxSplitVars ξ qs p t (parisiSplitIndex p i)))
    (pairHamG N _ c H lam a (couplingFactorSgn 1 (p.val + 2) 0)
      (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) z₀) = _
  have hmass : parisiSplitPhysicalMasses ms p p.succ ≠ 0 :=
    (halveBelow_pos (parisiResponseSplitMasses_pos ms p hm) _ (parisiSplitIndex p p.succ)).ne'
  rw [cascadeRec_pairHamG_remove_zero_eq _ _ p.succ hmass
    (parisiInnerAuxSplitVars_zero ξ qs p t), parisiSplitPhysicalMasses_remove_inner,
    parisiInnerAuxSplitVars_remove_zero, parisiSplitFactors_remove_inner]

end SpinGlass
