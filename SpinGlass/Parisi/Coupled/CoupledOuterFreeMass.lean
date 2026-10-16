import SpinGlass.Parisi.Coupled.CoupledMainInnerUniform

/-!
# Free outer mass in the coupled split

The varied scalar mass is halved at the shared outer level. Hence its
admissible upper bound is twice the old matching mass. This includes a
neighborhood above the terminal scalar mass one.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

noncomputable def parisiOuterFreeCoupledMasses {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) (b : ℝ) : Fin (k + 2) → ℝ :=
  Function.update (parisiSplitPhysicalMasses ms p) p.castSucc (b / 2)

theorem parisiLevelMasses_splitParisiMassLeft_apply {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) (b : ℝ) (i : Fin (k + 2)) :
    parisiLevelMasses (splitParisiMassLeft ms p b) i =
      if i.val < p.val then mExt ms (i.val + 1)
      else if i.val = p.val then b else mExt ms i.val := by
  rw [parisiLevelMasses_apply]
  by_cases hi : i.val < p.val
  · rw [ite_eq_left hi, mExt_splitParisiMassLeft_before ms p b (by omega)]
  · rw [ite_eq_right hi]
    by_cases heq : i.val = p.val
    · rw [ite_eq_left heq, heq, mExt_splitParisiMassLeft_inserted]
    · rw [ite_eq_right heq, mExt_splitParisiMassLeft_after ms p b (by omega)]

theorem parisiOuterFreeCoupledMasses_apply {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) (b : ℝ) (i : Fin (k + 2)) :
    parisiOuterFreeCoupledMasses ms p b i =
      if i.val < p.val then mExt ms (i.val + 1) / 2
      else if i.val = p.val then b / 2 else mExt ms i.val := by
  unfold parisiOuterFreeCoupledMasses
  rw [Function.update_apply, parisiSplitPhysicalMasses_apply]
  by_cases hi : i = p.castSucc
  · subst i
    simp only [Fin.val_castSucc, lt_self_iff_false, ite_false, ite_true]
  · have hv : i.val ≠ p.val := fun h => hi (Fin.ext h)
    rw [ite_eq_right hi, ite_eq_right hv]
    by_cases hbefore : i.val < p.val
    · rw [ite_eq_left (by omega), ite_eq_left hbefore]
    · rw [ite_eq_right (by omega), ite_eq_right hbefore]

/-- The concrete physical list is the scalar split list with its
common-prefix masses halved, including the freely varied outer mass. -/
theorem parisiOuterFreeCoupledMasses_eq_halveBelow {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) (b : ℝ) :
    parisiOuterFreeCoupledMasses ms p b =
      halveBelow (p.val + 1) (parisiLevelMasses (splitParisiMassLeft ms p b)) := by
  funext i
  rw [parisiOuterFreeCoupledMasses_apply]
  unfold halveBelow
  rw [parisiLevelMasses_splitParisiMassLeft_apply]
  by_cases hi : i.val < p.val
  · simp only [hi, ite_true, show i.val < p.val + 1 by omega]
  · by_cases heq : i.val = p.val
    · simp [heq]
    · simp only [hi, heq, ite_false, show ¬i.val < p.val + 1 by omega]

theorem parisiOuterFreeCoupledMasses_remove_outer {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) (b : ℝ) :
    p.castSucc.removeNth (parisiOuterFreeCoupledMasses ms p b) =
      halveBelow p.val (parisiLevelMasses ms) := by
  unfold parisiOuterFreeCoupledMasses
  rw [Fin.removeNth_update]
  exact parisiSplitPhysicalMasses_remove_outer ms p

theorem parisiLevelMasses_splitParisiMassLeft_pos {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) (hm : ParisiMAdmissible ms) {b : ℝ} (hb : 0 < b) (i : Fin (k + 2)) :
    0 < parisiLevelMasses (splitParisiMassLeft ms p b) i := by
  rw [parisiLevelMasses_splitParisiMassLeft_apply]
  split_ifs
  · exact hm.mExt_pos (by omega)
  · exact hb
  · exact hm.mExt_pos (by omega)

theorem parisiOuterFreeCoupledMasses_pos {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) (hm : ParisiMAdmissible ms) {b : ℝ} (hb : 0 < b) (i : Fin (k + 2)) :
    0 < parisiOuterFreeCoupledMasses ms p b i := by
  rw [parisiOuterFreeCoupledMasses_eq_halveBelow]
  exact halveBelow_pos (parisiLevelMasses_splitParisiMassLeft_pos ms p hm hb) _ i

/-- Physical masses remain at most one even when the varied scalar
mass exceeds one, up to its actual coupled upper bound two. -/
theorem parisiOuterFreeCoupledMasses_le_one {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) (hm : ParisiMAdmissible ms) {b : ℝ} (hb : b ≤ 2) (i : Fin (k + 2)) :
    parisiOuterFreeCoupledMasses ms p b i ≤ 1 := by
  rw [parisiOuterFreeCoupledMasses_apply]
  split_ifs
  · have hh := mExt_le_one (fun r => (hm.2.2 r).le) (i.val + 1)
    linarith
  · linarith
  · exact mExt_le_one (fun r => (hm.2.2 r).le) _

/-- The exact coupled range allows both signs of mass variation,
including an increase from the terminal matching scalar mass one. -/
theorem parisiOuterFreeCoupledMasses_monotone {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) (hm : ParisiMAdmissible ms) {b : ℝ}
    (hbL : mExt ms p.val ≤ b) (hbR : b ≤ 2 * mExt ms (p.val + 1)) :
    Monotone (parisiOuterFreeCoupledMasses ms p b) := by
  intro i j hij
  have hval : i.val ≤ j.val := hij
  rw [parisiOuterFreeCoupledMasses_apply, parisiOuterFreeCoupledMasses_apply]
  by_cases hi : i.val < p.val
  · rw [ite_eq_left hi]
    by_cases hj : j.val < p.val
    · rw [ite_eq_left hj]
      exact div_le_div_of_nonneg_right (hm.monotone_mExt (by omega)) (by norm_num)
    · rw [ite_eq_right hj]
      by_cases hjeq : j.val = p.val
      · rw [ite_eq_left hjeq]
        exact div_le_div_of_nonneg_right ((hm.monotone_mExt (by omega)).trans hbL) (by norm_num)
      · rw [ite_eq_right hjeq]
        have hn := (hm.mExt_pos (by omega : 0 < i.val + 1)).le
        have hh := hm.monotone_mExt (show i.val + 1 ≤ j.val by omega)
        linarith
  · rw [ite_eq_right hi, ite_eq_right (by omega : ¬j.val < p.val)]
    by_cases hieq : i.val = p.val
    · rw [ite_eq_left hieq]
      by_cases hjeq : j.val = p.val
      · rw [ite_eq_left hjeq]
      · rw [ite_eq_right hjeq]
        have hh := hm.monotone_mExt (show p.val + 1 ≤ j.val by omega)
        linarith
    · rw [ite_eq_right hieq, ite_eq_right (by omega : j.val ≠ p.val)]
      exact hm.monotone_mExt hval

theorem parisiOuterFreeMass_mem_nhds_matching {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) (hm : ParisiMAdmissible ms) :
    Ioo (mExt ms p.val) (2 * mExt ms (p.val + 1)) ∈ nhds (mExt ms (p.val + 1)) := by
  exact Ioo_mem_nhds (sub_pos.1 (hm.mExt_gap_pos p)) (by linarith [hm.mExt_pos (by omega : 0 < p.val + 1)])

end SpinGlass
