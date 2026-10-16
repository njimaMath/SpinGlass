import SpinGlass.Parisi.Coupled.CoupledMainRootSigned

/-!
# Free inner mass in the coupled split

The one-copy split retains the old outer mass and gives the inner piece
the free mass b. Halving the common-prefix masses makes a small decrease
from the matching mass admissible for the actual coupled recursion.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The free inner coordinate in the canonical split dimension. -/
def parisiInnerFreeMassIndex {k : ℕ} (p : Fin k) : Fin (k + 2) := p.castSucc.succ

/-- The actual positive-level coupled masses. The scalar recursion
need not have a monotone mass list when the free inner mass is decreased. -/
noncomputable def parisiInnerFreeCoupledMasses {k : ℕ} (ms : Fin k → ℝ) (p : Fin k) (b : ℝ) :
    Fin (k + 2) → ℝ :=
  halveBelow (p.val + 1) (parisiLevelMasses (splitParisiMassRight ms p b))

theorem parisiLevelMasses_splitParisiMassRight_apply {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin k) (b : ℝ) (i : Fin (k + 2)) :
    parisiLevelMasses (splitParisiMassRight ms p b) i =
      if i.val ≤ p.val then mExt ms (i.val + 1)
      else if i.val = p.val + 1 then b else mExt ms i.val := by
  rw [parisiLevelMasses_apply]
  by_cases hi : i.val ≤ p.val
  · rw [ite_eq_left hi, mExt_splitParisiMassRight_before ms p b (by omega)]
  · rw [ite_eq_right hi]
    by_cases heq : i.val = p.val + 1
    · rw [ite_eq_left heq, heq, show p.val + 1 + 1 = p.val + 2 by omega,
        mExt_splitParisiMassRight_inserted]
    · rw [ite_eq_right heq, mExt_splitParisiMassRight_after ms p b (by omega)]

theorem parisiInnerFreeCoupledMasses_apply {k : ℕ} (ms : Fin k → ℝ) (p : Fin k)
    (b : ℝ) (i : Fin (k + 2)) :
    parisiInnerFreeCoupledMasses ms p b i =
      if i.val < p.val + 1 then mExt ms (i.val + 1) / 2
      else if i.val = p.val + 1 then b else mExt ms i.val := by
  unfold parisiInnerFreeCoupledMasses halveBelow
  rw [parisiLevelMasses_splitParisiMassRight_apply]
  by_cases hi : i.val < p.val + 1
  · simp only [hi, ite_true, show i.val ≤ p.val by omega]
  · simp only [hi, ite_false, show ¬i.val ≤ p.val by omega]

/-- Only the inner deterministic auxiliary coordinate changes when
the inserted mass varies. -/
theorem parisiInnerFreeCoupledMasses_eq_update {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin k) (b : ℝ) :
    parisiInnerFreeCoupledMasses ms p b =
      Function.update (parisiSplitPhysicalMasses ms p.castSucc) (parisiInnerFreeMassIndex p) b := by
  funext i
  rw [parisiInnerFreeCoupledMasses_apply, Function.update_apply]
  by_cases hi : i = parisiInnerFreeMassIndex p
  · subst i
    simp [parisiInnerFreeMassIndex]
  · have hv : i.val ≠ p.val + 1 := fun h => hi (Fin.ext h)
    rw [ite_eq_right hi, parisiSplitPhysicalMasses_apply]
    simp only [Fin.val_castSucc, hv, ite_false]

/-- Deleting the zero-variance inner level recovers the original
coupled masses for every free mass. -/
theorem parisiInnerFreeCoupledMasses_remove_inner {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin k) (b : ℝ) :
    (parisiInnerFreeMassIndex p).removeNth (parisiInnerFreeCoupledMasses ms p b) =
      halveBelow (p.val + 1) (parisiLevelMasses ms) := by
  rw [parisiInnerFreeCoupledMasses_eq_update, Fin.removeNth_update]
  exact parisiSplitPhysicalMasses_remove_inner ms p.castSucc

theorem parisiLevelMasses_splitParisiMassRight_pos {k : ℕ} (ms : Fin k → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) {b : ℝ} (hb : 0 < b) (i : Fin (k + 2)) :
    0 < parisiLevelMasses (splitParisiMassRight ms p b) i := by
  rw [parisiLevelMasses_splitParisiMassRight_apply]
  split_ifs
  · exact hm.mExt_pos (by omega)
  · exact hb
  · exact hm.mExt_pos (by omega)

theorem parisiLevelMasses_splitParisiMassRight_le_one {k : ℕ} (ms : Fin k → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) {b : ℝ} (hb : b ≤ 1) (i : Fin (k + 2)) :
    parisiLevelMasses (splitParisiMassRight ms p b) i ≤ 1 := by
  rw [parisiLevelMasses_splitParisiMassRight_apply]
  split_ifs
  · exact mExt_le_one (fun r => (hm.2.2 r).le) _
  · exact hb
  · exact mExt_le_one (fun r => (hm.2.2 r).le) _

theorem parisiInnerFreeCoupledMasses_pos {k : ℕ} (ms : Fin k → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) {b : ℝ} (hb : 0 < b) (i : Fin (k + 2)) :
    0 < parisiInnerFreeCoupledMasses ms p b i :=
  halveBelow_pos (parisiLevelMasses_splitParisiMassRight_pos ms p hm hb) _ i

theorem parisiInnerFreeCoupledMasses_le_one {k : ℕ} (ms : Fin k → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) {b : ℝ} (hb : b ≤ 1) (i : Fin (k + 2)) :
    parisiInnerFreeCoupledMasses ms p b i ≤ 1 :=
  halveBelow_le_one (parisiLevelMasses_splitParisiMassRight_le_one ms p hm hb) _ i

/-- The free coupled mass may lie below the old matching mass. Its
precise lower bound is the last common-prefix mass, one half of that old mass. -/
theorem parisiInnerFreeCoupledMasses_monotone {k : ℕ} (ms : Fin k → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) {b : ℝ}
    (hbL : ms p / 2 ≤ b) (hbR : b ≤ mExt ms (p.val + 2)) :
    Monotone (parisiInnerFreeCoupledMasses ms p b) := by
  intro i j hij
  have hval : i.val ≤ j.val := hij
  rw [parisiInnerFreeCoupledMasses_apply, parisiInnerFreeCoupledMasses_apply]
  by_cases hi : i.val < p.val + 1
  · rw [ite_eq_left hi]
    by_cases hj : j.val < p.val + 1
    · rw [ite_eq_left hj]
      exact div_le_div_of_nonneg_right (hm.monotone_mExt (by omega)) (by norm_num)
    · rw [ite_eq_right hj]
      by_cases hjeq : j.val = p.val + 1
      · rw [ite_eq_left hjeq]
        have hh := div_le_div_of_nonneg_right
          (hm.monotone_mExt (show i.val + 1 ≤ p.val + 1 by omega)) (by norm_num : (0 : ℝ) ≤ 2)
        rw [mExt_val_succ ms p] at hh
        exact hh.trans hbL
      · rw [ite_eq_right hjeq]
        have hn := (hm.mExt_pos (by omega : 0 < i.val + 1)).le
        have hh := hm.monotone_mExt (show i.val + 1 ≤ j.val by omega)
        linarith
  · rw [ite_eq_right hi]
    have hj : ¬j.val < p.val + 1 := by omega
    rw [ite_eq_right hj]
    by_cases hieq : i.val = p.val + 1
    · rw [ite_eq_left hieq]
      by_cases hjeq : j.val = p.val + 1
      · rw [ite_eq_left hjeq]
      · rw [ite_eq_right hjeq]
        exact hbR.trans (hm.monotone_mExt (by omega))
    · rw [ite_eq_right hieq, ite_eq_right (by omega : j.val ≠ p.val + 1)]
      exact hm.monotone_mExt hval

/-- The coupled admissible interval contains a neighborhood of the
matching mass, so either sign of a mass derivative can give a strict gain. -/
theorem parisiInnerFreeMass_mem_nhds_matching {k : ℕ} (ms : Fin k → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) :
    Ioo (ms p / 2) (mExt ms (p.val + 2)) ∈ nhds (ms p) := by
  have hl : ms p / 2 < ms p := by linarith [hm.2.1 p]
  have hr : ms p < mExt ms (p.val + 2) := by
    have hh := hm.mExt_gap_pos p.succ
    simp only [Fin.val_succ, mExt_val_succ ms p, show p.val + 1 + 1 = p.val + 2 by omega] at hh
    exact sub_pos.1 hh
  exact Ioo_mem_nhds hl hr

end SpinGlass
