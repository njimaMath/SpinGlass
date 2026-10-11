import SpinGlass.Parisi.Minimizer.Full
import SpinGlass.Parisi.Variational.ParisiMassRecursion

/-!
# Inserting an overlap level for mass variations

The inserted overlap lies between `qExt qs (p.val + 1)` and
`qExt qs (p.val + 2)`. In the left split the inserted mass controls the left
subinterval; in the mirror split it controls the right subinterval. The mirror
split applies to nonterminal intervals, whose old mass has an array coordinate.
-/

open MeasureTheory ProbabilityTheory

namespace SpinGlass

/-- Insert a free mass immediately before the mass of interval `p`. -/
def splitParisiMassLeft {k : ℕ} (ms : Fin k → ℝ) (p : Fin (k + 1))
    (m : ℝ) : Fin (k + 1) → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) p m ms

/-- Insert a new overlap immediately after the left endpoint of interval `p`. -/
def splitParisiOverlap {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (p : Fin (k + 1)) (u : ℝ) : Fin (k + 2) → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) p.succ u qs

@[simp] theorem erase_splitParisiMassLeft {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) (m : ℝ) :
    eraseParisiMass (splitParisiMassLeft ms p m) p = ms := by
  funext i
  change Fin.insertNth (α := fun _ => ℝ) p m ms (p.succAbove i) = ms i
  exact Fin.insertNth_apply_succAbove _ _ _ _

@[simp] theorem erase_splitParisiOverlap {k : ℕ} (qs : Fin (k + 1) → ℝ)
    (p : Fin (k + 1)) (u : ℝ) :
    eraseParisiOverlap (splitParisiOverlap qs p u) p = qs := by
  funext i
  change Fin.insertNth (α := fun _ => ℝ) p.succ u qs (p.succ.succAbove i) = qs i
  exact Fin.insertNth_apply_succAbove _ _ _ _

/-- At the left endpoint, the inserted Gaussian interval has zero variance. -/
theorem splitParisiOverlap_left_adjacent_eq {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) :
    splitParisiOverlap qs p (qs p) p.castSucc =
      splitParisiOverlap qs p (qs p) p.succ := by
  unfold splitParisiOverlap
  rw [← Fin.succAbove_succ_self p, Fin.insertNth_apply_succAbove,
    Fin.insertNth_apply_same]

/-- Updating the inserted coordinate gives the split at any other overlap. -/
theorem splitParisiOverlap_eq_qUpdate_left {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (u : ℝ) :
    splitParisiOverlap qs p u =
      qUpdate (splitParisiOverlap qs p (qs p)) p.succ u := by
  funext i
  by_cases hi : i = p.succ
  · subst i
    simp only [splitParisiOverlap, Fin.insertNth_apply_same, qUpdate_self]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    simp only [splitParisiOverlap, Fin.insertNth_apply_succAbove]
    have hne : p.succ.succAbove j ≠ p.succ := Fin.succAbove_ne p.succ j
    rw [qUpdate_of_ne _ _ hne, Fin.insertNth_apply_succAbove]

/-- Splitting at the left endpoint preserves the closed functional for every
inserted mass. -/
theorem closedRandomFieldParisiFunctional_split_left_endpoint
    (μh : Measure ℝ) {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (p : Fin (k + 1)) (m : ℝ) :
    closedRandomFieldParisiFunctional μh ξ
      (splitParisiMassLeft ms p m) (splitParisiOverlap qs p (qs p)) =
        closedRandomFieldParisiFunctional μh ξ ms qs := by
  have h := closedRandomFieldParisiFunctional_erase_adjacent_eq
    μh (ξ := ξ) (splitParisiMassLeft ms p m) (splitParisiOverlap qs p (qs p))
      p (splitParisiOverlap_left_adjacent_eq qs p)
  simpa only [erase_splitParisiMassLeft, erase_splitParisiOverlap] using h.symm

/-- If the two masses on either side of the new overlap agree, moving that
overlap within its neighboring interval leaves the functional unchanged. -/
theorem closedRandomFieldParisiFunctional_split_eq_of_equal_mass
    (μh : Measure ℝ) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hq : qs ∈ parisiOverlapDomain k) (p : Fin (k + 1))
    (m u : ℝ)
    (hm : mExt (splitParisiMassLeft ms p m) p.succ.val =
      mExt (splitParisiMassLeft ms p m) (p.succ.val + 1))
    (hu : qExt (splitParisiOverlap qs p (qs p)) p.succ.val ≤ u ∧
      u ≤ qExt (splitParisiOverlap qs p (qs p)) (p.succ.val + 2)) :
    closedRandomFieldParisiFunctional μh ξ
      (splitParisiMassLeft ms p m) (splitParisiOverlap qs p u) =
        closedRandomFieldParisiFunctional μh ξ ms qs := by
  rw [splitParisiOverlap_eq_qUpdate_left]
  have hbase : splitParisiOverlap qs p (qs p) ∈
      parisiOverlapDomain (k + 1) := by
    change repeatParisiOverlap qs p ∈ parisiOverlapDomain (k + 1)
    exact repeatParisiOverlap_mem_domain hq p
  exact (closedRandomFieldParisiFunctional_qUpdate_eq_of_equal_mass
    μh hξ (splitParisiMassLeft ms p m) (splitParisiOverlap qs p (qs p))
      hbase p.succ u hm hu).trans
        (closedRandomFieldParisiFunctional_split_left_endpoint μh ms qs p m)

/-- Inserting the mass of the unsplit interval makes the two masses adjacent to
the new overlap equal. The terminal interval uses the endpoint mass `1`. -/
theorem splitParisiMassLeft_matching_mass {k : ℕ}
    (ms : Fin k → ℝ) (p : Fin (k + 1)) :
    mExt (splitParisiMassLeft ms p (mExt ms (p.val + 1))) p.succ.val =
      mExt (splitParisiMassLeft ms p (mExt ms (p.val + 1))) (p.succ.val + 1) := by
  let ms' := splitParisiMassLeft ms p (mExt ms (p.val + 1))
  have h := mExt_eraseParisiMass ms' p (p.val + 1)
  have he : eraseParisiMass ms' p = ms :=
    erase_splitParisiMassLeft ms p (mExt ms (p.val + 1))
  rw [he, ite_eq_right (by omega : ¬p.val + 1 ≤ p.val)] at h
  rw [show p.succ.val = p.val + 1 from rfl, mExt_val_succ ms' p]
  change ms' p = mExt ms' (p.val + 2)
  have hp : ms' p = mExt ms (p.val + 1) := by
    change Fin.insertNth (α := fun _ => ℝ) p (mExt ms (p.val + 1)) ms p = _
    exact Fin.insertNth_apply_same _ _ _
  rw [hp]
  exact h

/-- The neighboring overlap bounds of the split are exactly those of the
original interval. -/
theorem splitParisiOverlap_neighbor_bounds {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) :
    qExt (splitParisiOverlap qs p (qs p)) p.succ.val = qExt qs (p.val + 1) ∧
    qExt (splitParisiOverlap qs p (qs p)) (p.succ.val + 2) =
      qExt qs (p.val + 2) := by
  let qs' := splitParisiOverlap qs p (qs p)
  have hleft := qExt_eraseParisiOverlap qs' p (p.val + 1)
  have hright := qExt_eraseParisiOverlap qs' p (p.val + 2)
  have he : eraseParisiOverlap qs' p = qs :=
    erase_splitParisiOverlap qs p (qs p)
  rw [he, ite_eq_left (by omega : p.val + 1 ≤ p.val + 1)] at hleft
  rw [he, ite_eq_right (by omega : ¬p.val + 2 ≤ p.val + 1)] at hright
  exact ⟨by simpa only [Fin.val_succ] using hleft.symm,
    by simpa only [Fin.val_succ] using hright.symm⟩

/-- The mass-matched split has exactly the original value for every overlap
inside the interval being split. -/
theorem closedRandomFieldParisiFunctional_split_matching_mass
    (μh : Measure ℝ) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hq : qs ∈ parisiOverlapDomain k) (p : Fin (k + 1)) (u : ℝ)
    (hu : qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2)) :
    closedRandomFieldParisiFunctional μh ξ
      (splitParisiMassLeft ms p (mExt ms (p.val + 1)))
      (splitParisiOverlap qs p u) =
        closedRandomFieldParisiFunctional μh ξ ms qs := by
  apply closedRandomFieldParisiFunctional_split_eq_of_equal_mass
    μh hξ ms qs hq p (mExt ms (p.val + 1)) u
    (splitParisiMassLeft_matching_mass ms p)
  rw [(splitParisiOverlap_neighbor_bounds qs p).1,
    (splitParisiOverlap_neighbor_bounds qs p).2]
  exact hu

/-- At the right endpoint the mass-matched split again has the unsplit value. -/
theorem closedRandomFieldParisiFunctional_split_right_endpoint
    (μh : Measure ℝ) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hq : qs ∈ parisiOverlapDomain k) (p : Fin (k + 1)) :
    closedRandomFieldParisiFunctional μh ξ
      (splitParisiMassLeft ms p (mExt ms (p.val + 1)))
      (splitParisiOverlap qs p (qExt qs (p.val + 2))) =
        closedRandomFieldParisiFunctional μh ξ ms qs := by
  have hb := mem_parisiOverlapDomain_iff.1 hq
  apply closedRandomFieldParisiFunctional_split_matching_mass
    μh hξ ms qs hq p (qExt qs (p.val + 2))
  exact ⟨qExt_le_succ hb.1 hb.2.1 hb.2.2 (by omega), le_refl _⟩

/-! ## Mirror insertion: the new mass controls the right subinterval -/

/-- Insert a free mass immediately after the mass of a nonterminal interval. -/
def splitParisiMassRight {k : ℕ} (ms : Fin k → ℝ) (p : Fin k)
    (m : ℝ) : Fin (k + 1) → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) p.succ m ms

@[simp] theorem erase_splitParisiMassRight {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin k) (m : ℝ) :
    eraseParisiMass (splitParisiMassRight ms p m) p.succ = ms := by
  funext i
  change Fin.insertNth (α := fun _ => ℝ) p.succ m ms (p.succ.succAbove i) = ms i
  exact Fin.insertNth_apply_succAbove _ _ _ _

/-- At the right endpoint, the overlap inserted after `p` equals the next old
overlap. Its zero-variance interval carries the freely inserted mass. -/
theorem splitParisiOverlap_right_adjacent_eq {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin k) :
    splitParisiOverlap qs p.castSucc (qs p.succ) p.succ.castSucc =
      splitParisiOverlap qs p.castSucc (qs p.succ) p.succ.succ := by
  unfold splitParisiOverlap
  have hleft : p.succ.castSucc = p.castSucc.succ := Fin.ext (by simp)
  have hright : p.succ.succ = p.castSucc.succ.succAbove p.succ := by
    apply Fin.ext
    simp [Fin.succAbove]
  rw [hleft, hright, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

@[simp] theorem erase_splitParisiOverlap_right {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin k) :
    eraseParisiOverlap (splitParisiOverlap qs p.castSucc (qs p.succ)) p.succ = qs := by
  funext i
  -- The deletion removes the old right endpoint and retains its inserted copy.
  by_cases hi : i = p.succ
  · subst i
    simp [eraseParisiOverlap, splitParisiOverlap]
  · have hidx : p.succ.succ.succAbove i = p.castSucc.succ.succAbove i := by
      by_cases hlt : i.val ≤ p.val
      · have h₁ : i.castSucc < p.succ.succ := by
          change i.val < p.val + 2
          omega
        have h₂ : i.castSucc < p.castSucc.succ := by
          change i.val < p.val + 1
          omega
        rw [Fin.succAbove_of_castSucc_lt _ _ h₁,
          Fin.succAbove_of_castSucc_lt _ _ h₂]
      · have hneval : i.val ≠ p.val + 1 := by
          intro he
          apply hi
          exact Fin.ext (by simpa only [Fin.val_succ] using he)
        have h₁ : p.succ.succ ≤ i.castSucc := by
          change p.val + 2 ≤ i.val
          omega
        have h₂ : p.castSucc.succ ≤ i.castSucc := by
          change p.val + 1 ≤ i.val
          omega
        rw [Fin.succAbove_of_le_castSucc _ _ h₁,
          Fin.succAbove_of_le_castSucc _ _ h₂]
    change Fin.insertNth (α := fun _ => ℝ) p.castSucc.succ (qs p.succ) qs
      (p.succ.succ.succAbove i) = qs i
    rw [hidx, Fin.insertNth_apply_succAbove]

/-- Splitting at the right endpoint preserves the closed functional for every
inserted mass. -/
theorem closedRandomFieldParisiFunctional_split_right_endpoint_any_mass
    (μh : Measure ℝ) {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (p : Fin k) (m : ℝ) :
    closedRandomFieldParisiFunctional μh ξ
      (splitParisiMassRight ms p m) (splitParisiOverlap qs p.castSucc (qs p.succ)) =
        closedRandomFieldParisiFunctional μh ξ ms qs := by
  have h := closedRandomFieldParisiFunctional_erase_adjacent_eq
    μh (ξ := ξ) (splitParisiMassRight ms p m)
      (splitParisiOverlap qs p.castSucc (qs p.succ)) p.succ
      (splitParisiOverlap_right_adjacent_eq qs p)
  simpa only [erase_splitParisiMassRight, erase_splitParisiOverlap_right] using h.symm

/-- Duplicating the old interval mass gives the same array in either insertion
order. -/
theorem splitParisiMassRight_matching_eq_left {k : ℕ}
    (ms : Fin k → ℝ) (p : Fin k) :
    splitParisiMassRight ms p (ms p) =
      splitParisiMassLeft ms p.castSucc (ms p) := by
  funext i
  simp [splitParisiMassRight, splitParisiMassLeft, Fin.insertNth,
    Fin.succAboveCases]
  split_ifs <;> try rfl
  all_goals
    try (apply congrArg ms; apply Fin.ext)
    try simp only [Fin.val_castSucc, Fin.val_succ] at *
    simp [Fin.castPred, Fin.val_pred] at *
    have hp₁ : p.succ.val = p.val + 1 := rfl
    have hp₀ : p.castSucc.val = p.val := rfl
    omega

/-- At the original mass, the mirror split is flat throughout the interval. -/
theorem closedRandomFieldParisiFunctional_split_right_matching_mass
    (μh : Measure ℝ) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hq : qs ∈ parisiOverlapDomain k) (p : Fin k) (u : ℝ)
    (hu : qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2)) :
    closedRandomFieldParisiFunctional μh ξ
      (splitParisiMassRight ms p (ms p))
      (splitParisiOverlap qs p.castSucc u) =
        closedRandomFieldParisiFunctional μh ξ ms qs := by
  have hm : mExt ms (p.castSucc.val + 1) = ms p := by
    simpa only [Fin.val_castSucc] using (mExt_val_succ ms p)
  rw [splitParisiMassRight_matching_eq_left, ← hm]
  exact closedRandomFieldParisiFunctional_split_matching_mass
    μh hξ ms qs hq p.castSucc u (by simpa only [Fin.val_castSucc] using hu)

/-- The mirror split at the left endpoint has the unsplit value when its
inserted mass matches the old interval mass. -/
theorem closedRandomFieldParisiFunctional_split_right_left_endpoint
    (μh : Measure ℝ) {ξ : ℝ → ℝ}
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (p : Fin k) :
    closedRandomFieldParisiFunctional μh ξ
      (splitParisiMassRight ms p (ms p))
      (splitParisiOverlap qs p.castSucc (qs p.castSucc)) =
        closedRandomFieldParisiFunctional μh ξ ms qs := by
  rw [splitParisiMassRight_matching_eq_left]
  exact closedRandomFieldParisiFunctional_split_left_endpoint
    μh ms qs p.castSucc (ms p)

/-! ## Admissible split competitors -/

/-- Inserting an overlap inside the original interval preserves the closed
overlap domain. This supplies the overlap coordinate of a mass-variation
competitor. -/
theorem splitParisiOverlap_mem_domain {k : ℕ}
    {qs : Fin (k + 1) → ℝ} (hq : qs ∈ parisiOverlapDomain k)
    (p : Fin (k + 1)) {u : ℝ}
    (hu : qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2)) :
    splitParisiOverlap qs p u ∈ parisiOverlapDomain (k + 1) := by
  have hleft : qs p ≤ u := by
    simpa only [qExt_succ_of_lt qs p.isLt] using hu.1
  have hu0 : 0 ≤ u := (mem_parisiOverlapCube_iff.1 hq.1 p).1.trans hleft
  have hu1 : u ≤ 1 :=
    hu.2.trans (qExt_mem_Icc_of_mem_cube hq.1 _).2
  refine ⟨mem_parisiOverlapCube_iff.2 (fun i => ?_), ?_⟩
  · by_cases hi : i = p.succ
    · subst i
      simpa only [splitParisiOverlap, Fin.insertNth_apply_same] using
        (show u ∈ Set.Icc (0 : ℝ) 1 from ⟨hu0, hu1⟩)
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      simpa only [splitParisiOverlap, Fin.insertNth_apply_succAbove] using
        mem_parisiOverlapCube_iff.1 hq.1 j
  · change Monotone (Fin.insertNth (α := fun _ => ℝ) p.succ u qs)
    cases p using Fin.lastCases with
    | last =>
        change Monotone (Fin.insertNth (α := fun _ => ℝ)
          (Fin.last (k + 1)) u qs)
        exact Fin.insertNth_last_monotone hq.2 u hleft
    | cast i =>
        have hright : u ≤ qs i.succ := by
          have h := hu.2
          simp only [Fin.val_castSucc] at h
          have he : i.val + 2 = (i.val + 1) + 1 := by omega
          rw [he] at h
          rw [qExt_succ_of_lt qs (by omega : i.val + 1 < k + 1)] at h
          convert h using 1
          congr 1
        exact Fin.insertNth_monotone hq.2 i u hleft hright

/-- A left split with its new mass between the neighboring old masses stays
in the closed mass domain. The endpoint masses are `0` and `1`. -/
theorem splitParisiMassLeft_mem_domain {k : ℕ}
    {ms : Fin k → ℝ} (hm : ms ∈ parisiMassDomain k)
    (p : Fin (k + 1)) {m : ℝ}
    (hmp : mExt ms p.val ≤ m ∧ m ≤ mExt ms (p.val + 1)) :
    splitParisiMassLeft ms p m ∈ parisiMassDomain (k + 1) := by
  have hb := mem_parisiMassDomain_iff.1 hm
  have hm0 : 0 ≤ m := (mExt_nonneg hb.2.1 _).trans hmp.1
  have hm1 : m ≤ 1 := hmp.2.trans (mExt_le_one hb.2.2 _)
  have hcoord : ∀ i, splitParisiMassLeft ms p m i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    by_cases hi : i = p
    · subst i
      simpa only [splitParisiMassLeft, Fin.insertNth_apply_same] using
        (show m ∈ Set.Icc (0 : ℝ) 1 from ⟨hm0, hm1⟩)
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      simpa only [splitParisiMassLeft, Fin.insertNth_apply_succAbove] using
        (show ms j ∈ Set.Icc (0 : ℝ) 1 from ⟨hb.2.1 j, hb.2.2 j⟩)
  refine mem_parisiMassDomain_iff.2
    ⟨?_, (fun i => (hcoord i).1), (fun i => (hcoord i).2)⟩
  change Monotone (Fin.insertNth (α := fun _ => ℝ) p m ms)
  induction k with
  | zero =>
      intro a b _
      have ha : a = 0 := Fin.eq_zero a
      have hb : b = 0 := Fin.eq_zero b
      rw [ha, hb]
  | succ k =>
      cases p using Fin.cases with
      | zero =>
          exact Fin.insertNth_zero_monotone hb.1 m (by
            simpa only [Fin.val_zero, zero_add, mExt_one] using hmp.2)
      | succ i =>
          cases i using Fin.lastCases with
          | last =>
              change Monotone (Fin.insertNth (α := fun _ => ℝ)
                (Fin.last (k + 1)) m ms)
              apply Fin.insertNth_last_monotone hb.1 m
              have he : mExt ms (k + 1) = ms (Fin.last k) := by
                simpa only [Fin.val_last] using mExt_val_succ ms (Fin.last k)
              simpa only [Fin.val_succ, Fin.val_last, he] using hmp.1
          | cast j =>
              have hleft : ms j.castSucc ≤ m := by
                have he : mExt ms (j.val + 1) = ms j.castSucc := by
                  simpa only [Fin.val_castSucc] using mExt_val_succ ms j.castSucc
                simpa only [Fin.val_succ, Fin.val_castSucc, he] using hmp.1
              have hright : m ≤ ms j.succ := by
                have h := hmp.2
                rw [show (j.castSucc.succ).val + 1 = j.succ.val + 1 by simp] at h
                simpa only [mExt_val_succ] using h
              exact Fin.insertNth_monotone hb.1 j m hleft hright

/-- The left split is a legal competitor whenever the new overlap and mass
lie in their respective neighboring intervals. -/
theorem splitParisiLeft_mem_parameterDomain {k : ℕ}
    {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ}
    (hm : ms ∈ parisiMassDomain k) (hq : qs ∈ parisiOverlapDomain k)
    (p : Fin (k + 1)) {m u : ℝ}
    (hmp : mExt ms p.val ≤ m ∧ m ≤ mExt ms (p.val + 1))
    (hu : qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2)) :
    (splitParisiMassLeft ms p m, splitParisiOverlap qs p u) ∈
      parisiParameterDomain (k + 1) :=
  ⟨splitParisiMassLeft_mem_domain hm p hmp,
    splitParisiOverlap_mem_domain hq p hu⟩

/-- A right split has its inserted mass between the old interval mass and
the next mass. The last possible next mass is the fixed endpoint `1`. -/
theorem splitParisiMassRight_mem_domain {k : ℕ}
    {ms : Fin k → ℝ} (hm : ms ∈ parisiMassDomain k)
    (p : Fin k) {m : ℝ}
    (hmp : mExt ms (p.val + 1) ≤ m ∧ m ≤ mExt ms (p.val + 2)) :
    splitParisiMassRight ms p m ∈ parisiMassDomain (k + 1) := by
  exact splitParisiMassLeft_mem_domain hm p.succ hmp

/-- The mirror split is a closed-domain competitor on a nonterminal interval. -/
theorem splitParisiRight_mem_parameterDomain {k : ℕ}
    {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ}
    (hm : ms ∈ parisiMassDomain k) (hq : qs ∈ parisiOverlapDomain k)
    (p : Fin k) {m u : ℝ}
    (hmp : mExt ms (p.val + 1) ≤ m ∧ m ≤ mExt ms (p.val + 2))
    (hu : qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2)) :
    (splitParisiMassRight ms p m, splitParisiOverlap qs p.castSucc u) ∈
      parisiParameterDomain (k + 1) :=
  ⟨splitParisiMassRight_mem_domain hm p hmp,
    splitParisiOverlap_mem_domain hq p.castSucc hu⟩

/-- The global variational infimum bounds the left split in (14.238), even
when the insertion introduces zero or repeated masses or overlaps. -/
theorem randomFieldParisiInf_le_split_left
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ}
    (hm : ms ∈ parisiMassDomain k) (hq : qs ∈ parisiOverlapDomain k)
    (p : Fin (k + 1)) {m u : ℝ}
    (hmp : mExt ms p.val ≤ m ∧ m ≤ mExt ms (p.val + 1))
    (hu : qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2)) :
    randomFieldParisiInf μh ξ ≤
      closedRandomFieldParisiFunctional μh ξ
        (splitParisiMassLeft ms p m) (splitParisiOverlap qs p u) :=
  randomFieldParisiInf_le_closedRandomFieldParisiFunctional hμ hξ
    (splitParisiLeft_mem_parameterDomain hm hq p hmp hu)

/-- The same infimum comparison for the mirror split in Section 14.7. -/
theorem randomFieldParisiInf_le_split_right
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ}
    (hm : ms ∈ parisiMassDomain k) (hq : qs ∈ parisiOverlapDomain k)
    (p : Fin k) {m u : ℝ}
    (hmp : mExt ms (p.val + 1) ≤ m ∧ m ≤ mExt ms (p.val + 2))
    (hu : qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2)) :
    randomFieldParisiInf μh ξ ≤
      closedRandomFieldParisiFunctional μh ξ
        (splitParisiMassRight ms p m) (splitParisiOverlap qs p.castSucc u) :=
  randomFieldParisiInf_le_closedRandomFieldParisiFunctional hμ hξ
    (splitParisiRight_mem_parameterDomain hm hq p hmp hu)

/-- MIN's tolerance gives the quantitative near-minimality of every left
split, as needed for the mass variation following (14.238). -/
theorem randomFieldParisiFunctional_sub_lt_split_left_of_near_inf
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ} {ε : ℝ}
    (hm : ms ∈ parisiMassDomain k) (hq : qs ∈ parisiOverlapDomain k)
    (hnear : randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε)
    (p : Fin (k + 1)) {m u : ℝ}
    (hmp : mExt ms p.val ≤ m ∧ m ≤ mExt ms (p.val + 1))
    (hu : qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2)) :
    randomFieldParisiFunctional μh ξ ms qs - ε <
      closedRandomFieldParisiFunctional μh ξ
        (splitParisiMassLeft ms p m) (splitParisiOverlap qs p u) :=
  randomFieldParisiFunctional_sub_lt_closed_of_near_inf hμ hξ hnear
    (splitParisiLeft_mem_parameterDomain hm hq p hmp hu)

/-- The quantitative near-minimality inequality for the right split. -/
theorem randomFieldParisiFunctional_sub_lt_split_right_of_near_inf
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hμ : Integrable id μh) (hξ : TalagrandXiCondition ξ)
    {k : ℕ} {ms : Fin k → ℝ} {qs : Fin (k + 1) → ℝ} {ε : ℝ}
    (hm : ms ∈ parisiMassDomain k) (hq : qs ∈ parisiOverlapDomain k)
    (hnear : randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε)
    (p : Fin k) {m u : ℝ}
    (hmp : mExt ms (p.val + 1) ≤ m ∧ m ≤ mExt ms (p.val + 2))
    (hu : qExt qs (p.val + 1) ≤ u ∧ u ≤ qExt qs (p.val + 2)) :
    randomFieldParisiFunctional μh ξ ms qs - ε <
      closedRandomFieldParisiFunctional μh ξ
        (splitParisiMassRight ms p m) (splitParisiOverlap qs p.castSucc u) :=
  randomFieldParisiFunctional_sub_lt_closed_of_near_inf hμ hξ hnear
    (splitParisiRight_mem_parameterDomain hm hq p hmp hu)

/-- Updating the freely inserted mass agrees with reinserting its new value. -/
theorem update_splitParisiMassLeft {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) (a b : ℝ) :
    Function.update (splitParisiMassLeft ms p a) p b = splitParisiMassLeft ms p b := by
  funext i
  by_cases hi : i = p
  · subst i
    simp only [Function.update_self, splitParisiMassLeft, Fin.insertNth_apply_same]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    rw [Function.update_of_ne (Fin.succAbove_ne p j)]
    simp only [splitParisiMassLeft, Fin.insertNth_apply_succAbove]

/-- Updating the inserted mirror mass agrees with the mirror constructor. -/
theorem update_splitParisiMassRight {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin k) (a b : ℝ) :
    Function.update (splitParisiMassRight ms p a) p.succ b = splitParisiMassRight ms p b :=
  update_splitParisiMassLeft ms p.succ a b

/-- Inserting a mass leaves all preceding mass coordinates unchanged. -/
theorem splitParisiMassLeft_apply_of_lt {k : ℕ} (ms : Fin k → ℝ)
    (p : Fin (k + 1)) (m : ℝ) {i : Fin (k + 1)} (hi : i < p) :
    splitParisiMassLeft ms p m i = ms ⟨i.val, by omega⟩ := by
  unfold splitParisiMassLeft
  rw [Fin.insertNth_apply_below hi]
  simp only [eq_rec_constant]
  rfl

/-- The concrete derivative of the left inserted-mass functional. Its moment
uses the actual prefix cascade, suffix recursion, and field expectation. -/
noncomputable def splitParisiLeftMassDeriv (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (u m : ℝ) : ℝ :=
  randomFieldParisiMassMoment μh ξ (splitParisiMassLeft ms p 0)
    (splitParisiOverlap qs p u) p m - (1 / 2) *
      (parisiTheta ξ (qExt (splitParisiOverlap qs p u) (p.val + 2)) -
        parisiTheta ξ (qExt (splitParisiOverlap qs p u) (p.val + 1)))

/-- Mass differentiation of the left split, valid at both endpoints of `[0,1]`.
This is a concrete version of the inserted variation (14.230), with no
derivative hypothesis and no exponential moment assumption on the field. -/
theorem hasDerivWithinAt_closedRandomFieldParisiFunctional_split_left_mass
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (p : Fin (k + 1)) (u : ℝ) {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun b => closedRandomFieldParisiFunctional μh ξ
        (splitParisiMassLeft ms p b) (splitParisiOverlap qs p u))
      (splitParisiLeftMassDeriv μh ξ ms qs p u m) (Set.Icc (0 : ℝ) 1) m := by
  have hpref (i : Fin p.val) :
      splitParisiMassLeft ms p 0 ⟨i.val, by omega⟩ = ms ⟨i.val, by omega⟩ :=
    splitParisiMassLeft_apply_of_lt ms p 0 (by exact i.isLt)
  have hd := hasDerivWithinAt_closedRandomFieldParisiFunctional_mass_update hμ ξ
    (splitParisiMassLeft ms p 0) (splitParisiOverlap qs p u) p
    (fun i => by rw [hpref i]; exact hpos _)
    (fun i => by rw [hpref i]; exact hle _) hm
  simpa only [update_splitParisiMassLeft, splitParisiLeftMassDeriv] using hd

/-- The concrete derivative of the mirror inserted-mass functional. -/
noncomputable def splitParisiRightMassDeriv (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) (u m : ℝ) : ℝ :=
  randomFieldParisiMassMoment μh ξ (splitParisiMassRight ms p 0)
    (splitParisiOverlap qs p.castSucc u) p.succ m - (1 / 2) *
      (parisiTheta ξ (qExt (splitParisiOverlap qs p.castSucc u) (p.val + 3)) -
        parisiTheta ξ (qExt (splitParisiOverlap qs p.castSucc u) (p.val + 2)))

/-- Mass differentiation of the mirror split, including one-sided zero-mass
and unit-mass endpoints. The original index remains nonterminal. -/
theorem hasDerivWithinAt_closedRandomFieldParisiFunctional_split_right_mass
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (p : Fin k) (u : ℝ) {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun b => closedRandomFieldParisiFunctional μh ξ
        (splitParisiMassRight ms p b) (splitParisiOverlap qs p.castSucc u))
      (splitParisiRightMassDeriv μh ξ ms qs p u m) (Set.Icc (0 : ℝ) 1) m := by
  have hpref (i : Fin p.succ.val) :
      splitParisiMassRight ms p 0 ⟨i.val, by omega⟩ = ms ⟨i.val, by omega⟩ :=
    splitParisiMassLeft_apply_of_lt ms p.succ 0 (by exact i.isLt)
  have hd := hasDerivWithinAt_closedRandomFieldParisiFunctional_mass_update hμ ξ
    (splitParisiMassRight ms p 0) (splitParisiOverlap qs p.castSucc u) p.succ
    (fun i => by rw [hpref i]; exact hpos _)
    (fun i => by rw [hpref i]; exact hle _) hm
  simpa only [update_splitParisiMassRight, splitParisiRightMassDeriv,
    Fin.val_succ, Nat.add_assoc] using hd

/-- At the empty left subinterval, the inserted-mass derivative vanishes.
This is the endpoint identity for the left orientation of (14.230). -/
theorem splitParisiLeftMassDeriv_left_endpoint
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (p : Fin (k + 1)) {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) 1) :
    splitParisiLeftMassDeriv μh ξ ms qs p (qs p) m = 0 := by
  have hd := hasDerivWithinAt_closedRandomFieldParisiFunctional_split_left_mass
    hμ ξ ms qs hpos hle p (qs p) hm
  have heq : (fun b => closedRandomFieldParisiFunctional μh ξ
      (splitParisiMassLeft ms p b) (splitParisiOverlap qs p (qs p))) =
      fun _ : ℝ => closedRandomFieldParisiFunctional μh ξ ms qs :=
    funext (closedRandomFieldParisiFunctional_split_left_endpoint μh ms qs p)
  rw [heq] at hd
  exact UniqueDiffWithinAt.eq_deriv (Set.Icc (0 : ℝ) 1)
    (uniqueDiffOn_Icc zero_lt_one m hm) hd
    (hasDerivAt_const m (closedRandomFieldParisiFunctional μh ξ ms qs)).hasDerivWithinAt

/-- At the empty right subinterval, the mirror inserted-mass derivative
vanishes, including one-sided endpoint masses. -/
theorem splitParisiRightMassDeriv_right_endpoint
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (p : Fin k) {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) 1) :
    splitParisiRightMassDeriv μh ξ ms qs p (qs p.succ) m = 0 := by
  have hd := hasDerivWithinAt_closedRandomFieldParisiFunctional_split_right_mass
    hμ ξ ms qs hpos hle p (qs p.succ) hm
  have heq : (fun b => closedRandomFieldParisiFunctional μh ξ
      (splitParisiMassRight ms p b) (splitParisiOverlap qs p.castSucc (qs p.succ))) =
      fun _ : ℝ => closedRandomFieldParisiFunctional μh ξ ms qs :=
    funext (closedRandomFieldParisiFunctional_split_right_endpoint_any_mass μh ms qs p)
  rw [heq] at hd
  exact UniqueDiffWithinAt.eq_deriv (Set.Icc (0 : ℝ) 1)
    (uniqueDiffOn_Icc zero_lt_one m hm) hd
    (hasDerivAt_const m (closedRandomFieldParisiFunctional μh ξ ms qs)).hasDerivWithinAt

end SpinGlass
