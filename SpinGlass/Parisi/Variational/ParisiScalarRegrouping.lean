import SpinGlass.Parisi.Variational.ParisiColeHopfRearrangement

/-!
# Regrouping equal scalar masses

The scalar order in (14.376) groups Gaussian pieces with the same
original mass. Their variances add through the actual Cole-Hopf
semigroup, independently of the order of tied pieces.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace SpinGlass

theorem coleHopf_equal_mass_swap {A : ℝ → ℝ} {L : ℝ}
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) (m : ℝ) (v w : ℝ≥0) (x : ℝ) :
    coleHopf m v (coleHopf m w A) x = coleHopf m w (coleHopf m v A) x := by
  have hAm := (lipschitzWith_toNNReal_of_abs_sub_le hA).continuous.measurable
  rw [coleHopf_coleHopf (HasLinearGrowth.of_lipschitz hA) hAm,
    coleHopf_coleHopf (HasLinearGrowth.of_lipschitz hA) hAm, add_comm v w]

theorem coleHopfIterateList_move_equal_mass {A : ℝ → ℝ} {L : ℝ}
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) (p : ℝ × ℝ≥0)
    (pre tail : List (ℝ × ℝ≥0)) (hm : ∀ q ∈ pre, q.1 = p.1) :
    coleHopfIterateList (pre ++ p :: tail) A = coleHopfIterateList (p :: (pre ++ tail)) A := by
  induction pre with
  | nil => rfl
  | cons q pre ih =>
    have hq := hm q (List.mem_cons_self)
    have hpre : ∀ r ∈ pre, r.1 = p.1 := fun r hr => hm r (List.mem_cons_of_mem _ hr)
    rw [List.cons_append, coleHopfIterateList_cons, ih hpre]
    funext x
    simp only [coleHopfIterateList_cons, List.cons_append]
    rw [hq]
    exact coleHopf_equal_mass_swap (abs_coleHopfIterateList_sub_le (pre ++ tail) hA) p.1 q.2 p.2 x

/-- Two mass-ordered permutations have identical actual recursive
values. Tied variances may occur in any order, including mass zero. -/
theorem coleHopfIterateList_eq_of_sorted_perm {A : ℝ → ℝ} {L : ℝ}
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|)
    (l r : List (ℝ × ℝ≥0)) (hl : List.Pairwise parisiLevelMassOrder l)
    (hr : List.Pairwise parisiLevelMassOrder r) (hp : l.Perm r) :
    coleHopfIterateList l A = coleHopfIterateList r A := by
  induction l generalizing r with
  | nil =>
    have he : r = [] := List.perm_nil.1 hp.symm
    subst r
    rfl
  | cons p l ih =>
    have hpr : p ∈ r := hp.mem_iff.1 (List.mem_cons_self)
    obtain ⟨pre, tail, rfl⟩ := List.mem_iff_append.1 hpr
    have hmin : ∀ q ∈ pre ++ p :: tail, p.1 ≤ q.1 := by
      intro q hq
      rcases List.mem_cons.1 (hp.mem_iff.2 hq) with rfl | hq
      · exact le_rfl
      · exact (List.pairwise_cons.1 hl).1 q hq
    have hpre : ∀ q ∈ pre, q.1 = p.1 := by
      intro q hq
      have hle := (List.pairwise_append.1 hr).2.2 q hq p (List.mem_cons_self)
      exact le_antisymm hle (hmin q (List.mem_append_left _ hq))
    have hsub : (pre ++ tail).Sublist (pre ++ p :: tail) :=
      List.Sublist.append (List.Sublist.refl pre) (List.Sublist.cons p (List.Sublist.refl tail))
    have hr' := hr.sublist hsub
    have hp' : l.Perm (pre ++ tail) :=
      (hp.trans (List.perm_middle)).cons_inv
    rw [coleHopfIterateList_move_equal_mass hA p pre tail hpre]
    rw [coleHopfIterateList_cons, coleHopfIterateList_cons,
      ih (pre ++ tail) (List.pairwise_cons.1 hl).2 hr' hp']

theorem coleHopfIterateList_sort_eq_of_perm {A : ℝ → ℝ} {L : ℝ}
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|)
    (l r : List (ℝ × ℝ≥0)) (hp : l.Perm r) :
    coleHopfIterateList (List.insertionSort parisiLevelMassOrder l) A =
      coleHopfIterateList (List.insertionSort parisiLevelMassOrder r) A := by
  apply coleHopfIterateList_eq_of_sorted_perm hA _ _
    (List.pairwise_insertionSort _ _) (List.pairwise_insertionSort _ _)
  exact ((List.perm_insertionSort _ l).trans hp).trans (List.perm_insertionSort _ r).symm

theorem coleHopfIterateList_same_mass {A : ℝ → ℝ} {L : ℝ}
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) (m : ℝ) (vs : List ℝ≥0) :
    coleHopfIterateList (vs.map (fun v => (m, v))) A = coleHopf m vs.sum A := by
  have hAm := (lipschitzWith_toNNReal_of_abs_sub_le hA).continuous.measurable
  induction vs with
  | nil => funext x; simp only [List.map_nil, coleHopfIterateList_nil, List.sum_nil, coleHopf_zero_var]
  | cons v vs ih =>
    simp only [List.map_cons, coleHopfIterateList_cons, ih, List.sum_cons]
    exact funext fun x => coleHopf_coleHopf (HasLinearGrowth.of_lipschitz hA) hAm m v vs.sum x

theorem coleHopfIterateList_merge_blocks {A : ℝ → ℝ} {L : ℝ}
    (hA : ∀ x y, |A y - A x| ≤ L * |y - x|) (blocks : List (ℝ × List ℝ≥0)) :
    coleHopfIterateList (blocks.flatMap (fun p => p.2.map (fun v => (p.1, v)))) A =
      coleHopfIterateList (blocks.map (fun p => (p.1, p.2.sum))) A := by
  induction blocks with
  | nil => rfl
  | cons p blocks ih =>
    simp only [List.flatMap_cons, List.map_cons, coleHopfIterateList_append,
      coleHopfIterateList_cons, ih]
    exact coleHopfIterateList_same_mass (abs_coleHopfIterateList_sub_le _ hA) p.1 p.2

end SpinGlass
