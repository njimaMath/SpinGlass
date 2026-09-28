import SpinGlass.Parisi.Variational.ParisiParameterContinuity
import Mathlib.Order.Fin.InsertNth

/-!
# Removing redundant Gaussian recursion levels

These local identities are used when a compact parameter minimum has repeated
overlaps. They preserve the recursion rather than approximating its value.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace SpinGlass

/-- Deleting any zero-variance level leaves the finite Cole-Hopf iterate
unchanged, including when its exponent is zero. -/
theorem coleHopfIterate_erase_zero_var (k : ℕ) :
    ∀ (ms : Fin (k + 1) → ℝ) (vs : Fin (k + 1) → ℝ≥0) (i : Fin (k + 1)),
      vs i = 0 → ∀ G : ℝ → ℝ,
      coleHopfIterate (k + 1) ms vs G =
        coleHopfIterate k (fun j => ms (i.succAbove j)) (fun j => vs (i.succAbove j)) G := by
  induction k with
  | zero =>
    intro ms vs i hi G
    fin_cases i
    change vs 0 = 0 at hi
    funext x
    rw [coleHopfIterate_succ, hi, coleHopf_zero_var]
    rfl
  | succ k ih =>
    intro ms vs i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi G
      funext x
      rw [coleHopfIterate_succ, hi, coleHopf_zero_var]
      rfl
    · intro hi G
      have htail (f : Fin (k + 2) → ℝ) :
          Fin.tail (fun p => f (j.succ.succAbove p)) =
            fun p => Fin.tail f (j.succAbove p) := by
        funext p
        simp only [Fin.tail, Fin.succ_succAbove_succ]
      have htailv (f : Fin (k + 2) → ℝ≥0) :
          Fin.tail (fun p => f (j.succ.succAbove p)) =
            fun p => Fin.tail f (j.succAbove p) := by
        funext p
        simp only [Fin.tail, Fin.succ_succAbove_succ]
      conv_lhs => rw [coleHopfIterate_succ]
      conv_rhs => rw [coleHopfIterate_succ]
      simp only [Fin.succ_succAbove_zero, htail, htailv]
      rw [ih (Fin.tail ms) (Fin.tail vs) j hi G]

/-- Remove the mass attached to the empty interval between consecutive equal
overlaps. The overlap removed is the latter of the two equal coordinates. -/
def eraseParisiMass {k : ℕ} (ms : Fin (k + 1) → ℝ) (p : Fin (k + 1)) : Fin k → ℝ :=
  fun i => ms (p.succAbove i)

def eraseParisiOverlap {k : ℕ} (qs : Fin (k + 2) → ℝ) (p : Fin (k + 1)) :
    Fin (k + 1) → ℝ := fun i => qs (p.succ.succAbove i)

theorem qExt_eraseParisiOverlap {k : ℕ} (qs : Fin (k + 2) → ℝ) (p : Fin (k + 1))
    (r : ℕ) :
    qExt (eraseParisiOverlap qs p) r = qExt qs (if r ≤ p.val + 1 then r else r + 1) := by
  rcases r with _ | r
  · simp
  · by_cases hr : r < k + 1
    · rw [qExt_succ_of_lt _ hr]
      unfold eraseParisiOverlap
      by_cases hp : r ≤ p.val
      · rw [Fin.succAbove_of_succ_le _ _ (by change r + 1 ≤ p.val + 1; omega)]
        rw [ite_eq_left (by omega), qExt_succ_of_lt qs (by omega)]
        rfl
      · rw [Fin.succAbove_of_lt_succ _ _ (by change p.val + 1 < r + 1; omega)]
        rw [ite_eq_right (by omega), qExt_succ_of_lt qs (by omega)]
        rfl
    · rw [qExt_of_le _ (by omega), ite_eq_right (by omega), qExt_of_le qs (by omega)]

theorem mExt_eraseParisiMass {k : ℕ} (ms : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (r : ℕ) :
    mExt (eraseParisiMass ms p) r = mExt ms (if r ≤ p.val then r else r + 1) := by
  rcases r with _ | r
  · simp
  · by_cases hr : r < k
    · rw [mExt_val_succ (eraseParisiMass ms p) (⟨r, hr⟩ : Fin k)]
      unfold eraseParisiMass
      by_cases hp : r < p.val
      · rw [Fin.succAbove_of_castSucc_lt _ _ (by exact hp)]
        rw [ite_eq_left (by omega), mExt_val_succ ms (⟨r, by omega⟩ : Fin (k + 1))]
        rfl
      · rw [Fin.succAbove_of_le_castSucc _ _ (by exact le_of_not_gt hp)]
        rw [ite_eq_right (by omega), mExt_val_succ ms (⟨r + 1, by omega⟩ : Fin (k + 1))]
        rfl
    · rw [mExt_eq_one_of_le _ (by omega), ite_eq_right (by omega),
        mExt_eq_one_of_le ms (by omega)]

/-- The deleted interval has zero variance, even with the variance clamping
used by the canonical recursion. -/
theorem parisiVar_eq_zero_of_adjacent_eq {ξ : ℝ → ℝ} {k : ℕ}
    (qs : Fin (k + 2) → ℝ) (p : Fin (k + 1)) (hq : qs p.castSucc = qs p.succ) :
    parisiVar ξ qs (p.val + 1) = 0 := by
  have heq : qExt qs (p.val + 1) = qExt qs (p.val + 2) := by
    rw [qExt_succ_of_lt qs (by omega), qExt_succ_of_lt qs (by omega)]
    exact hq
  unfold parisiVar
  rw [← heq, sub_self, Real.toNNReal_zero]

/-- Variances of the retained intervals agree exactly after redundant-overlap
removal; no approximation or sign hypothesis on the profile is used. -/
theorem parisiVar_eraseParisiOverlap {ξ : ℝ → ℝ} {k : ℕ}
    (qs : Fin (k + 2) → ℝ) (p : Fin (k + 1)) (hq : qs p.castSucc = qs p.succ)
    (r : ℕ) :
    parisiVar ξ (eraseParisiOverlap qs p) r =
      parisiVar ξ qs (if r ≤ p.val then r else r + 1) := by
  have heq : qExt qs (p.val + 1) = qExt qs (p.val + 2) := by
    rw [qExt_succ_of_lt qs (by omega), qExt_succ_of_lt qs (by omega)]
    exact hq
  unfold parisiVar
  rw [qExt_eraseParisiOverlap, qExt_eraseParisiOverlap]
  by_cases hr : r ≤ p.val
  · simp only [ite_eq_left hr, ite_eq_left (by omega : r ≤ p.val + 1),
      ite_eq_left (by omega : r + 1 ≤ p.val + 1)]
  · rw [ite_eq_right hr]
    by_cases he : r = p.val + 1
    · subst r
      simp only [ite_eq_left (le_refl _), ite_eq_right (by omega : ¬p.val + 1 + 1 ≤ p.val + 1)]
      rw [heq]
    · simp only [ite_eq_right (by omega : ¬r ≤ p.val + 1),
        ite_eq_right (by omega : ¬r + 1 ≤ p.val + 1)]

theorem parisiAllMasses_apply {k : ℕ} (ms : Fin k → ℝ) (i : Fin (k + 2)) :
    (Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms)) i = mExt ms i.val := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.cons_succ, parisiLevelMasses_apply, Fin.val_succ]

theorem parisiAllMasses_eraseParisiMass {k : ℕ} (ms : Fin (k + 1) → ℝ) (p : Fin (k + 1)) :
    Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses (eraseParisiMass ms p)) =
      fun i => (Fin.cons (α := fun _ => ℝ) 0 (parisiLevelMasses ms))
        (p.castSucc.succ.succAbove i) := by
  funext i
  rw [parisiAllMasses_apply, mExt_eraseParisiMass, parisiAllMasses_apply]
  by_cases hi : i.val ≤ p.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by change i.val < p.val + 1; omega),
      ite_eq_left hi]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by change p.val + 1 ≤ i.val; omega),
      ite_eq_right hi]
    rfl

theorem parisiAllVars_eraseParisiOverlap {ξ : ℝ → ℝ} {k : ℕ}
    (qs : Fin (k + 2) → ℝ) (p : Fin (k + 1)) (hq : qs p.castSucc = qs p.succ) :
    parisiAllVars ξ (eraseParisiOverlap qs p) =
      fun i => parisiAllVars ξ qs (p.castSucc.succ.succAbove i) := by
  funext i
  change parisiVar ξ (eraseParisiOverlap qs p) i.val =
    parisiVar ξ qs (p.castSucc.succ.succAbove i).val
  rw [parisiVar_eraseParisiOverlap qs p hq]
  by_cases hi : i.val ≤ p.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by change i.val < p.val + 1; omega),
      ite_eq_left hi]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by change p.val + 1 ≤ i.val; omega),
      ite_eq_right hi]
    rfl

theorem ParisiMAdmissible.eraseParisiMass {k : ℕ} {ms : Fin (k + 1) → ℝ}
    (hm : ParisiMAdmissible ms) (p : Fin (k + 1)) :
    ParisiMAdmissible (eraseParisiMass ms p) :=
  ⟨hm.1.comp (p.succAboveOrderEmb.strictMono),
    (fun i => hm.2.1 (p.succAbove i)), (fun i => hm.2.2 (p.succAbove i))⟩

/-- Removing a repeated overlap and its empty-interval mass preserves the
actual one-site Gaussian recursion for every external field. -/
theorem parisiX₀_erase_adjacent_eq {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin (k + 1) → ℝ) (qs : Fin (k + 2) → ℝ)
    (hm : ParisiMAdmissible ms) (p : Fin (k + 1)) (hq : qs p.castSucc = qs p.succ)
    (h : ℝ) :
    parisiX₀ ξ (eraseParisiMass ms p) (eraseParisiOverlap qs p) (parisiLogCoshTerminal h) =
      parisiX₀ ξ ms qs (parisiLogCoshTerminal h) := by
  rw [parisiX₀_eq_coleHopfIterate_all _ _ (hm.eraseParisiMass p),
    parisiX₀_eq_coleHopfIterate_all _ _ hm,
    parisiAllMasses_eraseParisiMass, parisiAllVars_eraseParisiOverlap qs p hq]
  have hz : parisiAllVars ξ qs p.castSucc.succ = 0 :=
    parisiVar_eq_zero_of_adjacent_eq qs p hq
  rw [coleHopfIterate_erase_zero_var (k + 2) _ _ p.castSucc.succ hz]

/-- The deletion identity commutes with the outer quenched field average. -/
theorem randomFieldParisiX₀_erase_adjacent_eq (μh : Measure ℝ) {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin (k + 1) → ℝ) (qs : Fin (k + 2) → ℝ)
    (hm : ParisiMAdmissible ms) (p : Fin (k + 1)) (hq : qs p.castSucc = qs p.succ) :
    randomFieldParisiX₀ μh ξ (eraseParisiMass ms p) (eraseParisiOverlap qs p) =
      randomFieldParisiX₀ μh ξ ms qs := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (parisiX₀_erase_adjacent_eq ms qs hm p hq)

/-- The deterministic correction sum is preserved by deletion of an empty
overlap interval. -/
theorem parisiCorrection_erase_adjacent_eq {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin (k + 1) → ℝ) (qs : Fin (k + 2) → ℝ)
    (p : Fin (k + 1)) (hq : qs p.castSucc = qs p.succ) :
    (∑ r : Fin (k + 1), mExt (eraseParisiMass ms p) (r.val + 1) *
      (parisiTheta ξ (qExt (eraseParisiOverlap qs p) (r.val + 2)) -
        parisiTheta ξ (qExt (eraseParisiOverlap qs p) (r.val + 1)))) =
      ∑ r : Fin (k + 2), mExt ms (r.val + 1) *
        (parisiTheta ξ (qExt qs (r.val + 2)) - parisiTheta ξ (qExt qs (r.val + 1))) := by
  have heq : qExt qs (p.val + 1) = qExt qs (p.val + 2) := by
    rw [qExt_succ_of_lt qs (by omega), qExt_succ_of_lt qs (by omega)]
    exact hq
  let f : Fin (k + 2) → ℝ := fun r => mExt ms (r.val + 1) *
    (parisiTheta ξ (qExt qs (r.val + 2)) - parisiTheta ξ (qExt qs (r.val + 1)))
  have hz : f p.castSucc = 0 := by
    dsimp [f]
    rw [← heq, sub_self, mul_zero]
  change _ = ∑ r, f r
  rw [Fin.sum_univ_succAbove f p.castSucc, hz]
  simp only [zero_add]
  apply Finset.sum_congr rfl
  intro r _
  dsimp [f]
  rw [mExt_eraseParisiMass, qExt_eraseParisiOverlap, qExt_eraseParisiOverlap]
  by_cases hr : r.val < p.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by exact hr)]
    simp only [Fin.val_castSucc,
      ite_eq_left (by omega : r.val + 1 ≤ p.val),
      ite_eq_left (by omega : r.val + 2 ≤ p.val + 1),
      ite_eq_left (by omega : r.val + 1 ≤ p.val + 1)]
  · rw [Fin.succAbove_of_le_castSucc _ _ (by exact le_of_not_gt hr)]
    by_cases he : r = p
    · subst r
      simp only [Fin.val_succ,
        ite_eq_right (by omega : ¬p.val + 1 ≤ p.val),
        ite_eq_right (by omega : ¬p.val + 2 ≤ p.val + 1),
        ite_eq_left (le_refl (p.val + 1))]
      rw [heq]
    · have hgt : p.val < r.val := by
        have hne : r.val ≠ p.val := fun h => he (Fin.ext h)
        omega
      simp only [Fin.val_succ,
        ite_eq_right (by omega : ¬r.val + 1 ≤ p.val),
        ite_eq_right (by omega : ¬r.val + 2 ≤ p.val + 1),
        ite_eq_right (by omega : ¬r.val + 1 ≤ p.val + 1)]

/-- Delete repeated neighboring overlaps without changing the canonical
random-field functional or any of its normalization terms. -/
theorem randomFieldParisiFunctional_erase_adjacent_eq (μh : Measure ℝ)
    {ξ : ℝ → ℝ} {k : ℕ} (ms : Fin (k + 1) → ℝ) (qs : Fin (k + 2) → ℝ)
    (hm : ParisiMAdmissible ms) (p : Fin (k + 1)) (hq : qs p.castSucc = qs p.succ) :
    randomFieldParisiFunctional μh ξ (eraseParisiMass ms p) (eraseParisiOverlap qs p) =
      randomFieldParisiFunctional μh ξ ms qs := by
  unfold randomFieldParisiFunctional
  rw [randomFieldParisiX₀_erase_adjacent_eq μh ms qs hm p hq]
  congr 1
  congr 1
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  exact parisiCorrection_erase_adjacent_eq ms qs p hq

/-- Repeat a coordinate to restore the dimension before an empty interval was
deleted. This is used to compare against every competitor in the smaller domain. -/
def repeatParisiOverlap {k : ℕ} (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) :
    Fin (k + 2) → ℝ := Fin.insertNth (α := fun _ => ℝ) p.succ (qs p) qs

theorem repeatParisiOverlap_adjacent_eq {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) :
    repeatParisiOverlap qs p p.castSucc = repeatParisiOverlap qs p p.succ := by
  unfold repeatParisiOverlap
  rw [← Fin.succAbove_succ_self p, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]

@[simp] theorem erase_repeatParisiOverlap {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) :
    eraseParisiOverlap (repeatParisiOverlap qs p) p = qs := by
  funext i
  change Fin.insertNth (α := fun _ => ℝ) p.succ (qs p) qs (p.succ.succAbove i) = qs i
  exact Fin.insertNth_apply_succAbove _ _ _ _

theorem repeatParisiOverlap_mem_domain {k : ℕ} {qs : Fin (k + 1) → ℝ}
    (hq : qs ∈ parisiOverlapDomain k) (p : Fin (k + 1)) :
    repeatParisiOverlap qs p ∈ parisiOverlapDomain (k + 1) := by
  refine ⟨mem_parisiOverlapCube_iff.2 (fun i => ?_), ?_⟩
  · by_cases hi : i = p.succ
    · subst i
      simpa only [repeatParisiOverlap, Fin.insertNth_apply_same] using
        mem_parisiOverlapCube_iff.1 hq.1 p
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      simpa only [repeatParisiOverlap, Fin.insertNth_apply_succAbove] using
        mem_parisiOverlapCube_iff.1 hq.1 j
  · change Monotone (repeatParisiOverlap qs p)
    refine Fin.lastCases ?_ (fun i => ?_) p
    · change Monotone (Fin.insertNth (α := fun _ => ℝ) (Fin.last (k + 1))
        (qs (Fin.last k)) qs)
      exact Fin.insertNth_last_monotone hq.2 (qs (Fin.last k)) (le_refl _)
    · exact Fin.insertNth_monotone hq.2 i (qs i.castSucc) (le_refl _)
        (hq.2 i.castSucc_le_succ)

theorem eraseParisiOverlap_mem_domain {k : ℕ} {qs : Fin (k + 2) → ℝ}
    (hq : qs ∈ parisiOverlapDomain (k + 1)) (p : Fin (k + 1)) :
    eraseParisiOverlap qs p ∈ parisiOverlapDomain k := by
  refine ⟨mem_parisiOverlapCube_iff.2 (fun i => mem_parisiOverlapCube_iff.1 hq.1 _), ?_⟩
  exact hq.2.comp p.succ.succAboveOrderEmb.monotone

/-- A closed-domain minimum remains a closed-domain minimum after deletion.
Every smaller competitor is lifted by repeating its corresponding coordinate. -/
theorem isMinOn_randomFieldParisiFunctional_erase_adjacent_eq
    (μh : Measure ℝ) {ξ : ℝ → ℝ} {k : ℕ}
    (ms : Fin (k + 1) → ℝ) (qs : Fin (k + 2) → ℝ)
    (hm : ParisiMAdmissible ms) (p : Fin (k + 1)) (hq : qs p.castSucc = qs p.succ)
    (hmin : IsMinOn (fun qs => randomFieldParisiFunctional μh ξ ms qs)
      (parisiOverlapDomain (k + 1)) qs) :
    IsMinOn (fun qs => randomFieldParisiFunctional μh ξ (eraseParisiMass ms p) qs)
      (parisiOverlapDomain k) (eraseParisiOverlap qs p) := by
  intro qs' hqs'
  change randomFieldParisiFunctional μh ξ (eraseParisiMass ms p) (eraseParisiOverlap qs p) ≤
    randomFieldParisiFunctional μh ξ (eraseParisiMass ms p) qs'
  rw [randomFieldParisiFunctional_erase_adjacent_eq μh ms qs hm p hq]
  have htest := randomFieldParisiFunctional_erase_adjacent_eq μh (ξ := ξ) ms
    (repeatParisiOverlap qs' p) hm p (repeatParisiOverlap_adjacent_eq qs' p)
  simp only [erase_repeatParisiOverlap] at htest
  rw [htest]
  exact hmin (repeatParisiOverlap_mem_domain hqs' p)

end SpinGlass
