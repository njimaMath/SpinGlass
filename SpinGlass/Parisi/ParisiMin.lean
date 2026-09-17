import SpinGlass.Parisi.ParisiInf
import SpinGlass.Parisi.ParisiQDeriv

/-!
# Approximation of the random-field Parisi infimum

This is the infimum-selection part of Lemma 14.5.5. It gives admissible
parameters within any positive tolerance. It does not assert finite-dimensional
minimality: that additionally requires compact minimization and removal of
redundant levels.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace SpinGlass

/-- On the physical interval, the correction function has derivative $q ξ''(q)$
and is nondecreasing, including when the second derivative vanishes at zero. -/
theorem TalagrandXiCondition.monotoneOn_parisiTheta {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) : MonotoneOn (parisiTheta ξ) (Icc (0 : ℝ) 1) := by
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :=
    hasDerivAt_parisiTheta (hξ.hasDeriv x hx) (hξ.hasDeriv_deriv x hx)
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
  intro x hx
  have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hx
  rw [(hd x (interior_subset hx)).deriv]
  exact mul_nonneg hx'.1.le (hξ.second_pos x (interior_subset hx) (ne_of_gt hx'.1)).le

/-- A uniform lower bound on admissible functional values. This uses local
regularity from (14.101), without global differentiability of the profile. -/
theorem randomFieldParisiFunctional_lower_bound_of_talagrand
    (μh : Measure ℝ) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1) :
    Real.log 2 - (1 / 2) * (parisiTheta ξ 1 - parisiTheta ξ 0) ≤
      randomFieldParisiFunctional μh ξ ms qs := by
  have hX : 0 ≤ randomFieldParisiX₀ μh ξ ms qs := by
    change 0 ≤ ∫ h, parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x))) ∂μh
    apply integral_nonneg
    intro h
    change 0 ≤ parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))
    rw [parisiX₀_logCosh_eq k ξ h ms qs hpos hle]
    exact add_nonneg (integral_nonneg fun a => logCoshRec_nonneg k ms _ hpos _)
      (by positivity)
  have htheta := hξ.monotoneOn_parisiTheta
  have hqmem := qExt_mem_Icc hmono hq0 hq1
  have hsum :
      (∑ p ∈ Finset.range (k + 1), mExt ms (p + 1) *
        (parisiTheta ξ (qExt qs (p + 2)) - parisiTheta ξ (qExt qs (p + 1)))) ≤
      parisiTheta ξ 1 - parisiTheta ξ 0 := by
    calc
      _ ≤ ∑ p ∈ Finset.range (k + 1),
          (parisiTheta ξ (qExt qs (p + 2)) - parisiTheta ξ (qExt qs (p + 1))) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : p + 1 ≤ k + 1 := Nat.succ_le_of_lt (Finset.mem_range.1 hp)
        have hdelta : 0 ≤ parisiTheta ξ (qExt qs (p + 2)) -
            parisiTheta ξ (qExt qs (p + 1)) := by
          apply sub_nonneg.2
          exact htheta (hqmem _) (hqmem _) (qExt_le_succ hmono hq0 hq1 hp')
        exact mul_le_of_le_one_left hdelta (mExt_le_one hle _)
      _ = parisiTheta ξ (qExt qs (k + 2)) - parisiTheta ξ (qExt qs 1) := by
        simpa only [Nat.add_assoc] using
          Finset.sum_range_sub (fun p => parisiTheta ξ (qExt qs (p + 1))) (k + 1)
      _ ≤ parisiTheta ξ 1 - parisiTheta ξ 0 := by
        rw [qExt_of_le qs (le_refl (k + 2))]
        exact sub_le_sub_left (htheta (by simp) (hqmem 1) (hqmem 1).1) _
  unfold randomFieldParisiFunctional
  linarith

/-- The variational set is bounded below under the book's local analytic assumptions. -/
theorem bddBelow_randomFieldParisiSet_of_talagrand
    (μh : Measure ℝ) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) :
    BddBelow (randomFieldParisiSet μh ξ) := by
  refine ⟨Real.log 2 - (1 / 2) * (parisiTheta ξ 1 - parisiTheta ξ 0), ?_⟩
  rintro y ⟨k, ms, qs, _, hpos, hlt, hmono, hq0, hq1, rfl⟩
  exact randomFieldParisiFunctional_lower_bound_of_talagrand μh hξ ms qs hpos
    (fun i => (hlt i).le) hmono hq0 hq1

/-- Choose an admissible finite list within a positive tolerance of the infimum.
Boundedness below is explicit, since `sInf` in the reals has a default value for
sets that are unbounded below. -/
theorem exists_randomFieldParisiFunctional_lt_inf_add
    (μh : Measure ℝ) (ξ : ℝ → ℝ)
    (hbdd : BddBelow (randomFieldParisiSet μh ξ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      StrictMono ms ∧ (∀ i, 0 < ms i) ∧ (∀ i, ms i < 1) ∧
      Monotone qs ∧ 0 ≤ qs 0 ∧ qs (Fin.last k) ≤ 1 ∧
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε := by
  have hlt : sInf (randomFieldParisiSet μh ξ) < randomFieldParisiInf μh ξ + ε :=
    lt_add_of_pos_right _ hε
  obtain ⟨y, hy, hylt⟩ :=
    (csInf_lt_iff hbdd (randomFieldParisiSet_nonempty μh ξ)).1 hlt
  rcases hy with ⟨k, ms, qs, hsm, hpos, hmass, hmono, hzero, hone, rfl⟩
  exact ⟨k, ms, qs, hsm, hpos, hmass, hmono, hzero, hone, hylt⟩

/-- Infimum selection under (14.101). Full MIN existence additionally needs
finite-dimensional minimality and a strict overlap list. -/
theorem exists_randomFieldParisiFunctional_lt_inf_add_of_talagrand
    (μh : Measure ℝ) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      StrictMono ms ∧ (∀ i, 0 < ms i) ∧ (∀ i, ms i < 1) ∧
      Monotone qs ∧ 0 ≤ qs 0 ∧ qs (Fin.last k) ≤ 1 ∧
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε :=
  exists_randomFieldParisiFunctional_lt_inf_add μh ξ
    (bddBelow_randomFieldParisiSet_of_talagrand μh hξ) hε

end SpinGlass
