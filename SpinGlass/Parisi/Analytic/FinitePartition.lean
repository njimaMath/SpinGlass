import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# FinitePartition analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped BigOperators

namespace SpinGlass.Aristotle

noncomputable section

/-- Finite log partition functions are stable under a uniform energy perturbation. -/
theorem abs_log_sum_exp_sub_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {H G : ι → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, |H i - G i| ≤ c) :
    |Real.log (∑ i, Real.exp (H i)) - Real.log (∑ i, Real.exp (G i))| ≤ c := by
  have key : ∀ H G : ι → ℝ, (∀ i, H i - G i ≤ c) →
      Real.log (∑ i, Real.exp (H i)) - Real.log (∑ i, Real.exp (G i)) ≤ c := by
    intro H G h
    have hG : 0 < ∑ i, Real.exp (G i) := Finset.sum_pos (fun i _ => Real.exp_pos _)
      Finset.univ_nonempty
    have hH : 0 < ∑ i, Real.exp (H i) := Finset.sum_pos (fun i _ => Real.exp_pos _)
      Finset.univ_nonempty
    rw [sub_le_iff_le_add, ← Real.log_exp c, ← Real.log_mul (Real.exp_pos c).ne' hG.ne']
    refine Real.log_le_log hH ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith [h i])
  rw [abs_sub_le_iff]
  exact ⟨key H G fun i => (abs_le.1 (h i)).2, key G H fun i => by linarith [(abs_le.1 (h i)).1]⟩

/-- Field continuity for an arbitrary finite spin system; replicas can be included
in the configuration type. The coefficient bound is one for a single replica. -/
theorem abs_normalized_log_partition_field_sub_le
    {Config : Type*} [Fintype Config] [Nonempty Config] {n : ℕ} (hn : 0 < n)
    (H : Config → ℝ) (σ : Config → Fin n → ℝ) (hσ : ∀ s i, |σ s i| ≤ 1)
    (h g : Fin n → ℝ) :
    |Real.log (∑ s, Real.exp (H s + ∑ i, h i * σ s i)) / n -
      Real.log (∑ s, Real.exp (H s + ∑ i, g i * σ s i)) / n| ≤
        (∑ i, |h i - g i|) / n := by
  rw [← sub_div, abs_div, Nat.abs_cast]
  gcongr
  refine abs_log_sum_exp_sub_le (Finset.sum_nonneg fun i _ => abs_nonneg _) fun s => ?_
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← sub_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hσ s i)

end

end SpinGlass.Aristotle
