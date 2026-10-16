import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

/-!
# Lipschitz bounds from real derivatives

These mean-value estimates require no Gaussian law or mass transform.
The public declarations retain their existing `SpinGlass.Aristotle` names.
-/

set_option autoImplicit false

open Filter Set Topology

namespace SpinGlass.Aristotle

noncomputable section

theorem lipschitz_of_iteratedDeriv {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C) (y z : ℝ) :
    |A (y + z) - A y| ≤ C * |z| := by
  have hd : ∀ u, HasDerivAt A (iteratedDeriv 1 A u) u := fun u => by
    rw [iteratedDeriv_one]
    exact ((hA.differentiable (by norm_num)) u).hasDerivAt
  have hmv := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := A) (f' := iteratedDeriv 1 A) (C := C) (fun u _ => (hd u).hasDerivWithinAt)
    (fun u _ => by rw [Real.norm_eq_abs]; exact hb 1 (by simp) u) (mem_univ y) (mem_univ (y + z))
  simpa [Real.norm_eq_abs] using hmv

/-- A derivative bounded by one gives a one-Lipschitz function. -/
theorem abs_sub_le_of_abs_deriv_le_one {A : ℝ → ℝ} (hA : Differentiable ℝ A)
    (h : ∀ x, |deriv A x| ≤ 1) (y w : ℝ) : |A y - A w| ≤ |y - w| := by
  have := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le (C := 1)
    (fun x _ => hA x) (fun x _ => by simpa [Real.norm_eq_abs] using h x) (mem_univ w) (mem_univ y)
  simpa [Real.norm_eq_abs] using this

end

end SpinGlass.Aristotle
