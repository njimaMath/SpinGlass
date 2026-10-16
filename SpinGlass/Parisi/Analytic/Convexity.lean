import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

/-!
# Weighted averages of concave functions

Concavity under an arbitrary measure is independent of Gaussian split calculus.
The public declaration retains its existing `SpinGlass.Aristotle` name.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace SpinGlass.Aristotle

noncomputable section

/-- A fixed nonnegative weighted average preserves the split concavity. -/
theorem concaveOn_integral_weighted {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {F : Ω → ℝ → ℝ} {W : Ω → ℝ} {a b : ℝ}
    (hW : ∀ᵐ ω ∂μ, 0 ≤ W ω)
    (hF : ∀ᵐ ω ∂μ, ConcaveOn ℝ (Icc a b) (F ω))
    (hint : ∀ v ∈ Icc a b, Integrable (fun ω => W ω * F ω v) μ) :
    ConcaveOn ℝ (Icc a b) (fun v => ∫ ω, W ω * F ω v ∂μ) := by
  refine ⟨convex_Icc a b, fun x hx y hy s t hs ht hst => ?_⟩
  have hxy : s • x + t • y ∈ Icc a b := convex_Icc a b hx hy hs ht hst
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((hint x hx).const_mul s) ((hint y hy).const_mul t)]
  refine integral_mono_ae (((hint x hx).const_mul s).add ((hint y hy).const_mul t))
    (hint _ hxy) ?_
  filter_upwards [hW, hF] with ω hWω hFω
  have := hFω.2 hx hy hs ht hst
  simp only [smul_eq_mul] at this ⊢
  nlinarith [mul_le_mul_of_nonneg_left this hWω]

end

end SpinGlass.Aristotle
