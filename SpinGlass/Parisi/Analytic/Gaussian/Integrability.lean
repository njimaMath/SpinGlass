import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian Envelope analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

/-- Gaussian increments supply centered envelopes without any assumption on the
additive external field. The variance may be zero. -/
theorem integrable_gaussian_exp_abs (a : ℝ) (v : ℝ≥0) :
    Integrable (fun z : ℝ => Real.exp (a * |z|)) (gaussianReal 0 v) := by
  refine ((integrable_exp_mul_gaussianReal a).add (integrable_exp_mul_gaussianReal (-a))).mono'
    (by fun_prop) (.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]; simp only [Pi.add_apply]; linarith [Real.exp_pos (-a * z)]
  · rw [abs_of_nonpos hz]; simp only [Pi.add_apply]
    have : a * -z = -a * z := by ring
    rw [this]; linarith [Real.exp_pos (a * z)]

/-- Functions of at most exponential growth are Gaussian integrable. -/
theorem integrable_gaussianReal_of_abs_le_exp {v : ℝ≥0} {g : ℝ → ℝ}
    (hg : AEStronglyMeasurable g (gaussianReal 0 v)) {C c : ℝ}
    (h : ∀ z, |g z| ≤ C * Real.exp (c * |z|)) : Integrable g (gaussianReal 0 v) :=
  ((integrable_gaussian_exp_abs c v).const_mul C).mono' hg (.of_forall fun z => by
    simpa [Real.norm_eq_abs] using h z)


end

end SpinGlass.Aristotle
