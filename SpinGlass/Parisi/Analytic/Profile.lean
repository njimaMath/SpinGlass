import SpinGlass.Parisi.Analytic.Taylor
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Convex.Deriv

/-!
# Profile analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped BigOperators

namespace SpinGlass.Aristotle

noncomputable section

/-! ## Covariance-profile remainders and a uniform first-overlap input

Search tag: `PARISI_LB_PROFILE`. Keywords: xi, convex remainder, negative overlap,
q1 lower bound, nondegenerate field, tanh moment, cosh curvature, Gaussian Jensen.

Consumer: exact Guerra remainder and Lemma 14.7.15. Derivative control is required
only on the overlap interval. In particular no positive second derivative at zero
or globally bounded third derivative is introduced.
-/

/-- A monotone second derivative on (0,1] bounds the first derivative up to zero. -/
theorem lipschitz_deriv_of_monotone_second {ξ : ℝ → ℝ}
    (hc : ContinuousOn (deriv ξ) (Icc (0 : ℝ) 1))
    (hd : ∀ x ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (deriv ξ) x)
    (hmono : MonotoneOn (deriv (deriv ξ)) (Ioc (0 : ℝ) 1))
    (hnonneg : ∀ x ∈ Ioc (0 : ℝ) 1, 0 ≤ deriv (deriv ξ) x) :
    ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |deriv ξ x - deriv ξ y| ≤ deriv (deriv ξ) 1 * |x - y| := by
  have key : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, x < y →
      |deriv ξ x - deriv ξ y| ≤ deriv (deriv ξ) 1 * |x - y| := by
    intro x hx y hy hxy
    obtain ⟨c, hc', hceq⟩ := exists_deriv_eq_slope (deriv ξ) hxy
      (hc.mono (Icc_subset_Icc hx.1 hy.2))
      (fun t ht => (hd t ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩).differentiableWithinAt)
    have hc0 : c ∈ Ioc (0 : ℝ) 1 := ⟨hx.1.trans_lt hc'.1, (hc'.2.trans_le hy.2).le⟩
    have h1 := hnonneg c hc0
    have h2 := hmono hc0 ⟨zero_lt_one, le_rfl⟩ hc0.2
    rw [eq_div_iff (by linarith)] at hceq
    rw [abs_sub_comm, ← hceq, abs_mul, abs_of_nonneg h1, abs_sub_comm]
    exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  intro x hx y hy
  rcases lt_trichotomy x y with h | rfl | h
  · exact key x hx y hy h
  · simp
  · rw [abs_sub_comm, abs_sub_comm x]
    exact key y hy x hx h

/-- Evenness extends first-derivative control to negative overlaps. -/
theorem lipschitz_deriv_even_extension {ξ : ℝ → ℝ} {L : ℝ}
    (heven : Function.Even ξ) (hL : 0 ≤ L)
    (hd : ∀ x ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ ξ x)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |deriv ξ x - deriv ξ y| ≤ L * |x - y|) :
    ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |deriv ξ x - deriv ξ y| ≤ L * |x - y| := by
  have hodd : ∀ x, deriv ξ (-x) = -deriv ξ x := by
    intro x
    have : ξ = fun y => ξ (-y) := funext fun y => (heven y).symm
    conv_lhs => rw [this]
    rw [deriv_comp_neg, neg_neg]
  have h0 : deriv ξ 0 = 0 := by
    have := hodd 0; rw [neg_zero] at this; linarith
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have mixed : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |deriv ξ u + deriv ξ v| ≤ L * (u + v) := by
    intro u hu v hv
    have h1 := hpos u hu 0 h01
    have h2 := hpos v hv 0 h01
    rw [h0, sub_zero, sub_zero, abs_of_nonneg hu.1] at h1
    rw [h0, sub_zero, sub_zero, abs_of_nonneg hv.1] at h2
    linarith [abs_add_le (deriv ξ u) (deriv ξ v)]
  intro x hx y hy
  rcases le_total 0 x with hx0 | hx0 <;> rcases le_total 0 y with hy0 | hy0
  · exact hpos x ⟨hx0, hx.2⟩ y ⟨hy0, hy.2⟩
  · have := mixed x ⟨hx0, hx.2⟩ (-y) ⟨by linarith, by linarith [hy.1]⟩
    rw [hodd, ← sub_eq_add_neg] at this
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
    linarith
  · have := mixed (-x) ⟨by linarith, by linarith [hx.1]⟩ y ⟨hy0, hy.2⟩
    rw [hodd, neg_add_eq_sub, abs_sub_comm] at this
    rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith
  · have := hpos (-x) ⟨by linarith, by linarith [hx.1]⟩ (-y) ⟨by linarith, by linarith [hy.1]⟩
    rw [hodd, hodd, neg_sub_neg, neg_sub_neg, abs_sub_comm, abs_sub_comm y] at this
    exact this

/-- Nonnegative Guerra remainder with a quadratic upper bound. -/
theorem convex_remainder_bounds {ξ : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) ξ)
    (hd : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivAt ξ (deriv ξ x) x)
    (hLip : ∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1 : ℝ) 1,
      |deriv ξ x - deriv ξ y| ≤ L * |x - y|)
    {u q : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) (hq : q ∈ Icc (-1 : ℝ) 1) :
    0 ≤ ξ u - ξ q - deriv ξ q * (u - q) ∧
      ξ u - ξ q - deriv ξ q * (u - q) ≤ L / 2 * (u - q) ^ 2 := by
  constructor
  · rcases lt_trichotomy q u with h | rfl | h
    · have := hconv.le_slope_of_hasDerivAt hq hu h (hd q hq)
      rw [slope_def_field, le_div_iff₀ (by linarith)] at this
      linarith
    · simp
    · have := hconv.slope_le_of_hasDerivAt hu hq h (hd q hq)
      rw [slope_def_field, div_le_iff₀ (by linarith)] at this
      linarith
  · exact (le_abs_self _).trans (abs_taylor_one_le (by norm_num) hL
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd x (Ioo_subset_Icc_self hx)) hLip hq hu)

end

end SpinGlass.Aristotle
