import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Variation analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped BigOperators

namespace SpinGlass.Aristotle

noncomputable section

/-! ## Quantitative one-sided variation

Search tag: `PARISI_LB_VARIATION`. Keywords: Taylor remainder, near minimum,
square-root epsilon, sixth-root epsilon, short mass interval, coupling lambda.

Consumers: (14.264), (14.283), and coupling optimization in Sections 14.8-14.10.
The endpoint comparison in the square-root estimate is essential when the
available mass interval is short. It comes from fixed-level minimality.
-/

/-- Algebraic core of (14.264), uniform even when d tends to zero. -/
theorem slope_ge_neg_sqrt_of_near_minimum {d M ε s : ℝ}
    (hd : 0 < d) (hM : 0 < M) (hε : 0 ≤ ε)
    (hend : 0 ≤ d * s + M * d ^ 2)
    (hnear : ∀ t ∈ Icc (0 : ℝ) d, -ε ≤ t * s + M * t ^ 2) :
    -(2 * Real.sqrt (M * ε)) ≤ s := by
  rcases le_or_gt 0 s with hs | hs
  · linarith [Real.sqrt_nonneg (M * ε)]
  have hsd : -s ≤ M * d := by nlinarith
  have ht := hnear (-s / (2 * M)) ⟨div_nonneg (by linarith) (by positivity), by
    rw [div_le_iff₀ (by positivity)]; nlinarith⟩
  have key : s ^ 2 ≤ (2 * Real.sqrt (M * ε)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp at ht
    nlinarith
  exact (abs_le_of_sq_le_sq' key (by positivity)).1

/-- Consumer form of the preceding estimate, with the split functional explicit. -/
theorem split_slope_ge_neg_sqrt {Φ : ℝ → ℝ} {a b M ε s : ℝ}
    (hab : a < b) (hM : 0 < M) (hε : 0 ≤ ε)
    (hend : Φ a ≤ Φ b)
    (hnear : ∀ m ∈ Icc a b, Φ a - ε ≤ Φ m)
    (htaylor : ∀ m ∈ Icc a b,
      Φ m ≤ Φ a + (m - a) * s + M * (m - a) ^ 2) :
    -(2 * Real.sqrt (M * ε)) ≤ s := by
  refine slope_ge_neg_sqrt_of_near_minimum (d := b - a) (by linarith) hM hε ?_ ?_
  · linarith [htaylor b ⟨hab.le, le_rfl⟩]
  · rintro t ⟨ht0, htd⟩
    have hm : a + t ∈ Icc a b := ⟨by linarith, by linarith⟩
    have h1 := hnear _ hm
    have h2 := htaylor _ hm
    simp only [add_sub_cancel_left] at h2
    linarith

/-- The two interval-length cases in (14.283), with ρ playing the role of ε^(1/6).
For the first level, provide ρ ≤ q-a; for other levels, provide f(a)=0. -/
theorem curvature_ge_of_cubic_remainder {f : ℝ → ℝ} {a q c M δ ρ : ℝ}
    (haq : a < q) (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hρ : 0 < ρ)
    (hlower : ∀ u ∈ Icc a q, -δ ≤ f u)
    (htaylor : ∀ u ∈ Icc a q,
      f u ≤ c / 2 * (u - q) ^ 2 + M * |u - q| ^ 3)
    (hend : ρ ≤ q - a ∨ f a = 0) :
    -c ≤ 2 * δ / ρ ^ 2 + 2 * M * ρ := by
  have short : ρ ≤ q - a → -c ≤ 2 * δ / ρ ^ 2 + 2 * M * ρ := by
    intro h
    have hu : q - ρ ∈ Icc a q := ⟨by linarith, by linarith⟩
    have h1 := (hlower _ hu).trans (htaylor _ hu)
    rw [show q - ρ - q = -ρ by ring, abs_neg, abs_of_pos hρ] at h1
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith
  rcases hend with h | h
  · exact short h
  rcases le_or_gt ρ (q - a) with h' | h'
  · exact short h'
  have h1 := htaylor a ⟨le_rfl, haq.le⟩
  rw [h, abs_sub_comm, abs_of_pos (by linarith)] at h1
  have : -c ≤ 2 * M * (q - a) := by
    have hqa : 0 < q - a := by linarith
    have : 0 ≤ (q - a) ^ 2 * (c + 2 * M * (q - a)) := by rw [sub_sq'] at h1; nlinarith
    nlinarith [(mul_nonneg_iff_of_pos_left (by positivity : (0:ℝ) < (q - a) ^ 2)).1 this]
  have : 0 ≤ 2 * δ / ρ ^ 2 := by positivity
  nlinarith

/-- Choose a coupling of the correct sign to obtain a quadratic gain. -/
theorem exists_quadratic_gain {B : ℝ → ℝ} {A d L r : ℝ}
    (hL : 0 < L) (hr : 0 ≤ r) (hd : |d| ≤ L * r)
    (hB : ∀ lam ∈ Icc (-r) r, B lam ≤ A + d * lam + L / 2 * lam ^ 2) :
    ∃ lam ∈ Icc (-r) r, B lam ≤ A - d ^ 2 / (2 * L) := by
  have hmem : -d / L ∈ Icc (-r) r := by
    rw [mem_Icc, le_div_iff₀ hL, div_le_iff₀ hL]
    constructor <;> linarith [abs_le.1 hd]
  refine ⟨-d / L, hmem, (hB _ hmem).trans (le_of_eq ?_)⟩
  field_simp
  ring

/-- Strict improvement from a nonzero derivative, within the permitted coupling range. -/
theorem exists_strict_gain_of_deriv_ne_zero {B : ℝ → ℝ} {d r : ℝ}
    (hB : HasDerivAt B d 0) (hd : d ≠ 0) (hr : 0 < r) :
    ∃ lam ∈ Ioo (-r) r, B lam < B 0 := by
  by_contra! h
  refine hd (IsLocalMin.hasDerivAt_eq_zero ?_ hB)
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 hr) hr] with x hx using h x hx

end

end SpinGlass.Aristotle
