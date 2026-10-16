import SpinGlass.Parisi.Analytic.Profile
import SpinGlass.Parisi.Minimizer.QVariation.Parameters

/-!
# The Guerra profile remainder under Talagrand's assumptions

Monotonicity of the second derivative on the positive interval and
evenness give a uniform quadratic remainder on the full overlap interval.
No positive second derivative at zero or global differentiability is assumed.
-/

open Set

namespace SpinGlass

/-- Evenness extends the actual profile derivative to negative overlaps. -/
theorem TalagrandXiCondition.hasDeriv_signed {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasDerivAt ξ (deriv ξ x) x := by
  rcases le_total 0 x with h0 | h0
  · exact hξ.hasDeriv x ⟨h0, hx.2⟩
  · have hn : -x ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [hx.1]⟩
    have hh := (hξ.hasDeriv (-x) hn).comp x (hasDerivAt_id x).neg
    have he : (fun y : ℝ => ξ (-y)) = ξ := funext hξ.even
    change HasDerivAt (fun y => ξ (-y)) _ x at hh
    rw [he] at hh
    exact hh.differentiableAt.hasDerivAt

/-- A profile-only Lipschitz bound for the first derivative, including
opposite signs and the possibly degenerate curvature at zero. -/
theorem TalagrandXiCondition.abs_deriv_sub_le {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {x y : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (hy : y ∈ Icc (-1 : ℝ) 1) :
    |deriv ξ x - deriv ξ y| ≤ deriv (deriv ξ) 1 * |x - y| := by
  have hL : 0 ≤ deriv (deriv ξ) 1 :=
    (hξ.second_pos 1 ⟨zero_le_one, le_rfl⟩ one_ne_zero).le
  apply Aristotle.lipschitz_deriv_even_extension hξ.even hL
    (fun z hz => (hξ.hasDeriv z hz).differentiableAt) _ x hx y hy
  exact Aristotle.lipschitz_deriv_of_monotone_second hξ.deriv_continuous
    (fun z hz => (hξ.hasDeriv_deriv z ⟨hz.1.le, hz.2.le⟩).differentiableAt)
    hξ.monotoneOn_second (fun z hz =>
      (hξ.second_pos z ⟨hz.1.le, hz.2⟩ (ne_of_gt hz.1)).le)

/-- The actual signed-overlap profile remainder. -/
noncomputable def parisiProfileRemainder (ξ : ℝ → ℝ) (u q : ℝ) : ℝ :=
  ξ u - ξ q - deriv ξ q * (u - q)

/-- Both signs of the overlap have a nonnegative remainder bounded
by the profile curvature at one times half the squared error. -/
theorem TalagrandXiCondition.profileRemainder_bounds {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {u q : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) (hq : q ∈ Icc (-1 : ℝ) 1) :
    0 ≤ parisiProfileRemainder ξ u q ∧
      parisiProfileRemainder ξ u q ≤ deriv (deriv ξ) 1 / 2 * (u - q) ^ 2 := by
  apply Aristotle.convex_remainder_bounds
    (hξ.second_pos 1 ⟨zero_le_one, le_rfl⟩ one_ne_zero).le
    (hξ.convex.subset (subset_univ _) (convex_Icc _ _))
    (fun _ hx => hξ.hasDeriv_signed hx)
    (fun _ hx _ hy => hξ.abs_deriv_sub_le hx hy) hu hq

end SpinGlass
