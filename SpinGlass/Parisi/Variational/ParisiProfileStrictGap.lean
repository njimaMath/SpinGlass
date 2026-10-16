import SpinGlass.Parisi.Variational.ParisiProfileRemainder
import Mathlib.Topology.Order.Compact

/-!
# Uniform strict tangent gaps for the preserved profile

Strict monotonicity of the profile derivative gives a positive tangent
remainder at distinct points. Compactness makes it uniform at any fixed
positive separation, including a point at zero.
-/

open Set

namespace SpinGlass

/-- Strict convexity follows from the named profile contract on its
closed overlap interval, including zero curvature at zero. -/
theorem TalagrandXiCondition.strictConvexOn {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1) ξ := by
  exact (hξ.strictMonoOn_deriv.mono interior_subset).strictConvexOn_of_deriv (convex_Icc (0 : ℝ) 1)
    (fun x hx => (hξ.hasDeriv x hx).continuousAt.continuousWithinAt)

/-- At any two distinct admissible overlaps the actual tangent
remainder is strictly positive, with no curvature hypothesis at zero. -/
theorem TalagrandXiCondition.tangent_remainder_pos {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {q u : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) (hqu : q ≠ u) :
    0 < ξ u - ξ q - (u - q) * deriv ξ q := by
  rcases lt_or_gt_of_ne hqu with hqu | huq
  · have hs := hξ.strictConvexOn.lt_slope_of_hasDerivAt hq hu hqu (hξ.hasDeriv q hq)
    have hh := mul_lt_mul_of_pos_right hs (sub_pos.2 hqu)
    have he : slope ξ q u * (u - q) = ξ u - ξ q := by
      rw [mul_comm, ← smul_eq_mul]
      exact sub_smul_slope ξ q u
    rw [he] at hh
    linarith
  · have hs := hξ.strictConvexOn.slope_lt_of_hasDerivAt hu hq huq (hξ.hasDeriv q hq)
    have hh := mul_lt_mul_of_pos_right hs (sub_pos.2 huq)
    have he : slope ξ u q * (q - u) = ξ q - ξ u := by
      rw [mul_comm, ← smul_eq_mul]
      exact sub_smul_slope ξ u q
    rw [he] at hh
    nlinarith

/-- The strict tangent gap is uniform over all admissible pairs a
fixed positive distance apart; its constant depends only on the profile
and the distance, before any MIN parameters are chosen. -/
theorem TalagrandXiCondition.exists_uniform_tangent_gap {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      ρ ≤ |u - q| → γ ≤ ξ u - ξ q - (u - q) * deriv ξ q := by
  let S : Set (ℝ × ℝ) := (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ∩ {s | ρ ≤ |s.2 - s.1|}
  let F : ℝ × ℝ → ℝ := fun s => ξ s.2 - ξ s.1 - (s.2 - s.1) * deriv ξ s.1
  have hcompact : IsCompact S := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_const (continuous_snd.sub continuous_fst).abs)
  have hξc : ContinuousOn ξ (Icc (0 : ℝ) 1) :=
    fun x hx => (hξ.hasDeriv x hx).continuousAt.continuousWithinAt
  have hξdc : ContinuousOn (deriv ξ) (Icc (0 : ℝ) 1) :=
    fun x hx => (hξ.hasDeriv_deriv x hx).continuousAt.continuousWithinAt
  have hF : ContinuousOn F S :=
    ((hξc.comp continuous_snd.continuousOn (fun _ hs => hs.1.2)).sub
      (hξc.comp continuous_fst.continuousOn (fun _ hs => hs.1.1))).sub
        ((continuous_snd.sub continuous_fst).continuousOn.mul
          (hξdc.comp continuous_fst.continuousOn (fun _ hs => hs.1.1)))
  have hpos (s : ℝ × ℝ) (hs : s ∈ S) : 0 < F s := by
    apply hξ.tangent_remainder_pos hs.1.1 hs.1.2
    intro heq
    have hh : ρ ≤ |s.2 - s.1| := hs.2
    rw [heq, sub_self, abs_zero] at hh
    linarith
  by_cases hS : S.Nonempty
  · obtain ⟨s, hs, hmin⟩ := hcompact.exists_isMinOn hS hF
    refine ⟨F s, hpos s hs, ?_⟩
    intro q hq u hu hdist
    exact hmin (show (q, u) ∈ S from ⟨⟨hq, hu⟩, hdist⟩)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro q hq u hu hdist
    exact (hS ⟨(q, u), ⟨⟨hq, hu⟩, hdist⟩⟩).elim

end SpinGlass
