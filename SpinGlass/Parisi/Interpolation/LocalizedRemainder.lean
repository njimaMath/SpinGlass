import SpinGlass.Parisi.Interpolation.ProfileRemainder
import SpinGlass.Parisi.Localization.SecondMoment

/-!
# Localization bounds for the physical Guerra remainder

The remainder is the profile defect averaged against the exact joint
overlap and meeting masses. Its derivative interpretation is a separate
interpolation identity; every bound here concerns the concrete observable.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The normalized profile defect in the Guerra derivative formula. -/
noncomputable def parisiGuerraRemainder (N : ℕ) (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ r : Fin (k + 1), ∑ u ∈ parisiOverlapValues N,
    parisiProfileRemainder ξ u (qs r) * parisiBranchMeetingMass N μh ξ ms qs r t u

theorem parisiGuerraRemainder_nonneg
    {N k : ℕ} (μh : Measure ℝ) [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) (t : ℝ) :
    0 ≤ parisiGuerraRemainder N μh ξ ms qs t := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro r _
  apply Finset.sum_nonneg
  intro u hu
  exact mul_nonneg (hξ.profileRemainder_bounds (parisiOverlapValues_mem_Icc hu)
    ⟨by linarith [(hq.mem_Icc r).1], (hq.mem_Icc r).2⟩).1
    (parisiBranchMeetingMass_nonneg μh ξ ms qs hm r t u)

theorem parisiGuerraRemainder_le_second_moment
    {N k : ℕ} (μh : Measure ℝ) [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) (t : ℝ) :
    parisiGuerraRemainder N μh ξ ms qs t ≤
      deriv (deriv ξ) 1 / 4 *
        ∑ r : Fin (k + 1), parisiBranchSecondMoment N μh ξ ms qs r t := by
  have hh : (∑ r : Fin (k + 1), ∑ u ∈ parisiOverlapValues N,
      parisiProfileRemainder ξ u (qs r) * parisiBranchMeetingMass N μh ξ ms qs r t u) ≤
      ∑ r : Fin (k + 1), ∑ u ∈ parisiOverlapValues N,
        (deriv (deriv ξ) 1 / 2 * (u - qs r) ^ 2) *
          parisiBranchMeetingMass N μh ξ ms qs r t u := by
    apply Finset.sum_le_sum
    intro r _
    apply Finset.sum_le_sum
    intro u hu
    exact mul_le_mul_of_nonneg_right
      (hξ.profileRemainder_bounds (parisiOverlapValues_mem_Icc hu)
        ⟨by linarith [(hq.mem_Icc r).1], (hq.mem_Icc r).2⟩).2
      (parisiBranchMeetingMass_nonneg μh ξ ms qs hm r t u)
  have hc := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  simp_rw [mul_assoc, ← Finset.mul_sum] at hc
  calc
    _ ≤ (1 / 2 : ℝ) * (deriv (deriv ξ) 1 / 2 *
        ∑ r : Fin (k + 1), parisiBranchSecondMoment N μh ξ ms qs r t) := hc
    _ = _ := by ring

/-- A profile-only coarse remainder bound, uniform in the parameters,
field law, interpolation time and volume. -/
theorem parisiGuerraRemainder_le_curvature
    {N k : ℕ} (μh : Measure ℝ) [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) (t : ℝ) :
    parisiGuerraRemainder N μh ξ ms qs t ≤ deriv (deriv ξ) 1 := by
  have hL := (hξ.second_pos 1 ⟨zero_le_one, le_rfl⟩ one_ne_zero).le
  have hh := mul_le_mul_of_nonneg_left
    (sum_parisiBranchSecondMoment_le_four (N := N) μh ξ ms qs hm hq t)
    (div_nonneg hL (by norm_num : (0 : ℝ) ≤ 4))
  have hb := parisiGuerraRemainder_le_second_moment (N := N) μh hξ ms qs hm hq t
  nlinarith only [hb, hh]

/-- The localized concrete remainder bound with the required MIN
tolerance and accuracy quantifiers. -/
theorem exists_uniform_parisiGuerraRemainder_bound
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hPSD : ∀ N : ℕ, (overlapCovMatrix N ξ).PosSemidef)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ᵐ h ∂μh, |h| ≤ R)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + δ →
      ∃ C : ℝ, 0 < C ∧ ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc (0 : ℝ) t₀,
        parisiGuerraRemainder N μh ξ ms qs t ≤
          C * (max (parisiInterpolationBracket μh ξ ms qs t -
            parisiInterpolationPressure N μh ξ ms qs t) 0 + ε) := by
  obtain ⟨δ, hδ, hloc⟩ :=
    exists_uniform_parisiBranchMeetingMass_localization hμ hξ hPSD hR hbound ht₀
  refine ⟨δ, hδ, ?_⟩
  intro k ms qs hm hmin hfull hvalue
  obtain ⟨K, hK, hlocal⟩ := hloc k ms qs hm hmin hfull hvalue
  have hL : 0 < deriv (deriv ξ) 1 / 4 :=
    div_pos (hξ.second_pos 1 ⟨zero_le_one, le_rfl⟩ one_ne_zero) (by norm_num)
  refine ⟨deriv (deriv ξ) 1 / 4 * (K + 1), mul_pos hL (by linarith), ?_⟩
  intro ε hε
  filter_upwards [eventually_sum_parisiBranchSecondMoment_le_of_localization
    μh ξ ms qs hm hmin.1 hK hlocal ε hε] with N hN t ht
  have hh := mul_le_mul_of_nonneg_left (hN t ht) hL.le
  rw [← mul_assoc] at hh
  exact (parisiGuerraRemainder_le_second_moment μh hξ ms qs hm hmin.1 t).trans hh

end SpinGlass
