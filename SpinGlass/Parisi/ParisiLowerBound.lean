import SpinGlass.Parisi.ParisiInf
import SpinGlass.Parisi.ParisiQDeriv
import SpinGlass.Parisi.ExternalFieldZero
import SpinGlass.Parisi.FieldContinuity

/-!
# The lower half of the Parisi formula and the convergence corollary

The target is Talagrand, Vol. II, Theorem 14.5.1, equation (14.102), for the
Gaussian covariance (14.55) and the i.i.d. external field in (14.65).
`TalagrandXiCondition` packages the analytic assumptions (14.101).
Positive semidefiniteness is stated separately: it expresses the existence
of the Gaussian Hamiltonian and does not follow from convexity.

The nondegenerate theorem corresponds to Theorem 14.5.2 and is the target of
the main §§14.5–14.10 argument. The general finite-second-moment theorem then
adds the zero-second-moment case by Talagrand's field-to-zero reduction.
No bounded-support or exponential-moment assumption is imposed.

The proof gap in the nondegenerate lower bound remains: it needs MIN parameters,
the main estimate, overlap localization, and the interpolation limit.
The zero-field branch is reduced to that theorem by identification of the law
with the Dirac mass at zero and uniform continuity in a constant field.
The convergence and liminf corollaries below depend on the nondegenerate placeholder.
They use the proved finite-volume Guerra bound from `ParisiInf`, retaining
its global differentiability and derivative-at-zero hypotheses explicitly.
-/

open MeasureTheory Filter Topology

namespace SpinGlass

/-- The lower half of Talagrand, Vol. II, Theorem 14.5.2, in eventual epsilon
form. Nondegeneracy means $0 < \mathbb E h^2 < \infty$, not that the field is
almost surely nonzero. This is the main §§14.5–14.10 proof obligation. -/
theorem eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_nondegenerate
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : NondegenerateExternalFieldLaw μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hPSD : ∀ N : ℕ, (overlapCovMatrix N ξ).PosSemidef) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      randomFieldParisiInf μh ξ - ε ≤ iidFieldMixedPSpinFreeEnergy N μh ξ := by
  -- TODO: Theorem 14.5.4 and the endpoint comparison (14.109), then let t₀ tend to 1.
  sorry

/-- The lower half of Talagrand, Vol. II, Theorem 14.5.1, (14.102): for every
$\varepsilon > 0$, eventually $\mathcal P(\xi,\mu_h)-\varepsilon\le p_N$.

This formulation does not assume existence of the thermodynamic limit. The
site law has finite second moment, possibly zero; the field vector and its
independence from the Gaussian disorder are built into
`iidFieldMixedPSpinFreeEnergy`. The positive-second-moment branch uses
    Theorem 14.5.2; the remaining branch uses the uniform field-to-zero reduction. -/
theorem eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h ^ 2) μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hPSD : ∀ N : ℕ, (overlapCovMatrix N ξ).PosSemidef) :
    ∀ ε > 0, ∀ᶠ N in atTop,
      randomFieldParisiInf μh ξ - ε ≤ iidFieldMixedPSpinFreeEnergy N μh ξ := by
  by_cases hpos : 0 < ∫ h, h ^ 2 ∂μh
  · exact eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_nondegenerate
      ⟨hμh, hpos⟩ hξ hPSD
  · have hzero : ∫ h, h ^ 2 ∂μh = 0 :=
      le_antisymm (le_of_not_gt hpos) (integral_nonneg fun h => sq_nonneg h)
    have hlaw : μh = Measure.dirac 0 :=
      externalFieldLaw_eq_dirac_zero_of_second_moment_eq_zero hμh hzero
    subst μh
    simp only [randomFieldParisiInf_dirac, iidFieldMixedPSpinFreeEnergy_dirac]
    intro ε hε
    let a : ℝ := ε / 4
    have ha : 0 < a := by dsimp [a]; positivity
    have hconst : NondegenerateExternalFieldLaw (Measure.dirac a) := by
      constructor
      · simp
      · simpa only [integral_dirac] using sq_pos_of_pos ha
    have hevent :=
      eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_nondegenerate
        hconst hξ hPSD (ε / 2) (by positivity)
    simp only [randomFieldParisiInf_dirac, iidFieldMixedPSpinFreeEnergy_dirac] at hevent
    filter_upwards [hevent, eventually_gt_atTop (0 : ℕ)] with N hbound hN
    have hP := (abs_le.1 (abs_parisiInf_sub_field_le hξ 0 a)).2
    have hp := (abs_le.1 (abs_mixedPSpinFreeEnergy_sub_field_le hN ξ a 0)).2
    rw [zero_sub, abs_neg, abs_of_pos ha] at hP
    rw [sub_zero, abs_of_pos ha] at hp
    dsimp [a] at hP hp
    linarith

/-- Talagrand, Vol. II, Theorem 14.5.1, equation (14.102): convergence to the
Parisi value for an i.i.d. external field with finite second moment.

This squeeze corollary uses the lower-bound proof obligations above and the
finite-volume Guerra upper bound. Global differentiability is an additional
hypothesis of the current Guerra API, not a consequence asserted here of
`TalagrandXiCondition`; its derivative-at-zero assumption is also explicit. -/
theorem tendsto_iidFieldMixedPSpinFreeEnergy_randomFieldParisiInf
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h ^ 2) μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hPSD : ∀ N : ℕ, (overlapCovMatrix N ξ).PosSemidef)
    (hdiff : Differentiable ℝ ξ) (h0 : deriv ξ 0 = 0) :
    Tendsto (fun N => iidFieldMixedPSpinFreeEnergy N μh ξ) atTop
      (𝓝 (randomFieldParisiInf μh ξ)) := by
  have hid : Integrable (fun h : ℝ => h) μh := by
    apply ((integrable_const (1 : ℝ)).add hμh).mono' measurable_id.aestronglyMeasurable
    filter_upwards [] with h
    change ‖h‖ ≤ 1 + h ^ 2
    rw [Real.norm_eq_abs]
    rcases le_total 0 h with hh | hh
    · rw [abs_of_nonneg hh]
      nlinarith [sq_nonneg (h - 1)]
    · rw [abs_of_nonpos hh]
      nlinarith [sq_nonneg (h + 1)]
  apply tendsto_order.2
  constructor
  · intro a ha
    have hε : 0 < (randomFieldParisiInf μh ξ - a) / 2 := by linarith
    filter_upwards
      [eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy
        hμh hξ hPSD _ hε] with N hN
    linarith
  · intro b hb
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact lt_of_le_of_lt
      (iidFieldMixedPSpinFreeEnergy_le_randomFieldParisiInf N hN hid ξ (hPSD N)
        hξ.convex hdiff h0) hb

/-- The liminf form of the Parisi lower bound, obtained from the convergence
corollary of Theorem 14.5.1. The extra Guerra hypotheses provide the upper
control needed for the real-valued liminf; no convergence is assumed. -/
theorem randomFieldParisiInf_le_liminf_iidFieldMixedPSpinFreeEnergy
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h ^ 2) μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hPSD : ∀ N : ℕ, (overlapCovMatrix N ξ).PosSemidef)
    (hdiff : Differentiable ℝ ξ) (h0 : deriv ξ 0 = 0) :
    randomFieldParisiInf μh ξ ≤
      Filter.liminf (fun N => iidFieldMixedPSpinFreeEnergy N μh ξ) atTop := by
  exact (tendsto_iidFieldMixedPSpinFreeEnergy_randomFieldParisiInf
    hμh hξ hPSD hdiff h0).liminf_eq.ge

end SpinGlass
