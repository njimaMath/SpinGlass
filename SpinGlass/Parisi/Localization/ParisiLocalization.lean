import SpinGlass.Parisi.Analytic.Localization
import SpinGlass.Parisi.Localization.OverlapValues
import SpinGlass.Parisi.Coupled.CoupledMainEstimate

/-!
# Uniform localization of the original branch-meeting masses

The quadratic main estimate supplies a fixed pressure gap on the bad
overlap set. Concentration and the linear overlap count then give one
volume threshold uniform in interpolation time and meeting level.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The joint mass of bad overlaps and the specified meeting level,
as the finite sum of its exact physical overlap atoms. -/
noncomputable def parisiBadOverlapMass (N : ℕ) (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (r : Fin (k + 1)) (t a : ℝ) : ℝ :=
  ∑ u ∈ (parisiOverlapValues N).filter (fun u => a ≤ (u - qs r) ^ 2),
    parisiBranchMeetingMass N μh ξ ms qs r t u

/-- The concrete concentration estimate turns a uniform main estimate
into uniform localization. No sign assumption on the pressure difference
is needed for this implication. -/
theorem eventually_parisiBadOverlapMass_le_of_main_estimate
    {k : ℕ} (μh : Measure ℝ) [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hPSD : ∀ N : ℕ, (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : qs ∈ parisiOverlapDomain k)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ᵐ h ∂μh, |h| ≤ R)
    {t₀ K : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (hK : 0 < K)
    (hmain : ∀ N : ℕ, 0 < N → ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) t₀),
      ∀ r : Fin (k + 1), ∀ u ∈ parisiOverlapValues N,
        randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u
          (GaussianField.ofMultivariateGaussian
            (posSemidef_overlapCovMatrix_parisiTimeProfile (hPSD N) ht.1)) ≤
          2 * parisiInterpolationBracket μh ξ ms qs t - (u - qs r) ^ 2 / K) :
    ∀ ε > 0, ∀ᶠ N in atTop, ∀ t ∈ Icc (0 : ℝ) t₀, ∀ r : Fin (k + 1),
      parisiBadOverlapMass N μh ξ ms qs r t
        (2 * K * (parisiInterpolationBracket μh ξ ms qs t -
          parisiInterpolationPressure N μh ξ ms qs t + ε)) ≤ ε := by
  classical
  intro ε hε
  obtain ⟨c, hc, hconcentration⟩ := exists_uniform_parisiBranchMeetingMass_exponential_bound
    μh hξ ms qs hm hq hR hbound (show 0 < 2 * ε by positivity)
  filter_upwards [Aristotle.eventually_overlap_exponential_small (C := 2) (by norm_num) hc hε,
    eventually_gt_atTop (0 : ℕ)] with N hsmall hN t ht r
  have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2.le⟩
  let bad := (parisiOverlapValues N).filter (fun u =>
    2 * K * (parisiInterpolationBracket μh ξ ms qs t -
      parisiInterpolationPressure N μh ξ ms qs t + ε) ≤ (u - qs r) ^ 2)
  have hcard : bad.card ≤ 2 * N + 1 :=
    (Finset.card_filter_le _ _).trans (card_parisiOverlapValues_le_two_mul N)
  have hbad (u : ℝ) (hu : u ∈ bad) :
      parisiBranchMeetingMass N μh ξ ms qs r t u ≤ 2 * Real.exp (-c * N) := by
    obtain ⟨hu, hfar⟩ := Finset.mem_filter.1 hu
    apply hconcentration N hN (hPSD N) t ht1 r u (mem_parisiOverlapValues_iff.1 hu)
    have hp := hmain N hN t ht r u hu
    have hdiv : 2 * (parisiInterpolationBracket μh ξ ms qs t -
        parisiInterpolationPressure N μh ξ ms qs t + ε) ≤ (u - qs r) ^ 2 / K := by
      apply (le_div_iff₀ hK).2
      nlinarith only [hfar]
    linarith only [hp, hdiv]
  exact (Aristotle.finite_overlap_sum_le bad hcard (show (0 : ℝ) ≤ 2 by norm_num) hbad).trans hsmall

/-- The bounded-site-law version of Proposition 14.5.6 for the actual
joint branch masses. The localization constant is chosen before the
auxiliary accuracy, and its volume threshold works for every time and level. -/
theorem exists_uniform_parisiBranchMeetingMass_localization
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
      ∃ K : ℝ, 0 < K ∧ ∀ ε > 0, ∀ᶠ N in atTop,
        ∀ t ∈ Icc (0 : ℝ) t₀, ∀ r : Fin (k + 1),
        parisiBadOverlapMass N μh ξ ms qs r t
          (K * (parisiInterpolationBracket μh ξ ms qs t -
            parisiInterpolationPressure N μh ξ ms qs t + ε)) ≤ ε := by
  obtain ⟨δ, hδ, hmain⟩ := exists_uniform_randomFieldParisiAuxPairPressure_main_estimate hμ hξ ht₀
  refine ⟨δ, hδ, ?_⟩
  intro k ms qs hm hmin hfull hvalue
  obtain ⟨K, hK, hp⟩ := hmain k ms qs hm hmin hfull hvalue
  refine ⟨2 * K, by positivity, ?_⟩
  apply eventually_parisiBadOverlapMass_le_of_main_estimate μh hξ hPSD ms qs hm
    (mem_parisiOverlapDomain_iff.2 ⟨hmin.1.monotone, hmin.1.2.1, hmin.1.2.2⟩)
    hR hbound ht₀ hK
  intro N hN t ht r u hu
  exact hp N hN (EnergySpace N)
    (multivariateGaussian 0 (overlapCovMatrix N (parisiTimeProfile ξ t))) t ht
    (GaussianField.ofMultivariateGaussian
      (posSemidef_overlapCovMatrix_parisiTimeProfile (hPSD N) ht.1)) r u
    (parisiOverlapValues_mem_Icc hu) (mem_parisiOverlapValues_iff.1 hu)

end SpinGlass
