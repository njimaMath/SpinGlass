import SpinGlass.Parisi.Coupled.CoupledCanonicalFieldComparison
import SpinGlass.Parisi.Coupled.CoupledCanonicalSignedGap

/-!
# Physical pressure strictness outside neighboring overlaps

The canonical equality exclusion is applied to the original finite-volume
auxiliary pressure using proved Gaussian-law, recursion and normalization
bridges. At each fixed time and overlap its positive gap is chosen before
the volume and the Gaussian probability realization. Uniformity over time
and separated overlaps is a subsequent compactness argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The physical application of the equality exclusion in Proposition
14.8.6. At each positive interior time and outside overlap, except the
initial interval of Proposition 14.8.3, a positive gap works for every
volume and disorder realization under the original i.i.d. field law. -/
theorem exists_randomFieldParisiAuxPairPressure_outside_point_gap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hq0 : 0 < qs 0) (hq1 : qs (Fin.last k) < 1)
    (r : Fin (k + 1)) {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Icc (-1 : ℝ) 1)
    (hfar : u < qExt qs r.val ∨ qExt qs (r.val + 2) < u)
    (hexception : ¬(r.val = 0 ∧ |u| ≤ qs 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
      (Pm : Measure Ω) [IsProbabilityMeasure Pm],
    ∀ G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
    (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
    randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u G₀ ≤
      2 * parisiInterpolationBracket μh ξ ms qs t - δ := by
  classical
  obtain ⟨p, hp, hgap⟩ := exists_randomFieldPairColeHopfListValue_parisiCanonical_outside_gap
    hμ hξ ms qs hm hq hq0 hq1 r ht hu hfar hexception
  let δ := 2 * (∫ h, closedParisiX₀ ξ ms qs h ∂μh) - randomFieldPairColeHopfListValue μh
    (parisiCanonicalPairLevels ξ ms qs (decide (u < 0)) r p t |u|)
  have hδ : 0 < δ := sub_pos.2 hgap
  refine ⟨δ, hδ, ?_⟩
  intro N hN Ω _ Pm _ G₀ hreach
  have hsign : (if decide (u < 0) then -|u| else |u|) = u := by
    by_cases hn : u < 0
    · simp [hn, abs_of_neg hn]
    · simp [hn, abs_of_nonneg (le_of_not_gt hn)]
  have hreach' : ∃ σ : Fin 2 → Config N,
      overlap N (σ 0) (σ 1) = if decide (u < 0) then -|u| else |u| := by
    simpa only [hsign] using hreach
  have hb := randomFieldParisiAuxPairPressure_le_parisiCanonical hμ hN hξ ms qs hm hq
    (decide (u < 0)) r p ⟨ht.1.le, ht.2.le⟩ hp G₀ hreach'
  rw [hsign] at hb
  unfold parisiInterpolationBracket parisiSplitBracket
  dsimp only [δ]
  linarith

end SpinGlass
