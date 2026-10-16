import SpinGlass.Parisi.Coupled.CoupledMainOutsideCompact

/-!
# One physical gap for all separated outside regions

Concrete closed outside regions are compact, including time zero.
A finite minimum over the original overlap levels gives one positive
gap before all times, overlaps, volumes and Gaussian realizations in
these regions. The neighboring boundaries and initial root strip are
retained as the other cases of the full main estimate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The compact outside gaps can be chosen uniformly over all original
levels, before every volume and Gaussian realization. -/
theorem exists_uniform_randomFieldParisiAuxPairPressure_outside_compact_all_levels
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (s : Fin (k + 1) → Set (ℝ × ℝ))
    (hs : ∀ r, IsCompact (s r)) (ht : ∀ r x, x ∈ s r → x.1 ∈ Icc (0 : ℝ) t₀)
    (hu : ∀ r x, x ∈ s r → x.2 ∈ Icc (-1 : ℝ) 1)
    (hfar : ∀ r x, x ∈ s r → x.2 < qExt qs r.val ∨ qExt qs (r.val + 2) < x.2)
    (hexception : ∀ r x, x ∈ s r → ¬(r.val = 0 ∧ |x.2| ≤ qs 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : Fin (k + 1), ∀ t u : ℝ, (t, u) ∈ s r →
      ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
        (Pm : Measure Ω) [IsProbabilityMeasure Pm],
      ∀ G₀ : GaussianField (α := Config N) Pm
        (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
      (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
      randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u G₀ ≤
        2 * parisiInterpolationBracket μh ξ ms qs t - δ := by
  classical
  have hex (r : Fin (k + 1)) := exists_uniform_randomFieldParisiAuxPairPressure_outside_compact_gap
    hμ hξ ms qs hm hmin r ht₀ (s r) (hs r) (ht r) (hu r) (hfar r) (hexception r)
  choose d hd hbound using hex
  obtain ⟨δ, hδ, hδr⟩ := exists_uniform_positive_lower_bound_of_finite d hd
  refine ⟨δ, hδ, ?_⟩
  intro r t u htu N hN Ω _ Pm _ G₀ hreach
  exact (hbound r t u htu N hN Ω Pm G₀ hreach).trans
    (sub_le_sub_left (hδr r) _)

def parisiOutsideCompactRegion {k : ℕ} (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (t₀ ρ : ℝ) : Set (ℝ × ℝ) :=
  (Icc (0 : ℝ) t₀ ×ˢ Icc (-1 : ℝ) 1) ∩
    {x | x.2 + ρ ≤ qExt qs r.val ∨ qExt qs (r.val + 2) + ρ ≤ x.2} ∩
    {x | r.val = 0 → qs 0 + ρ ≤ |x.2|}

theorem isCompact_parisiOutsideCompactRegion {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) (t₀ ρ : ℝ) :
    IsCompact (parisiOutsideCompactRegion qs r t₀ ρ) := by
  have hfar : IsClosed {x : ℝ × ℝ |
      x.2 + ρ ≤ qExt qs r.val ∨ qExt qs (r.val + 2) + ρ ≤ x.2} :=
    (isClosed_le (continuous_snd.add continuous_const) continuous_const).union
      (isClosed_le continuous_const continuous_snd)
  have hroot : IsClosed {x : ℝ × ℝ | r.val = 0 → qs 0 + ρ ≤ |x.2|} := by
    by_cases hr : r.val = 0
    · simpa only [hr, true_implies] using isClosed_le
        (continuous_const (y := qs 0 + ρ)) continuous_snd.abs
    · simpa only [hr, false_implies, ofPred_true] using isClosed_univ (X := ℝ × ℝ)
  exact ((isCompact_Icc.prod isCompact_Icc).inter_right hfar).inter_right hroot

/-- One positive pressure gap works on every separated outside region
of every original level, including time zero and k=0. Its remaining root
strip and neighboring-boundary cases are separate main-estimate inputs. -/
theorem exists_uniform_randomFieldParisiAuxPairPressure_outside_separated_gap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs)
    {t₀ ρ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : Fin (k + 1), ∀ t ∈ Icc (0 : ℝ) t₀,
      ∀ u ∈ Icc (-1 : ℝ) 1,
      (u + ρ ≤ qExt qs r.val ∨ qExt qs (r.val + 2) + ρ ≤ u) →
      (r.val = 0 → qs 0 + ρ ≤ |u|) →
      ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
        (Pm : Measure Ω) [IsProbabilityMeasure Pm],
      ∀ G₀ : GaussianField (α := Config N) Pm
        (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
      (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
      randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u G₀ ≤
        2 * parisiInterpolationBracket μh ξ ms qs t - δ := by
  have hex := exists_uniform_randomFieldParisiAuxPairPressure_outside_compact_all_levels
    hμ hξ ms qs hm hmin ht₀ (fun r => parisiOutsideCompactRegion qs r t₀ ρ)
    (fun r => isCompact_parisiOutsideCompactRegion qs r t₀ ρ)
    (fun _ _ hx => hx.1.1.1) (fun _ _ hx => hx.1.1.2)
    (fun r x hx => by
      rcases hx.1.2 with hleft | hright
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith))
    (fun r x hx he => by
      have hh := hx.2 he.1
      linarith [he.2])
  obtain ⟨δ, hδ, hb⟩ := hex
  refine ⟨δ, hδ, ?_⟩
  intro r t ht u hu hfar hroot N hN Ω _ Pm _ G₀ hreach
  exact hb r t u ⟨⟨⟨ht, hu⟩, hfar⟩, hroot⟩ N hN Ω Pm G₀ hreach

end SpinGlass
