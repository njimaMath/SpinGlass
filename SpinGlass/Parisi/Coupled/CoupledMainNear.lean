import SpinGlass.Parisi.Coupled.CoupledOriginalPressure

/-!
# Nearby main-estimate cases for the original physical pressure

The original k-level constrained auxiliary pressure satisfies the quadratic
near-overlap penalty. All Gaussian-law, inserted-level and terminal-mass
identifications are proved, and the tolerance and radius precede the MIN
parameters, finite volume, probability realization and interpolation time.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

theorem randomFieldParisiAuxPairPressure_outer_le_gain {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 1) t u G₀ ≤
      2 * parisiInterpolationBracket μh ξ ms qs t - parisiLeftResponseGap μh ξ ms qs p t u ^ 2 / 2 := by
  have hb := randomFieldParisiSplitPressure_outer_le_gain hμ hN hξ ms qs p hm hq ht hu G₀ hreach
  rw [randomFieldParisiAuxPairPressure_outer_eq hμ hN ξ ms qs p u hm ht G₀ hreach]
  unfold parisiInterpolationBracket
  linarith

theorem randomFieldParisiAuxPairPressure_inner_le_gain {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p.castSucc) (qs p.succ))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 2) t u G₀ ≤
      2 * parisiInterpolationBracket μh ξ ms qs t - parisiRightResponseGap μh ξ ms qs p t u ^ 2 / 2 := by
  have hb := randomFieldParisiSplitPressure_inner_le_gain hμ hN hξ ms qs p hm hq ht hu G₀ hreach
  rw [randomFieldParisiAuxPairPressure_inner_eq hμ hN ξ ms qs p u hm ht G₀ hreach]
  unfold parisiInterpolationBracket
  linarith

/-- The near-overlap part of Theorem 14.5.7 for the original physical
auxiliary cascade. The terminal outer interval and k=0 are included; the
root interval, far cases and probabilistic localization are separate. -/
theorem exists_uniform_randomFieldParisiAuxPairPressure_near_gap {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
        ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
        IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
          (parisiParameterDomain k) (ms, qs) →
        randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
        ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
          (Pm : Measure Ω) [IsProbabilityMeasure Pm], ∀ t ∈ Icc (0 : ℝ) t₀,
          ∀ G₀ : GaussianField (α := Config N) Pm
            (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
          (∀ p : Fin k, ∀ u ∈ Icc (qs p.castSucc) (qs p.succ), qs p.succ - u ≤ ρ →
            (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
            randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 2) t u G₀ ≤
              2 * parisiInterpolationBracket μh ξ ms qs t - (1 - t₀) ^ 2 * (u - qs p.succ) ^ 2 / 32) ∧
          (∀ p : Fin (k + 1), ∀ u ∈ Icc (qs p) (qExt qs (p.val + 2)), u - qs p ≤ ρ →
            (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
            randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 1) t u G₀ ≤
              2 * parisiInterpolationBracket μh ξ ms qs t - (1 - t₀) ^ 2 * (u - qs p) ^ 2 / 32) := by
  obtain ⟨ε, hε, ρ, hρ, hgap⟩ := exists_uniform_randomFieldParisiSplitPressure_near_gap hξ hμ ht₀
  refine ⟨ε, hε, ρ, hρ, ?_⟩
  intro k ms qs hm hmin hfull hnear N hN Ω _ Pm _ t ht G₀
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2.le⟩
  have hg := hgap k ms qs hm hmin hfull hnear N hN Ω Pm t ht G₀
  constructor
  · intro p u hu hdist hreach
    have hb := hg.1 p u hu hdist hreach
    rw [randomFieldParisiAuxPairPressure_inner_eq hμ.integrable_id hN ξ ms qs p u hm ht01 G₀ hreach]
    unfold parisiInterpolationBracket
    linarith
  · intro p u hu hdist hreach
    have hb := hg.2 p u hu hdist hreach
    rw [randomFieldParisiAuxPairPressure_outer_eq hμ.integrable_id hN ξ ms qs p u hm ht01 G₀ hreach]
    unfold parisiInterpolationBracket
    linarith

end SpinGlass
