import SpinGlass.Parisi.Coupled.CoupledRootComparison

/-!
# Root pressure gain and its uniform nearby estimate

The initial nonnegative-overlap pressure gain follows by taking the actual
positive inserted-mass limit of the finite-volume comparison. The nearby
quadratic bound uses the already proved root response separation, with
tolerance and radius selected before MIN parameters, volume and time.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The initial-interval pressure gain, with the zero inserted-mass
limit proved from positive comparisons rather than assumed as an API input. -/
theorem randomFieldParisiAuxPairPressure_root_le_gain {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (0 : ℝ) (qs 0))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
      2 * parisiInterpolationBracket μh ξ ms qs t - parisiRootResponseGap μh ξ ms qs t u ^ 2 / 2 := by
  let v := t * (deriv ξ (qs 0) - deriv ξ u)
  let F := fun m : ℝ => 2 * Real.log 2 + 2 * parisiRootCouplingZeroValue μh ξ ms qs v m -
    (parisiRootCouplingMoment μh ξ ms qs v m - u) ^ 2 / 2 -
    t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ u)) -
    parisiAuxTerminalVar ξ qs t
  have hVal := continuousAt_parisiRootCouplingZeroValue_zero hμ ξ ms qs v
  have hMom := continuousAt_parisiRootCouplingMoment_zero (μh := μh) ξ ms qs v
  have hFc : ContinuousAt F 0 := by dsimp only [F]; fun_prop
  have ha : 0 < mExt ms 1 := hm.mExt_pos (by norm_num)
  have hsmall0 : ∀ᶠ m : ℝ in 𝓝 0, m < mExt ms 1 := Iio_mem_nhds ha
  have hsmall : ∀ᶠ m : ℝ in 𝓝[>] 0, m < mExt ms 1 :=
    hsmall0.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ m : ℝ in 𝓝[>] 0, 0 < m := self_mem_nhdsWithin
  have hbound : ∀ᶠ m : ℝ in 𝓝[>] 0,
      randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤ F m := by
    filter_upwards [hsmall, hpos] with m hmr hm0
    exact randomFieldParisiAuxPairPressure_root_le_mass_gain hμ hN hξ ms qs hm hq ht hu hm0 hmr.le G₀ hreach
  have hle := ge_of_tendsto (hFc.tendsto.mono_left nhdsWithin_le_nhds) hbound
  have hv := parisi_root_time_variance_mem_Icc hξ qs hq ht hu
  dsimp only [F] at hle
  rw [parisiRootCouplingZeroValue_zero hμ ξ ms qs hv, parisiRootCouplingMoment_zero ξ ms qs] at hle
  simp only [zero_mul, add_zero] at hle
  unfold parisiInterpolationBracket parisiSplitBracket parisiRootResponseGap
  dsimp only [v] at hle
  linarith

/-- The nearby root part of the main estimate, uniform in every
finite-volume Gaussian realization and time below the fixed cutoff.
The negative-overlap and far initial-interval cases remain separate. -/
theorem exists_uniform_randomFieldParisiAuxPairPressure_root_near_gap {μh : Measure ℝ}
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
          ∀ u ∈ Icc (0 : ℝ) (qs 0), qs 0 - u ≤ ρ →
            (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
            randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
              2 * parisiInterpolationBracket μh ξ ms qs t - (1 - t₀) ^ 2 * (u - qs 0) ^ 2 / 32 := by
  obtain ⟨ε, hε, ρ, hρ, hgap⟩ := exists_uniform_parisi_critical_response_gap hξ hμ ht₀
  refine ⟨ε, hε, ρ, hρ, ?_⟩
  intro k ms qs hm hmin hfull hnear N hN Ω _ Pm _ t ht G₀ u hu hdist hreach
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2.le⟩
  have hb := randomFieldParisiAuxPairPressure_root_le_gain hμ.integrable_id hN hξ ms qs hm hmin.1 ht01 hu G₀ hreach
  have hg := (hgap k ms qs hm hmin hfull hnear t ht).1 u hu hdist
  have hnonneg : 0 ≤ (1 - t₀) / 4 * (qs 0 - u) :=
    mul_nonneg (by linarith [ht₀.2]) (sub_nonneg.2 hu.2)
  have hsquare := mul_self_le_mul_self hnonneg hg
  nlinarith

end SpinGlass
