import SpinGlass.Parisi.Coupled.CoupledRootSignedComparison

/-!
# The whole initial overlap interval

The signed finite-volume comparison passes to its actual zero inserted-mass
limit. Uniform signed response separation gives the negative-overlap pressure
penalty, and combines with the proved nonnegative case at the same root.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The original signed pressure gains the square of its actual
zero-mass response gap, with every finite-volume input discharged. -/
theorem randomFieldParisiAuxPairPressure_root_signed_le_gain {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : u ∈ Icc (-(qs 0)) (0 : ℝ))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
      2 * parisiInterpolationBracket μh ξ ms qs t - parisiRootSignedResponseGap μh ξ ms qs t u ^ 2 / 2 := by
  let v := t * (deriv ξ (qs 0) - deriv ξ |u|)
  let F := fun m : ℝ => 2 * Real.log 2 + 2 * parisiRootCouplingZeroValue μh ξ ms qs v m -
    (parisiRootSignedCouplingMassMoment μh ξ ms qs t u m - u) ^ 2 / 2 -
    t * (parisiCorrection ξ ms qs + m * (parisiTheta ξ (qs 0) - parisiTheta ξ |u|)) -
    parisiAuxTerminalVar ξ qs t
  have hVal := continuousAt_parisiRootCouplingZeroValue_zero hμ ξ ms qs v
  have hMom := continuousAt_parisiRootSignedCouplingMassMoment_zero (μh := μh) ξ ms qs t u
  have hFc : ContinuousAt F 0 := by dsimp only [F]; fun_prop
  have ha : 0 < mExt ms 1 := hm.mExt_pos (by norm_num)
  have hsmall0 : ∀ᶠ m : ℝ in 𝓝 0, m < mExt ms 1 := Iio_mem_nhds ha
  have hsmall : ∀ᶠ m : ℝ in 𝓝[>] 0, m < mExt ms 1 := hsmall0.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ m : ℝ in 𝓝[>] 0, 0 < m := self_mem_nhdsWithin
  have hbound : ∀ᶠ m : ℝ in 𝓝[>] 0,
      randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤ F m := by
    filter_upwards [hsmall, hpos] with m hmr hm0
    exact randomFieldParisiAuxPairPressure_root_signed_le_mass_gain hμ hN hξ ms qs hm hq ht hu hm0 hmr.le G₀ hreach
  have hle := ge_of_tendsto (hFc.tendsto.mono_left nhdsWithin_le_nhds) hbound
  have huabs : |u| ≤ qs 0 := by rw [abs_of_nonpos hu.2]; linarith [hu.1]
  have hv := parisi_root_time_variance_mem_Icc hξ qs hq ht ⟨abs_nonneg _, huabs⟩
  dsimp only [F] at hle
  rw [parisiRootCouplingZeroValue_zero hμ ξ ms qs hv,
    parisiRootSignedCouplingMassMoment_zero hξ ms qs hq ht huabs] at hle
  simp only [zero_mul, add_zero] at hle
  unfold parisiInterpolationBracket parisiSplitBracket parisiRootSignedResponseGap
  linarith

/-- The negative initial interval has a uniform quadratic physical
pressure penalty, with the tolerance chosen before MIN, volume and time. -/
theorem exists_uniform_randomFieldParisiAuxPairPressure_root_signed_gap {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
        (Pm : Measure Ω) [IsProbabilityMeasure Pm], ∀ t ∈ Icc (0 : ℝ) t₀,
        ∀ G₀ : GaussianField (α := Config N) Pm
          (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
        ∀ u ∈ Icc (-(qs 0)) (0 : ℝ),
          (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
          randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
            2 * parisiInterpolationBracket μh ξ ms qs t - (1 - t₀) ^ 2 * (u - qs 0) ^ 2 / 8 := by
  obtain ⟨ε, hε, hgap⟩ := exists_uniform_parisi_root_signed_response_gap hξ hμ ht₀
  refine ⟨ε, hε, ?_⟩
  intro k ms qs hm hmin hfull hnear N hN Ω _ Pm _ t ht G₀ u hu hreach
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2.le⟩
  have hb := randomFieldParisiAuxPairPressure_root_signed_le_gain hμ.integrable_id hN hξ ms qs hm hmin.1 ht01 hu G₀ hreach
  have hg := hgap k ms qs hm hmin hfull hnear t ht u hu
  have hnonneg : 0 ≤ (1 - t₀) / 2 * (qs 0 - u) :=
    mul_nonneg (by linarith [ht₀.2]) (by linarith [(hmin.1.mem_Icc 0).1, hu.2])
  have hsquare := mul_self_le_mul_self hnonneg hg
  nlinarith

/-- Proposition 14.8.3's whole initial interval, including negative
overlaps, for the original physical pressure and i.i.d. external-field law. -/
theorem exists_uniform_randomFieldParisiAuxPairPressure_root_gap {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
        (Pm : Measure Ω) [IsProbabilityMeasure Pm], ∀ t ∈ Icc (0 : ℝ) t₀,
        ∀ G₀ : GaussianField (α := Config N) Pm
          (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
        ∀ u : ℝ, |u| ≤ qs 0 →
          (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
          randomFieldParisiAuxPairPressure μh ξ ms qs 1 t u G₀ ≤
            2 * parisiInterpolationBracket μh ξ ms qs t - (1 - t₀) ^ 2 * (u - qs 0) ^ 2 / 8 := by
  obtain ⟨ε₁, hε₁, hpos⟩ := exists_uniform_randomFieldParisiAuxPairPressure_root_nonnegative_gap hξ hμ ht₀
  obtain ⟨ε₂, hε₂, hneg⟩ := exists_uniform_randomFieldParisiAuxPairPressure_root_signed_gap hξ hμ ht₀
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro k ms qs hm hmin hfull hnear N hN Ω _ Pm _ t ht G₀ u hu hreach
  rcases le_total 0 u with hu0 | hu0
  · have hnear₁ := hnear.trans_le (add_le_add le_rfl (min_le_left ε₁ ε₂))
    exact hpos k ms qs hm hmin hfull hnear₁ N hN Ω Pm t ht G₀ u
      ⟨hu0, (le_abs_self u).trans hu⟩ hreach
  · have hnear₂ := hnear.trans_le (add_le_add le_rfl (min_le_right ε₁ ε₂))
    exact hneg k ms qs hm hmin hfull hnear₂ N hN Ω Pm t ht G₀ u
      ⟨by rw [abs_of_nonpos hu0] at hu; linarith, hu0⟩ hreach

end SpinGlass
