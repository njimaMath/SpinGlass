import SpinGlass.Parisi.Coupled.CoupledInnerMassGain
import SpinGlass.Parisi.Coupled.CoupledMainNear
import SpinGlass.Parisi.Variational.ParisiProfileStrictGap

/-!
# The far inner-overlap alternative

The tolerance is chosen from the profile tangent gap and the uniform
MIN mass estimate before all level counts, parameters, site laws and
times. A zero coupling response then forces a positive mass response.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The concrete mass derivative in (14.335) is uniformly positive
when the coupling response vanishes away from the right endpoint.
Both constants precede every MIN and every probability field law. -/
theorem exists_uniform_inner_massResponse_pos_of_coupling_eq_zero
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {t₀ ρ : ℝ}
    (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {μh : Measure ℝ} [IsProbabilityMeasure μh], Integrable id μh →
      ∀ {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → ParisiQAdmissible qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ p : Fin k, ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (qs p.castSucc) (qs p.succ),
      ρ ≤ qs p.succ - u → parisiRightResponseGap μh ξ ms qs p t u = 0 →
      η ≤ parisiRightU μh ξ ms qs p (t * (deriv ξ (qs p.succ) - deriv ξ u)) -
        t * (parisiTheta ξ (qs p.succ) - parisiTheta ξ u) := by
  obtain ⟨M, hM, hf⟩ := exists_uniform_parisiRightf_lower_bound hξ
  obtain ⟨γ, hγ, hgap⟩ := hξ.exists_uniform_tangent_gap hρ
  let D := (1 - t₀) * γ
  have hD : 0 < D := mul_pos (sub_pos.2 ht₀.2) hγ
  let ε := (D / 8) ^ 2 / M
  have hε : 0 < ε := div_pos (sq_pos_of_pos (by positivity)) hM
  have hMε : M * ε = (D / 8) ^ 2 := by dsimp only [ε]; field_simp
  have hsqrt : Real.sqrt (M * ε) = D / 8 := by rw [hMε, Real.sqrt_sq (by positivity)]
  refine ⟨ε, hε, D / 2, by positivity, ?_⟩
  intro μh _ hμ k ms qs hm hq hfull hnear p t ht u hu hdist hzero
  have humem : u ∈ Icc (0 : ℝ) 1 :=
    ⟨(hq.mem_Icc p.castSucc).1.trans hu.1, hu.2.trans (hq.mem_Icc p.succ).2⟩
  have huR : u < qs p.succ := by linarith
  have hrem := hgap (qs p.succ) (hq.mem_Icc p.succ) u humem (by
    rw [abs_of_nonpos (sub_nonpos.2 hu.2)]
    linarith)
  have hlo := hf hμ hm hq hfull hε.le hnear p u hu
  rw [hsqrt] at hlo
  have hcomp := parisiRightf_le_inner_massResponse_tangent (μh := μh) hξ ms qs p hm hq
    ⟨ht.1, ht.2.trans_lt ht₀.2⟩ hu huR
  rw [hzero, mul_zero, zero_sub] at hcomp
  have htγ : D ≤ (1 - t) * γ := by
    dsimp only [D]
    exact mul_le_mul_of_nonneg_right (by linarith [ht.2]) hγ.le
  have hprod := mul_le_mul_of_nonneg_left hrem (by linarith [ht.2, ht₀.2] : 0 ≤ 1 - t)
  linarith

/-- The far inner interval has a strict pressure gap at each time
and overlap. The tolerance precedes every MIN; each witness gap precedes
every finite volume and probability realization of its Hamiltonian.
Compact uniformization over time and overlap is a separate conclusion. -/
theorem exists_uniform_randomFieldParisiAuxPairPressure_inner_far_pointwise_gap
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {t₀ ρ : ℝ}
    (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ {μh : Measure ℝ} [IsProbabilityMeasure μh], Integrable id μh →
      ∀ {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → ParisiQAdmissible qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ p : Fin k, ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (qs p.castSucc) (qs p.succ),
      ρ ≤ qs p.succ - u → ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
        (Pm : Measure Ω) [IsProbabilityMeasure Pm],
      ∀ G₀ : GaussianField (α := Config N) Pm
        (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
      (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
      randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 2) t u G₀ ≤
        2 * parisiInterpolationBracket μh ξ ms qs t - δ := by
  obtain ⟨ε, hε, η, hη, hd⟩ := exists_uniform_inner_massResponse_pos_of_coupling_eq_zero hξ ht₀ hρ
  refine ⟨ε, hε, ?_⟩
  intro μh _ hμ k ms qs hm hq hfull hnear p t ht u hu hdist
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2.le⟩
  by_cases hzero : parisiRightResponseGap μh ξ ms qs p t u = 0
  · have hpos := hd hμ ms qs hm hq hfull hnear p t ht u hu hdist hzero
    apply exists_randomFieldParisiAuxPairPressure_inner_mass_gap hμ hξ ms qs p hm hq ht01 hu
    exact ne_of_gt (hη.trans_le hpos)
  · refine ⟨parisiRightResponseGap μh ξ ms qs p t u ^ 2 / 2,
      div_pos (sq_pos_of_ne_zero hzero) (by norm_num), ?_⟩
    intro N hN Ω _ Pm _ G₀ hreach
    exact randomFieldParisiAuxPairPressure_inner_le_gain hμ hN hξ ms qs p hm hq ht01 hu G₀ hreach

end SpinGlass
