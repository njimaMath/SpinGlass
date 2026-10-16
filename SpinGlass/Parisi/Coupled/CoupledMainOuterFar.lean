import SpinGlass.Parisi.Coupled.CoupledOuterMassGain

/-!
# The far outer-overlap alternative

The tolerance precedes all MIN parameters, site laws and times.
Convexity of the actual outer response and the uniform MIN upper
mass estimate force a negative derivative at zero coupling response.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

theorem exists_uniform_outer_massResponse_neg_of_coupling_eq_zero
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {t₀ ρ : ℝ}
    (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ η : ℝ, 0 < η ∧
      ∀ {μh : Measure ℝ} [IsProbabilityMeasure μh], Integrable id μh →
      ∀ {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
      ParisiMAdmissible ms → ParisiQAdmissible qs →
      IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
        (parisiParameterDomain k) (ms, qs) →
      randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
      ∀ p : Fin (k + 1), ∀ t ∈ Icc (0 : ℝ) t₀, ∀ u ∈ Icc (qs p) (qExt qs (p.val + 2)),
      ρ ≤ u - qs p → parisiLeftResponseGap μh ξ ms qs p t u = 0 →
      parisiLeftU μh ξ ms qs p (t * (deriv ξ u - deriv ξ (qs p))) -
        t * (parisiTheta ξ u - parisiTheta ξ (qs p)) ≤ -η := by
  obtain ⟨M, hM, hf⟩ := exists_uniform_parisiLeftf_upper_bound hξ
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
    ⟨(hq.mem_Icc p).1.trans hu.1, hu.2.trans (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _).2⟩
  have huL : qs p < u := by linarith
  have hrem := hgap (qs p) (hq.mem_Icc p) u humem (by
    rw [abs_of_nonneg (sub_nonneg.2 hu.1)]
    exact hdist)
  have hup := hf hμ hm hq hfull hε.le hnear p u hu
  rw [hsqrt] at hup
  have hcomp := parisiLeftf_ge_outer_massResponse_tangent (μh := μh) hξ ms qs p hm hq
    ⟨ht.1, ht.2.trans_lt ht₀.2⟩ hu huL
  rw [hzero, mul_zero, zero_add] at hcomp
  have htγ : D ≤ (1 - t) * γ := by
    dsimp only [D]
    exact mul_le_mul_of_nonneg_right (by linarith [ht.2]) hγ.le
  have hprod := mul_le_mul_of_nonneg_left hrem (by linarith [ht.2, ht₀.2] : 0 ≤ 1 - t)
  linarith

end SpinGlass
