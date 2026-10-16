import SpinGlass.Parisi.Coupled.CoupledInnerFreeComparison

/-!
# Strict pressure witnesses from the actual inner mass derivative

The witness mass and pressure gap depend only on the scalar Parisi
parameters, time and overlap. They precede the finite volume and the
probability realization of its Hamiltonian.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- A nonzero concrete mass response gives a strictly smaller actual
scalar comparison value at an admissible coupled mass. -/
theorem exists_parisiInnerFreeScalarBound_lt_of_deriv_ne_zero
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p.castSucc) (qs p.succ))
    (hd : parisiRightU μh ξ ms qs p (t * (deriv ξ (qs p.succ) - deriv ξ u)) -
      t * (parisiTheta ξ (qs p.succ) - parisiTheta ξ u) ≠ 0) :
    ∃ b ∈ Ioo (ms p / 2) (mExt ms (p.val + 2)),
      parisiInnerFreeScalarBound μh ξ ms qs p t u b < 2 * parisiInterpolationBracket μh ξ ms qs t := by
  by_contra hn
  push Not at hn
  have he := parisiInnerFreeScalarBound_matching hμ hξ ms qs p hq ht hu
  have hmin : IsMinOn (parisiInnerFreeScalarBound μh ξ ms qs p t u)
      (Ioo (ms p / 2) (mExt ms (p.val + 2))) (ms p) := by
    intro b hb
    rw [he]
    exact hn b hb
  exact hd ((hmin.isLocalMin (parisiInnerFreeMass_mem_nhds_matching ms p hm)).hasDerivAt_eq_zero
    (hasDerivAt_parisiInnerFreeScalarBound_matching hμ hξ ms qs p hm hq ht hu))

/-- The concrete mass response produces a strict physical pressure
gap uniform in every positive volume and Gaussian-field realization. -/
theorem exists_randomFieldParisiAuxPairPressure_inner_mass_gap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p.castSucc) (qs p.succ))
    (hd : parisiRightU μh ξ ms qs p (t * (deriv ξ (qs p.succ) - deriv ξ u)) -
      t * (parisiTheta ξ (qs p.succ) - parisiTheta ξ u) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
      (Pm : Measure Ω) [IsProbabilityMeasure Pm],
      ∀ G₀ : GaussianField (α := Config N) Pm
        (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
      (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
      randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 2) t u G₀ ≤
        2 * parisiInterpolationBracket μh ξ ms qs t - δ := by
  obtain ⟨b, hb, hgain⟩ := exists_parisiInnerFreeScalarBound_lt_of_deriv_ne_zero hμ hξ ms qs p hm hq ht hu hd
  refine ⟨2 * parisiInterpolationBracket μh ξ ms qs t - parisiInnerFreeScalarBound μh ξ ms qs p t u b,
    sub_pos.2 hgain, ?_⟩
  intro N hN Ω _ Pm _ G₀ hreach
  have hh := randomFieldParisiAuxPairPressure_inner_free_le_scalarBound hμ hN hξ ms qs p hm hq
    ht hu hb.1.le hb.2.le G₀ hreach
  linarith

/-- Concavity of the actual U-response gives the mass-versus-coupling
alternative in (14.336). The remainder is the strict profile tangent gap. -/
theorem parisiRightf_le_inner_massResponse_tangent
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) (hu : u ∈ Icc (qs p.castSucc) (qs p.succ))
    (huR : u < qs p.succ) :
    parisiRightf μh ξ ms qs p u ≤
      (parisiRightU μh ξ ms qs p (t * (deriv ξ (qs p.succ) - deriv ξ u)) -
        t * (parisiTheta ξ (qs p.succ) - parisiTheta ξ u)) +
      (1 - t) * ((deriv ξ (qs p.succ) - deriv ξ u) * parisiRightResponseGap μh ξ ms qs p t u -
        (ξ u - ξ (qs p.succ) - (u - qs p.succ) * deriv ξ (qs p.succ))) := by
  let Δ := deriv ξ (qs p.succ) - deriv ξ u
  let v := t * Δ
  have humem : u ∈ Icc (0 : ℝ) 1 :=
    ⟨(hq.mem_Icc p.castSucc).1.trans hu.1, hu.2.trans (hq.mem_Icc p.succ).2⟩
  have hΔ : 0 < Δ := sub_pos.2 (hξ.strictMonoOn_deriv humem (hq.mem_Icc p.succ) huR)
  have hv := parisi_inner_time_variance_mem_Icc hξ qs p hq ⟨ht.1, ht.2.le⟩ hu
  have hw := mapsTo_parisi_variance_coordinate hξ (hq.mem_Icc p.castSucc) (hq.mem_Icc p.succ) hu
  have hvw : v < Δ := by simpa only [v, one_mul] using mul_lt_mul_of_pos_right ht.2 hΔ
  have hs := (concaveOn_parisiRightU (μh := μh) hξ ms qs p hm hq).slope_le_of_hasDerivWithinAt hv hw hvw
    (hasDerivWithinAt_parisiRightU (μh := μh) hξ ms qs p hm hq hv)
  have hh := mul_le_mul_of_nonneg_right hs (sub_pos.2 hvw).le
  have he : slope (parisiRightU μh ξ ms qs p) v Δ * (Δ - v) =
      parisiRightU μh ξ ms qs p Δ - parisiRightU μh ξ ms qs p v := by
    rw [mul_comm, ← smul_eq_mul]
    exact sub_smul_slope _ v Δ
  rw [he] at hh
  unfold parisiRightf parisiRightResponseGap
  calc
    _ ≤ parisiRightU μh ξ ms qs p v +
        (Δ - v) * parisiRightUSpatialMoment 1 μh ξ ms qs p v -
          (parisiTheta ξ (qs p.succ) - parisiTheta ξ u) := by linarith
    _ = _ := by dsimp only [v, Δ]; unfold parisiTheta; ring

end SpinGlass
