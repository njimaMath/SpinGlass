import SpinGlass.Parisi.Coupled.CoupledOuterFreeComparison

/-!
# Strict pressure witnesses from the actual outer mass derivative

The physical shared mass allows either sign of variation around the
matching scalar mass, including the terminal value one. The concrete
convex U-response supplies the mirror mass-versus-coupling alternative.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

theorem exists_parisiOuterFreeScalarBound_lt_of_deriv_ne_zero
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (hd : parisiLeftU μh ξ ms qs p (t * (deriv ξ u - deriv ξ (qs p))) -
      t * (parisiTheta ξ u - parisiTheta ξ (qs p)) ≠ 0) :
    ∃ b ∈ Ioo (mExt ms p.val) (2 * mExt ms (p.val + 1)),
      parisiOuterFreeScalarBound μh ξ ms qs p t u b < 2 * parisiInterpolationBracket μh ξ ms qs t := by
  by_contra hn
  push Not at hn
  have he := parisiOuterFreeScalarBound_matching hμ hξ ms qs p hq ht hu
  have hmin : IsMinOn (parisiOuterFreeScalarBound μh ξ ms qs p t u)
      (Ioo (mExt ms p.val) (2 * mExt ms (p.val + 1))) (mExt ms (p.val + 1)) := by
    intro b hb
    rw [he]
    exact hn b hb
  exact hd ((hmin.isLocalMin (parisiOuterFreeMass_mem_nhds_matching ms p hm)).hasDerivAt_eq_zero
    (hasDerivAt_parisiOuterFreeScalarBound_matching hμ hξ ms qs p hm hq ht hu))

theorem exists_randomFieldParisiAuxPairPressure_outer_mass_gap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (hd : parisiLeftU μh ξ ms qs p (t * (deriv ξ u - deriv ξ (qs p))) -
      t * (parisiTheta ξ u - parisiTheta ξ (qs p)) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
      (Pm : Measure Ω) [IsProbabilityMeasure Pm],
      ∀ G₀ : GaussianField (α := Config N) Pm
        (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
      (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
      randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 1) t u G₀ ≤
        2 * parisiInterpolationBracket μh ξ ms qs t - δ := by
  obtain ⟨b, hb, hgain⟩ := exists_parisiOuterFreeScalarBound_lt_of_deriv_ne_zero hμ hξ ms qs p hm hq ht hu hd
  refine ⟨2 * parisiInterpolationBracket μh ξ ms qs t - parisiOuterFreeScalarBound μh ξ ms qs p t u b,
    sub_pos.2 hgain, ?_⟩
  intro N hN Ω _ Pm _ G₀ hreach
  have hb0 : 0 < b := lt_of_le_of_lt (mExt_nonneg (fun i => (hm.2.1 i).le) _) hb.1
  have hh := randomFieldParisiAuxPairPressure_outer_free_le_scalarBound hμ hN hξ ms qs p hm hq
    ht hu hb0 hb.1.le hb.2.le G₀ hreach
  linarith

/-- Convexity of the actual outer U-response gives the mirror of
(14.336), with the same positive strict tangent remainder. -/
theorem parisiLeftf_ge_outer_massResponse_tangent
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (huL : qs p < u) :
    (parisiLeftU μh ξ ms qs p (t * (deriv ξ u - deriv ξ (qs p))) -
        t * (parisiTheta ξ u - parisiTheta ξ (qs p))) +
      (1 - t) * ((deriv ξ u - deriv ξ (qs p)) * parisiLeftResponseGap μh ξ ms qs p t u +
        (ξ u - ξ (qs p) - (u - qs p) * deriv ξ (qs p))) ≤ parisiLeftf μh ξ ms qs p u := by
  let Δ := deriv ξ u - deriv ξ (qs p)
  let v := t * Δ
  have humem : u ∈ Icc (0 : ℝ) 1 :=
    ⟨(hq.mem_Icc p).1.trans hu.1, hu.2.trans (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _).2⟩
  have hΔ : 0 < Δ := sub_pos.2 (hξ.strictMonoOn_deriv (hq.mem_Icc p) humem huL)
  have hv := parisi_outer_time_variance_mem_Icc hξ qs p hq ⟨ht.1, ht.2.le⟩ hu
  have hw := mapsTo_parisi_outer_variance_coordinate hξ (hq.mem_Icc p)
    (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _) hu
  have hvw : v < Δ := by simpa only [v, one_mul] using mul_lt_mul_of_pos_right ht.2 hΔ
  have hs := (convexOn_parisiLeftU (μh := μh) hξ ms qs p hm hq).le_slope_of_hasDerivWithinAt hv hw hvw
    (hasDerivWithinAt_parisiLeftU (μh := μh) hξ ms qs p hm hq (huL.trans_le hu.2) hv)
  have hh := mul_le_mul_of_nonneg_right hs (sub_pos.2 hvw).le
  have he : slope (parisiLeftU μh ξ ms qs p) v Δ * (Δ - v) =
      parisiLeftU μh ξ ms qs p Δ - parisiLeftU μh ξ ms qs p v := by
    rw [mul_comm, ← smul_eq_mul]
    exact sub_smul_slope _ v Δ
  rw [he] at hh
  unfold parisiLeftf parisiLeftResponseGap
  calc
    _ = parisiLeftU μh ξ ms qs p v +
        (Δ - v) * parisiLeftUSpatialMoment 1 μh ξ ms qs p v -
          (parisiTheta ξ u - parisiTheta ξ (qs p)) := by dsimp only [v, Δ]; unfold parisiTheta; ring
    _ ≤ _ := by linarith

end SpinGlass
