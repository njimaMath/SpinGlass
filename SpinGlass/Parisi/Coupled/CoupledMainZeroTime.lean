import SpinGlass.Parisi.Coupled.CoupledZeroTimeComparison

/-!
# The zero-time main estimate at all overlaps

The actual coupled slope at zero time is the original stationary
overlap moment. Its coupling Taylor bound gives a quadratic pressure
penalty at every realizable overlap, including negative overlaps.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

theorem randomFieldParisiAuxPairPressure_zero_le_gain {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) (u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ 0) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 1) 0 u G₀ ≤
      2 * parisiInterpolationBracket μh ξ ms qs 0 - (parisiLeftUSpatialMoment 1 μh ξ ms qs p 0 - u) ^ 2 / 2 := by
  have ht0 : (0 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  have hLR : qs p ≤ qExt qs (p.val + 2) := by
    have hh := qExt_le_succ hq.monotone hq.2.1 hq.2.2 (by omega : p.val + 1 ≤ k + 1)
    simpa only [qExt_succ_of_lt qs p.isLt] using hh
  have ha : 0 ≤ deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p) := sub_nonneg.2
    (hξ.strictMonoOn_deriv.monotoneOn (hq.mem_Icc p)
      (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _) hLR)
  have hds (w : ℝ) : (fun i => parisiDrivenSplitVars ξ qs p 0 w i + parisiOuterAuxSplitVars ξ qs p 0 i) =
      parisiOuterAuxSplitVars ξ qs p 0 := by
    funext i
    simp only [parisiDrivenSplitVars, Real.toNNReal_zero, zero_mul, zero_add]
  have htotal := parisiDrivenSplitVars_add_outerAux_eq hξ qs p hq ht0 (u := qs p) ⟨le_rfl, hLR⟩
  rw [hds] at htotal
  simp only [zero_mul, sub_zero] at htotal
  let β := parisiLeftUSpatialMoment 1 μh ξ ms qs p 0 - u
  have hb := randomFieldParisiSplitPressure_zero_le_siteValue hμ hN ξ ms qs p hm u G₀
    (parisiOuterAuxSplitVars ξ qs p 0) (-β) hreach
  rw [hds] at hb
  have hg := randomFieldPairSiteY₀_parisi_outer_split_le_gain hμ ξ ms qs p hm (w := 0) ⟨le_rfl, ha⟩ u
  dsimp only at hg
  simp only [sub_zero] at hg
  rw [← htotal] at hg
  rw [randomFieldParisiAuxPairPressure_outer_eq hμ hN ξ ms qs p u hm ht0 G₀ hreach]
  unfold parisiInterpolationBracket parisiSplitBracket
  simp only [zero_mul, zero_div, sub_zero]
  dsimp only [β] at hb
  linarith

/-- Proposition 14.8.7 from the original q-minimum and its concrete
moment equation. The bound holds for every realizable overlap and
every original level, including the terminal index and k=0. -/
theorem randomFieldParisiAuxPairPressure_zero_le_quadratic_gap {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : NondegenerateExternalFieldLaw μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hmin : IsRandomFieldParisiQMinimizer μh ξ ms qs) (u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ 0) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 1) 0 u G₀ ≤
      2 * parisiInterpolationBracket μh ξ ms qs 0 - (u - qs p) ^ 2 / 2 := by
  have hb := randomFieldParisiAuxPairPressure_zero_le_gain hμ.integrable_id hN hξ ms qs p hm hmin.1 u G₀ hreach
  rw [parisiLeftUSpatialMoment_one_zero_eq_randomFieldParisiQMoment hξ ms qs p hm hmin.1,
    ← (randomFieldParisiQ_strict_chain_and_eq_concrete_moment_of_isMin ms qs hm hξ hμ hmin).2 p] at hb
  nlinarith

end SpinGlass
