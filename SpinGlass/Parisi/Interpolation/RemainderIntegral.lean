import SpinGlass.Parisi.Interpolation.RemainderLimit

/-!
# Passing the time integral of the remainder to the full cascade

The same curvature bound controls the finite Gaussian remainders and
their limit on every closed interpolation interval.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

theorem parisiTruncatedGuerraRemainder_bounds (M : ℕ)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hne : ∃ α : TruncBranch k M, truncWt k M w α ≠ 0) (t : ℝ) :
    0 ≤ parisiTruncatedGuerraRemainder N k M ξ qs h w t ∧
      parisiTruncatedGuerraRemainder N k M ξ qs h w t ≤ deriv (deriv ξ) 1 := by
  let wt := branchWt (N := N) (truncWt k M w)
  have hwt (x) : 0 ≤ wt x := truncWt_nonneg k M w x.2
  have hne' : ∃ x, wt x ≠ 0 := ⟨(fun _ => true, hne.choose), hne.choose_spec⟩
  have hqt (α γ : TruncBranch k M) : treeOverlap qs α γ ∈ Icc (0 : ℝ) 1 :=
    qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _
  have hb (ω : EnergySpace N × MarksSpace N k) :
      0 ≤ weightedTreeProfileRemainder ξ (treeOverlap qs) wt (truncHam N k M t h ω) ∧
        weightedTreeProfileRemainder ξ (treeOverlap qs) wt (truncHam N k M t h ω) ≤
          deriv (deriv ξ) 1 :=
    ⟨weightedTreeProfileRemainder_nonneg hξ _ hqt wt hwt hne' _,
      weightedTreeProfileRemainder_le_curvature hξ _ hqt wt hwt hne' _⟩
  have hn (ω : EnergySpace N × MarksSpace N k) :
      ‖weightedTreeProfileRemainder ξ (treeOverlap qs) wt (truncHam N k M t h ω)‖ ≤
        deriv (deriv ξ) 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hb ω).1] using (hb ω).2
  refine ⟨integral_nonneg (fun ω => (hb ω).1), ?_⟩
  apply le_trans (le_abs_self _)
  simpa only [parisiTruncatedGuerraRemainder, wt, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := (gaussField N (overlapCovMatrix N ξ)).prod
      (marksLaw N k (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1))))
        (Eventually.of_forall hn)

theorem intervalIntegrable_parisiFixedWeightRemainder
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞) (a b : ℝ) :
    IntervalIntegrable (parisiFixedWeightRemainder N k ξ qs h w) volume a b := by
  apply (intervalIntegrable_const (c := deriv (deriv ξ) 1)).mono_fun
    (measurable_parisiFixedWeightRemainder N k ξ qs h w).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  have hb := parisiFixedWeightRemainder_bounds N k hξ qs hq h w hW0 hW t
  dsimp only
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2.trans (le_abs_self _)

/-- Gaussian expectation and the time integral both commute with the
actual finite-tree remainder limit, on every finite interval. -/
theorem tendsto_intervalIntegral_parisiTruncatedGuerraRemainder
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞) (a b : ℝ) :
    Tendsto (fun M => ∫ t in a..b, parisiTruncatedGuerraRemainder N k M ξ qs h w t)
      atTop (𝓝 (∫ t in a..b, parisiFixedWeightRemainder N k ξ qs h w t)) := by
  obtain ⟨M₀, hM₀⟩ := exists_truncWt_ne_zero k w hW0 hW
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => deriv (deriv ξ) 1)
  · filter_upwards [eventually_ge_atTop M₀] with M hM
    exact (continuous_parisiTruncatedGuerraRemainder N k M hξ qs hq h w
      (hM₀ M hM)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop M₀] with M hM
    apply Eventually.of_forall
    intro t _
    have hb := parisiTruncatedGuerraRemainder_bounds N k M hξ qs hq h w (hM₀ M hM) t
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t _ =>
      tendsto_parisiTruncatedGuerraRemainder N k hξ qs hq h w hW0 hW t

end

end SpinGlass
