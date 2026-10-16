import SpinGlass.Parisi.Interpolation.PressureLimit
import SpinGlass.Parisi.Interpolation.RemainderIntegral

/-!
# The exact interpolation identity at fixed cascade weights

The pressure, bound and remainder all pass to the full cascade on any
closed subinterval of the interpolation. No derivative of an infinite
partition function is assumed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

theorem norm_guerraBound_le (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ)
    (h : Fin N → ℝ) (w : CascadeWeights k) (t : ℝ) :
    ‖guerraBound N k ξ qs h w t‖ ≤
      (1 / 2) * |ξ 1 - deriv ξ (qs (Fin.last k))| +
        (1 / 2) * ∑ r ∈ Finset.range (k + 1), |parisiTheta ξ (qExt qs (r + 1))| := by
  exact abs_guerraBound_le N k ξ qs h w t

theorem norm_guerraTruncBound_le (M : ℕ) (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ)
    (h : Fin N → ℝ) (w : CascadeWeights k) (hw : ∀ α, branchWeight k w α ≠ ∞) (t : ℝ) :
    ‖guerraTruncBound N k M ξ qs h w t‖ ≤
      (1 / 2) * |ξ 1 - deriv ξ (qs (Fin.last k))| +
        (1 / 2) * ∑ r ∈ Finset.range (k + 1), |parisiTheta ξ (qExt qs (r + 1))| := by
  unfold guerraTruncBound
  refine (norm_integral_le_of_norm_le_const (Eventually.of_forall fun ω => ?_)).trans
    (by rw [probReal_univ, mul_one])
  rw [treeBoundIntegrand_eq_levelBound N k M ξ qs _ t h w hw ω, Real.norm_eq_abs]
  exact abs_levelBound_le k _ _ _ (fun r => truncPair_nonneg k M r _ w _)
    (fun r => truncPair_le_one k M r _ w _)

theorem intervalIntegrable_guerraBound (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ)
    (h : Fin N → ℝ) (w : CascadeWeights k) (a b : ℝ) :
    IntervalIntegrable (guerraBound N k ξ qs h w) volume a b := by
  have hmap : Measurable (fun t : ℝ => (w, t)) := measurable_const.prodMk measurable_id
  have hm : Measurable (guerraBound N k ξ qs h w) := by
    have hh := (measurable_guerraBound N k ξ qs h).comp hmap
    simp only [Function.comp_def] at hh
    exact hh
  apply (intervalIntegrable_const (c := (1 / 2) * |ξ 1 - deriv ξ (qs (Fin.last k))| +
    (1 / 2) * ∑ r ∈ Finset.range (k + 1), |parisiTheta ξ (qExt qs (r + 1))|)).mono_fun
      hm.aestronglyMeasurable
  exact Eventually.of_forall fun t => (norm_guerraBound_le N k ξ qs h w t).trans (le_abs_self _)

/-- The bound term converges under the time integral on arbitrary finite
intervals, extending the existing full-interval limit. -/
theorem tendsto_intervalIntegral_guerraTruncBound
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞) (a b : ℝ) :
    Tendsto (fun M => ∫ t in a..b, guerraTruncBound N k M ξ qs h w t) atTop
      (𝓝 (∫ t in a..b, guerraBound N k ξ qs h w t)) := by
  obtain ⟨M₀, hM₀⟩ := exists_truncWt_ne_zero k w hW0 hW
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (1 / 2) * |ξ 1 - deriv ξ (qs (Fin.last k))| +
      (1 / 2) * ∑ r ∈ Finset.range (k + 1), |parisiTheta ξ (qExt qs (r + 1))|)
  · filter_upwards [eventually_ge_atTop M₀] with M hM
    exact (continuous_guerraTruncBound N k M ξ qs h w (hM₀ M hM)).aestronglyMeasurable
  · exact Eventually.of_forall fun M => Eventually.of_forall fun t _ =>
      norm_guerraTruncBound_le N k M ξ qs h w
        (fun α => ne_top_of_le_ne_top hW (branchWeight_le_weightSum k w α)) t
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t _ => tendsto_guerraTruncBound N k ξ qs h w hW0 hW t

/-- The exact full-cascade interpolation identity, before averaging the
weights or external fields, including both closed time endpoints. -/
theorem parisiFixedWeightPressure_sub_eq_integral
    (hN : 0 < N) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    parisiFixedWeightPressure N k ξ qs h w b - parisiFixedWeightPressure N k ξ qs h w a =
      ∫ t in a..b, guerraBound N k ξ qs h w t - parisiFixedWeightRemainder N k ξ qs h w t := by
  have hp := (tendsto_parisiTruncatedPressure N k ξ hS qs h w hW0 hW b).sub
    (tendsto_parisiTruncatedPressure N k ξ hS qs h w hW0 hW a)
  have hi := (tendsto_intervalIntegral_guerraTruncBound N k ξ qs h w hW0 hW a b).sub
    (tendsto_intervalIntegral_parisiTruncatedGuerraRemainder N k hξ qs hq h w hW0 hW a b)
  obtain ⟨M₀, hM₀⟩ := exists_truncWt_ne_zero k w hW0 hW
  have he : (fun M => parisiTruncatedPressure N k M ξ qs h w b -
      parisiTruncatedPressure N k M ξ qs h w a) =ᶠ[atTop]
      (fun M => (∫ t in a..b, guerraTruncBound N k M ξ qs h w t) -
        ∫ t in a..b, parisiTruncatedGuerraRemainder N k M ξ qs h w t) := by
    filter_upwards [eventually_ge_atTop M₀] with M hM
    rw [parisiTruncatedPressure_sub_eq_integral N k M hN hξ hS qs hq h w
      (hM₀ M hM) ha hab hb]
    exact intervalIntegral.integral_sub
      ((continuous_guerraTruncBound N k M ξ qs h w (hM₀ M hM)).intervalIntegrable a b)
      ((continuous_parisiTruncatedGuerraRemainder N k M hξ qs hq h w
        (hM₀ M hM)).intervalIntegrable a b)
  rw [intervalIntegral.integral_sub (intervalIntegrable_guerraBound N k ξ qs h w a b)
    (intervalIntegrable_parisiFixedWeightRemainder N k hξ qs hq h w hW0 hW a b)]
  exact tendsto_nhds_unique (hp.congr' he) hi

/-- Pressure differences have a bound independent of the site field and
weight sample. Thus averaging the exact identity does not require a
moment hypothesis on the logarithm of total cascade weight. -/
theorem norm_parisiFixedWeightPressure_sub_le
    (hN : 0 < N) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ‖parisiFixedWeightPressure N k ξ qs h w b - parisiFixedWeightPressure N k ξ qs h w a‖ ≤
      ((1 / 2) * |ξ 1 - deriv ξ (qs (Fin.last k))| +
        (1 / 2) * ∑ r ∈ Finset.range (k + 1), |parisiTheta ξ (qExt qs (r + 1))| +
          deriv (deriv ξ) 1) * (b - a) := by
  rw [parisiFixedWeightPressure_sub_eq_integral N k hN hξ hS qs hq h w hW0 hW ha hab hb,
    ← abs_of_nonneg (sub_nonneg.2 hab)]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t _
  have hR := parisiFixedWeightRemainder_bounds N k hξ qs hq h w hW0 hW t
  have hn : ‖parisiFixedWeightRemainder N k ξ qs h w t‖ ≤ deriv (deriv ξ) 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hR.1] using hR.2
  exact (norm_sub_le _ _).trans (add_le_add (norm_guerraBound_le N k ξ qs h w t) hn)

end

end SpinGlass
