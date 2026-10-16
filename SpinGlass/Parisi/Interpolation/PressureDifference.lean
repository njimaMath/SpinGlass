import SpinGlass.Parisi.Interpolation.PressureFieldAverage
import SpinGlass.Parisi.Interpolation.FixedWeightIdentity

/-!
# Averaging pressure differences under the original field law

The exact interpolation bound controls pressure differences uniformly
in the field and weights. This suffices for joint integrability without
requiring a field exponential moment or a logarithmic weight moment.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

variable (N k : ℕ)

theorem measurable_parisiFixedWeightPressure_field_weights
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ) :
    Measurable (fun q : (Fin N → ℝ) × CascadeWeights k =>
      parisiFixedWeightPressure N k ξ qs q.1 q.2 t) := by
  have hG : Measurable (Function.uncurry
      (fun a : (Fin N → ℝ) × (EnergySpace N × (Fin N → ℝ)) =>
        hamG N k t a.1 a.2.1 a.2.2)) := by
    unfold Function.uncurry hamG branchZX branchHamX
    fun_prop
  have hmap : Measurable (fun q : ((Fin N → ℝ) × CascadeWeights k) ×
      ((EnergySpace N × (Fin N → ℝ)) × CascadeMarks (Fin N → ℝ) k) =>
        ((q.1.1, q.2.1), cascadeZip k (q.1.2, q.2.2))) :=
    (measurable_fst.fst.prodMk measurable_snd.fst).prodMk
      ((measurable_cascadeZip k).comp (measurable_fst.snd.prodMk measurable_snd.snd))
  have hlog : Measurable (fun q : ((Fin N → ℝ) × CascadeWeights k) ×
      ((EnergySpace N × (Fin N → ℝ)) × CascadeMarks (Fin N → ℝ) k) =>
        Real.log (cascadeSum k (hamG N k t q.1.1 q.2.1.1 q.2.1.2)
          (cascadeZip k (q.1.2, q.2.2))).toReal) := by
    have hh := (measurable_cascadeSum_prod k hG).comp hmap
    simp only [Function.comp_def] at hh
    exact hh.ennreal_toReal.log
  unfold parisiFixedWeightPressure
  exact (measurable_const.mul hlog.stronglyMeasurable.integral_prod_right'.measurable).sub
    (measurable_const.mul ((measurable_weightSum k).comp measurable_snd).ennreal_toReal.log)

theorem integrable_parisiFixedWeightPressure_sub
    (hN : 0 < N) (μh : Measure ℝ) [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Integrable (fun q : (Fin N → ℝ) × CascadeWeights k =>
      parisiFixedWeightPressure N k ξ qs q.1 q.2 b - parisiFixedWeightPressure N k ξ qs q.1 q.2 a)
      ((externalFieldVecLaw N μh).prod (cascadeWeightsLaw k ms)) := by
  apply Integrable.of_bound
    ((measurable_parisiFixedWeightPressure_field_weights N k ξ qs b).sub
      (measurable_parisiFixedWeightPressure_field_weights N k ξ qs a)).aestronglyMeasurable
    (((1 / 2) * |ξ 1 - deriv ξ (qs (Fin.last k))| +
      (1 / 2) * ∑ r ∈ Finset.range (k + 1), |parisiTheta ξ (qExt qs (r + 1))| +
        deriv (deriv ξ) 1) * (b - a))
  have hw := (measurePreserving_snd (μ := externalFieldVecLaw N μh) (ν := cascadeWeightsLaw k ms))
    |>.quasiMeasurePreserving.ae (ae_weightSum_ne_zero_ne_top k ms hm.1 hm.2.1 hm.2.2)
  filter_upwards [hw] with q hq'
  exact norm_parisiFixedWeightPressure_sub_le N k hN hξ hS qs hq q.1 q.2 hq'.1 hq'.2 ha hab hb

/-- The physical pressure difference is exactly the joint field/weight
average of the normalized fixed-weight pressure difference. -/
theorem parisiInterpolationPressure_sub_eq_average
    (hN : 0 < N) {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    parisiInterpolationPressure N μh ξ ms qs b - parisiInterpolationPressure N μh ξ ms qs a =
      ∫ q : (Fin N → ℝ) × CascadeWeights k,
        parisiFixedWeightPressure N k ξ qs q.1 q.2 b -
          parisiFixedWeightPressure N k ξ qs q.1 q.2 a
        ∂(externalFieldVecLaw N μh).prod (cascadeWeightsLaw k ms) := by
  have ha' : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.trans hb⟩
  have hb' : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab, hb⟩
  rw [parisiInterpolationPressure_eq_field_weight_average N k hμ ξ ms hm qs hS hb',
    parisiInterpolationPressure_eq_field_weight_average N k hμ ξ ms hm qs hS ha',
    ← integral_sub (integrable_weightAverage_parisiFixedWeightPressure N k hμ ξ ms hm qs hS hb')
      (integrable_weightAverage_parisiFixedWeightPressure N k hμ ξ ms hm qs hS ha'),
    integral_prod _
      (integrable_parisiFixedWeightPressure_sub N k hN μh hξ hS ms hm qs hq ha hab hb)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro h
  exact (integral_sub (integrable_parisiFixedWeightPressure N k ξ hS ms hm qs b h)
    (integrable_parisiFixedWeightPressure N k ξ hS ms hm qs a h)).symm

end

end SpinGlass
