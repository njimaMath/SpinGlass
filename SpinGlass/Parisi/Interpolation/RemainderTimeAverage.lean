import SpinGlass.Parisi.Interpolation.RemainderAverage

/-!
# The averaged time integral of the physical remainder

The fixed-law representation supplies time integrability and permits
averaging the exact interpolation remainder over fields and weights.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

theorem integral_parisiFixedWeightRemainder_prod_eq
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hS : (overlapCovMatrix N ξ).PosSemidef) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ q : (Fin N → ℝ) × CascadeWeights k, parisiFixedWeightRemainder N k ξ qs q.1 q.2 t
      ∂(externalFieldVecLaw N μh).prod (cascadeWeightsLaw k ms)) =
        parisiGuerraRemainder N μh ξ ms qs t := by
  have hmap : Measurable (fun q : (Fin N → ℝ) × CascadeWeights k => (q, t)) :=
    measurable_id.prodMk measurable_const
  have hm' : Measurable (fun q : (Fin N → ℝ) × CascadeWeights k =>
      parisiFixedWeightRemainder N k ξ qs q.1 q.2 t) := by
    have hh := (measurable_parisiFixedWeightRemainder_joint N k ξ qs).comp hmap
    simp only [Function.comp_def] at hh
    exact hh
  have hi : Integrable (fun q : (Fin N → ℝ) × CascadeWeights k =>
      parisiFixedWeightRemainder N k ξ qs q.1 q.2 t)
      ((externalFieldVecLaw N μh).prod (cascadeWeightsLaw k ms)) :=
    Integrable.of_bound hm'.aestronglyMeasurable _ (Filter.Eventually.of_forall fun q =>
      norm_parisiFixedWeightRemainder_le N k ξ qs t q.1 q.2)
  rw [integral_prod _ hi]
  exact integral_parisiFixedWeightRemainder_eq N k μh ξ ms qs hm hS ht

theorem integrable_parisiFixedWeightRemainder_prod_time
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (a b : ℝ) :
    Integrable (fun q : ((Fin N → ℝ) × CascadeWeights k) × ℝ =>
      parisiFixedWeightRemainder N k ξ qs q.1.1 q.1.2 q.2)
      (((externalFieldVecLaw N μh).prod (cascadeWeightsLaw k ms)).prod
        (volume.restrict (Ioc a b))) := by
  let : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  exact Integrable.of_bound
    (measurable_parisiFixedWeightRemainder_joint N k ξ qs).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun q =>
        norm_parisiFixedWeightRemainder_le N k ξ qs q.2 q.1.1 q.1.2)

/-- The physical remainder is integrable on every closed interpolation
subinterval, using the actual Gaussian and field laws. -/
theorem intervalIntegrable_parisiGuerraRemainder
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (parisiGuerraRemainder N μh ξ ms qs) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply (integrable_parisiFixedWeightRemainder_prod_time N k μh ξ ms qs a b)
    |>.integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact integral_parisiFixedWeightRemainder_prod_eq N k μh ξ ms qs hm hS
    ⟨ha.trans ht.1.le, ht.2.trans hb⟩

/-- The exact fixed-weight time remainder averages to the time integral
of the physical localized remainder. -/
theorem integral_intervalIntegral_parisiFixedWeightRemainder_eq
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hS : (overlapCovMatrix N ξ).PosSemidef)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ q : (Fin N → ℝ) × CascadeWeights k,
      (∫ t in a..b, parisiFixedWeightRemainder N k ξ qs q.1 q.2 t)
      ∂(externalFieldVecLaw N μh).prod (cascadeWeightsLaw k ms)) =
        ∫ t in a..b, parisiGuerraRemainder N μh ξ ms qs t := by
  simp_rw [intervalIntegral.integral_of_le hab]
  rw [integral_integral_swap
    (integrable_parisiFixedWeightRemainder_prod_time N k μh ξ ms qs a b)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  exact integral_parisiFixedWeightRemainder_prod_eq N k μh ξ ms qs hm hS
    ⟨ha.trans ht.1.le, ht.2.trans hb⟩

end

end SpinGlass
