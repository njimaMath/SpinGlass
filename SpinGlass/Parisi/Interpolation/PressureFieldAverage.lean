import SpinGlass.Parisi.Interpolation.PressureWeightAverage
import SpinGlass.Parisi.Interpolation.PressureIntegrability

/-!
# The field and weight average of the actual pressure

Conditional Gaussian integrability at every fixed field combines with
the proved first-moment recursion integrability. Thus no exponential
moment of the external-field law enters the pressure identification.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

variable (N k : ℕ)

theorem integrable_weightAverage_parisiFixedWeightPressure
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun h => ∫ w, parisiFixedWeightPressure N k ξ qs h w t
      ∂cascadeWeightsLaw k ms) (externalFieldVecLaw N μh) := by
  have hi := integrable_parisiBaseLogPartition hμ ξ ms qs hm.2.1 (fun p => (hm.2.2 p).le) hS ht
  unfold parisiBaseDisorderFieldLaw at hi
  have hh := hi.integral_prod_right.const_mul (1 / (N : ℝ))
  apply hh.congr
  exact Filter.Eventually.of_forall fun h =>
    (integral_parisiFixedWeightPressure_eq N k ξ hS ms hm qs t h).symm

/-- The original physical pressure equals the field average of the
weight-averaged normalized cascade pressure under a first field moment. -/
theorem parisiInterpolationPressure_eq_field_weight_average
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiInterpolationPressure N μh ξ ms qs t =
      ∫ h, ∫ w, parisiFixedWeightPressure N k ξ qs h w t
        ∂cascadeWeightsLaw k ms ∂externalFieldVecLaw N μh := by
  simp_rw [integral_parisiFixedWeightPressure_eq N k ξ hS ms hm qs t]
  rw [integral_const_mul, parisiInterpolationPressure_eq_base_recursion μh ξ ms qs hS ht]
  congr 1
  have hi := integrable_parisiBaseLogPartition hμ ξ ms qs hm.2.1 (fun p => (hm.2.2 p).le) hS ht
  exact integral_prod_symm _ hi

end

end SpinGlass
