import SpinGlass.Parisi.Concentration.ParisiPressureIdentification
import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateScaling

/-!
# A fixed Gaussian law for the single-copy interpolation

The time-scaled pressure is exactly the original `hamG` recursion under
one fixed interaction/root/field law. This includes both endpoints and
zero auxiliary variances, with no division by an interpolation coefficient.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ}

/-- The fixed interaction, root and i.i.d. field law used throughout
the original single-copy interpolation. -/
noncomputable def parisiBaseDisorderFieldLaw (N : ℕ) (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) :=
  ((multivariateGaussian 0 (overlapCovMatrix N ξ)).prod
    (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0)))).prod
      (externalFieldVecLaw N μh)

instance isProbabilityMeasure_parisiBaseDisorderFieldLaw
    (N : ℕ) (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    {k : ℕ} (qs : Fin (k + 1) → ℝ) :
    IsProbabilityMeasure (parisiBaseDisorderFieldLaw N μh ξ qs) := by
  unfold parisiBaseDisorderFieldLaw
  infer_instance

noncomputable def parisiInterpolationScaling (N : ℕ) (t : ℝ)
    (z : (EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ)) :=
  ((Real.sqrt t • z.1.1, fun i => Real.sqrt (1 - t) * z.1.2 i), z.2)

theorem measurable_parisiInterpolationScaling (t : ℝ) :
    Measurable (parisiInterpolationScaling N t) := by
  unfold parisiInterpolationScaling
  fun_prop

theorem map_pi_gaussianReal_sqrt_scale {I : Type*} [Fintype I]
    (v : ℝ≥0) {a : ℝ} (ha : 0 ≤ a) :
    (Measure.pi (fun _ : I => gaussianReal 0 v)).map
      (fun z i => Real.sqrt a * z i) =
        Measure.pi (fun _ : I => gaussianReal 0 (a.toNNReal * v)) := by
  rw [Measure.pi_map_pi (fun _ => (measurable_const_mul _).aemeasurable)]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 2
  apply NNReal.eq
  change Real.sqrt a ^ 2 = (a.toNNReal : ℝ)
  rw [Real.sq_sqrt ha, Real.coe_toNNReal _ ha]

/-- Exact joint-law transport of interaction disorder and root marks. -/
theorem measurePreserving_parisiInterpolationScaling
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (qs : Fin (k + 1) → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    MeasurePreserving (parisiInterpolationScaling N t)
      (parisiBaseDisorderFieldLaw N μh ξ qs) (parisiInterpolationFieldLaw N μh ξ qs t) := by
  have hH : MeasurePreserving (fun H : EnergySpace N => Real.sqrt t • H)
      (multivariateGaussian 0 (overlapCovMatrix N ξ))
      (multivariateGaussian 0 (overlapCovMatrix N (parisiTimeProfile ξ t))) := by
    refine ⟨by fun_prop, ?_⟩
    rw [multivariateGaussian_map_smul _ hS, smul_zero, Real.sq_sqrt ht.1]
    congr 1
    ext σ τ
    simp only [Matrix.smul_apply, smul_eq_mul, overlapCovMatrix_apply, parisiTimeProfile]
    ring
  have hz : MeasurePreserving (fun z : Fin N → ℝ => fun i => Real.sqrt (1 - t) * z i)
      (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0)))
      (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiAuxRootVar ξ qs t))) :=
    ⟨by fun_prop, map_pi_gaussianReal_sqrt_scale _ (sub_nonneg.2 ht.2)⟩
  exact (hH.prod hz).prod (MeasurePreserving.id _)

/-- Transporting the positive Gaussian levels recovers the existing
single-branch `hamG` recursion. -/
theorem parisiInterpolationLogPartition_scaling_eq
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    {t : ℝ} (ht : t ≤ 1)
    (z : (EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ)) :
    parisiInterpolationLogPartition N ξ ms qs t (parisiInterpolationScaling N t z) =
      Real.log (cascadeRec k ms (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1)))
        (hamG N k t z.2 z.1.1 z.1.2)).toReal := by
  let vs := fun p : Fin k => parisiVar ξ qs (p.val + 1)
  let f := fun _ : Fin k => fun x : Fin N → ℝ => fun i => Real.sqrt (1 - t) * x i
  have hf (p : Fin k) : Measurable (f p) := by unfold f; fun_prop
  have hmap : gaussianMarks N k (parisiAuxLevelVars ξ qs t) =
      fun p => (gaussianMarks N k vs p).map (f p) := by
    funext p
    exact (map_pi_gaussianReal_sqrt_scale (vs p) (sub_nonneg.2 ht)).symm
  unfold parisiInterpolationLogPartition
  rw [hmap, cascadeRec_map k ms _ f hf (measurable_unscaledHamG _ _ _)]
  congr 2
  apply congrArg (cascadeRec k ms (gaussianMarks N k vs))
  funext x
  exact unscaledHamG_interpolation_eq_hamG t z.1.1 z.2 z.1.2 x

/-- The physical pressure is the actual single-copy recursion under a
time-independent Gaussian/field law. -/
theorem parisiInterpolationPressure_eq_base_recursion
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiInterpolationPressure N μh ξ ms qs t =
      (1 / (N : ℝ)) * ∫ z,
        Real.log (cascadeRec k ms (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1)))
          (hamG N k t z.2 z.1.1 z.1.2)).toReal ∂parisiBaseDisorderFieldLaw N μh ξ qs := by
  have hT := measurePreserving_parisiInterpolationScaling μh ξ qs hS ht
  unfold parisiInterpolationPressure
  rw [← hT.map_eq, integral_map hT.measurable.aemeasurable
    (measurable_parisiInterpolationLogPartition ξ ms qs t).aestronglyMeasurable]
  simp_rw [parisiInterpolationLogPartition_scaling_eq ξ ms qs ht.2]

/-- The recursion pressure is exactly the normalized infinite-tree
Guerra pressure, written as an iterated expectation under fixed laws. -/
theorem parisiInterpolationPressure_eq_expected_tree
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hS : (overlapCovMatrix N ξ).PosSemidef) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiInterpolationPressure N μh ξ ms qs t =
      (1 / (N : ℝ)) * ∫ z, ∫ ω,
        Real.log ((cascadeSum k (hamG N k t z.2 z.1.1 z.1.2) ω).toReal /
          (cascadeSum k (fun _ => 1) ω).toReal)
          ∂cascadeLaw k ms (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1)))
          ∂parisiBaseDisorderFieldLaw N μh ξ qs := by
  rw [parisiInterpolationPressure_eq_base_recursion μh ξ ms qs hS ht]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  exact (integral_log_cascadeSum_div_eq k ms _ (measurable_hamG' N k t z.2 z.1.1 z.1.2)
    (hamG_pos N k t z.2 z.1.1 z.1.2) hm.1 hm.2.1 hm.2.2
    (cascadeRec_hamG_ne_top N k ms _ hm.2.1 (fun i => (hm.2.2 i).le)
      t z.2 z.1.1 z.1.2)).symm

end SpinGlass
