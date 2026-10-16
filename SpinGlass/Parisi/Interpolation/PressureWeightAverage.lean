import SpinGlass.Parisi.Interpolation.PressureLimit
import SpinGlass.Parisi.Tree.CascadeLogIntegrable

/-!
# Averaging the normalized pressure over cascade weights

At every fixed site field the actual Gaussian branch partition and its
logarithm are integrable. The normalized cascade identity therefore
identifies the weight-averaged pressure with the original recursion.
-/

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

theorem integrable_log_hamG_gaussianLaw
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (t : ℝ) (h : Fin N → ℝ) :
    Integrable (fun q : (EnergySpace N × (Fin N → ℝ)) × (Fin k → Fin N → ℝ) =>
      Real.log (hamG N k t h q.1.1 q.1.2 q.2).toReal)
      (((gaussField N (overlapCovMatrix N ξ)).prod
        (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀))).prod
          (Measure.pi (gaussianMarks N k vs))) := by
  let P := (gaussField N (overlapCovMatrix N ξ)).prod
    (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀))
  let α : Fin k → ℕ × ℕ := fun _ => (0, 0)
  let σ : Config N := fun _ => true
  have hT := (MeasurePreserving.id P).prod
    (show MeasurePreserving (fun z : CascadeMarks (Fin N → ℝ) k => branchMarks k z α)
      (cascadeMarksLaw k (gaussianMarks N k vs)) (Measure.pi (gaussianMarks N k vs)) from
        ⟨measurable_branchMarks k α, cascadeMarksLaw_map_branchMarks k _ α⟩)
  have hE : Measurable (fun q : (EnergySpace N × (Fin N → ℝ)) × (Fin k → Fin N → ℝ) =>
      branchHamX N k t h q.1.1 q.1.2 q.2 σ) := by
    unfold branchHamX
    fun_prop
  have hiE : Integrable (fun q : (EnergySpace N × (Fin N → ℝ)) × (Fin k → Fin N → ℝ) =>
      branchHamX N k t h q.1.1 q.1.2 q.2 σ) (P.prod (Measure.pi (gaussianMarks N k vs))) :=
    (hT.integrable_comp hE.aestronglyMeasurable).1
      (integrable_branchHamX_gaussianLaw N k ξ hS v₀ vs t h α σ)
  have hG : Measurable (fun q : (EnergySpace N × (Fin N → ℝ)) × (Fin k → Fin N → ℝ) =>
      hamG N k t h q.1.1 q.1.2 q.2) := measurable_hamG_fixedTime N k t h
  have hmean : (∫⁻ q : (EnergySpace N × (Fin N → ℝ)) × (Fin k → Fin N → ℝ),
      hamG N k t h q.1.1 q.1.2 q.2 ∂P.prod (Measure.pi (gaussianMarks N k vs))) ≠ ∞ := by
    rw [lintegral_prod _ hG.aemeasurable]
    exact lintegral_lintegral_hamG_ne_top N k ξ hS v₀ vs t h
  have hiG := integrable_toReal_of_lintegral_ne_top hG.aemeasurable hmean
  apply (hiG.add hiE.abs).mono' (hG.ennreal_toReal.log.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro q
  have hlow := neg_branchHamX_le_log_hamG N k t h q.1.1 q.1.2 q.2 σ
  have hpos : 0 < (hamG N k t h q.1.1 q.1.2 q.2).toReal :=
    ENNReal.toReal_pos (hamG_pos N k t h q.1.1 q.1.2 q.2).ne' ENNReal.ofReal_ne_top
  have hhigh := Real.log_le_sub_one_of_pos hpos
  dsimp only [Pi.add_apply] at ⊢
  rw [Real.norm_eq_abs]
  apply abs_le.2
  constructor <;> linarith only [hlow, hhigh, hpos.le,
    le_abs_self (branchHamX N k t h q.1.1 q.1.2 q.2 σ),
    abs_nonneg (branchHamX N k t h q.1.1 q.1.2 q.2 σ)]

theorem lintegral_lintegral_norm_log_hamG_ne_top
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (t : ℝ) (h : Fin N → ℝ) :
    (∫⁻ q, ∫⁻ x, ‖Real.log (hamG N k t h q.1 q.2 x).toReal‖ₑ
      ∂Measure.pi (gaussianMarks N k vs)
      ∂(gaussField N (overlapCovMatrix N ξ)).prod
        (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀))) ≠ ∞ := by
  have hi := (integrable_log_hamG_gaussianLaw N k ξ hS v₀ vs t h).hasFiniteIntegral
  have hG : Measurable (fun q : (EnergySpace N × (Fin N → ℝ)) × (Fin k → Fin N → ℝ) =>
      hamG N k t h q.1.1 q.1.2 q.2) := measurable_hamG_fixedTime N k t h
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hG.ennreal_toReal.log.enorm.aemeasurable] at hi
  exact hi.ne

/-- Joint Gaussian and weight integrability of the actual normalized
log partition at an arbitrary fixed site field. -/
theorem integrable_log_ratio_hamG_weights_gaussian
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (t : ℝ) (h : Fin N → ℝ) :
    Integrable (fun q : CascadeWeights k ×
      ((EnergySpace N × (Fin N → ℝ)) × CascadeMarks (Fin N → ℝ) k) =>
        Real.log ((cascadeSum k (hamG N k t h q.2.1.1 q.2.1.2)
          (cascadeZip k (q.1, q.2.2))).toReal / (weightSum k q.1).toReal))
      ((cascadeWeightsLaw k ms).prod (((gaussField N (overlapCovMatrix N ξ)).prod
        (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀))).prod
          (cascadeMarksLaw k (gaussianMarks N k vs)))) := by
  have hi := integrable_log_cascadeSum_div_prod k
    ((gaussField N (overlapCovMatrix N ξ)).prod
      (Measure.pi (fun _ : Fin N => gaussianReal 0 v₀))) ms (gaussianMarks N k vs)
      (fun q : EnergySpace N × (Fin N → ℝ) => hamG N k t h q.1 q.2)
      hm.1 hm.2.1 hm.2.2 (measurable_hamG_fixedTime N k t h)
      (fun q => hamG_pos N k t h q.1 q.2) (fun _ _ => ENNReal.ofReal_ne_top)
      (lintegral_lintegral_hamG_ne_top N k ξ hS v₀ vs t h)
      (lintegral_lintegral_norm_log_hamG_ne_top N k ξ hS v₀ vs t h)
  simpa only [cascadeSum_one_cascadeZip] using hi

theorem integrable_parisiFixedWeightPressure
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) (t : ℝ) (h : Fin N → ℝ) :
    Integrable (fun w => parisiFixedWeightPressure N k ξ qs h w t) (cascadeWeightsLaw k ms) := by
  have hi := (integrable_log_ratio_hamG_weights_gaussian N k ξ hS ms hm (parisiVar ξ qs 0)
    (fun p => parisiVar ξ qs (p.val + 1)) t h).integral_prod_left.const_mul (1 / (N : ℝ))
  apply hi.congr
  filter_upwards [ae_weightSum_ne_zero_ne_top k ms hm.1 hm.2.1 hm.2.2] with w hw
  exact (parisiFixedWeightPressure_eq_integral_log_ratio N k ξ hS qs h w hw.1 hw.2 t).symm

/-- Weight averaging of the actual normalized fixed-weight pressure
recovers the original Gaussian mean of the Parisi recursion. -/
theorem integral_parisiFixedWeightPressure_eq
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (ms : Fin k → ℝ) (hm : ParisiMAdmissible ms)
    (qs : Fin (k + 1) → ℝ) (t : ℝ) (h : Fin N → ℝ) :
    (∫ w, parisiFixedWeightPressure N k ξ qs h w t ∂cascadeWeightsLaw k ms) =
      (1 / (N : ℝ)) * ∫ q : EnergySpace N × (Fin N → ℝ),
        Real.log (cascadeRec k ms (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1)))
          (hamG N k t h q.1 q.2)).toReal
        ∂(gaussField N (overlapCovMatrix N ξ)).prod
          (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0))) := by
  have he : (∫ w, parisiFixedWeightPressure N k ξ qs h w t ∂cascadeWeightsLaw k ms) =
      (1 / (N : ℝ)) * ∫ w, ∫ q : (EnergySpace N × (Fin N → ℝ)) ×
        CascadeMarks (Fin N → ℝ) k,
        Real.log ((cascadeSum k (hamG N k t h q.1.1 q.1.2) (cascadeZip k (w, q.2))).toReal /
          (weightSum k w).toReal)
        ∂((gaussField N (overlapCovMatrix N ξ)).prod
          (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0)))).prod
            (cascadeMarksLaw k (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1))))
        ∂cascadeWeightsLaw k ms := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_weightSum_ne_zero_ne_top k ms hm.1 hm.2.1 hm.2.2] with w hw
    exact parisiFixedWeightPressure_eq_integral_log_ratio N k ξ hS qs h w hw.1 hw.2 t
  rw [he, ← integral_prod _ (integrable_log_ratio_hamG_weights_gaussian N k ξ hS ms hm
    (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1)) t h)]
  congr 1
  have hh := integral_log_cascadeSum_div_prod_eq k
    ((gaussField N (overlapCovMatrix N ξ)).prod
      (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0)))) ms
      (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1)))
      (fun q : EnergySpace N × (Fin N → ℝ) => hamG N k t h q.1 q.2)
      hm.1 hm.2.1 hm.2.2 (measurable_hamG_fixedTime N k t h)
      (fun q => hamG_pos N k t h q.1 q.2) (fun _ _ => ENNReal.ofReal_ne_top)
      (lintegral_lintegral_hamG_ne_top N k ξ hS _ _ t h)
      (lintegral_lintegral_norm_log_hamG_ne_top N k ξ hS _ _ t h)
      (fun q => cascadeRec_hamG_ne_top N k ms _ hm.2.1 (fun p => (hm.2.2 p).le) t h q.1 q.2)
  simpa only [cascadeSum_one_cascadeZip] using hh

end

end SpinGlass
