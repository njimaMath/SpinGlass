import SpinGlass.Parisi.Interpolation.PressureLogLimit
import SpinGlass.Parisi.Interpolation.TruncatedDerivative

/-!
# The normalized pressure limit at fixed cascade weights

The Gaussian law is explicitly reassociated to match the logarithmic
limit. Both the partition and the total-weight normalization pass to the
limit in the actual finite-tree pressure.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

def parisiFixedWeightPressure (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ)
    (h : Fin N → ℝ) (w : CascadeWeights k) (t : ℝ) : ℝ :=
  (1 / (N : ℝ)) * (∫ q : (EnergySpace N × (Fin N → ℝ)) × CascadeMarks (Fin N → ℝ) k,
    Real.log (cascadeSum k (hamG N k t h q.1.1 q.1.2) (cascadeZip k (w, q.2))).toReal
    ∂((gaussField N (overlapCovMatrix N ξ)).prod
      (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0)))).prod
        (cascadeMarksLaw k (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1))))) -
    (1 / (N : ℝ)) * Real.log (weightSum k w).toReal

theorem wZ_truncHam_eq_truncSum (M : ℕ) (t : ℝ) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hw : ∀ α, branchWeight k w α ≠ ∞)
    (ω : EnergySpace N × MarksSpace N k) :
    wZ (branchWt (N := N) (truncWt k M w)) (truncHam N k M t h ω) =
      (truncSum k M w (hamG N k t h ω.1 ω.2.1) ω.2.2).toReal := by
  rw [wZ_truncHam, toReal_truncSum k M w hw
    (Gt := hamG N k t h ω.1 ω.2.1) (fun _ => ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro α _
  rw [hamG, ENNReal.toReal_ofReal (branchZX_pos N k t h ω.1 ω.2.1 _).le, branchZ_eq]

theorem parisiTruncatedPressure_eq_log_truncSum (M : ℕ)
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hw : ∀ α, branchWeight k w α ≠ ∞) :
    parisiTruncatedPressure N k M ξ qs h w t =
      (1 / (N : ℝ)) * (∫ q : (EnergySpace N × (Fin N → ℝ)) × CascadeMarks (Fin N → ℝ) k,
        Real.log (truncSum k M w (hamG N k t h q.1.1 q.1.2) q.2).toReal
        ∂((gaussField N (overlapCovMatrix N ξ)).prod
          (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0)))).prod
            (cascadeMarksLaw k (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1))))) -
        (1 / (N : ℝ)) * Real.log (∑ α, truncWt k M w α) := by
  have hm₀ : Measurable (fun q : (EnergySpace N × (Fin N → ℝ)) ×
      CascadeMarks (Fin N → ℝ) k =>
        Real.log (truncSum k M w (hamG N k t h q.1.1 q.1.2) q.2).toReal) :=
    measurable_log_truncSum_of k (fun q : EnergySpace N × (Fin N → ℝ) =>
      hamG N k t h q.1 q.2) (measurable_hamG_fixedTime N k t h) M w
  have hmap : Measurable (fun ω : EnergySpace N × MarksSpace N k =>
      ((ω.1, ω.2.1), ω.2.2)) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd
  have hm : Measurable (fun ω : EnergySpace N × MarksSpace N k =>
      Real.log (truncSum k M w (hamG N k t h ω.1 ω.2.1) ω.2.2).toReal) := by
    have hh := hm₀.comp hmap
    simp only [Function.comp_def] at hh
    exact hh
  unfold parisiTruncatedPressure
  simp_rw [wFreeEnergy, wZ_truncHam_eq_truncSum N k M t h w hw]
  rw [integral_const_mul]
  congr 2
  unfold marksLaw
  rw [← Measure.prodAssoc_prod,
    integral_map MeasurableEquiv.prodAssoc.measurable.aemeasurable hm.aestronglyMeasurable]
  rfl

/-- The actual normalized finite-tree pressure converges at every fixed
time and every weight sample of positive finite total mass. -/
theorem tendsto_parisiTruncatedPressure
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) (w : CascadeWeights k)
    (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞) (t : ℝ) :
    Tendsto (fun M => parisiTruncatedPressure N k M ξ qs h w t) atTop
      (𝓝 (parisiFixedWeightPressure N k ξ qs h w t)) := by
  have hw (α) : branchWeight k w α ≠ ∞ :=
    ne_top_of_le_ne_top hW (branchWeight_le_weightSum k w α)
  simp_rw [parisiTruncatedPressure_eq_log_truncSum N k _ ξ qs t h w hw]
  have hp := (tendsto_integral_log_truncSum_hamG N k ξ hS (parisiVar ξ qs 0)
    (fun p => parisiVar ξ qs (p.val + 1)) t h w hW0 hW).const_mul (1 / (N : ℝ))
  have hnorm := ((tendsto_toReal_sum_truncBranch k (branchWeight k w) hW).log
    (ENNReal.toReal_pos hW0 hW).ne').const_mul (1 / (N : ℝ))
  exact hp.sub hnorm

/-- The limiting pressure is the expectation of the original normalized
cascade partition at fixed weights. -/
theorem parisiFixedWeightPressure_eq_integral_log_ratio
    (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef)
    (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) (w : CascadeWeights k)
    (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞) (t : ℝ) :
    parisiFixedWeightPressure N k ξ qs h w t =
      (1 / (N : ℝ)) * (∫ q : (EnergySpace N × (Fin N → ℝ)) × CascadeMarks (Fin N → ℝ) k,
        Real.log ((cascadeSum k (hamG N k t h q.1.1 q.1.2) (cascadeZip k (w, q.2))).toReal /
          (weightSum k w).toReal)
        ∂((gaussField N (overlapCovMatrix N ξ)).prod
          (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0)))).prod
            (cascadeMarksLaw k (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1))))) := by
  let P := ((gaussField N (overlapCovMatrix N ξ)).prod
    (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0)))).prod
      (cascadeMarksLaw k (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1))))
  let S := fun q : (EnergySpace N × (Fin N → ℝ)) × CascadeMarks (Fin N → ℝ) k =>
    cascadeSum k (hamG N k t h q.1.1 q.1.2) (cascadeZip k (w, q.2))
  have hmap : Measurable (fun q : (EnergySpace N × (Fin N → ℝ)) ×
      CascadeMarks (Fin N → ℝ) k => (q.1.1, (q.1.2, q.2))) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  have hSm : Measurable S := by
    have hh := (measurable_cascadeSum_hamG' N k t h w).comp hmap
    simp only [Function.comp_def] at hh
    exact hh
  have htop : ∀ᵐ q ∂P, S q < ∞ := ae_lt_top hSm
    (lintegral_cascadeSum_hamG_ne_top N k ξ hS (parisiVar ξ qs 0)
      (fun p => parisiVar ξ qs (p.val + 1)) t h w hW)
  have hi : Integrable (fun q => Real.log (S q).toReal) P :=
    integrable_log_cascadeSum_hamG N k ξ hS (parisiVar ξ qs 0)
      (fun p => parisiVar ξ qs (p.val + 1)) t h w hW0 hW
  have he : (∫ q, Real.log ((S q).toReal / (weightSum k w).toReal) ∂P) =
      (∫ q, Real.log (S q).toReal ∂P) - Real.log (weightSum k w).toReal := by
    calc
      _ = ∫ q, Real.log (S q).toReal - Real.log (weightSum k w).toReal ∂P := by
        apply integral_congr_ae
        filter_upwards [htop] with q hq
        exact Real.log_div (ENNReal.toReal_pos
          (cascadeSum_hamG_ne_zero N k t h q.1.1 q.1.2 w hW0 q.2) hq.ne).ne'
          (ENNReal.toReal_pos hW0 hW).ne'
      _ = _ := by rw [integral_sub hi (integrable_const _), integral_const,
        probReal_univ, one_smul]
  change (1 / (N : ℝ)) * (∫ q, Real.log (S q).toReal ∂P) -
    (1 / (N : ℝ)) * Real.log (weightSum k w).toReal =
      (1 / (N : ℝ)) * (∫ q, Real.log ((S q).toReal / (weightSum k w).toReal) ∂P)
  rw [he, mul_sub]

end

end SpinGlass
