import SpinGlass.Parisi.Interpolation.RemainderLaw

/-!
# Averaging the fixed-weight remainder

A finite coefficient bound gives joint integrability before imposing
profile assumptions. Fubini and explicit product-law reassociation
identify the weight and field average with the physical remainder.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

theorem measurable_cascadeProfileRemainder_joint
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) :
    Measurable (fun q : (ℝ × ((EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ))) ×
      (CascadeWeights k × CascadeMarks (Fin N → ℝ) k) =>
        cascadeProfileRemainder N k ξ qs q.1.1 q.1.2.2 q.2.1
          (q.1.2.1.1, (q.1.2.1.2, q.2.2))) :=
  measurable_const.mul (Finset.measurable_sum _ fun r _ =>
    Finset.measurable_sum _ fun u _ => measurable_const.mul
      ((measurable_cascadePairObservable_pairHamGt N k (constraintR N u) r).sub
        (measurable_cascadePairObservable_pairHamGt N k (constraintR N u) (r + 1))))

theorem norm_cascadeProfileRemainder_le
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ) (h : Fin N → ℝ)
    (w : CascadeWeights k) (ω : EnergySpace N × MarksSpace N k) :
    ‖cascadeProfileRemainder N k ξ qs t h w ω‖ ≤
      (1 / 2 : ℝ) * ∑ r ∈ Finset.range (k + 1), ∑ u ∈ parisiOverlapValues N,
        |parisiProfileRemainder ξ u (qExt qs (r + 1))| := by
  unfold cascadeProfileRemainder
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro r _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro u _
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (norm_cascadePairObservable_pairHamGt_sub_le_one N k r t (constraintR_le_one N u)
      h ω.1 ω.2.1 w ω.2.2)

theorem measurable_parisiFixedWeightRemainder_joint
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) :
    Measurable (fun q : ((Fin N → ℝ) × CascadeWeights k) × ℝ =>
      parisiFixedWeightRemainder N k ξ qs q.1.1 q.1.2 q.2) := by
  have hmap : Measurable (fun p : (((Fin N → ℝ) × CascadeWeights k) × ℝ) ×
      (EnergySpace N × MarksSpace N k) =>
        ((p.1.2, ((p.2.1, p.2.2.1), p.1.1.1)), (p.1.1.2, p.2.2.2))) := by fun_prop
  have hm := (measurable_cascadeProfileRemainder_joint N k ξ qs).comp hmap
  simp only [Function.comp_def] at hm
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem norm_parisiFixedWeightRemainder_le
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ) (h : Fin N → ℝ) (w : CascadeWeights k) :
    ‖parisiFixedWeightRemainder N k ξ qs h w t‖ ≤
      (1 / 2 : ℝ) * ∑ r ∈ Finset.range (k + 1), ∑ u ∈ parisiOverlapValues N,
        |parisiProfileRemainder ξ u (qExt qs (r + 1))| := by
  unfold parisiFixedWeightRemainder
  exact (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun ω =>
    norm_cascadeProfileRemainder_le N k ξ qs t h w ω)).trans_eq (by rw [probReal_univ, mul_one])

/-- Averaging the exact fixed-weight remainder in the weights and the
i.i.d. fields recovers the original physical remainder. -/
theorem integral_parisiFixedWeightRemainder_eq
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hS : (overlapCovMatrix N ξ).PosSemidef) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ h, ∫ w, parisiFixedWeightRemainder N k ξ qs h w t
      ∂cascadeWeightsLaw k ms ∂externalFieldVecLaw N μh) =
        parisiGuerraRemainder N μh ξ ms qs t := by
  let P := (gaussField N (overlapCovMatrix N ξ)).prod
    (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0)))
  let Ph := externalFieldVecLaw N μh
  let Pw := cascadeWeightsLaw k ms
  let Pc := cascadeMarksLaw k (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1)))
  let C := (1 / 2 : ℝ) * ∑ r ∈ Finset.range (k + 1), ∑ u ∈ parisiOverlapValues N,
    |parisiProfileRemainder ξ u (qExt qs (r + 1))|
  let F := fun q : ((Fin N → ℝ) × CascadeWeights k) ×
      ((EnergySpace N × (Fin N → ℝ)) × CascadeMarks (Fin N → ℝ) k) =>
    cascadeProfileRemainder N k ξ qs t q.1.1 q.1.2 (q.2.1.1, (q.2.1.2, q.2.2))
  have hmapF : Measurable (fun q : ((Fin N → ℝ) × CascadeWeights k) ×
      ((EnergySpace N × (Fin N → ℝ)) × CascadeMarks (Fin N → ℝ) k) =>
        ((t, (q.2.1, q.1.1)), (q.1.2, q.2.2))) := by fun_prop
  have hFm : Measurable F := by
    have hh := (measurable_cascadeProfileRemainder_joint N k ξ qs).comp hmapF
    simp only [Function.comp_def] at hh
    exact hh
  have hFi : Integrable F ((Ph.prod Pw).prod (P.prod Pc)) :=
    Integrable.of_bound hFm.aestronglyMeasurable C (Filter.Eventually.of_forall fun q =>
      norm_cascadeProfileRemainder_le N k ξ qs t q.1.1 q.1.2 (q.2.1.1, (q.2.1.2, q.2.2)))
  have he (h : Fin N → ℝ) (w : CascadeWeights k) :
      parisiFixedWeightRemainder N k ξ qs h w t = ∫ z, F ((h, w), z) ∂P.prod Pc := by
    have hmap : Measurable (fun z : (EnergySpace N × (Fin N → ℝ)) ×
        CascadeMarks (Fin N → ℝ) k => (z.1.1, (z.1.2, z.2))) := by fun_prop
    have hf : Measurable (cascadeProfileRemainder N k ξ qs t h w) := by
      have ha : Measurable (fun ω : EnergySpace N × MarksSpace N k => (t, ω)) :=
        measurable_const.prodMk measurable_id
      have hh := (measurable_cascadeProfileRemainder N k ξ qs h w).comp ha
      simp only [Function.comp_def] at hh
      exact hh
    unfold parisiFixedWeightRemainder marksLaw
    rw [← Measure.prodAssoc_prod,
      integral_map MeasurableEquiv.prodAssoc.measurable.aemeasurable hf.aestronglyMeasurable]
    rfl
  simp_rw [he]
  rw [← integral_prod _ hFi.integral_prod_left, ← integral_prod _ hFi]
  rw [parisiGuerraRemainder_eq_base_tree N k μh ξ ms qs hm hS ht]
  let A := fun q : (EnergySpace N × (Fin N → ℝ)) ×
      ((Fin N → ℝ) × (CascadeWeights k × CascadeMarks (Fin N → ℝ) k)) =>
    cascadeProfileRemainder N k ξ qs t q.2.1 q.2.2.1 (q.1.1, (q.1.2, q.2.2.2))
  have hmapA : Measurable (fun q : (EnergySpace N × (Fin N → ℝ)) ×
      ((Fin N → ℝ) × (CascadeWeights k × CascadeMarks (Fin N → ℝ) k)) =>
        ((t, (q.1, q.2.1)), q.2.2)) := by fun_prop
  have hAm : Measurable A := by
    have hh := (measurable_cascadeProfileRemainder_joint N k ξ qs).comp hmapA
    simp only [Function.comp_def] at hh
    exact hh
  have hleft : (∫ q, F q ∂(Ph.prod Pw).prod (P.prod Pc)) =
      ∫ q, A q ∂P.prod (Ph.prod (Pw.prod Pc)) := by
    have hp : Measurable (fun q : ((Fin N → ℝ) × CascadeWeights k) ×
        ((EnergySpace N × (Fin N → ℝ)) × CascadeMarks (Fin N → ℝ) k) =>
          (q.2.1, (q.1.1, (q.1.2, q.2.2)))) := by fun_prop
    rw [Measure.prod_swap_left₄ P Ph Pw Pc,
      integral_map hp.aemeasurable hAm.aestronglyMeasurable]
  rw [hleft, ← Measure.prodAssoc_prod,
    integral_map MeasurableEquiv.prodAssoc.measurable.aemeasurable hAm.aestronglyMeasurable]
  rfl

end

end SpinGlass
