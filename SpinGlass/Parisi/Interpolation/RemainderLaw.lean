import SpinGlass.Parisi.Interpolation.PairGaussianTransport
import SpinGlass.Parisi.Interpolation.RemainderLimit
import SpinGlass.Parisi.Interpolation.LocalizedRemainder

/-!
# Identifying the cascade remainder with the physical remainder

The joint tree law, Gaussian disorder, root marks and i.i.d. field law
are transported explicitly. The resulting observable is precisely the
one to which the localization estimates apply.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

theorem measurable_cascadePairObservable_pairHamGt
    (c : (Fin 2 → Config N) → ℝ) (r : ℕ) :
    Measurable (fun q : (ℝ × ((EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ))) ×
      (CascadeWeights k × CascadeMarks (Fin N → ℝ) k) =>
        cascadePairObservable k r (pairHamGt N k q.1.1 c q.1.2.2 q.1.2.1.1 q.1.2.1.2)
          (hamG N k q.1.1 q.1.2.2 q.1.2.1.1 q.1.2.1.2) q.2.1 q.2.2) := by
  apply measurable_cascadePairObservable_prod k
    (U := fun a : ℝ × ((EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ)) =>
      pairHamGt N k a.1 c a.2.2 a.2.1.1 a.2.1.2)
    (G := fun a : ℝ × ((EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ)) =>
      hamG N k a.1 a.2.2 a.2.1.1 a.2.1.2)
  · unfold Function.uncurry pairHamGt branchHamX
    fun_prop
  · unfold Function.uncurry hamG branchZX branchHamX
    fun_prop

theorem norm_cascadePairObservable_pairHamGt_sub_le_one
    (r : ℕ) (t : ℝ) {c : (Fin 2 → Config N) → ℝ} (hc : ∀ σ, c σ ≤ 1)
    (h : Fin N → ℝ) (H : EnergySpace N) (z : Fin N → ℝ)
    (w : CascadeWeights k) (y : CascadeMarks (Fin N → ℝ) k) :
    ‖cascadePairObservable k r (pairHamGt N k t c h H z) (hamG N k t h H z) w y -
      cascadePairObservable k (r + 1) (pairHamGt N k t c h H z) (hamG N k t h H z) w y‖ ≤ 1 := by
  have hlo (j) := cascadePairObservable_nonneg k j (pairHamGt N k t c h H z)
    (hamG N k t h H z) w y
  have hhi (j) := cascadePairObservable_le_one k j (measurable_hamG' N k t h H z)
    (pairHamGt_le_prod N k t hc h H z) w y
  rw [Real.norm_eq_abs, abs_sub_le_iff]
  constructor <;> linarith only [hlo r, hlo (r + 1), hhi r, hhi (r + 1)]

theorem parisiBranchMeetingMass_eq_base_tree
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (r : Fin (k + 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (u : ℝ) :
    parisiBranchMeetingMass N μh ξ ms qs r t u =
      ∫ z, ∫ q : CascadeWeights k × CascadeMarks (Fin N → ℝ) k,
        cascadePairObservable k r.val (pairHamGt N k t (constraintR N u) z.2 z.1.1 z.1.2)
            (hamG N k t z.2 z.1.1 z.1.2) q.1 q.2 -
          cascadePairObservable k (r.val + 1)
            (pairHamGt N k t (constraintR N u) z.2 z.1.1 z.1.2)
            (hamG N k t z.2 z.1.1 z.1.2) q.1 q.2
        ∂(cascadeWeightsLaw k ms).prod
          (cascadeMarksLaw k (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1))))
        ∂parisiBaseDisorderFieldLaw N μh ξ qs := by
  have hT := measurePreserving_parisiInterpolationScaling μh ξ qs hS ht
  have hF := measurable_unscaledBranchMeetingMass ms (parisiAuxLevelVars ξ qs t)
    hm r (constraintR_le_one N u)
  unfold parisiBranchMeetingMass
  rw [← hT.map_eq, integral_map hT.measurable.aemeasurable hF.aestronglyMeasurable]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  exact (integral_pairHamGt_meeting_eq_unscaledBranchMeetingMass N k ms
    (fun p => parisiVar ξ qs (p.val + 1)) r.val ht.2 (constraintR N u) z.2 z.1.1 z.1.2).symm

/-- The physical localized remainder is the actual full-cascade
remainder under the fixed joint Gaussian, field and tree laws. -/
theorem parisiGuerraRemainder_eq_base_tree
    (μh : Measure ℝ) [IsProbabilityMeasure μh] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hS : (overlapCovMatrix N ξ).PosSemidef) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiGuerraRemainder N μh ξ ms qs t =
      ∫ q : ((EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ)) ×
        (CascadeWeights k × CascadeMarks (Fin N → ℝ) k),
        cascadeProfileRemainder N k ξ qs t q.1.2 q.2.1 (q.1.1.1, (q.1.1.2, q.2.2))
        ∂(parisiBaseDisorderFieldLaw N μh ξ qs).prod ((cascadeWeightsLaw k ms).prod
          (cascadeMarksLaw k (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1))))) := by
  let P := parisiBaseDisorderFieldLaw N μh ξ qs
  let Q := (cascadeWeightsLaw k ms).prod
    (cascadeMarksLaw k (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1))))
  let F := fun r u (q : ((EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ)) ×
      (CascadeWeights k × CascadeMarks (Fin N → ℝ) k)) =>
    cascadePairObservable k r (pairHamGt N k t (constraintR N u) q.1.2 q.1.1.1 q.1.1.2)
        (hamG N k t q.1.2 q.1.1.1 q.1.1.2) q.2.1 q.2.2 -
      cascadePairObservable k (r + 1) (pairHamGt N k t (constraintR N u) q.1.2 q.1.1.1 q.1.1.2)
        (hamG N k t q.1.2 q.1.1.1 q.1.1.2) q.2.1 q.2.2
  have hmap : Measurable (fun q : ((EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ)) ×
      (CascadeWeights k × CascadeMarks (Fin N → ℝ) k) => ((t, q.1), q.2)) :=
    (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  have hFm (r : ℕ) (u : ℝ) : Measurable (F r u) := by
    have hh := ((measurable_cascadePairObservable_pairHamGt N k (constraintR N u) r).sub
      (measurable_cascadePairObservable_pairHamGt N k (constraintR N u) (r + 1))).comp hmap
    simp only [Function.comp_def] at hh
    exact hh
  have hi (r : ℕ) (u : ℝ) : Integrable (F r u) (P.prod Q) := by
    apply Integrable.of_bound (hFm r u).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun q =>
      norm_cascadePairObservable_pairHamGt_sub_le_one N k r t (constraintR_le_one N u)
        q.1.2 q.1.1.1 q.1.1.2 q.2.1 q.2.2
  have he (r : Fin (k + 1)) (u : ℝ) :
      parisiBranchMeetingMass N μh ξ ms qs r t u = ∫ q, F r.val u q ∂P.prod Q := by
    rw [parisiBranchMeetingMass_eq_base_tree N k μh ξ ms qs hm hS r ht u]
    exact (integral_prod _ (hi r.val u)).symm
  have hterm (r : ℕ) (u : ℝ) : Integrable
      (fun q => parisiProfileRemainder ξ u (qExt qs (r + 1)) * F r u q) (P.prod Q) :=
    (hi r u).const_mul _
  change (1 / 2 : ℝ) * (∑ r : Fin (k + 1), ∑ u ∈ parisiOverlapValues N,
    parisiProfileRemainder ξ u (qs r) * parisiBranchMeetingMass N μh ξ ms qs r t u) =
      ∫ q, (1 / 2 : ℝ) * (∑ r ∈ Finset.range (k + 1), ∑ u ∈ parisiOverlapValues N,
        parisiProfileRemainder ξ u (qExt qs (r + 1)) * F r u q) ∂P.prod Q
  rw [integral_const_mul]
  congr 1
  simp_rw [he]
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun u _ => hterm r u))]
  simp_rw [integral_finsetSum _ (fun u _ => hterm _ u), integral_const_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  rw [qExt_succ_of_lt qs r.isLt]

end

end SpinGlass
