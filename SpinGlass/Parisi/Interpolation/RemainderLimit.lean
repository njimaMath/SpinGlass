import SpinGlass.Parisi.Interpolation.TruncatedRemainderPairs
import SpinGlass.Parisi.Interpolation.PairFractionIntegral
import SpinGlass.Parisi.Interpolation.TruncatedDerivative

/-!
# The actual remainder at fixed cascade weights

The finite remainder converges to the constrained cascade expression.
Its Gaussian expectation and time integral converge with the same
profile curvature bound, independently of the number of branches.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

def cascadeProfileRemainder (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ)
    (t : ℝ) (h : Fin N → ℝ) (w : CascadeWeights k)
    (ω : EnergySpace N × MarksSpace N k) : ℝ :=
  (1 / 2 : ℝ) * ∑ r ∈ Finset.range (k + 1), ∑ u ∈ parisiOverlapValues N,
    parisiProfileRemainder ξ u (qExt qs (r + 1)) *
      (cascadePairObservable k r (pairHamGt N k t (constraintR N u) h ω.1 ω.2.1)
          (hamG N k t h ω.1 ω.2.1) w ω.2.2 -
        cascadePairObservable k (r + 1) (pairHamGt N k t (constraintR N u) h ω.1 ω.2.1)
          (hamG N k t h ω.1 ω.2.1) w ω.2.2)

def parisiFixedWeightRemainder (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ)
    (h : Fin N → ℝ) (w : CascadeWeights k) (t : ℝ) : ℝ :=
  ∫ ω, cascadeProfileRemainder N k ξ qs t h w ω
    ∂(gaussField N (overlapCovMatrix N ξ)).prod
      (marksLaw N k (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1)))

theorem measurable_cascadeProfileRemainder (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ)
    (h : Fin N → ℝ) (w : CascadeWeights k) :
    Measurable (fun q : ℝ × (EnergySpace N × MarksSpace N k) =>
      cascadeProfileRemainder N k ξ qs q.1 h w q.2) := by
  have hmap : Measurable (fun q : ℝ × (EnergySpace N × MarksSpace N k) =>
      ((q.1, q.2.1, q.2.2.1), (w, q.2.2.2))) :=
    (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd.fst)).prodMk
      (measurable_const.prodMk measurable_snd.snd.snd)
  have hp (r : ℕ) (u : ℝ) : Measurable
      (fun q : ℝ × (EnergySpace N × MarksSpace N k) =>
        cascadePairObservable k r (pairHamGt N k q.1 (constraintR N u) h q.2.1 q.2.2.1)
          (hamG N k q.1 h q.2.1 q.2.2.1) w q.2.2.2) := by
    have hh := (measurable_cascadePairObservable_prod k
      (U := fun a : ℝ × EnergySpace N × (Fin N → ℝ) =>
        pairHamGt N k a.1 (constraintR N u) h a.2.1 a.2.2)
      (G := fun a : ℝ × EnergySpace N × (Fin N → ℝ) => hamG N k a.1 h a.2.1 a.2.2)
      (measurable_pairHamGt N k (constraintR N u) h)
      (measurable_uncurry_hamG N k h) r).comp hmap
    simp only [Function.comp_def] at hh
    exact hh
  exact measurable_const.mul (Finset.measurable_sum _ fun r _ =>
    Finset.measurable_sum _ fun u _ => measurable_const.mul ((hp r u).sub (hp (r + 1) u)))

theorem measurable_parisiFixedWeightRemainder (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ)
    (h : Fin N → ℝ) (w : CascadeWeights k) :
    Measurable (parisiFixedWeightRemainder N k ξ qs h w) :=
  (measurable_cascadeProfileRemainder N k ξ qs h w).stronglyMeasurable
    |>.integral_prod_right'.measurable

/-- The exact finite remainder tends to its constrained cascade value
whenever the full partition is positive and finite. -/
theorem tendsto_weightedTreeProfileRemainder
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hw : ∀ α, branchWeight k w α ≠ ∞)
    (ω : EnergySpace N × MarksSpace N k)
    (hS0 : cascadeSum k (hamG N k t h ω.1 ω.2.1) (cascadeZip k (w, ω.2.2)) ≠ 0)
    (hS : cascadeSum k (hamG N k t h ω.1 ω.2.1) (cascadeZip k (w, ω.2.2)) ≠ ∞) :
    Tendsto (fun M => weightedTreeProfileRemainder ξ (treeOverlap qs)
      (branchWt (N := N) (truncWt k M w)) (truncHam N k M t h ω)) atTop
        (𝓝 (cascadeProfileRemainder N k ξ qs t h w ω)) := by
  simp_rw [weightedTreeProfileRemainder_eq_pairFractions N k _ ξ qs t h ω.1 ω.2 w hw]
  apply Tendsto.const_mul
  apply tendsto_finsetSum
  intro r _
  apply tendsto_finsetSum
  intro u _
  apply Tendsto.const_mul
  have hU : Measurable (pairHamGt N k t (constraintR N u) h ω.1 ω.2.1) := by
    unfold pairHamGt branchHamX
    fun_prop
  exact tendsto_truncPairObservable_meeting k r hU
    (measurable_hamG' N k t h ω.1 ω.2.1)
    (pairHamGt_le_prod N k t (constraintR_le_one N u) h ω.1 ω.2.1) w ω.2.2 hS0 hS

theorem cascadeProfileRemainder_bounds
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) (t : ℝ) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞)
    (ω : EnergySpace N × MarksSpace N k)
    (hS : cascadeSum k (hamG N k t h ω.1 ω.2.1) (cascadeZip k (w, ω.2.2)) ≠ ∞) :
    0 ≤ cascadeProfileRemainder N k ξ qs t h w ω ∧
      cascadeProfileRemainder N k ξ qs t h w ω ≤ deriv (deriv ξ) 1 := by
  have hw (α) := ne_top_of_le_ne_top hW (branchWeight_le_weightSum k w α)
  have ht := tendsto_weightedTreeProfileRemainder N k ξ qs t h w hw ω
    (cascadeSum_hamG_ne_zero N k t h ω.1 ω.2.1 w hW0 ω.2.2) hS
  obtain ⟨M₀, hM₀⟩ := exists_truncWt_ne_zero k w hW0 hW
  have hqt (M : ℕ) (α γ : TruncBranch k M) : treeOverlap qs α γ ∈ Icc (0 : ℝ) 1 :=
    qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _
  have hb : ∀ᶠ M in atTop,
      weightedTreeProfileRemainder ξ (treeOverlap qs)
        (branchWt (N := N) (truncWt k M w)) (truncHam N k M t h ω) ∈
          Icc (0 : ℝ) (deriv (deriv ξ) 1) := by
    filter_upwards [eventually_ge_atTop M₀] with M hM
    obtain ⟨α, hα⟩ := hM₀ M hM
    exact ⟨weightedTreeProfileRemainder_nonneg hξ _ (hqt M) _
      (fun x => truncWt_nonneg k M w x.2) ⟨(fun _ => true, α), hα⟩ _,
      weightedTreeProfileRemainder_le_curvature hξ _ (hqt M) _
        (fun x => truncWt_nonneg k M w x.2) ⟨(fun _ => true, α), hα⟩ _⟩
  exact isClosed_Icc.mem_of_tendsto ht hb

theorem tendsto_parisiTruncatedGuerraRemainder
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞) (t : ℝ) :
    Tendsto (fun M => parisiTruncatedGuerraRemainder N k M ξ qs h w t) atTop
      (𝓝 (parisiFixedWeightRemainder N k ξ qs h w t)) := by
  obtain ⟨M₀, hM₀⟩ := exists_truncWt_ne_zero k w hW0 hW
  have hqt (M : ℕ) (α γ : TruncBranch k M) : treeOverlap qs α γ ∈ Icc (0 : ℝ) 1 :=
    qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _
  unfold parisiTruncatedGuerraRemainder parisiFixedWeightRemainder
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ => deriv (deriv ξ) 1)
  · filter_upwards [eventually_ge_atTop M₀] with M hM
    obtain ⟨α, hα⟩ := hM₀ M hM
    exact ((continuous_weightedTreeProfileRemainder ξ (treeOverlap qs) _
      (fun x => truncWt_nonneg k M w x.2) ⟨(fun _ => true, α), hα⟩).measurable.comp
        (measurable_truncHam N k M t h)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop M₀] with M hM
    obtain ⟨α, hα⟩ := hM₀ M hM
    apply Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (weightedTreeProfileRemainder_nonneg
      hξ _ (hqt M) (branchWt (N := N) (truncWt k M w))
        (fun x => truncWt_nonneg k M w x.2) ⟨(fun _ => true, α), hα⟩ (truncHam N k M t h ω))]
    exact weightedTreeProfileRemainder_le_curvature hξ _ (hqt M) _
      (fun x => truncWt_nonneg k M w x.2) ⟨(fun _ => true, α), hα⟩ _
  · exact integrable_const _
  · filter_upwards [ae_cascadeSum_hamG_lt_top N k ξ qs t h w hW] with ω hω
    exact tendsto_weightedTreeProfileRemainder N k ξ qs t h w
      (fun α => ne_top_of_le_ne_top hW (branchWeight_le_weightSum k w α)) ω
      (cascadeSum_hamG_ne_zero N k t h ω.1 ω.2.1 w hW0 ω.2.2) hω.ne

theorem integrable_cascadeProfileRemainder
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) (t : ℝ) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞) :
    Integrable (cascadeProfileRemainder N k ξ qs t h w)
      ((gaussField N (overlapCovMatrix N ξ)).prod
        (marksLaw N k (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1)))) := by
  have hmap : Measurable (fun ω : EnergySpace N × MarksSpace N k => (t, ω)) :=
    measurable_const.prodMk measurable_id
  have hm : Measurable (cascadeProfileRemainder N k ξ qs t h w) := by
    have hh := (measurable_cascadeProfileRemainder N k ξ qs h w).comp hmap
    simp only [Function.comp_def] at hh
    exact hh
  apply Integrable.of_bound hm.aestronglyMeasurable (deriv (deriv ξ) 1)
  filter_upwards [ae_cascadeSum_hamG_lt_top N k ξ qs t h w hW] with ω hω
  have hb := cascadeProfileRemainder_bounds N k hξ qs hq t h w hW0 hW ω hω.ne
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

theorem parisiFixedWeightRemainder_bounds
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs) (h : Fin N → ℝ)
    (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞) (t : ℝ) :
    0 ≤ parisiFixedWeightRemainder N k ξ qs h w t ∧
      parisiFixedWeightRemainder N k ξ qs h w t ≤ deriv (deriv ξ) 1 := by
  have hb : ∀ᵐ ω ∂(gaussField N (overlapCovMatrix N ξ)).prod
      (marksLaw N k (parisiVar ξ qs 0) (fun p => parisiVar ξ qs (p.val + 1))),
      0 ≤ cascadeProfileRemainder N k ξ qs t h w ω ∧
        cascadeProfileRemainder N k ξ qs t h w ω ≤ deriv (deriv ξ) 1 := by
    filter_upwards [ae_cascadeSum_hamG_lt_top N k ξ qs t h w hW] with ω hω
    exact cascadeProfileRemainder_bounds N k hξ qs hq t h w hW0 hW ω hω.ne
  refine ⟨integral_nonneg_of_ae (hb.mono fun _ hω => hω.1), ?_⟩
  have hi := integrable_cascadeProfileRemainder N k hξ qs hq t h w hW0 hW
  simpa only [parisiFixedWeightRemainder, integral_const, probReal_univ, one_smul] using
    integral_mono_ae hi (integrable_const (deriv (deriv ξ) 1)) (hb.mono fun _ hω => hω.2)

end

end SpinGlass
