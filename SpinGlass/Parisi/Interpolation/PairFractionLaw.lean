import SpinGlass.Parisi.Interpolation.PairFractionIntegral
import SpinGlass.Parisi.Tree.LevelBound.Convergence
import SpinGlass.Parisi.Concentration.PairBranchMeeting

/-!
# Constrained finite-tree limits under the actual cascade law

Admissible cascade weights and a finite branch mean give positivity and
finiteness of the partition almost surely. The resulting finite-tree
meeting limit is identified with the physical branch-meeting observable.
-/

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

universe u

variable {T : Type u} [MeasurableSpace T] (k : ℕ)

theorem measurable_truncPairObservable
    {U : (Fin k → T × T) → ℝ≥0∞} {G : (Fin k → T) → ℝ≥0∞}
    (hU : Measurable U) (hG : Measurable G) (M r : ℕ) :
    Measurable (fun q : CascadeWeights k × CascadeMarks T k =>
      truncPairObservable k M r U G q.1 q.2) := by
  have hw (α : TruncBranch k M) : Measurable
      (fun q : CascadeWeights k × CascadeMarks T k =>
        branchWeight k q.1 (truncBranchCoe k M α)) :=
    (measurable_branchWeight k _).comp measurable_fst
  have hz (α : TruncBranch k M) : Measurable
      (fun q : CascadeWeights k × CascadeMarks T k =>
        branchMarks k q.2 (truncBranchCoe k M α)) :=
    (measurable_branchMarks k _).comp measurable_snd
  have hu (α γ : TruncBranch k M) : Measurable
      (fun q : CascadeWeights k × CascadeMarks T k =>
        U (fun p => (branchMarks k q.2 (truncBranchCoe k M α) p,
          branchMarks k q.2 (truncBranchCoe k M γ) p))) :=
    hU.comp (measurable_pi_lambda _ fun p =>
      ((measurable_pi_apply p).comp (hz α)).prodMk ((measurable_pi_apply p).comp (hz γ)))
  unfold truncPairObservable truncPairNumerator
  exact ((Finset.measurable_sum _ fun α _ => Finset.measurable_sum _ fun γ _ =>
    measurable_const.mul (((hw α).mul (hw γ)).mul (hu α γ))).mul
      ((Finset.measurable_sum _ fun α _ => (hw α).mul (hG.comp (hz α))).inv.pow_const 2))
    |>.ennreal_toReal

theorem ae_cascadeSum_cascadeZip_ne_zero_ne_top
    (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ p, IsProbabilityMeasure (μs p)]
    (hsm : StrictMono ms) (hpos : ∀ p, 0 < ms p) (hlt : ∀ p, ms p < 1)
    {G : (Fin k → T) → ℝ≥0∞} (hG : Measurable G) (hGpos : ∀ x, 0 < G x)
    (hfin : (∫⁻ x, G x ∂Measure.pi μs) ≠ ∞) :
    ∀ᵐ q ∂(cascadeWeightsLaw k ms).prod (cascadeMarksLaw k μs),
      cascadeSum k G (cascadeZip k q) ≠ 0 ∧ cascadeSum k G (cascadeZip k q) ≠ ∞ := by
  have hm : Measurable (fun q : CascadeWeights k × CascadeMarks T k =>
      cascadeSum k G (cascadeZip k q)) :=
    (measurable_cascadeSum k hG).comp (measurable_cascadeZip k)
  have hs : MeasurableSet {q : CascadeWeights k × CascadeMarks T k |
      cascadeSum k G (cascadeZip k q) ≠ 0 ∧ cascadeSum k G (cascadeZip k q) ≠ ∞} :=
    (hm (measurableSet_singleton 0)).compl.inter (hm (measurableSet_singleton ∞)).compl
  rw [Measure.ae_prod_iff_ae_ae hs]
  filter_upwards [ae_weightSum_ne_zero_ne_top k ms hsm hpos hlt] with w hw
  have hmean : (∫⁻ z, cascadeSum k G (cascadeZip k (w, z)) ∂cascadeMarksLaw k μs) ≠ ∞ := by
    rw [lintegral_cascadeSum_cascadeZip k μs w hG]
    exact ENNReal.mul_ne_top hw.2 hfin
  have hmeas : Measurable (fun z : CascadeMarks T k =>
      cascadeSum k G (cascadeZip k (w, z))) :=
    hm.comp (measurable_const.prodMk measurable_id)
  filter_upwards [ae_lt_top hmeas hmean] with z hz
  refine ⟨?_, hz.ne⟩
  rw [cascadeSum_cascadeZip k hG]
  intro he
  rw [ENNReal.tsum_eq_zero] at he
  apply hw.1
  apply ENNReal.tsum_eq_zero.2
  intro α
  exact (mul_eq_zero.1 (he α)).resolve_right (hGpos _).ne'

/-- Convergence in mean under the weights/marks product law, with its
limit expressed on the actual recursive cascade probability space. -/
theorem tendsto_integral_truncPairObservable_cascadeLaw [Nonempty T]
    (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ p, IsProbabilityMeasure (μs p)]
    (hsm : StrictMono ms) (hpos : ∀ p, 0 < ms p) (hlt : ∀ p, ms p < 1)
    {U : (Fin k → T × T) → ℝ≥0∞} {G : (Fin k → T) → ℝ≥0∞}
    (hU : Measurable U) (hG : Measurable G) (hGpos : ∀ x, 0 < G x)
    (hUG : ∀ x, U x ≤ G (fun p => (x p).1) * G (fun p => (x p).2))
    (hfin : (∫⁻ x, G x ∂Measure.pi μs) ≠ ∞) (r : ℕ) :
    Tendsto (fun M => ∫ q, truncPairObservable k M r U G q.1 q.2
      ∂(cascadeWeightsLaw k ms).prod (cascadeMarksLaw k μs)) atTop
      (𝓝 (∫ ω, (cascadeSqPair k r U ω * (cascadeSum k G ω)⁻¹ ^ 2).toReal
        ∂cascadeLaw k ms μs)) := by
  have he : (∫ ω, (cascadeSqPair k r U ω * (cascadeSum k G ω)⁻¹ ^ 2).toReal
      ∂cascadeLaw k ms μs) = ∫ q, cascadePairObservable k r U G q.1 q.2
        ∂(cascadeWeightsLaw k ms).prod (cascadeMarksLaw k μs) := by
    rw [cascadeLaw_eq_map_cascadeZip]
    exact integral_map (measurable_cascadeZip k).aemeasurable
      (((measurable_cascadeSqPair k r hU).mul
        ((measurable_cascadeSum k hG).inv.pow_const 2)).ennreal_toReal).aestronglyMeasurable
  rw [he]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro M
    exact (measurable_truncPairObservable k hU hG M r).aestronglyMeasurable
  · exact integrable_const _
  · intro M
    apply Filter.Eventually.of_forall
    intro q
    rw [Real.norm_eq_abs, abs_of_nonneg (truncPairObservable_nonneg k M r _ _ _ _)]
    exact truncPairObservable_le_one k M r hUG q.1 q.2
  · filter_upwards [ae_cascadeSum_cascadeZip_ne_zero_ne_top k ms μs hsm hpos hlt
      hG hGpos hfin] with q hq
    exact tendsto_truncPairObservable k r hU hG hUG q.1 q.2 hq.1 hq.2

/-- The finite constrained meeting mass converges to the physical
Gaussian branch-meeting mass, including empty constraints and endpoints. -/
theorem tendsto_integral_trunc_unscaledBranchMeetingMass {N : ℕ}
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hm : ParisiMAdmissible ms)
    (r : ℕ) {c : (Fin 2 → Config N) → ℝ} (hc1 : ∀ σ, c σ ≤ 1)
    (H : EnergySpace N) (h z : Fin N → ℝ) :
    Tendsto (fun M => ∫ q,
      truncPairObservable k M r (unscaledPairHamG N k c H h z)
          (unscaledHamG N k H h z) q.1 q.2 -
        truncPairObservable k M (r + 1) (unscaledPairHamG N k c H h z)
          (unscaledHamG N k H h z) q.1 q.2
      ∂(cascadeWeightsLaw k ms).prod (cascadeMarksLaw k (gaussianMarks N k vs))) atTop
      (𝓝 (unscaledBranchMeetingMass ms vs r c H h z)) := by
  have hU := measurable_unscaledPairHamG (k := k) c H h z
  have hG := measurable_unscaledHamG (k := k) H h z
  have hUG (x) : unscaledPairHamG N k c H h z x ≤
      unscaledHamG N k H h z (fun p => (x p).1) *
        unscaledHamG N k H h z (fun p => (x p).2) := by
    rw [← unscaledPairHamG_one_eq_prod]
    unfold unscaledPairHamG
    exact ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun σ _ =>
      mul_le_mul_of_nonneg_right (hc1 σ) (Real.exp_nonneg _))
  have hlim (j) := tendsto_integral_truncPairObservable_cascadeLaw k ms
    (gaussianMarks N k vs) hm.1 hm.2.1 hm.2.2 hU hG
    (unscaledHamG_pos H h z) hUG (lintegral_unscaledHamG_ne_top vs H h z) j
  have hi (M j) : Integrable (fun q : CascadeWeights k × CascadeMarks (Fin N → ℝ) k =>
      truncPairObservable k M j (unscaledPairHamG N k c H h z)
        (unscaledHamG N k H h z) q.1 q.2)
      ((cascadeWeightsLaw k ms).prod (cascadeMarksLaw k (gaussianMarks N k vs))) := by
    apply Integrable.of_bound (measurable_truncPairObservable k hU hG M j).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro q
    rw [Real.norm_eq_abs, abs_of_nonneg (truncPairObservable_nonneg k M j _ _ _ _)]
    exact truncPairObservable_le_one k M j hUG q.1 q.2
  unfold unscaledBranchMeetingMass
  simp_rw [integral_sub (hi _ r) (hi _ (r + 1))]
  rw [integral_sub (integrable_unscaledBranchPrefixMass ms vs r hc1 H h z)
    (integrable_unscaledBranchPrefixMass ms vs (r + 1) hc1 H h z)]
  exact (hlim r).sub (hlim (r + 1))

end

end SpinGlass
