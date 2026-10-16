import SpinGlass.Parisi.Interpolation.PairFractionLimit
import Common.Mathlib.Probability.PointProcess.CascadeBranchLaw

/-!
# Averaging the constrained finite-tree limit

Joint measurability and a bound by one allow the actual constrained prefix
fractions to pass to the limit under any finite joint parameter/tree law.
No independence or convergence of conditional means is assumed here.
-/

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace SpinGlass

noncomputable section

universe u

variable {T Θ : Type u} [MeasurableSpace T] [MeasurableSpace Θ] (k : ℕ)
    {G : Θ → (Fin k → T) → ℝ≥0∞} {U : Θ → (Fin k → T × T) → ℝ≥0∞}

theorem measurable_truncPairObservable_prod
    (hU : Measurable (uncurry U)) (hG : Measurable (uncurry G)) (M r : ℕ) :
    Measurable (fun q : Θ × (CascadeWeights k × CascadeMarks T k) =>
      truncPairObservable k M r (U q.1) (G q.1) q.2.1 q.2.2) := by
  have hw (α : TruncBranch k M) : Measurable
      (fun q : Θ × (CascadeWeights k × CascadeMarks T k) =>
        branchWeight k q.2.1 (truncBranchCoe k M α)) :=
    (measurable_branchWeight k _).comp measurable_snd.fst
  have hz (α : TruncBranch k M) : Measurable
      (fun q : Θ × (CascadeWeights k × CascadeMarks T k) =>
        branchMarks k q.2.2 (truncBranchCoe k M α)) :=
    (measurable_branchMarks k _).comp measurable_snd.snd
  have hGa (α : TruncBranch k M) : Measurable
      (fun q : Θ × (CascadeWeights k × CascadeMarks T k) =>
        G q.1 (branchMarks k q.2.2 (truncBranchCoe k M α))) :=
    hG.comp (measurable_fst.prodMk (hz α))
  have hUa (α γ : TruncBranch k M) : Measurable
      (fun q : Θ × (CascadeWeights k × CascadeMarks T k) =>
        U q.1 (fun p => (branchMarks k q.2.2 (truncBranchCoe k M α) p,
          branchMarks k q.2.2 (truncBranchCoe k M γ) p))) :=
    hU.comp (measurable_fst.prodMk (measurable_pi_lambda _ (fun p =>
      ((measurable_pi_apply p).comp (hz α)).prodMk ((measurable_pi_apply p).comp (hz γ)))))
  unfold truncPairObservable truncPairNumerator
  exact ((Finset.measurable_sum _ fun α _ => Finset.measurable_sum _ fun γ _ =>
    measurable_const.mul (((hw α).mul (hw γ)).mul (hUa α γ))).mul
      ((Finset.measurable_sum _ fun α _ => (hw α).mul (hGa α)).inv.pow_const 2)).ennreal_toReal

theorem measurable_cascadePairObservable_prod
    (hU : Measurable (uncurry U)) (hG : Measurable (uncurry G)) (r : ℕ) :
    Measurable (fun q : Θ × (CascadeWeights k × CascadeMarks T k) =>
      cascadePairObservable k r (U q.1) (G q.1) q.2.1 q.2.2) := by
  have hm : Measurable (fun q : Θ × (CascadeWeights k × CascadeMarks T k) =>
      (q.1, cascadeZip k q.2)) :=
    measurable_fst.prodMk ((measurable_cascadeZip k).comp measurable_snd)
  have hn := (measurable_cascadeSqPair_prod k r hU).comp hm
  have hd := (measurable_cascadeSum_prod k hG).comp hm
  exact (hn.mul (hd.inv.pow_const 2)).ennreal_toReal

theorem integrable_truncPairObservable
    (hU : Measurable (uncurry U)) (hG : Measurable (uncurry G))
    (hUG : ∀ θ x, U θ x ≤ G θ (fun p => (x p).1) * G θ (fun p => (x p).2))
    (M r : ℕ) (P : Measure (Θ × (CascadeWeights k × CascadeMarks T k))) [IsFiniteMeasure P] :
    Integrable (fun q => truncPairObservable k M r (U q.1) (G q.1) q.2.1 q.2.2) P := by
  apply Integrable.of_bound
    (measurable_truncPairObservable_prod k hU hG M r).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro q
  rw [Real.norm_eq_abs, abs_of_nonneg (truncPairObservable_nonneg k M r _ _ _ _)]
  exact truncPairObservable_le_one k M r (hUG q.1) q.2.1 q.2.2

theorem integrable_cascadePairObservable
    (hU : Measurable (uncurry U)) (hG : Measurable (uncurry G))
    (hUG : ∀ θ x, U θ x ≤ G θ (fun p => (x p).1) * G θ (fun p => (x p).2))
    (r : ℕ) (P : Measure (Θ × (CascadeWeights k × CascadeMarks T k))) [IsFiniteMeasure P] :
    Integrable (fun q => cascadePairObservable k r (U q.1) (G q.1) q.2.1 q.2.2) P := by
  apply Integrable.of_bound
    (measurable_cascadePairObservable_prod k hU hG r).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro q
  rw [Real.norm_eq_abs, abs_of_nonneg (cascadePairObservable_nonneg k r _ _ _ _)]
  exact cascadePairObservable_le_one k r
    (hG.comp (measurable_const.prodMk measurable_id)) (hUG q.1) q.2.1 q.2.2

/-- Dominated convergence of the joint constrained prefix expectation.
The only limit assumptions concern the actual full partition. -/
theorem tendsto_integral_truncPairObservable
    (hU : Measurable (uncurry U)) (hG : Measurable (uncurry G))
    (hUG : ∀ θ x, U θ x ≤ G θ (fun p => (x p).1) * G θ (fun p => (x p).2))
    (r : ℕ) (P : Measure (Θ × (CascadeWeights k × CascadeMarks T k))) [IsFiniteMeasure P]
    (hS : ∀ᵐ q ∂P, cascadeSum k (G q.1) (cascadeZip k q.2) ≠ 0 ∧
      cascadeSum k (G q.1) (cascadeZip k q.2) ≠ ∞) :
    Tendsto (fun M => ∫ q, truncPairObservable k M r (U q.1) (G q.1) q.2.1 q.2.2 ∂P)
      atTop (𝓝 (∫ q, cascadePairObservable k r (U q.1) (G q.1) q.2.1 q.2.2 ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro M
    exact (measurable_truncPairObservable_prod k hU hG M r).aestronglyMeasurable
  · exact integrable_const _
  · intro M
    apply Filter.Eventually.of_forall
    intro q
    rw [Real.norm_eq_abs, abs_of_nonneg (truncPairObservable_nonneg k M r _ _ _ _)]
    exact truncPairObservable_le_one k M r (hUG q.1) q.2.1 q.2.2
  · filter_upwards [hS] with q hq
    exact tendsto_truncPairObservable k r
      (hU.comp (measurable_const.prodMk measurable_id))
      (hG.comp (measurable_const.prodMk measurable_id)) (hUG q.1) q.2.1 q.2.2 hq.1 hq.2

/-- The expected meeting mass, written as a difference of prefix
expectations, also passes to the limit under the same joint law. -/
theorem tendsto_integral_truncPairObservable_meeting
    (hU : Measurable (uncurry U)) (hG : Measurable (uncurry G))
    (hUG : ∀ θ x, U θ x ≤ G θ (fun p => (x p).1) * G θ (fun p => (x p).2))
    (r : ℕ) (P : Measure (Θ × (CascadeWeights k × CascadeMarks T k))) [IsFiniteMeasure P]
    (hS : ∀ᵐ q ∂P, cascadeSum k (G q.1) (cascadeZip k q.2) ≠ 0 ∧
      cascadeSum k (G q.1) (cascadeZip k q.2) ≠ ∞) :
    Tendsto (fun M => (∫ q, truncPairObservable k M r (U q.1) (G q.1) q.2.1 q.2.2 ∂P) -
      ∫ q, truncPairObservable k M (r + 1) (U q.1) (G q.1) q.2.1 q.2.2 ∂P)
      atTop (𝓝 ((∫ q, cascadePairObservable k r (U q.1) (G q.1) q.2.1 q.2.2 ∂P) -
        ∫ q, cascadePairObservable k (r + 1) (U q.1) (G q.1) q.2.1 q.2.2 ∂P)) :=
  (tendsto_integral_truncPairObservable k hU hG hUG r P hS).sub
    (tendsto_integral_truncPairObservable k hU hG hUG (r + 1) P hS)

/-- The actual integral of the difference of successive prefix fractions
converges, with both finite and infinite integrability discharged. -/
theorem tendsto_integral_truncPairMeetingObservable
    (hU : Measurable (uncurry U)) (hG : Measurable (uncurry G))
    (hUG : ∀ θ x, U θ x ≤ G θ (fun p => (x p).1) * G θ (fun p => (x p).2))
    (r : ℕ) (P : Measure (Θ × (CascadeWeights k × CascadeMarks T k))) [IsFiniteMeasure P]
    (hS : ∀ᵐ q ∂P, cascadeSum k (G q.1) (cascadeZip k q.2) ≠ 0 ∧
      cascadeSum k (G q.1) (cascadeZip k q.2) ≠ ∞) :
    Tendsto (fun M => ∫ q, truncPairObservable k M r (U q.1) (G q.1) q.2.1 q.2.2 -
      truncPairObservable k M (r + 1) (U q.1) (G q.1) q.2.1 q.2.2 ∂P)
      atTop (𝓝 (∫ q, cascadePairObservable k r (U q.1) (G q.1) q.2.1 q.2.2 -
        cascadePairObservable k (r + 1) (U q.1) (G q.1) q.2.1 q.2.2 ∂P)) := by
  simp_rw [integral_sub (integrable_truncPairObservable k hU hG hUG _ r P)
    (integrable_truncPairObservable k hU hG hUG _ (r + 1) P),
    integral_sub (integrable_cascadePairObservable k hU hG hUG r P)
      (integrable_cascadePairObservable k hU hG hUG (r + 1) P)]
  exact tendsto_integral_truncPairObservable_meeting k hU hG hUG r P hS

end

end SpinGlass
