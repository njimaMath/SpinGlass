import SpinGlass.Parisi.Coupled.CoupledPairVarianceContinuity
import SpinGlass.Parisi.Coupled.Derivative.First

/-!
# The coupled terminal and arbitrary paired terminal averages

The symmetry of the actual one-site terminal transfers the coupling
derivative bound to both effective fields. Its separate unit Lipschitz
bounds allow the proved paired recursion and variance modulus to be used
at any fixed coupling, including the witnesses at time zero.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

theorem pairSiteY_swap_coupling_field (lam A B : ℝ) :
    pairSiteY lam A B = pairSiteY A lam B := by
  unfold pairSiteY
  congr 1
  ring

theorem pairSiteY_swap_fields (lam A B : ℝ) :
    pairSiteY lam A B = pairSiteY lam B A := by
  unfold pairSiteY
  congr 1
  ring

theorem abs_pairSiteY_sub_coupling_le (lam lam' A B : ℝ) :
    |pairSiteY lam' A B - pairSiteY lam A B| ≤ |lam' - lam| := by
  have hh := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun l => pairSiteY l A B) (f' := fun l => pairSiteY' l A B) (C := (1 : ℝ))
    (fun l _ => (hasDerivAt_pairSiteY A B l).hasDerivWithinAt)
    (fun l _ => by rw [Real.norm_eq_abs]; exact abs_pairSiteY'_le_one l A B)
    (mem_univ lam) (mem_univ lam')
  simpa only [Real.norm_eq_abs, one_mul] using hh

/-- The actual terminal (14.144) has unit Lipschitz bounds in both
fields at every coupling. No Gaussian or field-law assumption is used. -/
theorem pairUnitLipschitz_pairSiteY (lam : ℝ) : PairUnitLipschitz (pairSiteY lam) := by
  apply pairUnitLipschitz_of_separate
  · intro y x x'
    rw [pairSiteY_swap_coupling_field lam x' y, pairSiteY_swap_coupling_field lam x y]
    exact abs_pairSiteY_sub_coupling_le x x' lam y
  · intro x y y'
    rw [pairSiteY_swap_fields lam x y', pairSiteY_swap_fields lam x y,
      pairSiteY_swap_coupling_field lam y' x, pairSiteY_swap_coupling_field lam y x]
    exact abs_pairSiteY_sub_coupling_le y y' lam x

/-- Every separately unit-Lipschitz paired terminal remains integrable
on the common field diagonal under a finite first field moment. -/
theorem integrable_pairColeHopfIterate_terminal_externalField
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (l : List PairColeHopfLevel) {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) :
    Integrable (fun h => pairColeHopfIterate l F h h) μh := by
  let A := fun h => pairColeHopfIterate l F h h
  have hp := pairColeHopfIterate_lipschitz l hF
  have hA : ∀ x y, |A y - A x| ≤ 2 * |y - x| := fun x y => by
    simpa only [two_mul] using hp x x y y
  apply ((integrable_const |A 0|).add (hμ.abs.const_mul 2)).mono'
    (lipschitzWith_toNNReal_of_abs_sub_le hA).continuous.measurable.aestronglyMeasurable
  refine .of_forall fun h => ?_
  change |A h| ≤ |A 0| + 2 * |h|
  have hh := hA 0 h
  have ha := abs_sub_abs_le_abs_sub (A h) (A 0)
  simp only [sub_zero] at hh
  linarith

noncomputable def randomFieldPairColeHopfTerminalValue (μh : Measure ℝ)
    (l : List PairColeHopfLevel) (F : ℝ → ℝ → ℝ) : ℝ :=
  ∫ h, pairColeHopfIterate l F h h ∂μh

/-- The field-uniform variance modulus survives the field integral
for every separately unit-Lipschitz terminal, at arbitrary fixed coupling. -/
theorem abs_randomFieldPairColeHopfTerminalValue_sub_variance_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) {α : Type*}
    (l : List α) (mass : α → ℝ) (kind : α → PairColeHopfKind) (vs ws : α → ℝ≥0)
    {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) :
    |randomFieldPairColeHopfTerminalValue μh (l.map (fun e => ⟨mass e, vs e, kind e⟩)) F -
        randomFieldPairColeHopfTerminalValue μh (l.map (fun e => ⟨mass e, ws e, kind e⟩)) F| ≤
      (l.map (fun e => pairColeHopfVarianceModulus (mass e) (kind e)
        (Real.toNNReal |(vs e : ℝ) - (ws e : ℝ)|))).sum := by
  unfold randomFieldPairColeHopfTerminalValue
  rw [← integral_sub (integrable_pairColeHopfIterate_terminal_externalField hμ _ hF)
    (integrable_pairColeHopfIterate_terminal_externalField hμ _ hF)]
  have hb := norm_integral_le_of_norm_le_const (μ := μh)
    (f := fun h => pairColeHopfIterate (l.map (fun e => ⟨mass e, vs e, kind e⟩)) F h h -
      pairColeHopfIterate (l.map (fun e => ⟨mass e, ws e, kind e⟩)) F h h)
    (.of_forall fun h => by
      rw [Real.norm_eq_abs]
      exact abs_pairColeHopfIterate_sub_variance_le l mass kind vs ws hF h h)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb

theorem continuous_randomFieldPairColeHopfTerminalValue_of_continuous_variance
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {α X : Type*} [TopologicalSpace X] (l : List α) (mass : α → ℝ)
    (kind : α → PairColeHopfKind) (vs : X → α → ℝ≥0)
    (hvs : ∀ e, Continuous (fun x => vs x e))
    {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) :
    Continuous (fun x => randomFieldPairColeHopfTerminalValue μh
      (l.map (fun e => ⟨mass e, vs x e, kind e⟩)) F) := by
  apply continuous_iff_continuousAt.2
  intro x₀
  apply tendsto_iff_dist_tendsto_zero.2
  have hmod (e : α) : Tendsto (fun x => pairColeHopfVarianceModulus (mass e) (kind e)
      (Real.toNNReal |(vs x e : ℝ) - (vs x₀ e : ℝ)|)) (nhds x₀) (nhds 0) := by
    have hd : Tendsto (fun x => |(vs x e : ℝ) - (vs x₀ e : ℝ)|) (nhds x₀) (nhds 0) := by
      simpa only [Function.comp_apply, Pi.sub_apply, sub_self, abs_zero] using
        ((NNReal.continuous_coe.comp (hvs e)).sub
          (continuous_const (y := (vs x₀ e : ℝ)))).abs.tendsto x₀
    exact (tendsto_pairColeHopfVarianceModulus (mass e) (kind e)).comp hd
  have hsum : Tendsto (fun x => (l.map (fun e => pairColeHopfVarianceModulus (mass e) (kind e)
      (Real.toNNReal |(vs x e : ℝ) - (vs x₀ e : ℝ)|))).sum) (nhds x₀) (nhds 0) := by
    induction l with
    | nil => simpa only [List.map_nil, List.sum_nil] using tendsto_const_nhds
    | cons e l ih =>
      simpa only [List.map_cons, List.sum_cons, zero_add] using (hmod e).add ih
  simp only [Real.dist_eq]
  exact squeeze_zero (fun _ => abs_nonneg _)
    (fun x => abs_randomFieldPairColeHopfTerminalValue_sub_variance_le hμ l mass kind
      (vs x) (vs x₀) hF) hsum

end SpinGlass
