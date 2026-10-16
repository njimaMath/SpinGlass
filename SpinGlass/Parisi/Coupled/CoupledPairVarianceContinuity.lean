import SpinGlass.Parisi.Coupled.CoupledPairRecursion
import SpinGlass.Parisi.Variational.ParisiParameterContinuity

/-!
# Variance continuity of the actual paired Gaussian recursion

The scalar Cole-Hopf variance modulus passes through each of the three
paired Gaussian operators and through the full finite list. The bound is
uniform in the two fields and includes the genuine mass-zero expectations.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

theorem abs_correlatedPairColeHopf_sub_le_of_sup {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) {C η : ℝ}
    (hη : |η| = 1) (hFG : ∀ x y, |F x y - G x y| ≤ C)
    (m : ℝ) (v : ℝ≥0) (x y : ℝ) :
    |correlatedPairColeHopf η m v F x y - correlatedPairColeHopf η m v G x y| ≤ C := by
  have h₁ := hF.signed_diagonal hη x y
  have h₂ := hG.signed_diagonal hη x y
  exact abs_coleHopf_sub_le_of_sup (HasLinearGrowth.of_lipschitz h₁)
    (lipschitzWith_toNNReal_of_abs_sub_le h₁).continuous.measurable
    (HasLinearGrowth.of_lipschitz h₂)
    (lipschitzWith_toNNReal_of_abs_sub_le h₂).continuous.measurable
    (fun z => hFG (x + z) (y + η * z)) m v 0

theorem abs_independentPairColeHopf_sub_le_of_sup {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) {C : ℝ}
    (hFG : ∀ x y, |F x y - G x y| ≤ C)
    (m : ℝ) (v : ℝ≥0) (x y : ℝ) :
    |independentPairColeHopf m v F x y - independentPairColeHopf m v G x y| ≤ C := by
  have h₁ := independentPairColeHopf_inner_lipschitz hF m v y
  have h₂ := independentPairColeHopf_inner_lipschitz hG m v y
  apply abs_coleHopf_sub_le_of_sup (HasLinearGrowth.of_lipschitz h₁)
    (lipschitzWith_toNNReal_of_abs_sub_le h₁).continuous.measurable
    (HasLinearGrowth.of_lipschitz h₂)
    (lipschitzWith_toNNReal_of_abs_sub_le h₂).continuous.measurable
    (fun a => ?_) m v x
  exact abs_coleHopf_sub_le_of_sup (HasLinearGrowth.of_lipschitz (hF.right a))
    (lipschitzWith_toNNReal_of_abs_sub_le (hF.right a)).continuous.measurable
    (HasLinearGrowth.of_lipschitz (hG.right a))
    (lipschitzWith_toNNReal_of_abs_sub_le (hG.right a)).continuous.measurable
    (hFG a) m v y

theorem abs_pairColeHopfOperator_sub_le_of_sup {F G : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (hG : PairUnitLipschitz G) {C : ℝ}
    (hFG : ∀ x y, |F x y - G x y| ≤ C) (p : PairColeHopfLevel) (x y : ℝ) :
    |pairColeHopfOperator p F x y - pairColeHopfOperator p G x y| ≤ C := by
  cases hk : p.kind <;> simp only [pairColeHopfOperator, hk]
  · exact abs_independentPairColeHopf_sub_le_of_sup hF hG hFG p.mass p.variance x y
  · exact abs_correlatedPairColeHopf_sub_le_of_sup hF hG (by norm_num : |(1 : ℝ)| = 1)
      hFG p.mass p.variance x y
  · exact abs_correlatedPairColeHopf_sub_le_of_sup hF hG (by norm_num : |(-1 : ℝ)| = 1)
      hFG p.mass p.variance x y

noncomputable def pairColeHopfVarianceModulus (m : ℝ) (kind : PairColeHopfKind) (v : ℝ≥0) : ℝ :=
  match kind with
  | .independent => 2 * coleHopfModulus m 1 v
  | _ => coleHopfModulus m 2 v

theorem abs_independentPairColeHopf_sub_variance_le {F : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (m : ℝ) (v w : ℝ≥0) (x y : ℝ) :
    |independentPairColeHopf m v F x y - independentPairColeHopf m w F x y| ≤
      2 * coleHopfModulus m 1 (Real.toNNReal |(v : ℝ) - (w : ℝ)|) := by
  let A := fun a => coleHopf m v (F a) y
  let B := fun a => coleHopf m w (F a) y
  have hA := independentPairColeHopf_inner_lipschitz hF m v y
  have hB := independentPairColeHopf_inner_lipschitz hF m w y
  have hi : ∀ a, |A a - B a| ≤ coleHopfModulus m 1 (Real.toNNReal |(v : ℝ) - (w : ℝ)|) :=
    fun a => abs_coleHopf_sub_var_le_modulus
      (lipschitzWith_toNNReal_of_abs_sub_le (hF.right a)).continuous.measurable
      (hF.right a) m v w y
  have hc := abs_coleHopf_sub_le_of_sup (HasLinearGrowth.of_lipschitz hA)
    (lipschitzWith_toNNReal_of_abs_sub_le hA).continuous.measurable
    (HasLinearGrowth.of_lipschitz hB)
    (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable hi m v x
  have hv := abs_coleHopf_sub_var_le_modulus
    (lipschitzWith_toNNReal_of_abs_sub_le hB).continuous.measurable hB m v w x
  calc
    _ = |coleHopf m v A x - coleHopf m w B x| := rfl
    _ ≤ |coleHopf m v A x - coleHopf m v B x| +
        |coleHopf m v B x - coleHopf m w B x| := abs_sub_le _ _ _
    _ ≤ _ := by linarith

/-- The paired layer variance modulus is independent of both fields. -/
theorem abs_pairColeHopfOperator_sub_variance_le {F : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (m : ℝ) (kind : PairColeHopfKind)
    (v w : ℝ≥0) (x y : ℝ) :
    |pairColeHopfOperator ⟨m, v, kind⟩ F x y - pairColeHopfOperator ⟨m, w, kind⟩ F x y| ≤
      pairColeHopfVarianceModulus m kind (Real.toNNReal |(v : ℝ) - (w : ℝ)|) := by
  cases kind with
  | independent => exact abs_independentPairColeHopf_sub_variance_le hF m v w x y
  | common =>
    exact abs_coleHopf_sub_var_le_modulus
      (lipschitzWith_toNNReal_of_abs_sub_le
        (hF.signed_diagonal (by norm_num : |(1 : ℝ)| = 1) x y)).continuous.measurable
      (hF.signed_diagonal (by norm_num : |(1 : ℝ)| = 1) x y) m v w 0
  | antisymmetric =>
    exact abs_coleHopf_sub_var_le_modulus
      (lipschitzWith_toNNReal_of_abs_sub_le
        (hF.signed_diagonal (by norm_num : |(-1 : ℝ)| = 1) x y)).continuous.measurable
      (hF.signed_diagonal (by norm_num : |(-1 : ℝ)| = 1) x y) m v w 0

theorem tendsto_pairColeHopfVarianceModulus (m : ℝ) (kind : PairColeHopfKind) :
    Tendsto (fun v : ℝ => pairColeHopfVarianceModulus m kind (Real.toNNReal v))
      (nhds 0) (nhds 0) := by
  cases kind
  · simpa only [pairColeHopfVarianceModulus, mul_zero] using
      (tendsto_coleHopfModulus m 1).const_mul 2
  · exact tendsto_coleHopfModulus m 2
  · exact tendsto_coleHopfModulus m 2

/-- The field-uniform variance modulus adds over the actual finite
paired recursion, with no mass positivity or ordering assumption. -/
theorem abs_pairColeHopfIterate_sub_variance_le {α : Type*}
    (l : List α) (mass : α → ℝ) (kind : α → PairColeHopfKind) (vs ws : α → ℝ≥0)
    {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) (x y : ℝ) :
    |pairColeHopfIterate (l.map (fun e => ⟨mass e, vs e, kind e⟩)) F x y -
        pairColeHopfIterate (l.map (fun e => ⟨mass e, ws e, kind e⟩)) F x y| ≤
      (l.map (fun e => pairColeHopfVarianceModulus (mass e) (kind e)
        (Real.toNNReal |(vs e : ℝ) - (ws e : ℝ)|))).sum := by
  induction l generalizing x y with
  | nil => simp [pairColeHopfIterate]
  | cons e l ih =>
    let A := pairColeHopfIterate (l.map (fun e => ⟨mass e, vs e, kind e⟩)) F
    let B := pairColeHopfIterate (l.map (fun e => ⟨mass e, ws e, kind e⟩)) F
    have hA : PairUnitLipschitz A := pairColeHopfIterate_lipschitz _ hF
    have hB : PairUnitLipschitz B := pairColeHopfIterate_lipschitz _ hF
    have hc := abs_pairColeHopfOperator_sub_le_of_sup hA hB ih ⟨mass e, ws e, kind e⟩ x y
    have hv := abs_pairColeHopfOperator_sub_variance_le hA (mass e) (kind e) (vs e) (ws e) x y
    simp only [List.map_cons, List.sum_cons, pairColeHopfIterate]
    calc
      _ ≤ |pairColeHopfOperator ⟨mass e, vs e, kind e⟩ A x y -
            pairColeHopfOperator ⟨mass e, ws e, kind e⟩ A x y| +
          |pairColeHopfOperator ⟨mass e, ws e, kind e⟩ A x y -
            pairColeHopfOperator ⟨mass e, ws e, kind e⟩ B x y| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hv hc

/-- The same modulus survives the actual external-field average,
using only a probability law and a finite first moment. -/
theorem abs_randomFieldPairColeHopfListValue_sub_variance_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) {α : Type*}
    (l : List α) (mass : α → ℝ) (kind : α → PairColeHopfKind) (vs ws : α → ℝ≥0) :
    |randomFieldPairColeHopfListValue μh (l.map (fun e => ⟨mass e, vs e, kind e⟩)) -
        randomFieldPairColeHopfListValue μh (l.map (fun e => ⟨mass e, ws e, kind e⟩))| ≤
      (l.map (fun e => pairColeHopfVarianceModulus (mass e) (kind e)
        (Real.toNNReal |(vs e : ℝ) - (ws e : ℝ)|))).sum := by
  let F := fun a b => parisiLogCoshTerminal 0 a + parisiLogCoshTerminal 0 b
  have hF : PairUnitLipschitz F := pairUnitLipschitz_sum (abs_parisiLogCoshTerminal_sub_le 0)
  unfold randomFieldPairColeHopfListValue
  rw [← integral_sub (integrable_pairColeHopfIterate_externalField hμ _)
    (integrable_pairColeHopfIterate_externalField hμ _)]
  have hb := norm_integral_le_of_norm_le_const (μ := μh)
    (f := fun h => pairColeHopfIterate (l.map (fun e => ⟨mass e, vs e, kind e⟩)) F h h -
      pairColeHopfIterate (l.map (fun e => ⟨mass e, ws e, kind e⟩)) F h h)
    (.of_forall fun h => by
      rw [Real.norm_eq_abs]
      exact abs_pairColeHopfIterate_sub_variance_le l mass kind vs ws hF h h)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb

/-- The actual field-averaged paired list is continuous in any
continuous finite variance family, including clamped zero variances. -/
theorem continuous_randomFieldPairColeHopfListValue_of_continuous_variance
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {α X : Type*} [TopologicalSpace X] (l : List α) (mass : α → ℝ)
    (kind : α → PairColeHopfKind) (vs : X → α → ℝ≥0)
    (hvs : ∀ e, Continuous (fun x => vs x e)) :
    Continuous (fun x => randomFieldPairColeHopfListValue μh
      (l.map (fun e => ⟨mass e, vs x e, kind e⟩))) := by
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
    (fun x => abs_randomFieldPairColeHopfListValue_sub_variance_le hμ l mass kind
      (vs x) (vs x₀)) hsum

end SpinGlass
