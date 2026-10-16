import SpinGlass.Parisi.Coupled.CoupledMainOuterFar

/-!
# Continuity of the actual free outer comparison bounds

Uniform Cole-Hopf variance moduli pass through the field and root
Gaussian integrals. The bounds therefore remain continuous for a site
law with finite first moment, including zero split variances.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

/-- The concrete total-variance array is continuous in the split
coordinate on the whole real line, with the prescribed clamping. -/
theorem continuous_parisiOuterFreeTotalVars (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) :
    Continuous (parisiOuterFreeTotalVars ξ qs p) := by
  have hc : Continuous (fun v => parisiResponseSplitVars ξ qs p v) := by
    apply continuous_pi
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [parisiResponseSplitVars, Fin.append_left, Fin.snoc_last]
        exact continuous_real_toNNReal.comp
          ((continuous_const (y := deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))).sub continuous_id)
      · simpa only [parisiResponseSplitVars, Fin.append_left, Fin.snoc_castSucc] using
          (continuous_const : Continuous (fun _ : ℝ => parisiOuterMassPrefixVars ξ qs p j))
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [parisiResponseSplitVars, Fin.append_right, Fin.cons_zero] using continuous_real_toNNReal
      · simpa only [parisiResponseSplitVars, Fin.append_right, Fin.cons_succ] using
          (continuous_const : Continuous (fun _ : ℝ => parisiQSuffixVars ξ qs p j))
  apply continuous_pi
  intro i
  exact ((continuous_apply (parisiSplitIndex p i)).comp hc).comp
    ((continuous_const (y := deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))).sub continuous_id)

/-- A variance modulus for the actual scalar split survives both
the field and root Gaussian averages, uniformly in their arguments. -/
theorem abs_parisiOuterFreeZeroValue_sub_le_sum_modulus
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (v w b : ℝ) :
    |parisiOuterFreeZeroValue μh ξ ms qs p v b - parisiOuterFreeZeroValue μh ξ ms qs p w b| ≤
      ∑ i, coleHopfModulus (parisiLevelMasses (splitParisiMassLeft ms p b) i) 1
        (Real.toNNReal |(parisiOuterFreeTotalVars ξ qs p v i : ℝ) -
          (parisiOuterFreeTotalVars ξ qs p w i : ℝ)|) := by
  unfold parisiOuterFreeZeroValue
  rw [← integral_sub (integrable_parisiOuterFreeSplit_externalField hμ ξ ms qs p v b)
    (integrable_parisiOuterFreeSplit_externalField hμ ξ ms qs p w b)]
  rw [← coleHopfIterate_parisiOuterFree_eq_split ξ ms qs p v b,
    ← coleHopfIterate_parisiOuterFree_eq_split ξ ms qs p w b]
  have hb := norm_integral_le_of_norm_le_const
    (μ := μh.prod (gaussianReal 0 (parisiVar ξ qs 0)))
    (f := fun hz : ℝ × ℝ =>
      coleHopfIterate (k + 2) (parisiLevelMasses (splitParisiMassLeft ms p b))
        (parisiOuterFreeTotalVars ξ qs p v) (parisiLogCoshTerminal 0) (hz.1 + hz.2) -
      coleHopfIterate (k + 2) (parisiLevelMasses (splitParisiMassLeft ms p b))
        (parisiOuterFreeTotalVars ξ qs p w) (parisiLogCoshTerminal 0) (hz.1 + hz.2)) (.of_forall fun hz => by
      rw [Real.norm_eq_abs]
      exact abs_coleHopfIterate_sub_var_le_sum_modulus
        (measurable_of_hasDerivAt (hasDerivAt_parisiLogCoshTerminal 0))
        (L := 1) (fun x y => by simpa only [one_mul] using abs_parisiLogCoshTerminal_sub_le 0 x y)
        (k + 2) (parisiLevelMasses (splitParisiMassLeft ms p b))
        (parisiOuterFreeTotalVars ξ qs p v) (parisiOuterFreeTotalVars ξ qs p w) (hz.1 + hz.2))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb

/-- The actual field-averaged zero-coupling value is continuous in
the variance coordinate at every fixed mass, with no mass ordering. -/
theorem continuous_parisiOuterFreeZeroValue_variance
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (b : ℝ) :
    Continuous (fun v => parisiOuterFreeZeroValue μh ξ ms qs p v b) := by
  apply continuous_iff_continuousAt.2
  intro w
  apply tendsto_iff_dist_tendsto_zero.2
  have hmod (i : Fin (k + 2)) : Tendsto
      (fun v => coleHopfModulus (parisiLevelMasses (splitParisiMassLeft ms p b) i) 1
        (Real.toNNReal |(parisiOuterFreeTotalVars ξ qs p v i : ℝ) -
          (parisiOuterFreeTotalVars ξ qs p w i : ℝ)|)) (nhds w) (nhds 0) := by
    have hc := NNReal.continuous_coe.comp
      ((continuous_apply i).comp (continuous_parisiOuterFreeTotalVars ξ qs p))
    have he : Tendsto (fun v => |(parisiOuterFreeTotalVars ξ qs p v i : ℝ) -
        (parisiOuterFreeTotalVars ξ qs p w i : ℝ)|) (nhds w) (nhds 0) := by
      simpa only [Function.comp_apply, Pi.sub_apply, sub_self, abs_zero] using
        (hc.sub (continuous_const (y := (parisiOuterFreeTotalVars ξ qs p w i : ℝ)))).abs.tendsto w
    exact (tendsto_coleHopfModulus _ 1).comp he
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hmod i)
  simp only [Finset.sum_const_zero] at hsum
  simp only [Real.dist_eq]
  exact squeeze_zero (fun _ => abs_nonneg _)
    (fun v => abs_parisiOuterFreeZeroValue_sub_le_sum_modulus hμ ξ ms qs p v w b) hsum

/-- At a fixed admissible mass, the actual scalar pressure bound is
jointly continuous in time and overlap on the closed outer rectangle. -/
theorem continuousOn_parisiOuterFreeScalarBound_time_overlap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hq : ParisiQAdmissible qs) (t₀ b : ℝ) :
    ContinuousOn (fun x : ℝ × ℝ => parisiOuterFreeScalarBound μh ξ ms qs p x.1 x.2 b)
      (Icc (0 : ℝ) t₀ ×ˢ Icc (qs p) (qExt qs (p.val + 2))) := by
  have hmaps : MapsTo (Prod.snd : ℝ × ℝ → ℝ)
      (Icc (0 : ℝ) t₀ ×ˢ Icc (qs p) (qExt qs (p.val + 2))) (Icc (0 : ℝ) 1) := by
    intro x hx
    exact ⟨(hq.mem_Icc p).1.trans hx.2.1, hx.2.2.trans (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _).2⟩
  have hd := hξ.deriv_continuous.comp continuous_snd.continuousOn hmaps
  have hθ : ContinuousOn (fun x : ℝ × ℝ => parisiTheta ξ x.2)
      (Icc (0 : ℝ) t₀ ×ˢ Icc (qs p) (qExt qs (p.val + 2))) :=
    (show ContinuousOn (parisiTheta ξ) (Icc (0 : ℝ) 1) from
      fun u hu => (hasDerivAt_parisiTheta (hξ.hasDeriv u hu)
        (hξ.hasDeriv_deriv u hu)).continuousAt.continuousWithinAt).comp
      continuous_snd.continuousOn hmaps
  have hv : ContinuousOn (fun x : ℝ × ℝ => x.1 * (deriv ξ x.2 - deriv ξ (qs p)))
      (Icc (0 : ℝ) t₀ ×ˢ Icc (qs p) (qExt qs (p.val + 2))) :=
    continuous_fst.continuousOn.mul (hd.sub continuousOn_const)
  have hz := (continuous_parisiOuterFreeZeroValue_variance hμ ξ ms qs p b).comp_continuousOn hv
  have hcor : ContinuousOn (fun x : ℝ × ℝ => x.1 * (parisiCorrection ξ ms qs +
      (b - mExt ms (p.val + 1)) * (parisiTheta ξ x.2 - parisiTheta ξ (qs p))))
      (Icc (0 : ℝ) t₀ ×ˢ Icc (qs p) (qExt qs (p.val + 2))) :=
    continuous_fst.continuousOn.mul
      (continuousOn_const.add (continuousOn_const.mul (hθ.sub continuousOn_const)))
  have ht : Continuous (fun x : ℝ × ℝ => (parisiAuxTerminalVar ξ qs x.1 : ℝ)) :=
    (continuous_parisiAuxTerminalVar_time ξ qs).comp continuous_fst
  unfold parisiOuterFreeScalarBound
  exact ((continuousOn_const.add (hz.const_mul 2)).sub hcor).sub ht.continuousOn

/-- The concrete coupling response is jointly continuous on the
closed outer rectangle, using its actual variance derivative. -/
theorem continuousOn_parisiLeftResponseGap_time_overlap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ}
    (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun x : ℝ × ℝ => parisiLeftResponseGap μh ξ ms qs p x.1 x.2)
      (Icc (0 : ℝ) t₀ ×ˢ Icc (qs p) (qExt qs (p.val + 2))) := by
  by_cases hg : qs p < qExt qs (p.val + 2)
  · have hmaps : MapsTo (Prod.snd : ℝ × ℝ → ℝ)
        (Icc (0 : ℝ) t₀ ×ˢ Icc (qs p) (qExt qs (p.val + 2))) (Icc (0 : ℝ) 1) := by
      intro x hx
      exact ⟨(hq.mem_Icc p).1.trans hx.2.1, hx.2.2.trans (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _).2⟩
    have hd := hξ.deriv_continuous.comp continuous_snd.continuousOn hmaps
    have hv : ContinuousOn (fun x : ℝ × ℝ => x.1 * (deriv ξ x.2 - deriv ξ (qs p)))
        (Icc (0 : ℝ) t₀ ×ˢ Icc (qs p) (qExt qs (p.val + 2))) :=
      continuous_fst.continuousOn.mul (hd.sub continuousOn_const)
    have hvm : MapsTo (fun x : ℝ × ℝ => x.1 * (deriv ξ x.2 - deriv ξ (qs p)))
        (Icc (0 : ℝ) t₀ ×ˢ Icc (qs p) (qExt qs (p.val + 2)))
        (Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) := by
      intro x hx
      exact parisi_outer_time_variance_mem_Icc hξ qs p hq ⟨hx.1.1, hx.1.2.trans ht₀.2⟩ hx.2
    have hM : ContinuousOn (parisiLeftUSpatialMoment 1 μh ξ ms qs p)
        (Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) :=
      fun v hv => (hasDerivWithinAt_parisiLeftUSpatialMoment_one hξ ms qs p hm hq hg hv).continuousWithinAt
    unfold parisiLeftResponseGap
    exact (hM.comp hv hvm).sub continuous_snd.continuousOn
  · have he (x : ℝ × ℝ) (hx : x ∈ Icc (0 : ℝ) t₀ ×ˢ Icc (qs p) (qExt qs (p.val + 2))) :
        x.2 = qs p := le_antisymm (hx.2.2.trans (le_of_not_gt hg)) hx.2.1
    have hc : ContinuousOn (fun _ : ℝ × ℝ => parisiLeftUSpatialMoment 1 μh ξ ms qs p 0 - qs p)
        (Icc (0 : ℝ) t₀ ×ˢ Icc (qs p) (qExt qs (p.val + 2))) := continuousOn_const
    apply hc.congr
    intro x hx
    simp only [parisiLeftResponseGap, he x hx, sub_self, mul_zero]

end SpinGlass
