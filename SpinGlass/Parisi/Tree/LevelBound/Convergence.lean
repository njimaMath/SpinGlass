import SpinGlass.Parisi.Tree.LevelBound.Basic

/-!
# Convergence of truncated cascade bounds

Convergence of the level bound and log partition function under truncation.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

universe u

variable {T : Type u} [MeasurableSpace T] [Nonempty T] (k : ℕ)
variable {Θ : Type u} [MeasurableSpace Θ] (Pθ : Measure Θ) [IsProbabilityMeasure Pθ]
variable (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
variable (G : ℝ → Θ → (Fin k → T) → ℝ≥0∞)

/-! ### Convergence of the truncated bounds -/

omit [Nonempty T] in
/-- For weights of positive total mass, the cascade sum of positive branch functions is
positive. -/
lemma cascadeSum_of_ne_zero (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2)
    (hGpos : ∀ t θ x, 0 < G t θ x) (t : ℝ) (θ : Θ) (w : CascadeWeights k)
    (hW0 : weightSum k w ≠ 0) (z : CascadeMarks T k) :
    cascadeSum k (G t θ) (cascadeZip k (w, z)) ≠ 0 := by
  rw [cascadeSum_cascadeZip k (measurable_of_uncurry₃ k G hG t θ)]
  intro hzero
  rw [ENNReal.tsum_eq_zero] at hzero
  refine hW0 (ENNReal.tsum_eq_zero.2 fun α => ?_)
  rcases mul_eq_zero.1 (hzero α) with h0 | h0
  · exact h0
  · exact absurd h0 (hGpos t θ _).ne'

omit [Nonempty T] [IsProbabilityMeasure Pθ] in
/-- For weights of finite total mass and branch functions with finite Gaussian moments, the
cascade sum is almost surely finite. -/
lemma ae_cascadeSum_of_lt_top
    (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2)
    (hfin : ∀ t θ, ∫⁻ x, G t θ x ∂Measure.pi μs ≠ ∞) (t : ℝ) (w : CascadeWeights k)
    (hW : weightSum k w ≠ ∞) :
    ∀ᵐ q ∂Pθ.prod (cascadeMarksLaw k μs),
      cascadeSum k (G t q.1) (cascadeZip k (w, q.2)) < ∞ := by
  have hmeas := measurable_cascadeSum_of k G hG w t
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt hmeas measurable_const)]
  refine Filter.Eventually.of_forall fun θ => ?_
  have hmeas' : Measurable fun z : CascadeMarks T k =>
      cascadeSum k (G t θ) (cascadeZip k (w, z)) := by
    have := hmeas.comp (measurable_const.prodMk measurable_id :
      Measurable fun z : CascadeMarks T k => (θ, z))
    simp only [Function.comp_def] at this
    exact this
  refine ae_lt_top hmeas' ?_
  rw [lintegral_cascadeSum_cascadeZip k μs w (measurable_of_uncurry₃ k G hG t θ)]
  exact ENNReal.mul_ne_top hW (hfin t θ)

omit [MeasurableSpace T] [Nonempty T] in
lemma abs_levelBound_truncPair_le (M : ℕ) (c₀ : ℝ) (θf : ℕ → ℝ) (Gt : (Fin k → T) → ℝ≥0∞)
    (w : CascadeWeights k) (z : CascadeMarks T k) :
    |levelBound k c₀ θf fun r => truncPair k M r Gt w z|
      ≤ (1 / 2) * |c₀| + (1 / 2) * ∑ r ∈ Finset.range (k + 1), |θf r| :=
  abs_levelBound_le k c₀ θf _ (fun r => truncPair_nonneg k M r _ w _)
    (fun r => truncPair_le_one k M r _ w _)

omit [Nonempty T] in
/-- **The truncated bounds converge to the bound for the whole cascade**, at every time `t`. -/
theorem tendsto_truncLevelBoundLaw
    (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2)
    (hGpos : ∀ t θ x, 0 < G t θ x) (hfin : ∀ t θ, ∫⁻ x, G t θ x ∂Measure.pi μs ≠ ∞) (c₀ : ℝ)
    (θf : ℕ → ℝ) (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞)
    (t : ℝ) :
    Tendsto (fun M => truncLevelBoundLaw k Pθ μs G M c₀ θf w t) atTop
      (𝓝 (levelBoundLaw k Pθ μs G c₀ θf w t)) := by
  unfold truncLevelBoundLaw levelBoundLaw
  refine tendsto_integral_filter_of_dominated_convergence
    (fun _ => (1 / 2) * |c₀| + (1 / 2) * ∑ r ∈ Finset.range (k + 1), |θf r|) ?_ ?_
    (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun M => (measurable_const.add (measurable_const.mul
      (Finset.measurable_sum _ fun r _ => measurable_const.mul
        ((measurable_truncPair_of k G hG M r w t).sub
          (measurable_truncPair_of k G hG M (r + 1) w t))))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun M => Filter.Eventually.of_forall fun q => ?_
    rw [Real.norm_eq_abs]
    exact abs_levelBound_truncPair_le k M c₀ θf _ w q.2
  · filter_upwards [ae_cascadeSum_of_lt_top k Pθ μs G hG hfin t w hW] with q hq
    exact tendsto_levelBound k c₀ θf fun r => tendsto_truncPair k r
      (measurable_of_uncurry₃ k G hG t q.1) w q.2
      (cascadeSum_of_ne_zero k G hG hGpos t q.1 w hW0 q.2) hq.ne

omit [Nonempty T] in
/-- The integrated truncated bounds converge to the integrated bound for the whole cascade,
given the continuity in `t` of the truncated bounds. -/
theorem tendsto_integral_truncLevelBoundLaw
    (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2)
    (hGpos : ∀ t θ x, 0 < G t θ x) (hfin : ∀ t θ, ∫⁻ x, G t θ x ∂Measure.pi μs ≠ ∞) (c₀ : ℝ)
    (θf : ℕ → ℝ) (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) (hW : weightSum k w ≠ ∞)
    {M₀ : ℕ} (hcont : ∀ M, M₀ ≤ M → Continuous (truncLevelBoundLaw k Pθ μs G M c₀ θf w)) :
    Tendsto (fun M => ∫ t in (0 : ℝ)..1, truncLevelBoundLaw k Pθ μs G M c₀ θf w t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, levelBoundLaw k Pθ μs G c₀ θf w t)) := by
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (1 / 2) * |c₀| + (1 / 2) * ∑ r ∈ Finset.range (k + 1), |θf r|) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [Filter.eventually_ge_atTop M₀] with M hM
    exact (hcont M hM).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun M => Filter.Eventually.of_forall fun t _ => ?_
    unfold truncLevelBoundLaw
    refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun q => ?_)).trans
      (by rw [probReal_univ, mul_one])
    rw [Real.norm_eq_abs]
    exact abs_levelBound_truncPair_le k M c₀ θf _ w q.2
  · exact Filter.Eventually.of_forall fun t _ =>
      tendsto_truncLevelBoundLaw k Pθ μs G hG hGpos hfin c₀ θf w hW0 hW t

/-! ### Convergence of the truncated partition functions -/

omit [Nonempty T] in
lemma measurable_log_truncSum_of (Gt : Θ → (Fin k → T) → ℝ≥0∞)
    (hGm : Measurable (Function.uncurry Gt)) (M : ℕ) (w : CascadeWeights k) :
    Measurable fun q : Θ × CascadeMarks T k => Real.log (truncSum k M w (Gt q.1) q.2).toReal := by
  refine Real.measurable_log.comp (ENNReal.measurable_toReal.comp
    (Finset.measurable_sum _ fun α _ => measurable_const.mul ?_))
  have := hGm.comp (measurable_fst.prodMk
    ((measurable_branchMarks k (truncBranchCoe k M α)).comp measurable_snd) :
      Measurable fun q : Θ × CascadeMarks T k => (q.1, branchMarks k q.2 (truncBranchCoe k M α)))
  exact this

omit [Nonempty T] in
lemma measurable_log_cascadeSum_of (Gt : Θ → (Fin k → T) → ℝ≥0∞)
    (hGm : Measurable (Function.uncurry Gt)) (w : CascadeWeights k) :
    Measurable fun q : Θ × CascadeMarks T k =>
      Real.log (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal :=
  Real.measurable_log.comp (ENNReal.measurable_toReal.comp
    (measurable_cascadeSum_of k (fun _ θ => Gt θ)
      (hGm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)) w 0))

omit [Nonempty T] in
/-- The logarithm of the cascade sum is integrable, under the hypotheses of
`tendsto_integral_log_truncSum`. -/
theorem integrable_log_cascadeSum_of (Gt : Θ → (Fin k → T) → ℝ≥0∞)
    (hGm : Measurable (Function.uncurry Gt)) (hGpos : ∀ θ x, 0 < Gt θ x)
    (hGfin : ∀ θ x, Gt θ x ≠ ∞) (w : CascadeWeights k) (hW : weightSum k w ≠ ∞)
    (hSfin : ∫⁻ q, cascadeSum k (Gt q.1) (cascadeZip k (w, q.2)) ∂Pθ.prod (cascadeMarksLaw k μs)
      ≠ ∞)
    {α₀ : Fin k → ℕ × ℕ} (hα₀ : branchWeight k w α₀ ≠ 0) {ℓ : Θ × CascadeMarks T k → ℝ}
    (hℓ : Integrable ℓ (Pθ.prod (cascadeMarksLaw k μs)))
    (hℓle : ∀ q, ℓ q ≤ Real.log (Gt q.1 (branchMarks k q.2 α₀)).toReal) :
    Integrable (fun q => Real.log (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal)
      (Pθ.prod (cascadeMarksLaw k μs)) := by
  set P := Pθ.prod (cascadeMarksLaw k μs) with hP
  have hGm' : ∀ θ, Measurable (Gt θ) := fun θ => by
    have := hGm.comp (measurable_const.prodMk measurable_id :
      Measurable fun x : Fin k → T => (θ, x))
    exact this
  have hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => Gt q.1.2 q.2 :=
    hGm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hSm : Measurable fun q : Θ × CascadeMarks T k =>
      cascadeSum k (Gt q.1) (cascadeZip k (w, q.2)) :=
    measurable_cascadeSum_of k (fun _ θ => Gt θ) hG w 0
  have hSlt : ∀ᵐ q ∂P, cascadeSum k (Gt q.1) (cascadeZip k (w, q.2)) < ∞ := ae_lt_top hSm hSfin
  have hSint : Integrable (fun q => (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hSm.aemeasurable hSfin
  have hw : ∀ α, branchWeight k w α ≠ ∞ :=
    fun α => ne_top_of_le_ne_top hW (branchWeight_le_weightSum k w α)
  set c : ℝ := (branchWeight k w α₀).toReal with hc
  have hcpos : 0 < c := ENNReal.toReal_pos hα₀ (hw α₀)
  have hbound : Integrable (fun q : Θ × CascadeMarks T k =>
      (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal + (|Real.log c| + |ℓ q|)) P :=
    hSint.add ((integrable_const |Real.log c|).add hℓ.abs)
  refine Integrable.mono' hbound
    (Real.measurable_log.comp (ENNReal.measurable_toReal.comp hSm)).aestronglyMeasurable ?_
  filter_upwards [hSlt] with q hq
  rw [Real.norm_eq_abs]
  have hlow : branchWeight k w α₀ * Gt q.1 (branchMarks k q.2 α₀)
      ≤ cascadeSum k (Gt q.1) (cascadeZip k (w, q.2)) :=
    le_cascadeSum_cascadeZip k w (hGm' q.1) q.2 α₀
  have hbpos : 0 < (branchWeight k w α₀ * Gt q.1 (branchMarks k q.2 α₀)).toReal :=
    ENNReal.toReal_pos (mul_ne_zero hα₀ (hGpos _ _).ne')
      (ENNReal.mul_ne_top (hw _) (hGfin _ _))
  have hSpos : 0 < (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal :=
    hbpos.trans_le (ENNReal.toReal_mono hq.ne hlow)
  have h1 : Real.log (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal
      ≤ (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal :=
    (Real.log_le_sub_one_of_pos hSpos).trans (by linarith)
  have h2 : Real.log c + ℓ q ≤ Real.log (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal := by
    calc Real.log c + ℓ q ≤ Real.log c + Real.log (Gt q.1 (branchMarks k q.2 α₀)).toReal :=
          add_le_add le_rfl (hℓle q)
      _ = Real.log (branchWeight k w α₀ * Gt q.1 (branchMarks k q.2 α₀)).toReal := by
          rw [ENNReal.toReal_mul, Real.log_mul hcpos.ne'
            (ENNReal.toReal_pos (hGpos _ _).ne' (hGfin _ _)).ne']
      _ ≤ _ := Real.log_le_log hbpos (ENNReal.toReal_mono hq.ne hlow)
  have hS0 : 0 ≤ (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal := ENNReal.toReal_nonneg
  have hc1 := neg_abs_le (Real.log c)
  have hc2 := neg_abs_le (ℓ q)
  have hc3 := abs_nonneg (Real.log c)
  have hc4 := abs_nonneg (ℓ q)
  rw [abs_le]
  constructor
  · linarith
  · linarith

omit [Nonempty T] in
/-- The logarithm of a truncated cascade sum containing a branch of positive weight is
integrable, under the hypotheses of `tendsto_integral_log_truncSum`. -/
theorem integrable_log_truncSum_of (Gt : Θ → (Fin k → T) → ℝ≥0∞)
    (hGm : Measurable (Function.uncurry Gt)) (hGpos : ∀ θ x, 0 < Gt θ x)
    (hGfin : ∀ θ x, Gt θ x ≠ ∞) (w : CascadeWeights k) (hW : weightSum k w ≠ ∞)
    (hSfin : ∫⁻ q, cascadeSum k (Gt q.1) (cascadeZip k (w, q.2)) ∂Pθ.prod (cascadeMarksLaw k μs)
      ≠ ∞)
    {α₀ : Fin k → ℕ × ℕ} (hα₀ : branchWeight k w α₀ ≠ 0) {ℓ : Θ × CascadeMarks T k → ℝ}
    (hℓ : Integrable ℓ (Pθ.prod (cascadeMarksLaw k μs)))
    (hℓle : ∀ q, ℓ q ≤ Real.log (Gt q.1 (branchMarks k q.2 α₀)).toReal) {M : ℕ}
    (hmem : α₀ ∈ truncFinset k M) :
    Integrable (fun q => Real.log (truncSum k M w (Gt q.1) q.2).toReal)
      (Pθ.prod (cascadeMarksLaw k μs)) := by
  set P := Pθ.prod (cascadeMarksLaw k μs) with hP
  have hGm' : ∀ θ, Measurable (Gt θ) := fun θ => by
    have := hGm.comp (measurable_const.prodMk measurable_id :
      Measurable fun x : Fin k → T => (θ, x))
    exact this
  have hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => Gt q.1.2 q.2 :=
    hGm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hSm : Measurable fun q : Θ × CascadeMarks T k =>
      cascadeSum k (Gt q.1) (cascadeZip k (w, q.2)) :=
    measurable_cascadeSum_of k (fun _ θ => Gt θ) hG w 0
  have hSlt : ∀ᵐ q ∂P, cascadeSum k (Gt q.1) (cascadeZip k (w, q.2)) < ∞ := ae_lt_top hSm hSfin
  have hSint : Integrable (fun q => (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hSm.aemeasurable hSfin
  have hw : ∀ α, branchWeight k w α ≠ ∞ :=
    fun α => ne_top_of_le_ne_top hW (branchWeight_le_weightSum k w α)
  set c : ℝ := (branchWeight k w α₀).toReal with hc
  have hcpos : 0 < c := ENNReal.toReal_pos hα₀ (hw α₀)
  have hmeasTM : Measurable fun q : Θ × CascadeMarks T k =>
      Real.log (truncSum k M w (Gt q.1) q.2).toReal := by
    refine Real.measurable_log.comp (ENNReal.measurable_toReal.comp
      (Finset.measurable_sum _ fun α _ => measurable_const.mul ?_))
    have := hGm.comp (measurable_fst.prodMk
      ((measurable_branchMarks k (truncBranchCoe k M α)).comp measurable_snd) :
        Measurable fun q : Θ × CascadeMarks T k => (q.1, branchMarks k q.2 (truncBranchCoe k M α)))
    exact this
  have hbound : Integrable (fun q : Θ × CascadeMarks T k =>
      (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal + (|Real.log c| + |ℓ q|)) P :=
    hSint.add ((integrable_const |Real.log c|).add hℓ.abs)
  refine Integrable.mono' hbound hmeasTM.aestronglyMeasurable ?_
  filter_upwards [hSlt] with q hq
  rw [Real.norm_eq_abs]
  have hTle : truncSum k M w (Gt q.1) q.2 ≤ cascadeSum k (Gt q.1) (cascadeZip k (w, q.2)) :=
    truncSum_le_cascadeSum k M w (hGm' q.1) q.2
  have hTfin : truncSum k M w (Gt q.1) q.2 ≠ ∞ := ne_top_of_le_ne_top hq.ne hTle
  have hlow : branchWeight k w α₀ * Gt q.1 (branchMarks k q.2 α₀) ≤ truncSum k M w (Gt q.1) q.2 :=
    le_truncSum_of_mem k M w _ q.2 hmem
  have hbpos : 0 < (branchWeight k w α₀ * Gt q.1 (branchMarks k q.2 α₀)).toReal :=
    ENNReal.toReal_pos (mul_ne_zero hα₀ (hGpos _ _).ne')
      (ENNReal.mul_ne_top (hw _) (hGfin _ _))
  have hTpos : 0 < (truncSum k M w (Gt q.1) q.2).toReal :=
    hbpos.trans_le (ENNReal.toReal_mono hTfin hlow)
  have h1 : Real.log (truncSum k M w (Gt q.1) q.2).toReal
      ≤ (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal :=
    (Real.log_le_sub_one_of_pos hTpos).trans (by linarith [ENNReal.toReal_mono hq.ne hTle])
  have h2 : Real.log c + ℓ q ≤ Real.log (truncSum k M w (Gt q.1) q.2).toReal := by
    calc Real.log c + ℓ q ≤ Real.log c + Real.log (Gt q.1 (branchMarks k q.2 α₀)).toReal :=
          add_le_add le_rfl (hℓle q)
      _ = Real.log (branchWeight k w α₀ * Gt q.1 (branchMarks k q.2 α₀)).toReal := by
          rw [ENNReal.toReal_mul, Real.log_mul hcpos.ne'
            (ENNReal.toReal_pos (hGpos _ _).ne' (hGfin _ _)).ne']
      _ ≤ _ := Real.log_le_log hbpos (ENNReal.toReal_mono hTfin hlow)
  have hS0 : 0 ≤ (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal := ENNReal.toReal_nonneg
  have hc1 := neg_abs_le (Real.log c)
  have hc2 := neg_abs_le (ℓ q)
  have hc3 := abs_nonneg (Real.log c)
  have hc4 := abs_nonneg (ℓ q)
  rw [abs_le]
  constructor
  · linarith
  · linarith

omit [Nonempty T] in
/-- **The logarithms of the truncated cascade sums converge in mean to that of the cascade sum**,
at fixed weights of positive finite mass, for positive finite branch functions with integrable
cascade sum, provided the logarithm of one branch of positive weight has an integrable lower
bound. -/
theorem tendsto_integral_log_truncSum (Gt : Θ → (Fin k → T) → ℝ≥0∞)
    (hGm : Measurable (Function.uncurry Gt)) (hGpos : ∀ θ x, 0 < Gt θ x)
    (hGfin : ∀ θ x, Gt θ x ≠ ∞) (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0)
    (hW : weightSum k w ≠ ∞)
    (hSfin : ∫⁻ q, cascadeSum k (Gt q.1) (cascadeZip k (w, q.2)) ∂Pθ.prod (cascadeMarksLaw k μs)
      ≠ ∞)
    {α₀ : Fin k → ℕ × ℕ} (hα₀ : branchWeight k w α₀ ≠ 0) {ℓ : Θ × CascadeMarks T k → ℝ}
    (hℓ : Integrable ℓ (Pθ.prod (cascadeMarksLaw k μs)))
    (hℓle : ∀ q, ℓ q ≤ Real.log (Gt q.1 (branchMarks k q.2 α₀)).toReal) :
    Tendsto (fun M => ∫ q, Real.log (truncSum k M w (Gt q.1) q.2).toReal
        ∂Pθ.prod (cascadeMarksLaw k μs)) atTop
      (𝓝 (∫ q, Real.log (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal
        ∂Pθ.prod (cascadeMarksLaw k μs))) := by
  set P := Pθ.prod (cascadeMarksLaw k μs) with hP
  have hGm' : ∀ θ, Measurable (Gt θ) := fun θ => by
    have := hGm.comp (measurable_const.prodMk measurable_id :
      Measurable fun x : Fin k → T => (θ, x))
    exact this
  have hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => Gt q.1.2 q.2 :=
    hGm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hSm : Measurable fun q : Θ × CascadeMarks T k =>
      cascadeSum k (Gt q.1) (cascadeZip k (w, q.2)) :=
    measurable_cascadeSum_of k (fun _ θ => Gt θ) hG w 0
  have hSlt : ∀ᵐ q ∂P, cascadeSum k (Gt q.1) (cascadeZip k (w, q.2)) < ∞ := ae_lt_top hSm hSfin
  have hSint : Integrable (fun q => (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hSm.aemeasurable hSfin
  have hw : ∀ α, branchWeight k w α ≠ ∞ :=
    fun α => ne_top_of_le_ne_top hW (branchWeight_le_weightSum k w α)
  obtain ⟨M₀, hM₀⟩ := exists_subset_truncFinset k {α₀}
  have hmem : ∀ M, M₀ ≤ M → α₀ ∈ truncFinset k M :=
    fun M hM => truncFinset_mono k hM (hM₀ (Finset.mem_singleton_self _))
  -- the lower bound through the branch `α₀`
  set c : ℝ := (branchWeight k w α₀).toReal with hc
  have hcpos : 0 < c := ENNReal.toReal_pos hα₀ (hw α₀)
  have hbranch : ∀ q : Θ × CascadeMarks T k,
      Real.log c + Real.log (Gt q.1 (branchMarks k q.2 α₀)).toReal
        = Real.log (branchWeight k w α₀ * Gt q.1 (branchMarks k q.2 α₀)).toReal := by
    intro q
    rw [ENNReal.toReal_mul, Real.log_mul hcpos.ne'
      (ENNReal.toReal_pos (hGpos _ _).ne' (hGfin _ _)).ne']
  have hmeasTM : ∀ M, Measurable fun q : Θ × CascadeMarks T k =>
      Real.log (truncSum k M w (Gt q.1) q.2).toReal := by
    intro M
    refine Real.measurable_log.comp (ENNReal.measurable_toReal.comp
      (Finset.measurable_sum _ fun α _ => measurable_const.mul ?_))
    have := hGm.comp (measurable_fst.prodMk
      ((measurable_branchMarks k (truncBranchCoe k M α)).comp measurable_snd) :
        Measurable fun q : Θ × CascadeMarks T k => (q.1, branchMarks k q.2 (truncBranchCoe k M α)))
    exact this
  refine tendsto_integral_filter_of_dominated_convergence
    (fun q => (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal + (|Real.log c| + |ℓ q|))
    ?_ ?_ (hSint.add ((integrable_const _).add hℓ.abs)) ?_
  · exact Filter.Eventually.of_forall fun M => (hmeasTM M).aestronglyMeasurable
  · filter_upwards [Filter.eventually_ge_atTop M₀] with M hM
    filter_upwards [hSlt] with q hq
    rw [Real.norm_eq_abs]
    have hTle : truncSum k M w (Gt q.1) q.2 ≤ cascadeSum k (Gt q.1) (cascadeZip k (w, q.2)) :=
      truncSum_le_cascadeSum k M w (hGm' q.1) q.2
    have hTfin : truncSum k M w (Gt q.1) q.2 ≠ ∞ := ne_top_of_le_ne_top hq.ne hTle
    have hlow : branchWeight k w α₀ * Gt q.1 (branchMarks k q.2 α₀) ≤ truncSum k M w (Gt q.1) q.2 :=
      le_truncSum_of_mem k M w _ q.2 (hmem M hM)
    have hbpos : 0 < (branchWeight k w α₀ * Gt q.1 (branchMarks k q.2 α₀)).toReal :=
      ENNReal.toReal_pos (mul_ne_zero hα₀ (hGpos _ _).ne')
        (ENNReal.mul_ne_top (hw _) (hGfin _ _))
    have hTpos : 0 < (truncSum k M w (Gt q.1) q.2).toReal :=
      hbpos.trans_le (ENNReal.toReal_mono hTfin hlow)
    have h1 : Real.log (truncSum k M w (Gt q.1) q.2).toReal
        ≤ (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal :=
      (Real.log_le_sub_one_of_pos hTpos).trans
        (by linarith [ENNReal.toReal_mono hq.ne hTle])
    have h2 : Real.log c + ℓ q ≤ Real.log (truncSum k M w (Gt q.1) q.2).toReal := by
      calc Real.log c + ℓ q ≤ Real.log c + Real.log (Gt q.1 (branchMarks k q.2 α₀)).toReal :=
            add_le_add le_rfl (hℓle q)
        _ = Real.log (branchWeight k w α₀ * Gt q.1 (branchMarks k q.2 α₀)).toReal := hbranch q
        _ ≤ _ := Real.log_le_log hbpos (ENNReal.toReal_mono hTfin hlow)
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log c), neg_abs_le (ℓ q), ENNReal.toReal_nonneg
        (a := cascadeSum k (Gt q.1) (cascadeZip k (w, q.2)))]
    · linarith [abs_nonneg (Real.log c), abs_nonneg (ℓ q)]
  · filter_upwards [hSlt] with q hq
    have hSpos : 0 < (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal :=
      ENNReal.toReal_pos (cascadeSum_of_ne_zero k (fun _ θ => Gt θ) hG (fun _ => hGpos) 0 q.1 w
        hW0 q.2) hq.ne
    have hT : Tendsto (fun M => (truncSum k M w (Gt q.1) q.2).toReal) atTop
        (𝓝 (cascadeSum k (Gt q.1) (cascadeZip k (w, q.2))).toReal) := by
      rw [cascadeSum_cascadeZip k (hGm' q.1)]
      refine (tendsto_toReal_sum_truncBranch k
        (fun α => branchWeight k w α * Gt q.1 (branchMarks k q.2 α))
        (by rw [← cascadeSum_cascadeZip k (hGm' q.1)]; exact hq.ne)).congr fun M => ?_
      rw [truncSum, ENNReal.toReal_sum fun α _ => ENNReal.mul_ne_top (hw _) (hGfin _ _)]
    exact (Real.continuousAt_log hSpos.ne').tendsto.comp hT

end

end SpinGlass
