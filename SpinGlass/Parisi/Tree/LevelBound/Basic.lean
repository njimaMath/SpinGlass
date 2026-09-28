/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.Tree.PairLevels
import Common.Mathlib.Probability.ProductMeasureProd

/-!
# The level-sum bound of a Guerra interpolation, averaged over the cascade

The common analytic layer of Guerra's bound (§14.4) and of the coupled scheme (§14.6). A scheme is
described by its **branch functions** `G t θ : (Fin k → T) → ℝ≥0∞` — the branch partition
function `exp F_t(x_α)` at time `t`, given the conditioning parameters `θ` (the disorder `H_N` and
the root marks) and the marks `x_α` along a branch — on a cascade with mark laws `μs` and weights
of parameters `ms`. At fixed weights `w`:

* `pairAvgOf r w t = 𝔼_{θ,z} ⟨1_{(α,γ) ≥ r}⟩_t` and, by Proposition 14.3.3 applied conditionally
  on `θ`, its average over the cascade weights is `1 - m_r` (`integral_pairAvgOf`, Talagrand's
  (14.76));
* the bound
  `levelBoundLaw c₀ θ w t = 𝔼_{θ,z} [(1/2) c₀ + (1/2) ∑_{r ≤ k} θ_r (⟨1_{≥r}⟩ - ⟨1_{≥r+1}⟩)]`
  has weight average `(1/2) c₀ + (1/2) ∑_{r ≤ k} θ_r (m_{r+1} - m_r)`, independently of `t`
  (`integral_levelBoundLaw`, `integral_intervalIntegral_levelBoundLaw`);
* the bounds of the trees truncated to indices `< M` converge to it as `M → ∞`
  (`tendsto_truncLevelBoundLaw`, `tendsto_integral_truncLevelBoundLaw`).
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

/-! ### The truncated cascade sums -/

section TruncSum

omit [Nonempty T]

/-- `S^M = ∑_{α ∈ A_M} u*_α G(z_α)`: the cascade sum restricted to the truncated tree. -/
def truncSum (M : ℕ) (w : CascadeWeights k) (Gt : (Fin k → T) → ℝ≥0∞)
    (z : CascadeMarks T k) : ℝ≥0∞ :=
  ∑ α : TruncBranch k M, branchWeight k w (truncBranchCoe k M α)
    * Gt (branchMarks k z (truncBranchCoe k M α))

lemma truncSum_le_cascadeSum (M : ℕ) (w : CascadeWeights k) {Gt : (Fin k → T) → ℝ≥0∞}
    (hG : Measurable Gt) (z : CascadeMarks T k) :
    truncSum k M w Gt z ≤ cascadeSum k Gt (cascadeZip k (w, z)) := by
  rw [cascadeSum_cascadeZip k hG, truncSum,
    sum_truncBranch_eq k M fun α => branchWeight k w α * Gt (branchMarks k z α)]
  exact ENNReal.sum_le_tsum _

omit [MeasurableSpace T] in
lemma le_truncSum_of_mem (M : ℕ) (w : CascadeWeights k) (Gt : (Fin k → T) → ℝ≥0∞)
    (z : CascadeMarks T k) {α₀ : Fin k → ℕ × ℕ} (hmem : α₀ ∈ truncFinset k M) :
    branchWeight k w α₀ * Gt (branchMarks k z α₀) ≤ truncSum k M w Gt z := by
  rw [truncSum, sum_truncBranch_eq k M fun α => branchWeight k w α * Gt (branchMarks k z α)]
  exact Finset.single_le_sum (f := fun α => branchWeight k w α * Gt (branchMarks k z α))
    (fun _ _ => bot_le) hmem

lemma le_cascadeSum_cascadeZip (w : CascadeWeights k) {Gt : (Fin k → T) → ℝ≥0∞}
    (hG : Measurable Gt) (z : CascadeMarks T k) (α₀ : Fin k → ℕ × ℕ) :
    branchWeight k w α₀ * Gt (branchMarks k z α₀) ≤ cascadeSum k Gt (cascadeZip k (w, z)) := by
  rw [cascadeSum_cascadeZip k hG]
  exact ENNReal.le_tsum α₀

omit [MeasurableSpace T] in
/-- The truncated sum as a real number, for finite weights and branch functions. -/
lemma toReal_truncSum (M : ℕ) (w : CascadeWeights k) (hw : ∀ α, branchWeight k w α ≠ ∞)
    {Gt : (Fin k → T) → ℝ≥0∞} (hGfin : ∀ x, Gt x ≠ ∞) (z : CascadeMarks T k) :
    (truncSum k M w Gt z).toReal
      = ∑ α : TruncBranch k M,
          truncWt k M w α * (Gt (branchMarks k z (truncBranchCoe k M α))).toReal := by
  unfold truncSum
  rw [ENNReal.toReal_sum fun α _ => ENNReal.mul_ne_top (hw _) (hGfin _)]
  exact Finset.sum_congr rfl fun α _ => ENNReal.toReal_mul

omit [MeasurableSpace T] in
/-- A branch of positive weight lies in all sufficiently large truncated trees. -/
lemma exists_mem_truncFinset (w : CascadeWeights k) (hW0 : weightSum k w ≠ 0) :
    ∃ α₀ : Fin k → ℕ × ℕ, branchWeight k w α₀ ≠ 0 ∧ ∃ M₀, ∀ M, M₀ ≤ M → α₀ ∈ truncFinset k M := by
  obtain ⟨α₀, hα₀⟩ : ∃ α₀, branchWeight k w α₀ ≠ 0 := by
    by_contra hcon
    exact hW0 (ENNReal.tsum_eq_zero.2 fun α => by simpa using fun h => hcon ⟨α, h⟩)
  obtain ⟨M₀, hM₀⟩ := exists_subset_truncFinset k {α₀}
  exact ⟨α₀, hα₀, M₀, fun M hM => truncFinset_mono k hM (hM₀ (Finset.mem_singleton_self _))⟩

lemma truncWt_ne_zero_of_mem {M : ℕ} (w : CascadeWeights k) (hW : weightSum k w ≠ ∞)
    {α₀ : Fin k → ℕ × ℕ} (hα₀ : branchWeight k w α₀ ≠ 0) (hmem : α₀ ∈ truncFinset k M) :
    ∃ β : TruncBranch k M, truncWt k M w β ≠ 0 := by
  obtain ⟨β, _, hβ⟩ := Finset.mem_map.1 hmem
  refine ⟨β, ?_⟩
  unfold truncWt
  rw [show truncBranchCoe k M β = α₀ from hβ]
  exact ENNReal.toReal_ne_zero.2 ⟨hα₀, ne_top_of_le_ne_top hW (branchWeight_le_weightSum k w α₀)⟩

end TruncSum

/-! ### Measurability -/

omit [Nonempty T] in
lemma measurable_of_uncurry₃ (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2)
    (t : ℝ) (θ : Θ) : Measurable (G t θ) := by
  have := hG.comp (measurable_const.prodMk measurable_id :
    Measurable fun x : Fin k → T => ((t, θ), x))
  exact this

omit [Nonempty T] in
/-- Joint measurability of the pair fraction in the time, the parameter, the weights and the
marks. -/
lemma measurable_gibbsPair_of
    (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2) (r : ℕ) :
    Measurable fun q : (ℝ × Θ) × (CascadeWeights k × CascadeMarks T k) =>
      gibbsPair k r (G q.1.1 q.1.2) q.2.1 q.2.2 := by
  unfold gibbsPair
  have hm : Measurable fun q : (ℝ × Θ) × (CascadeWeights k × CascadeMarks T k) =>
      (q.1, cascadeZip k q.2) :=
    measurable_fst.prodMk ((measurable_cascadeZip k).comp measurable_snd)
  have h1 := (measurable_cascadeSq_prod k r (G := fun a : ℝ × Θ => G a.1 a.2) hG).comp hm
  have h2 := (measurable_cascadeSum_prod k (G := fun a : ℝ × Θ => G a.1 a.2) hG).comp hm
  simp only [Function.comp_def] at h1 h2
  exact (h1.mul (h2.inv.pow_const 2)).ennreal_toReal

omit [Nonempty T] in
/-- Joint measurability of the truncated pair fraction in the parameter and the marks. -/
lemma measurable_truncPair_of
    (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2) (M r : ℕ)
    (w : CascadeWeights k) (t : ℝ) :
    Measurable fun q : Θ × CascadeMarks T k => truncPair k M r (G t q.1) w q.2 := by
  unfold truncPair
  have hGα : ∀ α : TruncBranch k M, Measurable fun q : Θ × CascadeMarks T k =>
      G t q.1 (branchMarks k q.2 (truncBranchCoe k M α)) := fun α => by
    have := hG.comp ((measurable_const.prodMk measurable_fst).prodMk
      ((measurable_branchMarks k (truncBranchCoe k M α)).comp measurable_snd) :
        Measurable fun q : Θ × CascadeMarks T k =>
          ((t, q.1), branchMarks k q.2 (truncBranchCoe k M α)))
    exact this
  refine Measurable.ennreal_toReal ((Finset.measurable_sum _ fun α _ =>
    Finset.measurable_sum _ fun γ _ => measurable_const.mul
      (measurable_const.mul ((hGα α).mul (hGα γ)))).mul
    ((Finset.measurable_sum _ fun α _ => measurable_const.mul (hGα α)).inv.pow_const 2))

omit [Nonempty T] in
/-- Joint measurability of the truncated level sum in the parameter and the marks. -/
lemma measurable_levelBound_truncPair_of
    (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2) (M : ℕ) (c₀ : ℝ)
    (θf : ℕ → ℝ) (w : CascadeWeights k) (t : ℝ) :
    Measurable fun q : Θ × CascadeMarks T k =>
      levelBound k c₀ θf (fun r => truncPair k M r (G t q.1) w q.2) :=
  measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun r _ =>
    measurable_const.mul ((measurable_truncPair_of k G hG M r w t).sub
      (measurable_truncPair_of k G hG M (r + 1) w t))))

omit [Nonempty T] in
/-- Measurability of the cascade sum of the branch functions in the parameter and the marks. -/
lemma measurable_cascadeSum_of
    (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2)
    (w : CascadeWeights k) (t : ℝ) :
    Measurable fun q : Θ × CascadeMarks T k =>
      cascadeSum k (G t q.1) (cascadeZip k (w, q.2)) := by
  have hm : Measurable fun q : Θ × CascadeMarks T k => ((t, q.1), cascadeZip k (w, q.2)) :=
    (measurable_const.prodMk measurable_fst).prodMk
      ((measurable_cascadeZip k).comp (measurable_const.prodMk measurable_snd))
  have := (measurable_cascadeSum_prod k (G := fun a : ℝ × Θ => G a.1 a.2) hG).comp hm
  simp only [Function.comp_def] at this
  exact this

/-! ### The pair averages and Proposition 14.3.3 integrated -/

/-- `𝔼_{θ,z} ⟨1_{(α,γ) ≥ r}⟩_t` at fixed weights `w`. -/
def pairAvgOf (r : ℕ) (w : CascadeWeights k) (t : ℝ) : ℝ :=
  ∫ q, gibbsPair k r (G t q.1) w q.2 ∂Pθ.prod (cascadeMarksLaw k μs)

omit [Nonempty T] in
lemma measurable_pairAvgOf
    (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2) (r : ℕ) :
    Measurable fun q : CascadeWeights k × ℝ => pairAvgOf k Pθ μs G r q.1 q.2 := by
  unfold pairAvgOf
  have hm : Measurable fun q : (CascadeWeights k × ℝ) × (Θ × CascadeMarks T k) =>
      ((q.1.2, q.2.1), (q.1.1, q.2.2)) :=
    ((measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  have := (measurable_gibbsPair_of k G hG r).comp hm
  simp only [Function.comp_def] at this
  exact this.stronglyMeasurable.integral_prod_right'.measurable

omit [Nonempty T] in
lemma integrable_gibbsPair_of
    (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2) (r : ℕ)
    (w : CascadeWeights k) (t : ℝ) :
    Integrable (fun q : Θ × CascadeMarks T k => gibbsPair k r (G t q.1) w q.2)
      (Pθ.prod (cascadeMarksLaw k μs)) := by
  have hm : Measurable fun q : Θ × CascadeMarks T k => ((t, q.1), (w, q.2)) :=
    (measurable_const.prodMk measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
  have hmeas := (measurable_gibbsPair_of k G hG r).comp hm
  simp only [Function.comp_def] at hmeas
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gibbsPair_nonneg k r _ _ _)]
  exact gibbsPair_le_one k r (measurable_of_uncurry₃ k G hG t q.1) _ _

omit [Nonempty T] [IsProbabilityMeasure Pθ] in
lemma pairAvgOf_nonneg (r : ℕ) (w : CascadeWeights k) (t : ℝ) : 0 ≤ pairAvgOf k Pθ μs G r w t :=
  integral_nonneg fun _ => gibbsPair_nonneg k r _ _ _

omit [Nonempty T] in
lemma pairAvgOf_le_one (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2)
    (r : ℕ) (w : CascadeWeights k) (t : ℝ) : pairAvgOf k Pθ μs G r w t ≤ 1 := by
  have := integral_mono (integrable_gibbsPair_of k Pθ μs G hG r w t) (integrable_const (1 : ℝ))
    fun q => gibbsPair_le_one k r (measurable_of_uncurry₃ k G hG t q.1) _ _
  rwa [integral_const, probReal_univ, one_smul] at this

omit [Nonempty T] in
lemma abs_pairAvgOf_le_one (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2)
    (r : ℕ) (w : CascadeWeights k) (t : ℝ) : |pairAvgOf k Pθ μs G r w t| ≤ 1 :=
  abs_le.2 ⟨by linarith [pairAvgOf_nonneg k Pθ μs G r w t], pairAvgOf_le_one k Pθ μs G hG r w t⟩

/-- **Proposition 14.3.3, integrated (Talagrand's (14.76))**: `𝔼⟨1_{(α,γ) ≥ r}⟩_t = 1 − m_r`,
the expectation being over the weights, the parameters and the marks. -/
theorem integral_pairAvgOf (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2)
    (hGpos : ∀ t θ x, 0 < G t θ x) (ms : Fin k → ℝ) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) (hfin : ∀ t θ, cascadeRec k ms μs (G t θ) ≠ ∞) (r : ℕ) (t : ℝ) :
    ∫ w, pairAvgOf k Pθ μs G r w t ∂cascadeWeightsLaw k ms = 1 - mExt ms r := by
  set Pw := cascadeWeightsLaw k ms with hPw
  set Pmk := cascadeMarksLaw k μs with hPmk
  have hmeas : Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T k) =>
      gibbsPair k r (G t q.2.1) q.1 q.2.2 := by
    have hm : Measurable fun q : CascadeWeights k × (Θ × CascadeMarks T k) =>
        ((t, q.2.1), (q.1, q.2.2)) :=
      (measurable_const.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    have := (measurable_gibbsPair_of k G hG r).comp hm
    simp only [Function.comp_def] at this
    exact this
  have hg : Integrable (fun q : CascadeWeights k × (Θ × CascadeMarks T k) =>
      gibbsPair k r (G t q.2.1) q.1 q.2.2) (Pw.prod (Pθ.prod Pmk)) :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gibbsPair_nonneg k r _ _ _)]
      exact gibbsPair_le_one k r (measurable_of_uncurry₃ k G hG t q.2.1) _ _)
  unfold pairAvgOf
  rw [← integral_prod _ hg]
  -- swap the weights with the parameter
  have hφ : Measurable fun p : Θ × (CascadeWeights k × CascadeMarks T k) =>
      ((p.2.1, (p.1, p.2.2)) : CascadeWeights k × (Θ × CascadeMarks T k)) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hswap : Pw.prod (Pθ.prod Pmk)
      = (Pθ.prod (Pw.prod Pmk)).map (fun p : Θ × (CascadeWeights k × CascadeMarks T k) =>
          ((p.2.1, (p.1, p.2.2)) : CascadeWeights k × (Θ × CascadeMarks T k))) :=
    Measure.prod_swap_left₃ Pw Pθ Pmk
  have hg' : Integrable (fun p : Θ × (CascadeWeights k × CascadeMarks T k) =>
      gibbsPair k r (G t p.1) p.2.1 p.2.2) (Pθ.prod (Pw.prod Pmk)) := by
    have := (integrable_map_measure hmeas.aestronglyMeasurable hφ.aemeasurable).1 (hswap ▸ hg)
    exact this
  rw [hswap, integral_map hφ.aemeasurable hmeas.aestronglyMeasurable, integral_prod _ hg']
  have hinner : ∀ θ : Θ, ∫ q', gibbsPair k r (G t θ) q'.1 q'.2 ∂Pw.prod Pmk = 1 - mExt ms r :=
    fun θ => integral_gibbsPair_eq k ms μs (measurable_of_uncurry₃ k G hG t θ) (hGpos t θ) hsm
      hpos hlt (hfin t θ) r
  simp_rw [hinner]
  rw [integral_const, probReal_univ, one_smul]

/-! ### The level-sum bound and its average over the weights -/

/-- The bound `𝔼_{θ,z} [(1/2) c₀ + (1/2) ∑_{r ≤ k} θ_r (⟨1_{≥ r}⟩_t − ⟨1_{≥ r+1}⟩_t)]` at fixed
weights. -/
def levelBoundLaw (c₀ : ℝ) (θf : ℕ → ℝ) (w : CascadeWeights k) (t : ℝ) : ℝ :=
  ∫ q, levelBound k c₀ θf (fun r => gibbsPair k r (G t q.1) w q.2) ∂Pθ.prod (cascadeMarksLaw k μs)

/-- The same bound for the tree truncated to indices `< M`. -/
def truncLevelBoundLaw (M : ℕ) (c₀ : ℝ) (θf : ℕ → ℝ) (w : CascadeWeights k) (t : ℝ) : ℝ :=
  ∫ q, levelBound k c₀ θf (fun r => truncPair k M r (G t q.1) w q.2)
    ∂Pθ.prod (cascadeMarksLaw k μs)

omit [Nonempty T] in
/-- The bound in terms of the pair averages. -/
lemma levelBoundLaw_eq (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2)
    (c₀ : ℝ) (θf : ℕ → ℝ) (w : CascadeWeights k) (t : ℝ) :
    levelBoundLaw k Pθ μs G c₀ θf w t
      = (1 / 2) * c₀ + (1 / 2) * ∑ r ∈ Finset.range (k + 1),
          θf r * (pairAvgOf k Pθ μs G r w t - pairAvgOf k Pθ μs G (r + 1) w t) := by
  have hint : ∀ r : ℕ, Integrable (fun q : Θ × CascadeMarks T k => gibbsPair k r (G t q.1) w q.2)
      (Pθ.prod (cascadeMarksLaw k μs)) := fun r => integrable_gibbsPair_of k Pθ μs G hG r w t
  have hterm : ∀ r : ℕ, Integrable (fun q : Θ × CascadeMarks T k =>
      θf r * (gibbsPair k r (G t q.1) w q.2 - gibbsPair k (r + 1) (G t q.1) w q.2))
      (Pθ.prod (cascadeMarksLaw k μs)) := fun r => ((hint r).sub (hint (r + 1))).const_mul _
  unfold levelBoundLaw levelBound pairAvgOf
  rw [integral_add (integrable_const _) ((integrable_finsetSum _ fun r _ => hterm r).const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_finsetSum _ fun r _ => hterm r]
  congr 2
  exact Finset.sum_congr rfl fun r _ => by
    rw [integral_const_mul, integral_sub (hint r) (hint (r + 1))]

/-- **The bound averaged over the cascade weights**:
`(1/2) c₀ + (1/2) ∑_{r ≤ k} θ_r (m_{r+1} − m_r)`, independently of `t`. -/
theorem integral_levelBoundLaw
    (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2)
    (hGpos : ∀ t θ x, 0 < G t θ x) (ms : Fin k → ℝ) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) (hfin : ∀ t θ, cascadeRec k ms μs (G t θ) ≠ ∞) (c₀ : ℝ) (θf : ℕ → ℝ)
    (t : ℝ) :
    ∫ w, levelBoundLaw k Pθ μs G c₀ θf w t ∂cascadeWeightsLaw k ms
      = (1 / 2) * c₀ + (1 / 2) * ∑ r ∈ Finset.range (k + 1),
          θf r * (mExt ms (r + 1) - mExt ms r) := by
  have hintP : ∀ r : ℕ, Integrable (fun w => pairAvgOf k Pθ μs G r w t) (cascadeWeightsLaw k ms) :=
    fun r => Integrable.of_bound
      (((measurable_pairAvgOf k Pθ μs G hG r).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]; exact abs_pairAvgOf_le_one k Pθ μs G hG r w t)
  have hterm : ∀ r : ℕ, Integrable (fun w : CascadeWeights k =>
      θf r * (pairAvgOf k Pθ μs G r w t - pairAvgOf k Pθ μs G (r + 1) w t))
      (cascadeWeightsLaw k ms) := fun r => ((hintP r).sub (hintP (r + 1))).const_mul _
  simp_rw [levelBoundLaw_eq k Pθ μs G hG c₀ θf _ t]
  rw [integral_add (integrable_const _) ((integrable_finsetSum _ fun r _ => hterm r).const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_finsetSum _ fun r _ => hterm r]
  congr 2
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_const_mul, integral_sub (hintP r) (hintP (r + 1)),
    integral_pairAvgOf k Pθ μs G hG hGpos ms hsm hpos hlt hfin r t,
    integral_pairAvgOf k Pθ μs G hG hGpos ms hsm hpos hlt hfin (r + 1) t]
  ring

omit [Nonempty T] in
lemma measurable_levelBoundLaw
    (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2) (c₀ : ℝ) (θf : ℕ → ℝ) :
    Measurable fun q : CascadeWeights k × ℝ => levelBoundLaw k Pθ μs G c₀ θf q.1 q.2 := by
  simp_rw [levelBoundLaw_eq k Pθ μs G hG c₀ θf]
  exact measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun r _ =>
    measurable_const.mul ((measurable_pairAvgOf k Pθ μs G hG r).sub
      (measurable_pairAvgOf k Pθ μs G hG (r + 1)))))

omit [Nonempty T] in
lemma abs_levelBoundLaw_le
    (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2) (c₀ : ℝ) (θf : ℕ → ℝ)
    (w : CascadeWeights k) (t : ℝ) :
    |levelBoundLaw k Pθ μs G c₀ θf w t|
      ≤ (1 / 2) * |c₀| + (1 / 2) * ∑ r ∈ Finset.range (k + 1), |θf r| := by
  rw [levelBoundLaw_eq k Pθ μs G hG c₀ θf w t]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun r _ => ?_)) (by norm_num)
    rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [abs_sub_le_iff]
    exact ⟨by linarith [pairAvgOf_nonneg k Pθ μs G (r + 1) w t,
        pairAvgOf_le_one k Pθ μs G hG r w t],
      by linarith [pairAvgOf_nonneg k Pθ μs G r w t, pairAvgOf_le_one k Pθ μs G hG (r + 1) w t]⟩

/-- **The time-integrated bound, averaged over the cascade weights.** -/
theorem integral_intervalIntegral_levelBoundLaw
    (hG : Measurable fun q : (ℝ × Θ) × (Fin k → T) => G q.1.1 q.1.2 q.2)
    (hGpos : ∀ t θ x, 0 < G t θ x) (ms : Fin k → ℝ) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) (hfin : ∀ t θ, cascadeRec k ms μs (G t θ) ≠ ∞) (c₀ : ℝ) (θf : ℕ → ℝ) :
    ∫ w, (∫ t in (0 : ℝ)..1, levelBoundLaw k Pθ μs G c₀ θf w t) ∂cascadeWeightsLaw k ms
      = (1 / 2) * c₀ + (1 / 2) * ∑ r ∈ Finset.range (k + 1),
          θf r * (mExt ms (r + 1) - mExt ms r) := by
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hswap : Integrable (Function.uncurry fun (w : CascadeWeights k) (t : ℝ) =>
      levelBoundLaw k Pθ μs G c₀ θf w t)
      ((cascadeWeightsLaw k ms).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    Integrable.of_bound (measurable_levelBoundLaw k Pθ μs G hG c₀ θf).aestronglyMeasurable
      ((1 / 2) * |c₀| + (1 / 2) * ∑ r ∈ Finset.range (k + 1), |θf r|)
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]; exact abs_levelBoundLaw_le k Pθ μs G hG c₀ θf q.1 q.2)
  simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  rw [integral_integral_swap hswap]
  simp_rw [integral_levelBoundLaw k Pθ μs G hG hGpos ms hsm hpos hlt hfin c₀ θf]
  rw [setIntegral_const, Measure.real, Real.volume_Ioc]
  norm_num


end

end SpinGlass
