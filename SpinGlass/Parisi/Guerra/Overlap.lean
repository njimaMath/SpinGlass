import SpinGlass.Parisi.Guerra.Initial

/-!
# Overlap

Integrated overlap averages and interpolation remainder.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

/-! ### The bound: Proposition 14.3.3 conditionally on `(t, H_N, z₀)` -/

/-- `𝔼_{H,z} ⟨1_{(α,γ) ≥ r}⟩_t` at fixed weights `w`. -/
def pairAvg (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) (r : ℕ) (w : CascadeWeights k) (t : ℝ) : ℝ :=
  ∫ ω, gibbsPair k r (hamG N k t h ω.1 ω.2.1) w ω.2.2
    ∂(gaussField N (overlapCovMatrix N ξ)).prod
      (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))

/-- Joint measurability of the pair fraction in `(w, t)` and the disorder and marks. -/
lemma measurable_gibbsPair_hamG_wt (r : ℕ) (h : Fin N → ℝ) :
    Measurable fun q : (CascadeWeights k × ℝ) × (EnergySpace N × MarksSpace N k) =>
      gibbsPair k r (hamG N k q.1.2 h q.2.1 q.2.2.1) q.1.1 q.2.2.2 := by
  have hm : Measurable fun q : (CascadeWeights k × ℝ) × (EnergySpace N × MarksSpace N k) =>
      ((q.1.2, q.2.1, q.2.2.1), (q.1.1, q.2.2.2)) :=
    ((measurable_snd.comp measurable_fst).prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))).prodMk
      ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have := (measurable_gibbsPair_hamG N k r h).comp hm
  simp only [Function.comp_def] at this
  exact this

/-- Joint measurability of the pair fraction in the weights and the disorder and marks. -/
lemma measurable_gibbsPair_hamG_w (r : ℕ) (t : ℝ) (h : Fin N → ℝ) :
    Measurable fun q : CascadeWeights k × (EnergySpace N × MarksSpace N k) =>
      gibbsPair k r (hamG N k t h q.2.1 q.2.2.1) q.1 q.2.2.2 := by
  have hm : Measurable fun q : CascadeWeights k × (EnergySpace N × MarksSpace N k) =>
      ((t, q.2.1, q.2.2.1), (q.1, q.2.2.2)) :=
    (measurable_const.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))).prodMk
      (measurable_fst.prodMk (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have := (measurable_gibbsPair_hamG N k r h).comp hm
  simp only [Function.comp_def] at this
  exact this

/-- The pair fraction in the disorder and the marks, at fixed `(t, H, z₀)` and the weights. -/
lemma measurable_gibbsPair_hamG_wz (r : ℕ) (t : ℝ) (h : Fin N → ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ) :
    Measurable fun q' : CascadeWeights k × CascadeMarks (Fin N → ℝ) k =>
      gibbsPair k r (hamG N k t h H z₀) q'.1 q'.2 := by
  have := (measurable_gibbsPair_hamG N k r h).comp
    (measurable_const.prodMk measurable_id :
      Measurable fun q' : CascadeWeights k × CascadeMarks (Fin N → ℝ) k => ((t, H, z₀), q'))
  simp only [Function.comp_def] at this
  exact this

/-- Proposition 14.3.3, integrated (Talagrand's (14.76)): `𝔼⟨1_{(α,γ) ≥ r}⟩_t = 1 − m_r`. -/
theorem integral_pairAvg (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) (ms : Fin k → ℝ)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) (r : ℕ) (t : ℝ) :
    ∫ w, pairAvg N k ξ qs h r w t ∂cascadeWeightsLaw k ms = 1 - mExt ms r := by
  set v₀ : ℝ≥0 := parisiVar ξ qs 0 with hv₀
  set vs : Fin k → ℝ≥0 := fun p => parisiVar ξ qs (p.val + 1) with hvs
  set Pw := cascadeWeightsLaw k ms with hPw
  set Pz := gaussField N (overlapCovMatrix N ξ) with hPz
  set P₀ : Measure (Fin N → ℝ) := Measure.pi (fun _ : Fin N => gaussianReal 0 v₀) with hP₀
  set Pmk := cascadeMarksLaw k (gaussianMarks N k vs) with hPmk
  have hle : ∀ i, ms i ≤ 1 := fun i => (hlt i).le
  have hmeas := measurable_gibbsPair_hamG_w N k r t h
  have hg : Integrable (fun q : CascadeWeights k × (EnergySpace N × MarksSpace N k) =>
      gibbsPair k r (hamG N k t h q.2.1 q.2.2.1) q.1 q.2.2.2) (Pw.prod (Pz.prod (marksLaw N k v₀ vs))) :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gibbsPair_nonneg k r _ _ _)]
      exact gibbsPair_le_one k r (measurable_hamG' N k t h _ _) _ _)
  unfold pairAvg
  rw [← integral_prod _ hg]
  -- swap `w` with `(H, z₀)`
  have hφ : Measurable fun p : (EnergySpace N × (Fin N → ℝ)) × (CascadeWeights k × CascadeMarks (Fin N → ℝ) k) =>
      ((p.2.1, (p.1.1, (p.1.2, p.2.2))) : CascadeWeights k × (EnergySpace N × MarksSpace N k)) :=
    (measurable_fst.comp measurable_snd).prodMk ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))
  have hswap : Pw.prod (Pz.prod (marksLaw N k v₀ vs))
      = ((Pz.prod P₀).prod (Pw.prod Pmk)).map
          (fun p : (EnergySpace N × (Fin N → ℝ)) × (CascadeWeights k × CascadeMarks (Fin N → ℝ) k) =>
            ((p.2.1, (p.1.1, (p.1.2, p.2.2))) : CascadeWeights k × (EnergySpace N × MarksSpace N k))) := by
    unfold marksLaw
    exact Measure.prod_swap_left₄ Pw Pz P₀ Pmk
  have hg' : Integrable (fun p : (EnergySpace N × (Fin N → ℝ))
        × (CascadeWeights k × CascadeMarks (Fin N → ℝ) k) =>
      gibbsPair k r (hamG N k t h p.1.1 p.1.2) p.2.1 p.2.2) ((Pz.prod P₀).prod (Pw.prod Pmk)) := by
    have := (integrable_map_measure hmeas.aestronglyMeasurable hφ.aemeasurable).1 (hswap ▸ hg)
    exact this
  rw [hswap, integral_map hφ.aemeasurable hmeas.aestronglyMeasurable, integral_prod _ hg']
  -- Proposition 14.3.3 at fixed `(H, z₀)`
  have hinner : ∀ a : EnergySpace N × (Fin N → ℝ),
      ∫ q', gibbsPair k r (hamG N k t h a.1 a.2) q'.1 q'.2 ∂Pw.prod Pmk = 1 - mExt ms r := fun a =>
    integral_gibbsPair_eq k ms (gaussianMarks N k vs) (measurable_hamG' N k t h a.1 a.2)
      (fun zs => hamG_pos N k t h a.1 a.2 zs) hsm hpos hlt
      (cascadeRec_hamG_ne_top N k ms vs hpos hle t h a.1 a.2) r
  simp_rw [hinner]
  rw [integral_const, probReal_univ, one_smul]

/-! ### The bound integrated over the weights -/

/-- Joint measurability of `𝔼⟨1_{(α,γ) ≥ r}⟩_t` in the weights and the time. -/
lemma measurable_pairAvg (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) (r : ℕ) :
    Measurable fun q : CascadeWeights k × ℝ => pairAvg N k ξ qs h r q.1 q.2 := by
  unfold pairAvg
  exact ((measurable_gibbsPair_hamG_wt N k r h).stronglyMeasurable.integral_prod_right').measurable

lemma abs_pairAvg_le_one (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) (r : ℕ)
    (w : CascadeWeights k) (t : ℝ) : |pairAvg N k ξ qs h r w t| ≤ 1 := by
  unfold pairAvg
  have := norm_integral_le_of_norm_le_const (C := 1)
    (μ := (gaussField N (overlapCovMatrix N ξ)).prod
      (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1)))
    (f := fun ω : EnergySpace N × MarksSpace N k =>
      gibbsPair k r (hamG N k t h ω.1 ω.2.1) w ω.2.2)
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gibbsPair_nonneg k r _ _ _)]
      exact gibbsPair_le_one k r (measurable_hamG' N k t h ω.1 ω.2.1) _ _)
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at this

lemma pairAvg_nonneg (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) (r : ℕ)
    (w : CascadeWeights k) (t : ℝ) : 0 ≤ pairAvg N k ξ qs h r w t :=
  integral_nonneg fun _ => gibbsPair_nonneg k r _ _ _

/-- The pair fraction is integrable in the disorder and the marks. -/
lemma integrable_gibbsPair (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) (r : ℕ)
    (w : CascadeWeights k) (t : ℝ) :
    Integrable (fun ω : EnergySpace N × MarksSpace N k =>
        gibbsPair k r (hamG N k t h ω.1 ω.2.1) w ω.2.2)
      ((gaussField N (overlapCovMatrix N ξ)).prod
        (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))) :=
  Integrable.of_bound (measurable_gibbsPair_hamG' N k r t h w).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gibbsPair_nonneg k r _ _ _)]
      exact gibbsPair_le_one k r (measurable_hamG' N k t h ω.1 ω.2.1) _ _)

lemma pairAvg_le_one (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) (r : ℕ)
    (w : CascadeWeights k) (t : ℝ) : pairAvg N k ξ qs h r w t ≤ 1 := by
  have := integral_mono (integrable_gibbsPair N k ξ qs h r w t) (integrable_const (1 : ℝ))
    fun ω => gibbsPair_le_one k r (measurable_hamG' N k t h ω.1 ω.2.1) _ _
  rwa [integral_const, probReal_univ, one_smul] at this

/-- The bound of the interpolation in terms of the pair averages (Talagrand's (14.75)). -/
lemma guerraBound_eq (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) (w : CascadeWeights k) (t : ℝ) :
    guerraBound N k ξ qs h w t
      = (1 / 2) * (ξ 1 - deriv ξ (qs (Fin.last k)))
        + (1 / 2) * ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1))
            * (pairAvg N k ξ qs h r w t - pairAvg N k ξ qs h (r + 1) w t) := by
  have hint : ∀ r : ℕ, Integrable (fun ω : EnergySpace N × MarksSpace N k =>
      gibbsPair k r (hamG N k t h ω.1 ω.2.1) w ω.2.2)
      ((gaussField N (overlapCovMatrix N ξ)).prod
        (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))) := fun r =>
    integrable_gibbsPair N k ξ qs h r w t
  have hsum : Integrable (fun ω : EnergySpace N × MarksSpace N k =>
      ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1))
        * (gibbsPair k r (hamG N k t h ω.1 ω.2.1) w ω.2.2
          - gibbsPair k (r + 1) (hamG N k t h ω.1 ω.2.1) w ω.2.2))
      ((gaussField N (overlapCovMatrix N ξ)).prod
        (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))) :=
    integrable_finsetSum _ fun r _ => ((hint r).sub (hint (r + 1))).const_mul _
  have hterm : ∀ r : ℕ, Integrable (fun ω : EnergySpace N × MarksSpace N k =>
      parisiTheta ξ (qExt qs (r + 1))
        * (gibbsPair k r (hamG N k t h ω.1 ω.2.1) w ω.2.2
          - gibbsPair k (r + 1) (hamG N k t h ω.1 ω.2.1) w ω.2.2))
      ((gaussField N (overlapCovMatrix N ξ)).prod
        (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))) := fun r =>
    ((hint r).sub (hint (r + 1))).const_mul _
  unfold guerraBound levelBound pairAvg
  rw [integral_add (integrable_const _) (hsum.const_mul _), integral_const, probReal_univ,
    one_smul, integral_const_mul, integral_finsetSum _ fun r _ => hterm r]
  congr 2
  exact Finset.sum_congr rfl fun r _ => by
    rw [integral_const_mul, integral_sub (hint r) (hint (r + 1))]

/-- The bound of the interpolation, averaged over the cascade weights (Talagrand's (14.79)):
`(1/2)(ξ(1) − ξ'(q_{k+1})) + (1/2) ∑_{r ≤ k} θ(q_{r+1}) (m_{r+1} − m_r)`, independently of `t`. -/
theorem integral_guerraBound (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) (ms : Fin k → ℝ)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) (t : ℝ) :
    ∫ w, guerraBound N k ξ qs h w t ∂cascadeWeightsLaw k ms
      = (1 / 2) * (ξ 1 - deriv ξ (qs (Fin.last k)))
        + (1 / 2) * ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1))
            * (mExt ms (r + 1) - mExt ms r) := by
  have hintP : ∀ r : ℕ, Integrable (fun w => pairAvg N k ξ qs h r w t) (cascadeWeightsLaw k ms) :=
    fun r => Integrable.of_bound
      (((measurable_pairAvg N k ξ qs h r).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable) 1
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]; exact abs_pairAvg_le_one N k ξ qs h r w t)
  have hterm : ∀ r : ℕ, Integrable (fun w : CascadeWeights k =>
      parisiTheta ξ (qExt qs (r + 1))
        * (pairAvg N k ξ qs h r w t - pairAvg N k ξ qs h (r + 1) w t))
      (cascadeWeightsLaw k ms) := fun r => ((hintP r).sub (hintP (r + 1))).const_mul _
  have hsum : Integrable (fun w : CascadeWeights k =>
      ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1))
        * (pairAvg N k ξ qs h r w t - pairAvg N k ξ qs h (r + 1) w t))
      (cascadeWeightsLaw k ms) := integrable_finsetSum _ fun r _ => hterm r
  simp_rw [guerraBound_eq N k ξ qs h _ t]
  rw [integral_add (integrable_const _) (hsum.const_mul _),
    integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_finsetSum _ fun r _ => hterm r]
  congr 2
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_const_mul, integral_sub (hintP r) (hintP (r + 1)),
    integral_pairAvg N k ξ qs h ms hsm hpos hlt r t,
    integral_pairAvg N k ξ qs h ms hsm hpos hlt (r + 1) t]
  ring

/-- The bound is jointly measurable in the weights and the time. -/
lemma measurable_guerraBound (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) :
    Measurable fun q : CascadeWeights k × ℝ => guerraBound N k ξ qs h q.1 q.2 := by
  simp_rw [guerraBound_eq N k ξ qs h]
  exact measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun r _ =>
    measurable_const.mul ((measurable_pairAvg N k ξ qs h r).sub
      (measurable_pairAvg N k ξ qs h (r + 1)))))

lemma abs_guerraBound_le (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) (w : CascadeWeights k)
    (t : ℝ) : |guerraBound N k ξ qs h w t|
      ≤ (1 / 2) * |ξ 1 - deriv ξ (qs (Fin.last k))|
        + (1 / 2) * ∑ r ∈ Finset.range (k + 1), |parisiTheta ξ (qExt qs (r + 1))| := by
  rw [guerraBound_eq N k ξ qs h w t]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun r _ => ?_)) (by norm_num)
    rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [abs_sub_le_iff]
    exact ⟨by linarith [pairAvg_nonneg N k ξ qs h (r + 1) w t, pairAvg_le_one N k ξ qs h r w t],
      by linarith [pairAvg_nonneg N k ξ qs h r w t, pairAvg_le_one N k ξ qs h (r + 1) w t]⟩

/-- The time-integrated bound, averaged over the cascade weights. -/
theorem integral_intervalIntegral_guerraBound (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ)
    (ms : Fin k → ℝ) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) :
    ∫ w, (∫ t in (0 : ℝ)..1, guerraBound N k ξ qs h w t) ∂cascadeWeightsLaw k ms
      = (1 / 2) * (ξ 1 - deriv ξ (qs (Fin.last k)))
        + (1 / 2) * ∑ r ∈ Finset.range (k + 1), parisiTheta ξ (qExt qs (r + 1))
            * (mExt ms (r + 1) - mExt ms r) := by
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hswap : Integrable (Function.uncurry fun (w : CascadeWeights k) (t : ℝ) =>
      guerraBound N k ξ qs h w t)
      ((cascadeWeightsLaw k ms).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) :=
    Integrable.of_bound (measurable_guerraBound N k ξ qs h).aestronglyMeasurable
      ((1 / 2) * |ξ 1 - deriv ξ (qs (Fin.last k))|
        + (1 / 2) * ∑ r ∈ Finset.range (k + 1), |parisiTheta ξ (qExt qs (r + 1))|)
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs]; exact abs_guerraBound_le N k ξ qs h q.1 q.2)
  simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  rw [integral_integral_swap hswap]
  simp_rw [integral_guerraBound N k ξ qs h ms hsm hpos hlt]
  rw [setIntegral_const, Measure.real, Real.volume_Ioc]
  norm_num


end

end SpinGlass
