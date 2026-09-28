import SpinGlass.Parisi.Guerra.LogCosh

/-!
# Initial

The initial value of Guerra interpolation.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable section

variable (N k : ℕ)

/-! ### The first term: `φ(0)` -/

/-- `∑_α u*_α ≤ ∑_α u*_α exp F(z_α)` since `exp F ≥ 1`. -/
lemma weightSum_le_cascadeSum_coshG (h : Fin N → ℝ) (z₀ : Fin N → ℝ) (w : CascadeWeights k)
    (z : CascadeMarks (Fin N → ℝ) k) :
    weightSum k w ≤ cascadeSum k (coshG N k h z₀) (cascadeZip k (w, z)) := by
  rw [cascadeSum_cascadeZip k (measurable_coshG' N k h z₀), weightSum]
  refine ENNReal.tsum_le_tsum fun α => ?_
  calc branchWeight k w α = branchWeight k w α * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul' le_rfl (one_le_coshG N k h z₀ _)

/-- Joint measurability of the cascade sum of `exp F_{k+1}` in the weights and the marks. -/
lemma measurable_cascadeSum_coshG_prod (h : Fin N → ℝ) :
    Measurable fun q : CascadeWeights k × MarksSpace N k =>
      cascadeSum k (coshG N k h q.2.1) (cascadeZip k (q.1, q.2.2)) := by
  have h1 := measurable_cascadeSum_prod k (measurable_uncurry_coshG N k h)
  have hm : Measurable fun q : CascadeWeights k × MarksSpace N k =>
      (q.2.1, cascadeZip k (q.1, q.2.2)) :=
    (measurable_fst.comp measurable_snd).prodMk
      ((measurable_cascadeZip k).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have := h1.comp hm
  simp only [Function.comp_def] at this
  exact this

/-- The integrand `log (∑_α v_α exp F(z_α))` of `φ(0)`, jointly in the weights and the marks. -/
def logRatio (h : Fin N → ℝ) (q : CascadeWeights k × MarksSpace N k) : ℝ :=
  Real.log ((cascadeSum k (coshG N k h q.2.1) (cascadeZip k (q.1, q.2.2))).toReal
    / (cascadeSum k (fun _ => 1) (cascadeZip k (q.1, q.2.2))).toReal)

lemma measurable_logRatio (h : Fin N → ℝ) : Measurable (logRatio N k h) := by
  unfold logRatio
  refine Real.measurable_log.comp (Measurable.div (ENNReal.measurable_toReal.comp
    (measurable_cascadeSum_coshG_prod N k h)) (ENNReal.measurable_toReal.comp ?_))
  have : Measurable fun q : CascadeWeights k × MarksSpace N k => weightSum k q.1 :=
    (measurable_weightSum k).comp measurable_fst
  simp_rw [cascadeSum_one_cascadeZip]
  exact this

/-- Integrability of `log ∑_α v_α exp F(z_α)` over the weights and the marks: it lies between
`0` and `∑_α v_α exp F(z_α)`, whose expectation is `𝔼 exp F_{k+1} < ∞`. -/
theorem integrable_logRatio (ms : Fin k → ℝ) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1) (v₀ : ℝ≥0) (vs : Fin k → ℝ≥0) (h : Fin N → ℝ) :
    Integrable (logRatio N k h) ((cascadeWeightsLaw k ms).prod (marksLaw N k v₀ vs)) := by
  set Pw := cascadeWeightsLaw k ms with hPw
  set Pm := marksLaw N k v₀ vs with hPm
  have hmS := measurable_cascadeSum_coshG_prod N k h
  have hmW : Measurable fun q : CascadeWeights k × MarksSpace N k => weightSum k q.1 :=
    (measurable_weightSum k).comp measurable_fst
  -- the weights are a.s. of positive finite total mass
  have haeW : ∀ᵐ q ∂Pw.prod Pm, weightSum k q.1 ≠ 0 ∧ weightSum k q.1 ≠ ∞ := by
    have hmeasW : MeasurableSet {q : CascadeWeights k × MarksSpace N k |
        weightSum k q.1 ≠ 0 ∧ weightSum k q.1 ≠ ∞} :=
      (hmW (measurableSet_singleton 0)).compl.inter (hmW (measurableSet_singleton ∞)).compl
    rw [Measure.ae_prod_iff_ae_ae hmeasW]
    filter_upwards [ae_weightSum_ne_zero_ne_top k ms hsm hpos hlt] with w hw
    exact Filter.Eventually.of_forall fun _ => hw
  -- the cascade sum is a.s. finite
  have haeS : ∀ᵐ q ∂Pw.prod Pm,
      cascadeSum k (coshG N k h q.2.1) (cascadeZip k (q.1, q.2.2)) < ∞ := by
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_lt hmS measurable_const)]
    filter_upwards [ae_weightSum_ne_zero_ne_top k ms hsm hpos hlt] with w hw
    refine ae_lt_top (measurable_cascadeSum_coshG N k h w) ?_
    rw [hPm, lintegral_cascadeSum_coshG]
    exact ENNReal.mul_ne_top hw.2 (coshConst_ne_top N k v₀ vs h)
  -- the dominating function `∑_α v_α exp F(z_α)` has finite integral `𝔼 exp F_{k+1}`
  have hdiv : Measurable fun q : CascadeWeights k × MarksSpace N k =>
      cascadeSum k (coshG N k h q.2.1) (cascadeZip k (q.1, q.2.2)) / weightSum k q.1 :=
    hmS.div hmW
  have hfin : ∫⁻ q, cascadeSum k (coshG N k h q.2.1) (cascadeZip k (q.1, q.2.2)) / weightSum k q.1
      ∂Pw.prod Pm ≠ ∞ := by
    rw [lintegral_prod _ hdiv.aemeasurable]
    have hinner : ∀ᵐ w ∂Pw, ∫⁻ z, cascadeSum k (coshG N k h z.1) (cascadeZip k (w, z.2))
        / weightSum k w ∂Pm = coshConst N k v₀ vs h := by
      filter_upwards [ae_weightSum_ne_zero_ne_top k ms hsm hpos hlt] with w hw
      simp_rw [div_eq_mul_inv]
      rw [lintegral_mul_const _ (measurable_cascadeSum_coshG N k h w), hPm,
        lintegral_cascadeSum_coshG, mul_right_comm, ENNReal.mul_inv_cancel hw.1 hw.2, one_mul]
    rw [lintegral_congr_ae hinner, lintegral_const, measure_univ, mul_one]
    exact coshConst_ne_top N k v₀ vs h
  refine Integrable.mono' (integrable_toReal_of_lintegral_ne_top hdiv.aemeasurable hfin)
    (measurable_logRatio N k h).aestronglyMeasurable ?_
  filter_upwards [haeW, haeS] with q hq hqS
  unfold logRatio
  rw [Real.norm_eq_abs, cascadeSum_one_cascadeZip, ENNReal.toReal_div]
  have hWpos : 0 < (weightSum k q.1).toReal := ENNReal.toReal_pos hq.1 hq.2
  have h1 : 1 ≤ (cascadeSum k (coshG N k h q.2.1) (cascadeZip k (q.1, q.2.2))).toReal
      / (weightSum k q.1).toReal := by
    rw [le_div_iff₀ hWpos, one_mul]
    exact ENNReal.toReal_mono hqS.ne (weightSum_le_cascadeSum_coshG N k h q.2.1 q.1 q.2.2)
  rw [abs_of_nonneg (Real.log_nonneg h1)]
  linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le h1)]

/-- `φ(0)` (Talagrand's (14.85)): `𝔼 log ∑_α v_α ∏ᵢ 2cosh(h i + z_{i,0} + ∑ₚ z_{i,p,α})
= N log 2 + ∑ᵢ (X₀(hᵢ) − (ξ'(1) − ξ'(q_{k+1}))/2)`. -/
theorem integral_logRatio_eq (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) (qs : Fin (k + 1) → ℝ) (h : Fin N → ℝ) :
    ∫ q, logRatio N k h q ∂(cascadeWeightsLaw k ms).prod
        (marksLaw N k (parisiVar ξ qs 0) fun p => parisiVar ξ qs (p.val + 1))
      = N * Real.log 2 + ∑ i,
          (parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h i + x)))
            - (parisiVar ξ qs (k + 1) : ℝ) / 2) := by
  set v₀ : ℝ≥0 := parisiVar ξ qs 0 with hv₀
  set vs : Fin k → ℝ≥0 := fun p => parisiVar ξ qs (p.val + 1) with hvs
  set Pw := cascadeWeightsLaw k ms with hPw
  set P₀ : Measure (Fin N → ℝ) := Measure.pi (fun _ : Fin N => gaussianReal 0 v₀) with hP₀
  set Pmk := cascadeMarksLaw k (gaussianMarks N k vs) with hPmk
  have hle : ∀ i, ms i ≤ 1 := fun i => (hlt i).le
  have hF := integrable_logRatio N k ms hsm hpos hlt v₀ vs h
  have hFmeas := measurable_logRatio N k h
  -- swap the weights and the root marks
  have hφ : Measurable fun p : (Fin N → ℝ) × CascadeWeights k × CascadeMarks (Fin N → ℝ) k =>
      ((p.2.1, (p.1, p.2.2)) : CascadeWeights k × MarksSpace N k) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hswap : Pw.prod (marksLaw N k v₀ vs)
      = (P₀.prod (Pw.prod Pmk)).map
          (fun p : (Fin N → ℝ) × CascadeWeights k × CascadeMarks (Fin N → ℝ) k =>
            ((p.2.1, (p.1, p.2.2)) : CascadeWeights k × MarksSpace N k)) := by
    unfold marksLaw
    exact Measure.prod_swap_left₃ Pw P₀ Pmk
  have hF' : Integrable (fun p : (Fin N → ℝ) × CascadeWeights k × CascadeMarks (Fin N → ℝ) k =>
      logRatio N k h (p.2.1, (p.1, p.2.2))) (P₀.prod (Pw.prod Pmk)) := by
    have := (integrable_map_measure hFmeas.aestronglyMeasurable hφ.aemeasurable).1
      (hswap ▸ hF)
    exact this
  rw [hswap, integral_map hφ.aemeasurable hFmeas.aestronglyMeasurable, integral_prod _ hF']
  -- Theorem 14.2.1 conditionally on the root marks
  have hinner : ∀ z₀ : Fin N → ℝ, ∫ q', logRatio N k h (q'.1, (z₀, q'.2)) ∂Pw.prod Pmk
      = parisiRec k ms (gaussianMarks N k vs) (coshF N k h z₀) := by
    intro z₀
    have hmeasF : Measurable fun ω : CascadeSpace (Fin N → ℝ) k =>
        Real.log ((cascadeSum k (fun zs => ENNReal.ofReal (Real.exp (coshF N k h z₀ zs))) ω).toReal
          / (cascadeSum k (fun _ => 1) ω).toReal) :=
      Real.measurable_log.comp ((ENNReal.measurable_toReal.comp
        (measurable_cascadeSum k (measurable_coshG' N k h z₀))).div
          (ENNReal.measurable_toReal.comp (measurable_cascadeSum k measurable_const)))
    rw [← integral_log_cascadeSum_exp_div_eq k ms (gaussianMarks N k vs) (measurable_coshF' N k h z₀)
      hsm hpos hlt (cascadeRec_coshG_ne_top N k ms vs hpos hle h z₀), cascadeLaw_eq_map_cascadeZip,
      integral_map (measurable_cascadeZip k).aemeasurable hmeasF.aestronglyMeasurable]
    rfl
  simp_rw [hinner, parisiRec_coshF N k ms vs hpos hle h]
  have hint : Integrable (fun z₀ : Fin N → ℝ => ∑ i, logCoshRec k ms vs (h i + z₀ i)) P₀ := by
    refine integrable_finsetSum _ fun i _ => ?_
    have hmp : MeasurePreserving (Function.eval i) P₀ (gaussianReal 0 v₀) :=
      measurePreserving_eval (μ := fun _ : Fin N => gaussianReal 0 v₀) i
    exact (hmp.integrable_comp ((measurable_logCoshRec k ms vs).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable).2
        (integrable_logCoshRec_add k ms vs hpos hle (h i) v₀)
  rw [integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul,
    integral_sum_logCoshRec N k ms vs hpos hle h v₀]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hX := parisiX₀_logCosh_eq k ξ (h i) ms qs hpos hle
  change _ = _ at hX
  linarith


end

end SpinGlass
