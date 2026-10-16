import SpinGlass.Parisi.Variational.ParisiHeatTwo

/-!
# Gaussian correlation with fixed marginal variance

Two Gaussian coordinates can be written as a common mark plus or minus
an independent mark. Backward heat differentiation gives their response
to covariance, including both degenerate endpoints.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

namespace SpinGlass

open Aristotle.Heat

private theorem integrable_bounded_continuous {f : ℝ → ℝ} (hc : Continuous f)
    {C : ℝ} (hb : ∀ z, |f z| ≤ C) (v : ℝ≥0) : Integrable f (gaussianReal 0 v) := by
  apply Integrable.mono' (integrable_const C) hc.aestronglyMeasurable
  exact .of_forall fun z => by simpa only [Real.norm_eq_abs] using hb z

private theorem abs_heat_le_bound {f : ℝ → ℝ} {C : ℝ} (hb : ∀ z, |f z| ≤ C)
    (t x : ℝ) : |heat t f x| ≤ C := by
  simpa only [heat, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := gaussianReal 0 t.toNNReal)
      (f := fun z => f (x + z)) (C := C)
      (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb (x + z))

private theorem continuous_heat_kernel {K : ℝ → ℝ → ℝ}
    (hc : Continuous (Function.uncurry K)) {C : ℝ} (hb : ∀ y z, |K y z| ≤ C) :
    Continuous (fun p : ℝ × ℝ => heat p.1 (K p.2) 0) := by
  have h := continuousOn_heat_family (S := univ) hc.continuousOn
    (show UExp univ K from ⟨C, 0, fun y _ z => by simpa using hb y z⟩)
  simp only [univ_prod_univ] at h
  exact (continuousOn_univ.1 h).comp
    (by fun_prop : Continuous fun p : ℝ × ℝ => (p.2, (p.1, (0 : ℝ))))

private theorem hasDerivAt_heat_kernel_param {K K₁ : ℝ → ℝ → ℝ}
    (hc : Continuous (Function.uncurry K)) (hc₁ : Continuous (Function.uncurry K₁))
    (hd : ∀ y z, HasDerivAt (fun x => K x z) (K₁ y z) y)
    {C C₁ : ℝ} (hb : ∀ y z, |K y z| ≤ C) (hb₁ : ∀ y z, |K₁ y z| ≤ C₁)
    (t y : ℝ) :
    HasDerivAt (fun x => heat t (K x) 0) (heat t (K₁ y) 0) y := by
  simp only [heat, zero_add]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ => C₁) (s := univ) (by simp)
    (.of_forall fun x => (hc.comp (by fun_prop : Continuous fun z : ℝ => (x, z))).aestronglyMeasurable)
    (integrable_bounded_continuous (hc.comp (by fun_prop)) (hb y) _)
    (hc₁.comp (by fun_prop : Continuous fun z : ℝ => (y, z))).aestronglyMeasurable
    (.of_forall fun z x _ => by simpa only [Real.norm_eq_abs] using hb₁ x z)
    (integrable_const C₁) (.of_forall fun z x _ => hd x z)).2

/-- Gaussian correlation with coordinate variances `a` and covariance `a - 2v`. -/
noncomputable def gaussianFixedVarianceCorrelation (a v : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  heat (a - v) (fun y => heat v (fun z => f (y + z) * f (y - z)) 0) x

/-- The fixed-variance correlation has a continuous extension to either
degenerate covariance endpoint. -/
theorem continuous_gaussianFixedVarianceCorrelation_joint {f : ℝ → ℝ} (hc : Continuous f)
    {C : ℝ} (hb : ∀ x, |f x| ≤ C) (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => gaussianFixedVarianceCorrelation a p.1 f p.2) := by
  have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hb 0)
  have hK : Continuous (fun p : ℝ × ℝ => f (p.1 + p.2) * f (p.1 - p.2)) := by fun_prop
  have hB : ∀ y z, |f (y + z) * f (y - z)| ≤ C ^ 2 := fun y z => by
    rw [abs_mul]
    nlinarith [mul_le_mul (hb (y + z)) (hb (y - z)) (abs_nonneg _) hC]
  have hinner := continuous_heat_kernel (K := fun y z => f (y + z) * f (y - z)) hK hB
  have houter := continuousOn_heat_family (S := univ) hinner.continuousOn
    (show UExp univ (fun v y => heat v (fun z => f (y + z) * f (y - z)) 0) from
      ⟨C ^ 2, 0, fun v _ y => by simpa using abs_heat_le_bound (hB y) v 0⟩)
  simp only [univ_prod_univ] at houter
  exact (continuousOn_univ.1 houter).comp
    (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1, (a - p.1, p.2)))

theorem continuous_gaussianFixedVarianceCorrelation {f : ℝ → ℝ} (hc : Continuous f)
    {C : ℝ} (hb : ∀ y, |f y| ≤ C) (a x : ℝ) :
    Continuous (fun v => gaussianFixedVarianceCorrelation a v f x) :=
  (continuous_gaussianFixedVarianceCorrelation_joint hc hb a).comp
    (by fun_prop : Continuous fun v : ℝ => (v, x))

/-- A bounded input gives the same square envelope for every covariance. -/
theorem abs_gaussianFixedVarianceCorrelation_le_const {f : ℝ → ℝ} {C : ℝ}
    (hb : ∀ y, |f y| ≤ C) (a v x : ℝ) :
    |gaussianFixedVarianceCorrelation a v f x| ≤ C ^ 2 := by
  have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hb 0)
  apply abs_heat_le_bound
  intro y
  apply abs_heat_le_bound
  intro z
  rw [abs_mul]
  simpa only [pow_two] using mul_le_mul (hb _) (hb _) (abs_nonneg _) hC

/-- The variance derivative equals minus twice the corresponding
correlation of the first derivatives. The formula holds one-sided at
both endpoints and uses two spatial derivatives of the input. -/
theorem hasDerivWithinAt_gaussianFixedVarianceCorrelation {f f₁ f₂ : ℝ → ℝ}
    (hd : ∀ y, HasDerivAt f (f₁ y) y) (hd₁ : ∀ y, HasDerivAt f₁ (f₂ y) y)
    (hc₂ : Continuous f₂) {C : ℝ}
    (hb : ∀ y, |f y| ≤ C) (hb₁ : ∀ y, |f₁ y| ≤ C) (hb₂ : ∀ y, |f₂ y| ≤ C)
    {a v : ℝ} (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivWithinAt (fun w => gaussianFixedVarianceCorrelation a w f x)
      (-2 * gaussianFixedVarianceCorrelation a v f₁ x) (Icc (0 : ℝ) a) v := by
  have hc : Continuous f := continuous_iff_continuousAt.2 fun y => (hd y).continuousAt
  have hc₁ : Continuous f₁ := continuous_iff_continuousAt.2 fun y => (hd₁ y).continuousAt
  have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hb 0)
  let K := fun y z => f (y + z) * f (y - z)
  let K₁ := fun y z => f₁ (y + z) * f (y - z) + f (y + z) * f₁ (y - z)
  let K₂ := fun y z => f₂ (y + z) * f (y - z) +
    2 * f₁ (y + z) * f₁ (y - z) + f (y + z) * f₂ (y - z)
  let D₁ := fun y z => f₁ (y + z) * f (y - z) - f (y + z) * f₁ (y - z)
  let D₂ := fun y z => f₂ (y + z) * f (y - z) -
    2 * f₁ (y + z) * f₁ (y - z) + f (y + z) * f₂ (y - z)
  have cK : Continuous (Function.uncurry K) := by dsimp [K, Function.uncurry]; fun_prop
  have cK₁ : Continuous (Function.uncurry K₁) := by dsimp [K₁, Function.uncurry]; fun_prop
  have cK₂ : Continuous (Function.uncurry K₂) := by dsimp [K₂, Function.uncurry]; fun_prop
  have cD₂ : Continuous (Function.uncurry D₂) := by dsimp [D₂, Function.uncurry]; fun_prop
  have prod_bound : ∀ g h : ℝ → ℝ, (∀ y, |g y| ≤ C) → (∀ y, |h y| ≤ C) →
      ∀ y z, |g (y + z) * h (y - z)| ≤ C ^ 2 := by
    intro g h hg hh y z
    rw [abs_mul]
    simpa only [pow_two] using mul_le_mul (hg _) (hh _) (abs_nonneg _) hC
  have bK : ∀ y z, |K y z| ≤ C ^ 2 := prod_bound f f hb hb
  have bK₁ : ∀ y z, |K₁ y z| ≤ 2 * C ^ 2 := fun y z =>
    (abs_add_le _ _).trans (by linarith [prod_bound f₁ f hb₁ hb y z, prod_bound f f₁ hb hb₁ y z])
  have bD₁ : ∀ y z, |D₁ y z| ≤ 2 * C ^ 2 := fun y z =>
    (abs_sub _ _).trans (by linarith [prod_bound f₁ f hb₁ hb y z, prod_bound f f₁ hb hb₁ y z])
  have bK₂ : ∀ y z, |K₂ y z| ≤ 4 * C ^ 2 := by
    intro y z
    dsimp [K₂]
    have hmiddle : |2 * f₁ (y + z) * f₁ (y - z)| ≤ 2 * C ^ 2 := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
      exact prod_bound f₁ f₁ hb₁ hb₁ y z
    calc
      _ ≤ |f₂ (y + z) * f (y - z)| + |2 * f₁ (y + z) * f₁ (y - z)| +
          |f (y + z) * f₂ (y - z)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 4 * C ^ 2 := by
        linarith [prod_bound f₂ f hb₂ hb y z, hmiddle, prod_bound f f₂ hb hb₂ y z]
  have bD₂ : ∀ y z, |D₂ y z| ≤ 4 * C ^ 2 := by
    intro y z
    dsimp [D₂]
    have hmiddle : |2 * f₁ (y + z) * f₁ (y - z)| ≤ 2 * C ^ 2 := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
      exact prod_bound f₁ f₁ hb₁ hb₁ y z
    calc
      _ ≤ |f₂ (y + z) * f (y - z)| + |2 * f₁ (y + z) * f₁ (y - z)| +
          |f (y + z) * f₂ (y - z)| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 4 * C ^ 2 := by
        linarith [prod_bound f₂ f hb₂ hb y z, hmiddle, prod_bound f f₂ hb hb₂ y z]
  have dyK : ∀ y z, HasDerivAt (fun s => K s z) (K₁ y z) y := by
    intro y z
    exact (((hd (y + z)).comp y ((hasDerivAt_id y).add_const z)).mul
      ((hd (y - z)).comp y ((hasDerivAt_id y).sub_const z))).congr_deriv
        (by dsimp [K₁, Function.comp]; ring)
  have dyK₁ : ∀ y z, HasDerivAt (fun s => K₁ s z) (K₂ y z) y := by
    intro y z
    exact ((((hd₁ (y + z)).comp y ((hasDerivAt_id y).add_const z)).mul
      ((hd (y - z)).comp y ((hasDerivAt_id y).sub_const z))).add
      (((hd (y + z)).comp y ((hasDerivAt_id y).add_const z)).mul
        ((hd₁ (y - z)).comp y ((hasDerivAt_id y).sub_const z)))).congr_deriv
          (by dsimp [K₂, Function.comp]; ring)
  have dzK : ∀ y z, HasDerivAt (K y) (D₁ y z) z := by
    intro y z
    exact (((hd (y + z)).comp z ((hasDerivAt_id z).const_add y)).mul
      ((hd (y - z)).comp z ((hasDerivAt_id z).const_sub y))).congr_deriv
        (by dsimp [D₁, Function.comp]; ring)
  have dzD₁ : ∀ y z, HasDerivAt (D₁ y) (D₂ y z) z := by
    intro y z
    exact ((((hd₁ (y + z)).comp z ((hasDerivAt_id z).const_add y)).mul
      ((hd (y - z)).comp z ((hasDerivAt_id z).const_sub y))).sub
      (((hd (y + z)).comp z ((hasDerivAt_id z).const_add y)).mul
        ((hd₁ (y - z)).comp z ((hasDerivAt_id z).const_sub y)))).congr_deriv
          (by dsimp [D₂, Function.comp]; ring)
  let H := fun w y => heat w (K y) 0
  let H₁ := fun w y => heat w (K₁ y) 0
  let H₂ := fun w y => heat w (K₂ y) 0
  let T := fun w y => heat w (D₂ y) 0 / 2
  have hU : ∀ {J : ℝ → ℝ → ℝ} {B : ℝ}, (∀ y z, |J y z| ≤ B) →
      UExp (Icc 0 a) (fun w y => heat w (J y) 0) := fun hb =>
    ⟨_, 0, fun w _ y => by simpa using abs_heat_le_bound (hb y) w 0⟩
  have htime : ∀ y w, w ∈ Icc 0 a →
      HasDerivWithinAt (fun u => H u y) (T w y) (Icc 0 a) w := by
    intro y w hw
    exact hasDerivWithinAt_heat_time_two (dzK y) (dzD₁ y)
      ⟨C ^ 2, 0, fun _ _ z => by simpa using bK y z⟩
      ⟨2 * C ^ 2, 0, fun _ _ z => by simpa using bD₁ y z⟩
      ⟨4 * C ^ 2, 0, fun _ _ z => by simpa using bD₂ y z⟩
      (cD₂.comp (by fun_prop : Continuous fun z : ℝ => (y, z))) hw 0
  refine (hasDerivWithinAt_heat_backward_two hv
    (h := H) (h₁ := H₁) (h₂ := H₂) (hv' := T)
    (fun w _ y => hasDerivAt_heat_kernel_param cK cK₁ dyK bK bK₁ w y)
    (fun w _ y => hasDerivAt_heat_kernel_param cK₁ cK₂ dyK₁ bK₁ bK₂ w y)
    (hU bK) (hU bK₁) (hU bK₂) ((hU bD₂).div_const 2) htime
    ((continuous_heat_kernel cD₂ bD₂).div_const 2).continuousOn
    (continuous_heat_kernel cK₂ bK₂).continuousOn).congr_deriv ?_
  change heat (a - v) (fun y => heat v (D₂ y) 0 / 2 - heat v (K₂ y) 0 / 2) x = _
  unfold gaussianFixedVarianceCorrelation
  rw [← heat_const_mul]
  apply heat_congr
  intro y
  simp only [heat, zero_add]
  have iD : Integrable (D₂ y) (gaussianReal 0 v.toNNReal) :=
    integrable_bounded_continuous
      (cD₂.comp (by fun_prop : Continuous fun z : ℝ => (y, z))) (bD₂ y) v.toNNReal
  have iK : Integrable (K₂ y) (gaussianReal 0 v.toNNReal) :=
    integrable_bounded_continuous
      (cK₂.comp (by fun_prop : Continuous fun z : ℝ => (y, z))) (bK₂ y) v.toNNReal
  have hs := integral_sub (iD.div_const 2) (iK.div_const 2)
  rw [← integral_div, ← integral_div, ← hs, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun z => by dsimp [D₂, K₂]; ring)

/-- The correlation is bounded by the squared marginal response, with
the common variance fixed even at perfect negative correlation. -/
theorem abs_gaussianFixedVarianceCorrelation_le_heat_sq {f : ℝ → ℝ}
    (hc : Continuous f) {C : ℝ} (hb : ∀ y, |f y| ≤ C)
    {a v : ℝ} (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    |gaussianFixedVarianceCorrelation a v f x| ≤ heat a (fun y => f y ^ 2) x := by
  have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hb 0)
  have hsq : ∀ y, |f y ^ 2| ≤ C ^ 2 := fun y => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb y) 2
  have hprod : ∀ y z, |f (y + z) * f (y - z)| ≤ C ^ 2 := fun y z => by
    rw [abs_mul]
    simpa only [pow_two] using mul_le_mul (hb _) (hb _) (abs_nonneg _) hC
  have hinner (y : ℝ) : |heat v (fun z => f (y + z) * f (y - z)) 0| ≤
      heat v (fun z => f z ^ 2) y := by
    have ip : Integrable (fun z => f (y + z) * f (y - z)) (gaussianReal 0 v.toNNReal) :=
      integrable_bounded_continuous (by fun_prop) (hprod y) _
    have isqP : Integrable (fun z => f (y + z) ^ 2) (gaussianReal 0 v.toNNReal) :=
      integrable_bounded_continuous (by fun_prop) (fun z => hsq _) _
    have isqM : Integrable (fun z => f (y - z) ^ 2) (gaussianReal 0 v.toNNReal) :=
      integrable_bounded_continuous (by fun_prop) (fun z => hsq _) _
    have hsym : (∫ z, f (y - z) ^ 2 ∂gaussianReal 0 v.toNNReal) =
        ∫ z, f (y + z) ^ 2 ∂gaussianReal 0 v.toNNReal := by
      have hm := integral_map (μ := gaussianReal 0 v.toNNReal)
        (f := fun z => f (y + z) ^ 2) measurable_neg.aemeasurable
        ((by fun_prop : Continuous fun z : ℝ => f (y + z) ^ 2).aestronglyMeasurable)
      rw [gaussianReal_map_neg, neg_zero] at hm
      simpa only [sub_eq_add_neg] using hm.symm
    unfold heat
    simp only [zero_add]
    calc
      _ ≤ ∫ z, |f (y + z) * f (y - z)| ∂gaussianReal 0 v.toNNReal := abs_integral_le_integral_abs
      _ ≤ ∫ z, (f (y + z) ^ 2 + f (y - z) ^ 2) / 2 ∂gaussianReal 0 v.toNNReal := by
        apply integral_mono ip.abs ((isqP.add isqM).div_const 2)
        intro z
        change |f (y + z) * f (y - z)| ≤ (f (y + z) ^ 2 + f (y - z) ^ 2) / 2
        rw [abs_mul]
        nlinarith [sq_nonneg (|f (y + z)| - |f (y - z)|), sq_abs (f (y + z)), sq_abs (f (y - z))]
      _ = _ := by rw [integral_div, integral_add isqP isqM, hsym]; ring
  have hK : Continuous (fun p : ℝ × ℝ => f (p.1 + p.2) * f (p.1 - p.2)) := by fun_prop
  have hcinner : Continuous (fun y => heat v (fun z => f (y + z) * f (y - z)) 0) :=
    (continuous_heat_kernel (K := fun y z => f (y + z) * f (y - z)) hK hprod).comp
      (by fun_prop : Continuous fun y : ℝ => (v, y))
  have hcsq : Continuous (heat v (fun y => f y ^ 2)) :=
    (continuous_heat (hc.pow 2) (C := C ^ 2) (K := 0)
      (fun y => by simpa using hsq y)).comp
        (by fun_prop : Continuous fun y : ℝ => (v, y))
  have hh : |gaussianFixedVarianceCorrelation a v f x| ≤ heat (a - v)
      (heat v (fun y => f y ^ 2)) x := by
    unfold gaussianFixedVarianceCorrelation heat
    apply abs_integral_le_integral_abs.trans
    apply integral_mono
      (integrable_bounded_continuous (hcinner.comp (by fun_prop))
        (fun z => abs_heat_le_bound (hprod (x + z)) v 0) _).abs
      (integrable_bounded_continuous (hcsq.comp (by fun_prop))
        (fun z => abs_heat_le_bound hsq v (x + z)) _)
    intro z
    exact hinner (x + z)
  rw [heat_heat (f := fun y => f y ^ 2) (sub_nonneg.2 hv.2) hv.1 (hc.pow 2)
    (C := C ^ 2) (K := 0) (fun y => by simpa using hsq y) x,
    sub_add_cancel] at hh
  exact hh

/-- Covariance variation is controlled by the squared marginal
first derivative. The factor two converts `v` to covariance `a - 2v`. -/
theorem abs_gaussianFixedVarianceCorrelation_sub_le {f f₁ f₂ : ℝ → ℝ}
    (hd : ∀ y, HasDerivAt f (f₁ y) y) (hd₁ : ∀ y, HasDerivAt f₁ (f₂ y) y)
    (hc₂ : Continuous f₂) {C : ℝ}
    (hb : ∀ y, |f y| ≤ C) (hb₁ : ∀ y, |f₁ y| ≤ C) (hb₂ : ∀ y, |f₂ y| ≤ C)
    {a v w : ℝ} (hv : v ∈ Icc (0 : ℝ) a) (hw : w ∈ Icc (0 : ℝ) a) (x : ℝ) :
    |gaussianFixedVarianceCorrelation a v f x - gaussianFixedVarianceCorrelation a w f x| ≤
      2 * heat a (fun y => f₁ y ^ 2) x * |v - w| := by
  have hc₁ : Continuous f₁ := continuous_iff_continuousAt.2 fun y => (hd₁ y).continuousAt
  have hh := (convex_Icc (0 : ℝ) a).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => gaussianFixedVarianceCorrelation a z f x)
    (f' := fun z => -2 * gaussianFixedVarianceCorrelation a z f₁ x)
    (C := 2 * heat a (fun y => f₁ y ^ 2) x)
    (fun z hz => hasDerivWithinAt_gaussianFixedVarianceCorrelation hd hd₁ hc₂ hb hb₁ hb₂ hz x)
    (fun z hz => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
      simp only [neg_neg]
      exact mul_le_mul_of_nonneg_left (abs_gaussianFixedVarianceCorrelation_le_heat_sq hc₁ hb₁ hz x)
        (by norm_num)) hw hv
  simpa only [Real.norm_eq_abs] using hh

/-- The covariance estimate survives averaging any probability law of
a common external field. Its coefficient is the averaged squared curvature. -/
theorem abs_integral_gaussianFixedVarianceCorrelation_sub_le {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {f f₁ f₂ : ℝ → ℝ}
    (hd : ∀ y, HasDerivAt f (f₁ y) y) (hd₁ : ∀ y, HasDerivAt f₁ (f₂ y) y)
    (hc₂ : Continuous f₂) {C : ℝ}
    (hb : ∀ y, |f y| ≤ C) (hb₁ : ∀ y, |f₁ y| ≤ C) (hb₂ : ∀ y, |f₂ y| ≤ C)
    {a v w : ℝ} (hv : v ∈ Icc (0 : ℝ) a) (hw : w ∈ Icc (0 : ℝ) a) :
    |(∫ h, gaussianFixedVarianceCorrelation a v f h ∂μ) -
      ∫ h, gaussianFixedVarianceCorrelation a w f h ∂μ| ≤
      2 * (∫ h, heat a (fun y => f₁ y ^ 2) h ∂μ) * |v - w| := by
  have hc : Continuous f := continuous_iff_continuousAt.2 fun y => (hd y).continuousAt
  have hc₁ : Continuous f₁ := continuous_iff_continuousAt.2 fun y => (hd₁ y).continuousAt
  have hi (z : ℝ) : Integrable (fun h => gaussianFixedVarianceCorrelation a z f h) μ :=
    Integrable.of_bound
      ((continuous_gaussianFixedVarianceCorrelation_joint hc hb a).comp
        (by fun_prop : Continuous fun h : ℝ => (z, h))).aestronglyMeasurable
      (C ^ 2) (.of_forall fun h => by
        rw [Real.norm_eq_abs]
        exact abs_gaussianFixedVarianceCorrelation_le_const hb a z h)
  have hsq : ∀ y, |f₁ y ^ 2| ≤ C ^ 2 := fun y => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb₁ y) 2
  have hisq : Integrable (fun h => heat a (fun y => f₁ y ^ 2) h) μ :=
    Integrable.of_bound
      ((continuous_heat (hc₁.pow 2) (C := C ^ 2) (K := 0)
        (fun y => by simpa using hsq y)).comp
          (by fun_prop : Continuous fun h : ℝ => (a, h))).aestronglyMeasurable
      (C ^ 2) (.of_forall fun h => by rw [Real.norm_eq_abs]; exact abs_heat_le_bound hsq a h)
  have hs : (∫ h, gaussianFixedVarianceCorrelation a v f h -
      gaussianFixedVarianceCorrelation a w f h ∂μ) = _ := integral_sub (hi v) (hi w)
  rw [← hs]
  calc
    _ ≤ ∫ h, |gaussianFixedVarianceCorrelation a v f h -
        gaussianFixedVarianceCorrelation a w f h| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ h, 2 * heat a (fun y => f₁ y ^ 2) h * |v - w| ∂μ := by
      apply integral_mono ((hi v).sub (hi w)).abs ((hisq.const_mul 2).mul_const |v - w|)
      intro h
      exact abs_gaussianFixedVarianceCorrelation_sub_le hd hd₁ hc₂ hb hb₁ hb₂ hv hw h
    _ = _ := by rw [integral_mul_const, integral_const_mul]

end SpinGlass
