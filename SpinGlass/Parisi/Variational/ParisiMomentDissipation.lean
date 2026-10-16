import SpinGlass.Parisi.Variational.ParisiHeatTwo
import SpinGlass.Parisi.Variational.ParisiMomentBounds

/-!
# Dissipation of the actual squared-curvature moment

The variance derivative is the tilted average of
$2m(B'')^3-(B''')^2$. Its uniform bound supplies the cubic overlap
remainder used in Talagrand, Vol. II, (14.272)-(14.283).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass.Aristotle.Heat

/-- Backward heat differentiation of the squared-curvature numerator.
Four terminal derivatives suffice, including both variance endpoints. -/
theorem backward_curvatureSq {g : ℕ → ℝ → ℝ} (hg : Jet g) (hlow : PosLow (g 0))
    {a x v : ℝ} (hv : v ∈ Icc 0 a) :
    HasDerivWithinAt (fun w => heat (a - w) (fun y =>
      (hfam g 2 w y * hfam g 0 w y - hfam g 1 w y ^ 2) ^ 2 *
        (hfam g 0 w y)⁻¹ ^ 3) x)
      (heat (a - v) (fun y => (2 *
        (hfam g 2 v y * hfam g 0 v y - hfam g 1 v y ^ 2) ^ 3 -
        (hfam g 3 v y * hfam g 0 v y ^ 2 -
          3 * hfam g 1 v y * hfam g 2 v y * hfam g 0 v y +
          2 * hfam g 1 v y ^ 3) ^ 2) * (hfam g 0 v y)⁻¹ ^ 5) x)
      (Icc 0 a) v := by
  let e := hfam g 0
  let b := hfam g 1
  let c := hfam g 2
  let d := hfam g 3
  let f := hfam g 4
  let R := fun w y => (e w y)⁻¹
  let D := fun w y => c w y * e w y - b w y ^ 2
  let D₁ := fun w y => d w y * e w y - b w y * c w y
  let D₂ := fun w y => f w y * e w y - c w y ^ 2
  have d0 : ∀ w y, HasDerivAt (e w) (b w y) y := hfam_deriv hg (by norm_num)
  have d1 : ∀ w y, HasDerivAt (b w) (c w y) y := hfam_deriv hg (by norm_num)
  have d2 : ∀ w y, HasDerivAt (c w) (d w y) y := hfam_deriv hg (by norm_num)
  have d3 : ∀ w y, HasDerivAt (d w) (f w y) y := hfam_deriv hg (by norm_num)
  have dR : ∀ w y, HasDerivAt (R w) (-b w y * R w y ^ 2) y :=
    hfam_inv_deriv hg hlow
  have dD : ∀ w y, HasDerivAt (D w) (D₁ w y) y := by
    intro w y
    exact (((d2 w y).mul (d0 w y)).sub ((d1 w y).pow 2)).congr_deriv
      (by dsimp [D₁]; ring)
  have dD₁ : ∀ w y, HasDerivAt (D₁ w) (D₂ w y) y := by
    intro w y
    exact (((d3 w y).mul (d0 w y)).sub ((d1 w y).mul (d2 w y))).congr_deriv
      (by dsimp [D₂]; ring)
  have hp : ∀ w y, e w y ≠ 0 := fun w y => (hfam_pos hg hlow w y).ne'
  have t0 : ∀ w ∈ Icc 0 a, ∀ y,
      HasDerivWithinAt (fun u => e u y) (c w y / 2) (Icc 0 a) w :=
    fun w hw y => hfam_time_two hg (by norm_num) hw y
  have t1 : ∀ w ∈ Icc 0 a, ∀ y,
      HasDerivWithinAt (fun u => b u y) (d w y / 2) (Icc 0 a) w :=
    fun w hw y => hfam_time_two hg (by norm_num) hw y
  have t2 : ∀ w ∈ Icc 0 a, ∀ y,
      HasDerivWithinAt (fun u => c u y) (f w y / 2) (Icc 0 a) w :=
    fun w hw y => hfam_time_two hg (by norm_num) hw y
  have U0 := hfam_uexp hg (j := 0) (by norm_num) a
  have U1 := hfam_uexp hg (j := 1) (by norm_num) a
  have U2 := hfam_uexp hg (j := 2) (by norm_num) a
  have U3 := hfam_uexp hg (j := 3) (by norm_num) a
  have U4 := hfam_uexp hg (j := 4) (by norm_num) a
  have UR := hfam_inv_uexp hg hlow a
  have UD : UExp (Icc 0 a) D := (U2.mul U0).sub (U1.pow 2)
  have UD₁ : UExp (Icc 0 a) D₁ := (U3.mul U0).sub (U1.mul U2)
  have UD₂ : UExp (Icc 0 a) D₂ := (U4.mul U0).sub (U2.pow 2)
  have C0 := hfam_cont hg (j := 0) (by norm_num)
  have C1 := hfam_cont hg (j := 1) (by norm_num)
  have C2 := hfam_cont hg (j := 2) (by norm_num)
  have C3 := hfam_cont hg (j := 3) (by norm_num)
  have C4 := hfam_cont hg (j := 4) (by norm_num)
  have CR := hfam_inv_cont hg hlow
  have CD : Continuous (fun p : ℝ × ℝ => D p.1 p.2) := by dsimp [D, e, b, c]; fun_prop
  have CD₁ : Continuous (fun p : ℝ × ℝ => D₁ p.1 p.2) := by dsimp [D₁, e, b, c, d]; fun_prop
  have CD₂ : Continuous (fun p : ℝ × ℝ => D₂ p.1 p.2) := by dsimp [D₂, e, c, f]; fun_prop
  refine (hasDerivWithinAt_heat_backward_two hv
    (h := fun w y => D w y ^ 2 * R w y ^ 3)
    (h₁ := fun w y => 2 * D w y * D₁ w y * R w y ^ 3 -
      3 * D w y ^ 2 * b w y * R w y ^ 4)
    (h₂ := fun w y => 2 * D₁ w y ^ 2 * R w y ^ 3 +
      2 * D w y * D₂ w y * R w y ^ 3 -
      12 * D w y * D₁ w y * b w y * R w y ^ 4 -
      3 * D w y ^ 2 * c w y * R w y ^ 4 +
      12 * D w y ^ 2 * b w y ^ 2 * R w y ^ 5)
    (hv' := fun w y => D w y * (f w y * e w y + c w y ^ 2 - 2 * b w y * d w y) *
      R w y ^ 3 - 3 / 2 * D w y ^ 2 * c w y * R w y ^ 4)
    (fun w _ y => ?_) (fun w _ y => ?_)
    (by uexp_tac) (by uexp_tac) (by uexp_tac) (by uexp_tac)
    (fun y w hw => ?_) (Continuous.continuousOn (by dsimp [e, b, c, d, f, R]; fun_prop))
    (Continuous.continuousOn (by dsimp [b, c, R]; fun_prop))).congr_deriv ?_
  · convert! ((dD w y).pow 2).mul ((dR w y).pow 3) using 1
    pi_norm; ring
  · convert! ((((dD w y).const_mul 2).mul (dD₁ w y)).mul ((dR w y).pow 3)).sub
      (((((dD w y).pow 2).const_mul 3).mul (d1 w y)).mul ((dR w y).pow 4)) using 1
    pi_norm; ring
  · have tD := ((t2 w hw y).mul (t0 w hw y)).sub ((t1 w hw y).pow 2)
    have tR := (t0 w hw y).inv (hp w y)
    convert! (tD.pow 2).mul (tR.pow 3) using 1
    dsimp [D, R]
    field_simp
    ring
  · apply heat_congr
    intro y
    dsimp [D, D₁, D₂, R, e, b, c, d, f]
    have hn := (hfam_pos hg hlow v y).ne'
    field_simp
    ring

/-- At zero mass the curvature moment dissipates by the third derivative squared. -/
theorem backward_curvatureSq_linear {f : ℕ → ℝ → ℝ} (hf : Jet f)
    {a x v : ℝ} (hv : v ∈ Icc 0 a) :
    HasDerivWithinAt (fun w => heat (a - w) (fun y => hfam f 2 w y ^ 2) x)
      (heat (a - v) (fun y => -hfam f 3 v y ^ 2) x) (Icc 0 a) v := by
  have d2 := hfam_deriv hf (j := 2) (by norm_num)
  have d3 := hfam_deriv hf (j := 3) (by norm_num)
  have t2 : ∀ w ∈ Icc 0 a, ∀ y,
      HasDerivWithinAt (fun u => hfam f 2 u y) (hfam f 4 w y / 2) (Icc 0 a) w :=
    fun w hw y => hfam_time_two hf (j := 2) (by norm_num) hw y
  have U2 := hfam_uexp hf (j := 2) (by norm_num) a
  have U3 := hfam_uexp hf (j := 3) (by norm_num) a
  have U4 := hfam_uexp hf (j := 4) (by norm_num) a
  have C2 := hfam_cont hf (j := 2) (by norm_num)
  have C3 := hfam_cont hf (j := 3) (by norm_num)
  have C4 := hfam_cont hf (j := 4) (by norm_num)
  refine (hasDerivWithinAt_heat_backward_two hv
    (h := fun w y => hfam f 2 w y ^ 2)
    (h₁ := fun w y => 2 * hfam f 2 w y * hfam f 3 w y)
    (h₂ := fun w y => 2 * hfam f 3 w y ^ 2 + 2 * hfam f 2 w y * hfam f 4 w y)
    (hv' := fun w y => hfam f 2 w y * hfam f 4 w y)
    (fun w _ y => ?_) (fun w _ y => ?_)
    (by uexp_tac) (by uexp_tac) (by uexp_tac) (by uexp_tac)
    (fun y w hw => ?_) (Continuous.continuousOn (by fun_prop))
    (Continuous.continuousOn (by fun_prop))).congr_deriv ?_
  · convert! (d2 w y).pow 2 using 1; ring
  · convert! ((d2 w y).const_mul 2).mul (d3 w y) using 1; ring
  · convert! (t2 w hw y).pow 2 using 1; ring
  · exact heat_congr (fun y => by ring) x

/-- The third spatial derivative of the logarithmic heat representation. -/
theorem deriv_curvature_hfam {g : ℕ → ℝ → ℝ} (hg : Jet g) (hlow : PosLow (g 0))
    (m v : ℝ) :
    deriv (fun y => (hfam g 2 v y * hfam g 0 v y - hfam g 1 v y * hfam g 1 v y) /
      hfam g 0 v y ^ 2 / m) = fun y =>
      (hfam g 3 v y * hfam g 0 v y ^ 2 -
        3 * hfam g 1 v y * hfam g 2 v y * hfam g 0 v y +
        2 * hfam g 1 v y ^ 3) / hfam g 0 v y ^ 3 / m := by
  funext y
  have d0 := hfam_deriv hg (j := 0) (by norm_num) v y
  have d1 := hfam_deriv hg (j := 1) (by norm_num) v y
  have d2 := hfam_deriv hg (j := 2) (by norm_num) v y
  have hn := (hfam_pos hg hlow v y).ne'
  have hd := ((((d2.mul d0).sub (d1.mul d1)).div (d0.pow 2) (pow_ne_zero 2 hn)).div_const m)
  apply HasDerivAt.deriv
  convert! hd using 1
  pi_norm
  field_simp
  ring

end SpinGlass.Aristotle.Heat

namespace SpinGlass.Aristotle

/-- The dissipation of the second split spatial moment under its actual tilt. -/
noncomputable def splitCurvatureDissipation (m a : ℝ) (A : ℝ → ℝ) (x v : ℝ) : ℝ :=
  tiltedMean (gaussianReal 0 (a - v).toNNReal)
    (fun z => gaussianLayer m v A (x + z))
    (fun z => 2 * m * iteratedDeriv 2 (gaussianLayer m v A) (x + z) ^ 3 -
      iteratedDeriv 3 (gaussianLayer m v A) (x + z) ^ 2) m

/-- C4 terminal regularity suffices for the squared-curvature variance derivative.
The calculation includes zero mass and both ends of the split interval. -/
theorem hasDerivWithinAt_splitSpatialMoment_two {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hbound : ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C)
    {m a v : ℝ} (hv : v ∈ Icc 0 a) (x : ℝ) :
    HasDerivWithinAt (splitSpatialMoment 2 m a A x)
      (splitCurvatureDissipation m a A x v) (Icc 0 a) v := by
  obtain ⟨C, hC⟩ := hbound
  have hJ := Heat.jet_iteratedDeriv hA hC
  obtain ⟨hC0, hlin⟩ := Heat.linear_bound_of_iteratedDeriv hA hC
  rcases eq_or_ne m 0 with rfl | hm0
  · have key := Heat.backward_curvatureSq_linear hJ (x := x) hv
    refine (key.congr_of_mem (fun w _ => splitSpatialMoment_zero_mass_eq hJ (Or.inr rfl) x w)
      hv).congr_deriv ?_
    have hder : iteratedDeriv 3 (gaussianLayer 0 v A) =
        Heat.hfam (fun j => iteratedDeriv j A) 3 v := by
      rw [gaussianLayer_zero_mass, ← hfam_iteratedDeriv_zero]
      simp only [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
        show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_zero,
        deriv_hfam hJ (j := 0) (by norm_num),
        deriv_hfam hJ (j := 1) (by norm_num),
        deriv_hfam hJ (j := 2) (by norm_num)]
    simp only [splitCurvatureDissipation, tiltedMean, hder, mul_zero, zero_mul,
      zero_sub, Real.exp_zero, mul_one, integral_const, probReal_univ, smul_eq_mul, div_one]
    rfl
  · have hlin' : ∀ y, |(fun j => iteratedDeriv j A) 0 y| ≤ |A 0| + C * |y| := by
      simpa using hlin
    have hg := hJ.exp hlin' m
    have hlow : Heat.PosLow (Heat.expJet m (fun j => iteratedDeriv j A) 0) :=
      Heat.posLow_exp_of_linear hC0 hlin' m
    let g := Heat.expJet m (fun j => iteratedDeriv j A)
    have hlay : ∀ w, gaussianLayer m w A = fun y => Real.log (Heat.hfam g 0 w y) / m := by
      intro w
      rw [gaussianLayer_eq_log hm0, hfam_expJet_zero]
    have hder₂ : iteratedDeriv 2 (gaussianLayer m v A) = fun y =>
        (Heat.hfam g 2 v y * Heat.hfam g 0 v y - Heat.hfam g 1 v y * Heat.hfam g 1 v y) /
          Heat.hfam g 0 v y ^ 2 / m := by
      rw [hlay v, iteratedDeriv_succ, iteratedDeriv_one,
        deriv_log_hfam hg hlow, deriv_ratio_hfam hg hlow]
    have hder₃ : iteratedDeriv 3 (gaussianLayer m v A) = fun y =>
        (Heat.hfam g 3 v y * Heat.hfam g 0 v y ^ 2 -
          3 * Heat.hfam g 1 v y * Heat.hfam g 2 v y * Heat.hfam g 0 v y +
          2 * Heat.hfam g 1 v y ^ 3) / Heat.hfam g 0 v y ^ 3 / m := by
      rw [iteratedDeriv_succ, hder₂, Heat.deriv_curvature_hfam hg hlow]
    have hE : ∀ y, Real.exp (m * gaussianLayer m v A y) = Heat.hfam g 0 v y := by
      intro y
      rw [hlay v]
      have hn := (Heat.hfam_pos hg hlow v y).ne'
      rw [show m * (Real.log (Heat.hfam g 0 v y) / m) =
        Real.log (Heat.hfam g 0 v y) by field_simp, Real.exp_log (Heat.hfam_pos hg hlow v y)]
    have key := ((Heat.backward_curvatureSq hg hlow (x := x) hv).const_mul (1 / m ^ 2)).div_const
      (Heat.heat a (g 0) x)
    refine (key.congr_of_mem (fun w hw => splitSpatialMoment_two_eq hm0 hg hlow hlay hw x)
      hv).congr_deriv ?_
    unfold splitCurvatureDissipation tiltedMean
    have hden : (∫ z, Real.exp (m * gaussianLayer m v A (x + z))
        ∂gaussianReal 0 (a - v).toNNReal) = Heat.heat a (g 0) x := by
      change Heat.heat (a - v) (fun y => Real.exp (m * gaussianLayer m v A y)) x = _
      rw [Heat.heat_congr hE, heat_hfam_zero hg hv]
    rw [hden, hder₂, hder₃]
    rw [← Heat.heat_const_mul]
    congr 1
    apply integral_congr_ae
    refine .of_forall fun z => ?_
    dsimp only
    rw [hE]
    dsimp only [g]
    have hn := (Heat.hfam_pos hg hlow v (x + z)).ne'
    field_simp

end SpinGlass.Aristotle

namespace SpinGlass

/-- The actual tilted dissipation integrand of the squared-curvature moment. -/
noncomputable def coleHopfSplitCurvatureDissipation (m a : ℝ)
    (A : ℝ → ℝ) (x v : ℝ) : ℝ :=
  ∫ z, (2 * m * iteratedDeriv 2 (coleHopf m v.toNNReal A) (x + z) ^ 3 -
    iteratedDeriv 3 (coleHopf m v.toNNReal A) (x + z) ^ 2) *
      coleHopfQ m (a - v).toNNReal (coleHopf m v.toNNReal A) x z
    ∂gaussianReal 0 (a - v).toNNReal

theorem coleHopfSplitCurvatureDissipation_eq {A : ℝ → ℝ} (hAm : Measurable A)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|) (m a x v : ℝ) :
    coleHopfSplitCurvatureDissipation m a A x v =
      Aristotle.splitCurvatureDissipation m a A x v := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by simpa only [one_mul] using hLip
  have hBL := abs_coleHopf_sub_le_of_lipschitz m hAm hL v.toNNReal
  have hBc := (lipschitzWith_toNNReal_of_abs_sub_le hBL).continuous
  have hBg := HasLinearGrowth.of_lipschitz hBL
  rw [coleHopfSplitCurvatureDissipation, Aristotle.splitCurvatureDissipation,
    ← coleHopf_toNNReal_eq_gaussianLayer]
  exact (tiltedMean_eq_integral_coleHopfQ hBg hBc.measurable
    (fun y => 2 * m * iteratedDeriv 2 (coleHopf m v.toNNReal A) y ^ 3 -
      iteratedDeriv 3 (coleHopf m v.toNNReal A) y ^ 2) m (a - v).toNNReal x).symm

/-- The actual squared-curvature moment has the dissipation derivative,
including zero mass and both variance endpoints. -/
theorem hasDerivWithinAt_coleHopfSplitSpatialMoment_two {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|)
    {m a v : ℝ} (hv : v ∈ Icc 0 a) (x : ℝ) :
    HasDerivWithinAt (coleHopfSplitSpatialMoment 2 m a A x)
      (coleHopfSplitCurvatureDissipation m a A x v) (Icc 0 a) v := by
  rw [coleHopfSplitSpatialMoment_eq hA.continuous.measurable hLip,
    coleHopfSplitCurvatureDissipation_eq hA.continuous.measurable hLip]
  exact Aristotle.hasDerivWithinAt_splitSpatialMoment_two hA hb hv x

/-- Conditional local envelope from sharp curvature and a proved third derivative bound.
The concrete Parisi split specializations use the uniform coefficient twelve. -/
theorem abs_coleHopfSplitCurvatureDissipation_le {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C)
    (hsharp : ∀ y, 0 ≤ deriv (deriv A) y ∧ deriv (deriv A) y + deriv A y ^ 2 ≤ 1)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    {C₃ v : ℝ} (hthird : ∀ y, |iteratedDeriv 3 (coleHopf m v.toNNReal A) y| ≤ C₃)
    (a x : ℝ) : |coleHopfSplitCurvatureDissipation m a A x v| ≤ 2 + C₃ ^ 2 := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by simpa only [one_mul] using hLip
  have hBL := abs_coleHopf_sub_le_of_lipschitz m hA.continuous.measurable hL v.toNNReal
  have hBc := (lipschitzWith_toNNReal_of_abs_sub_le hBL).continuous
  have hB4 := contDiff_four_coleHopf hA hb m v.toNNReal
  apply abs_integral_mul_coleHopfQ_le' (HasLinearGrowth.of_lipschitz hBL) hBc.measurable m
    (((hB4.continuous_iteratedDeriv 2 (by norm_num)).pow 3).const_mul (2 * m) |>.sub
      ((hB4.continuous_iteratedDeriv 3 (by norm_num)).pow 2)).measurable
  intro y
  have hs := coleHopf_sharp_spatial_bounds (hA.of_le (by norm_num)) hsharp hm v.toNNReal y
  have hcurv : iteratedDeriv 2 (coleHopf m v.toNNReal A) y ∈ Icc (0 : ℝ) 1 := by
    simp only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero]
    exact ⟨hs.1, by nlinarith [sq_nonneg (deriv (coleHopf m v.toNNReal A) y)]⟩
  have hcub : iteratedDeriv 2 (coleHopf m v.toNNReal A) y ^ 3 ≤ 1 := by
    simpa using pow_le_pow_left₀ hcurv.1 hcurv.2 3
  have hmcurv : m * iteratedDeriv 2 (coleHopf m v.toNNReal A) y ^ 3 ≤ 1 := by
    simpa using mul_le_mul hm.2 hcub (pow_nonneg hcurv.1 3) zero_le_one
  have hsq := pow_le_pow_left₀ (abs_nonneg _) (hthird y) 2
  rw [sq_abs] at hsq
  simp only [Pi.sub_apply, Pi.pow_apply]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hm.1) (pow_nonneg hcurv.1 3)),
    abs_of_nonneg (sq_nonneg _)]
  nlinarith

/-- A uniform third derivative bound gives a uniform split-variance Lipschitz bound.
This conditional lemma is instantiated with the actual recursion below. -/
theorem abs_coleHopfSplitSpatialMoment_two_sub_le {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C)
    (hsharp : ∀ y, 0 ≤ deriv (deriv A) y ∧ deriv (deriv A) y + deriv A y ^ 2 ≤ 1)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    {C₃ a v w : ℝ}
    (hthird : ∀ u ∈ Icc 0 a, ∀ y, |iteratedDeriv 3 (coleHopf m u.toNNReal A) y| ≤ C₃)
    (hv : v ∈ Icc 0 a) (hw : w ∈ Icc 0 a) (x : ℝ) :
    |coleHopfSplitSpatialMoment 2 m a A x v - coleHopfSplitSpatialMoment 2 m a A x w| ≤
      (2 + C₃ ^ 2) * |v - w| := by
  have hd : ∀ u ∈ Icc 0 a, HasDerivWithinAt (coleHopfSplitSpatialMoment 2 m a A x)
      (coleHopfSplitCurvatureDissipation m a A x u) (Icc 0 a) u :=
    fun u hu => hasDerivWithinAt_coleHopfSplitSpatialMoment_two hA ⟨C, hb⟩ hLip hu x
  have hbound := fun u (hu : u ∈ Icc 0 a) => abs_coleHopfSplitCurvatureDissipation_le
    hA hb hsharp hLip hm (hthird u hu) a x
  simpa only [Real.norm_eq_abs] using (convex_Icc 0 a).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := coleHopfSplitSpatialMoment 2 m a A x) (C := 2 + C₃ ^ 2)
    hd (fun u hu => by rw [Real.norm_eq_abs]; exact hbound u hu) hw hv

/-- The actual suffix moment has a level-independent variance Lipschitz constant. -/
theorem abs_parisiQSuffix_splitSpatialMoment_two_sub_le (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1))
    (hm : ParisiMAdmissible ms) {m : ℝ} (hm0 : 0 ≤ m)
    (hmr : m ≤ mExt ms (r.val + 2)) {a v w : ℝ}
    (hv : v ∈ Icc 0 a) (hw : w ∈ Icc 0 a) (x : ℝ) :
    |coleHopfSplitSpatialMoment 2 m a (parisiQSuffix ξ h ms qs r) x v -
      coleHopfSplitSpatialMoment 2 m a (parisiQSuffix ξ h ms qs r) x w| ≤ 146 * |v - w| := by
  obtain ⟨hA, C, hC⟩ := parisiQSuffix_spatial_regular_four ξ h ms qs r
  have hm1 := hmr.trans (mExt_le_one (fun s => (hm.2.2 s).le) _)
  simpa only [show (2 : ℝ) + 12 ^ 2 = 146 by norm_num] using
    abs_coleHopfSplitSpatialMoment_two_sub_le hA hC
      (parisiQSuffix_sharp_spatial_bounds ξ h qs r hm)
      (abs_parisiQSuffix_sub_le ξ h ms qs r) ⟨hm0, hm1⟩
      (fun u _ y => coleHopf_parisiQSuffix_third_spatial_bound ξ h qs r hm hm0 hmr u.toNNReal y)
      hv hw x

/-- The root suffix estimate includes the matching mass zero. -/
theorem abs_parisiRootSuffix_splitSpatialMoment_two_sub_le (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 ≤ m) (hmr : m ≤ mExt ms 1) {a v w : ℝ}
    (hv : v ∈ Icc 0 a) (hw : w ∈ Icc 0 a) (x : ℝ) :
    |coleHopfSplitSpatialMoment 2 m a (parisiRootSuffix ξ ms qs) x v -
      coleHopfSplitSpatialMoment 2 m a (parisiRootSuffix ξ ms qs) x w| ≤ 146 * |v - w| := by
  obtain ⟨hA, C, hC⟩ := parisiRootSuffix_spatial_regular_four ξ ms qs
  have hm1 := hmr.trans (mExt_le_one (fun s => (hm.2.2 s).le) _)
  simpa only [show (2 : ℝ) + 12 ^ 2 = 146 by norm_num] using
    abs_coleHopfSplitSpatialMoment_two_sub_le hA hC
      (parisiRootSuffix_sharp_spatial_bounds ξ qs hm)
      (abs_parisiRootSuffix_sub_le ξ ms qs) ⟨hm0, hm1⟩
      (fun u _ y => coleHopf_parisiRootSuffix_third_spatial_bound ξ qs hm hm0 hmr u.toNNReal y)
      hv hw x

private theorem abs_integral_sub_le_of_unit_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F G : Ω → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hbF : ∀ ω, |F ω| ≤ 1) (hbG : ∀ ω, |G ω| ≤ 1)
    {D : ℝ} (hD : ∀ ω, |F ω - G ω| ≤ D) :
    |(∫ ω, F ω ∂μ) - ∫ ω, G ω ∂μ| ≤ D := by
  have hiF := Integrable.of_bound (μ := μ) hF.aestronglyMeasurable 1
    (.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbF ω)
  have hiG := Integrable.of_bound (μ := μ) hG.aestronglyMeasurable 1
    (.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbG ω)
  rw [← integral_sub hiF hiG]
  have hh := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => F ω - G ω)
    (.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hD ω)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hh

/-- Fixed baseline prefix averaging preserves the variance Lipschitz coefficient. -/
theorem abs_coleHopfIterateSplitSpatialMoment_two_sub_le {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) (hpos : ∀ p, 0 < ms p) (hle : ∀ p, ms p ≤ 1)
    {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ i ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv i A x| ≤ C)
    (hsharp : ∀ y, 0 ≤ deriv (deriv A) y ∧ deriv (deriv A) y + deriv A y ^ 2 ≤ 1)
    (hLip : ∀ x y, |A y - A x| ≤ |y - x|) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    {a v w D : ℝ} (hD : ∀ y, |coleHopfSplitSpatialMoment 2 m a A y v -
      coleHopfSplitSpatialMoment 2 m a A y w| ≤ D) (x : ℝ) :
    |coleHopfIterateSplitSpatialMoment 2 ms vs m a A x v -
      coleHopfIterateSplitSpatialMoment 2 ms vs m a A x w| ≤ D := by
  have hL : ∀ y z, |A z - A y| ≤ 1 * |z - y| := by simpa only [one_mul] using hLip
  have hBL := abs_coleHopf_sub_le_of_lipschitz m hA.continuous.measurable hL a.toNNReal
  have := isProbabilityMeasure_cascadeTiltMeasure_comp_add_sum ms vs hpos hle
    (lipschitzWith_toNNReal_of_abs_sub_le hBL).continuous.measurable hBL x
  have hpoint : Measurable (fun zs : Fin j → ℝ => x + ∑ p, zs p) :=
    measurable_const.add (Finset.measurable_sum _ fun p _ => measurable_pi_apply p)
  have hmeas := fun u => (continuous_coleHopfSplitSpatialMoment hA ⟨C, hb⟩ hLip
    (j := 2) (by norm_num) m a u).measurable.comp hpoint
  have hunit : ∀ u y, |coleHopfSplitSpatialMoment 2 m a A y u| ≤ 1 := by
    intro u y
    have hh := coleHopfSplitSpatialMoment_mem_Icc_of_sharp hA hb hsharp hLip hm
      (i := 2) (by norm_num) a u y
    exact abs_le.2 ⟨by linarith [hh.1], hh.2⟩
  exact abs_integral_sub_le_of_unit_bound (hmeas v) (hmeas w)
    (fun zs => hunit v _) (fun zs => hunit w _) (fun zs => hD _)

/-- The actual root curvature moment is uniformly Lipschitz after field averaging.
Only a probability field law is required; its moments do not enter the coefficient. -/
theorem abs_parisiRootUSpatialMoment_two_sub_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) {v w : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0))
    (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qs 0) - deriv ξ 0)) :
    |parisiRootUSpatialMoment 2 μh ξ ms qs v - parisiRootUSpatialMoment 2 μh ξ ms qs w| ≤
      146 * |v - w| := by
  obtain ⟨hA, C, hC⟩ := parisiRootSuffix_spatial_regular_four ξ ms qs
  have hmeas := fun u => (continuous_coleHopfSplitSpatialMoment hA ⟨C, hC⟩
    (abs_parisiRootSuffix_sub_le ξ ms qs) (j := 2) (by norm_num) 0
    (deriv ξ (qs 0) - deriv ξ 0) u).measurable
  have hunit : ∀ u y, |coleHopfSplitSpatialMoment 2 0 (deriv ξ (qs 0) - deriv ξ 0)
      (parisiRootSuffix ξ ms qs) y u| ≤ 1 := by
    intro u y
    have hh := coleHopfSplitSpatialMoment_mem_Icc_of_sharp hA hC
      (parisiRootSuffix_sharp_spatial_bounds ξ qs hm) (abs_parisiRootSuffix_sub_le ξ ms qs)
      (m := 0) ⟨le_rfl, zero_le_one⟩ (i := 2) (by norm_num)
      (deriv ξ (qs 0) - deriv ξ 0) u y
    exact abs_le.2 ⟨by linarith [hh.1], hh.2⟩
  exact abs_integral_sub_le_of_unit_bound (hmeas v) (hmeas w)
    (hunit v) (hunit w) (fun h => abs_parisiRootSuffix_splitSpatialMoment_two_sub_le
      ξ ms qs hm le_rfl (mExt_nonneg (fun p => (hm.2.1 p).le) _) hv hw h)

/-- The actual nonroot curvature moment is uniformly Lipschitz after the fixed
prefix and independent field/root averages, including both split endpoints. -/
theorem abs_parisiRightUSpatialMoment_two_sub_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {v w : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)))
    (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) :
    |parisiRightUSpatialMoment 2 μh ξ ms qs p v - parisiRightUSpatialMoment 2 μh ξ ms qs p w| ≤
      146 * |v - w| := by
  obtain ⟨hA, C, hC⟩ := parisiQSuffix_spatial_regular_four ξ 0 ms qs p.castSucc
  have hpos : ∀ r, 0 < parisiMassPrefixMasses ms p r := fun r => hm.2.1 _
  have hle : ∀ r, parisiMassPrefixMasses ms p r ≤ 1 := fun r =>
    (hm.2.2 _).le
  have ha : 0 < deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc) := sub_pos.2
    (hξ.strictMonoOn_deriv (hq.mem_Icc p.castSucc) (hq.mem_Icc p.succ)
      (hq.1 (by change p.val < p.val + 1; omega)))
  have hmeas := fun u (hu : u ∈ Icc (0 : ℝ) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))) =>
    (measurable_coleHopfIterateSplitSpatialMoment_two_of_pos
      (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p) hpos hle hA ⟨C, hC⟩
      (abs_parisiQSuffix_sub_le ξ 0 ms qs p.castSucc) (hm.2.1 p) (hm.2.2 p).le ha hu).comp
      (measurable_fst.add measurable_snd)
  have hunit : ∀ u x, |coleHopfIterateSplitSpatialMoment 2
      (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p) (ms p)
      (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc))
      (parisiQSuffix ξ 0 ms qs p.castSucc) x u| ≤ 1 := by
    intro u x
    have hh := coleHopfIterateSplitSpatialMoment_mem_Icc_of_sharp
      (parisiMassPrefixMasses ms p) (parisiMassPrefixVars ξ qs p) hpos hle hA hC
      (parisiQSuffix_sharp_spatial_bounds ξ 0 qs p.castSucc hm)
      (abs_parisiQSuffix_sub_le ξ 0 ms qs p.castSucc) ⟨(hm.2.1 p).le, (hm.2.2 p).le⟩
      (i := 2) (by norm_num) (deriv ξ (qs p.succ) - deriv ξ (qs p.castSucc)) u x
    exact abs_le.2 ⟨by linarith [hh.1], hh.2⟩
  apply abs_integral_sub_le_of_unit_bound (hmeas v hv) (hmeas w hw)
    (fun hz => hunit v (hz.1 + hz.2)) (fun hz => hunit w (hz.1 + hz.2))
  intro hz
  apply abs_coleHopfIterateSplitSpatialMoment_two_sub_le _ _ hpos hle hA hC
    (parisiQSuffix_sharp_spatial_bounds ξ 0 qs p.castSucc hm)
    (abs_parisiQSuffix_sub_le ξ 0 ms qs p.castSucc) ⟨(hm.2.1 p).le, (hm.2.2 p).le⟩
  intro y
  apply abs_parisiQSuffix_splitSpatialMoment_two_sub_le ξ 0 ms qs p.castSucc hm (hm.2.1 p).le
    _ hv hw y
  have he := mExt_val_succ ms p
  exact he.symm.trans_le (hm.monotone_mExt (by simp only [Fin.val_castSucc]; omega))

/-- Reversing the matched inner variance preserves the coefficient 146
for the actual outer second moment. Terminal mass one and both admissible
variance endpoints are retained. -/
theorem abs_parisiLeftUSpatialMoment_two_sub_le
    {μh : Measure ℝ} [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (hgap : qs p < qExt qs (p.val + 2)) {v w : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p)))
    (hw : w ∈ Icc (0 : ℝ) (deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p))) :
    |parisiLeftUSpatialMoment 2 μh ξ ms qs p v - parisiLeftUSpatialMoment 2 μh ξ ms qs p w| ≤
      146 * |v - w| := by
  let a := deriv ξ (qExt qs (p.val + 2)) - deriv ξ (qs p)
  let m := mExt ms (p.val + 1)
  have hpos : ∀ r, 0 < parisiOuterMassPrefixMasses ms p r := fun r => hm.mExt_pos (by omega)
  have hle : ∀ r, parisiOuterMassPrefixMasses ms p r ≤ 1 := fun r =>
    mExt_le_one (fun s => (hm.2.2 s).le) _
  have hmpos : 0 < m := hm.mExt_pos (by omega)
  have hm1 : m ≤ 1 := mExt_le_one (fun s => (hm.2.2 s).le) _
  have hmr : m ≤ mExt ms (p.val + 2) := hm.monotone_mExt (by omega)
  have ha : 0 < a := sub_pos.2 (hξ.strictMonoOn_deriv (hq.mem_Icc p)
    (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 _) hgap)
  have hav : a - v ∈ Icc (0 : ℝ) a := ⟨sub_nonneg.2 hv.2, sub_le_self _ hv.1⟩
  have haw : a - w ∈ Icc (0 : ℝ) a := ⟨sub_nonneg.2 hw.2, sub_le_self _ hw.1⟩
  obtain ⟨hA, C, hC⟩ := parisiQSuffix_spatial_regular_four ξ 0 ms qs p
  have hLip := abs_parisiQSuffix_sub_le ξ 0 ms qs p
  have hsharp := parisiQSuffix_sharp_spatial_bounds ξ 0 qs p hm
  have hmeas := fun u (hu : u ∈ Icc (0 : ℝ) a) =>
    (measurable_coleHopfIterateSplitSpatialMoment_two_of_pos
      (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
      hpos hle hA ⟨C, hC⟩ hLip hmpos hm1 ha hu).comp
      (measurable_fst.add measurable_snd)
  have hunit : ∀ u x, |coleHopfIterateSplitSpatialMoment 2
      (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p) m a
      (parisiQSuffix ξ 0 ms qs p) x u| ≤ 1 := by
    intro u x
    have hh := coleHopfIterateSplitSpatialMoment_mem_Icc_of_sharp
      (parisiOuterMassPrefixMasses ms p) (parisiOuterMassPrefixVars ξ qs p)
      hpos hle hA hC hsharp hLip ⟨hmpos.le, hm1⟩ (i := 2) (by decide) a u x
    exact abs_le.2 ⟨by linarith [hh.1], hh.2⟩
  unfold parisiLeftUSpatialMoment coleHopfIterateOuterSplitSpatialMoment
  apply abs_integral_sub_le_of_unit_bound (hmeas (a - v) hav) (hmeas (a - w) haw)
    (fun hz => hunit (a - v) (hz.1 + hz.2)) (fun hz => hunit (a - w) (hz.1 + hz.2))
  intro hz
  apply abs_coleHopfIterateSplitSpatialMoment_two_sub_le _ _ hpos hle hA hC hsharp hLip
    ⟨hmpos.le, hm1⟩
  intro y
  have hh := abs_parisiQSuffix_splitSpatialMoment_two_sub_le ξ 0 ms qs p hm
    hmpos.le hmr hav haw y
  simpa only [show a - v - (a - w) = -(v - w) by ring, abs_neg] using hh

end SpinGlass
