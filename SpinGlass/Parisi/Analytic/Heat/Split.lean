import SpinGlass.Parisi.Analytic.Heat.Jet

/-!
# Heat Split analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle.Heat`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

namespace Heat

section Fam

variable {g : ℕ → ℝ → ℝ}

/-- Backward derivative of the squared-gradient integrand `e₁² / e`. -/
theorem backward_gradSq (hg : Jet g) (hlow : PosLow (g 0)) {a x v : ℝ} (hv : v ∈ Icc 0 a) :
    HasDerivWithinAt (fun w => heat (a - w) (fun y => hfam g 1 w y ^ 2 * (hfam g 0 w y)⁻¹) x)
      (heat (a - v) (fun y => -((hfam g 2 v y * hfam g 0 v y - hfam g 1 v y ^ 2) ^ 2 *
        (hfam g 0 v y)⁻¹ ^ 3)) x) (Icc 0 a) v := by
  have d0 : ∀ w y, HasDerivAt (hfam g 0 w) (hfam g 1 w y) y := fun w y =>
    hfam_deriv hg (by norm_num) w y
  have d1 : ∀ w y, HasDerivAt (hfam g 1 w) (hfam g 2 w y) y := fun w y =>
    hfam_deriv hg (by norm_num) w y
  have d2 : ∀ w y, HasDerivAt (hfam g 2 w) (hfam g 3 w y) y := fun w y =>
    hfam_deriv hg (by norm_num) w y
  have d3 : ∀ w y, HasDerivAt (hfam g 3 w) (hfam g 4 w y) y := fun w y =>
    hfam_deriv hg (by norm_num) w y
  have dE := hfam_inv_deriv hg hlow
  have hp := hfam_pos hg hlow
  have U0 := hfam_uexp hg (j := 0) (by norm_num) a
  have U1 := hfam_uexp hg (j := 1) (by norm_num) a
  have U2 := hfam_uexp hg (j := 2) (by norm_num) a
  have U3 := hfam_uexp hg (j := 3) (by norm_num) a
  have U4 := hfam_uexp hg (j := 4) (by norm_num) a
  have UE := hfam_inv_uexp hg hlow a
  have C0 := hfam_cont hg (j := 0) (by norm_num)
  have C1 := hfam_cont hg (j := 1) (by norm_num)
  have C2 := hfam_cont hg (j := 2) (by norm_num)
  have C3 := hfam_cont hg (j := 3) (by norm_num)
  have CE := hfam_inv_cont hg hlow
  have t0 : ∀ w ∈ Icc 0 a, ∀ y, HasDerivWithinAt (fun u => hfam g 0 u y)
      (hfam g 2 w y / 2) (Icc 0 a) w := fun w hw y => hfam_time hg (j := 0) (by norm_num) hw y
  have t1 : ∀ w ∈ Icc 0 a, ∀ y, HasDerivWithinAt (fun u => hfam g 1 u y)
      (hfam g 3 w y / 2) (Icc 0 a) w := fun w hw y => hfam_time hg (j := 1) (by norm_num) hw y
  have h2c : Continuous (fun p : ℝ × ℝ =>
      2 * hfam g 2 p.1 p.2 ^ 2 * (hfam g 0 p.1 p.2)⁻¹ +
      2 * hfam g 1 p.1 p.2 * hfam g 3 p.1 p.2 * (hfam g 0 p.1 p.2)⁻¹ -
      5 * hfam g 1 p.1 p.2 ^ 2 * hfam g 2 p.1 p.2 * (hfam g 0 p.1 p.2)⁻¹ ^ 2 +
      2 * hfam g 1 p.1 p.2 ^ 4 * (hfam g 0 p.1 p.2)⁻¹ ^ 3) := by fun_prop
  refine (hasDerivWithinAt_heat_backward hv
    (h := fun w y => hfam g 1 w y ^ 2 * (hfam g 0 w y)⁻¹)
    (h₁ := fun w y => 2 * hfam g 1 w y * hfam g 2 w y * (hfam g 0 w y)⁻¹ -
      hfam g 1 w y ^ 3 * (hfam g 0 w y)⁻¹ ^ 2)
    (h₂ := fun w y => 2 * hfam g 2 w y ^ 2 * (hfam g 0 w y)⁻¹ +
      2 * hfam g 1 w y * hfam g 3 w y * (hfam g 0 w y)⁻¹ -
      5 * hfam g 1 w y ^ 2 * hfam g 2 w y * (hfam g 0 w y)⁻¹ ^ 2 +
      2 * hfam g 1 w y ^ 4 * (hfam g 0 w y)⁻¹ ^ 3)
    (h₃ := fun w y => 6 * hfam g 2 w y * hfam g 3 w y * (hfam g 0 w y)⁻¹ +
      2 * hfam g 1 w y * hfam g 4 w y * (hfam g 0 w y)⁻¹ -
      12 * hfam g 1 w y * hfam g 2 w y ^ 2 * (hfam g 0 w y)⁻¹ ^ 2 -
      7 * hfam g 1 w y ^ 2 * hfam g 3 w y * (hfam g 0 w y)⁻¹ ^ 2 +
      18 * hfam g 1 w y ^ 3 * hfam g 2 w y * (hfam g 0 w y)⁻¹ ^ 3 -
      6 * hfam g 1 w y ^ 5 * (hfam g 0 w y)⁻¹ ^ 4)
    (hv' := fun w y => hfam g 1 w y * hfam g 3 w y * (hfam g 0 w y)⁻¹ -
      hfam g 1 w y ^ 2 * hfam g 2 w y * (hfam g 0 w y)⁻¹ ^ 2 / 2)
    (fun w _ y => ?_) (fun w _ y => ?_) (fun w _ y => ?_) (by uexp_tac) (by uexp_tac)
    (by uexp_tac) (by uexp_tac) (fun y w hw => ?_) (Continuous.continuousOn (by fun_prop))
    (fun y => (h2c.comp (Continuous.prodMk_left y)).continuousWithinAt)).congr_deriv ?_
  · convert! ((d1 w y).pow 2).mul (dE w y) using 1; pi_norm; ring
  · convert! ((((d1 w y).const_mul 2).mul (d2 w y)).mul (dE w y)).sub
      (((d1 w y).pow 3).mul ((dE w y).pow 2)) using 1; pi_norm; ring
  · convert! (((((d2 w y).pow 2).const_mul 2).mul (dE w y)).add
      ((((d1 w y).const_mul 2).mul (d3 w y)).mul (dE w y))).sub
      ((((d1 w y).pow 2).const_mul 5).mul (d2 w y) |>.mul ((dE w y).pow 2)) |>.add
      ((((d1 w y).pow 4).const_mul 2).mul ((dE w y).pow 3)) using 1; pi_norm; ring
  · have := ((t1 w hw y).pow 2).mul ((t0 w hw y).inv (hp w y).ne')
    convert! this using 1
    pi_norm
    field_simp
    ring
  · exact heat_congr (fun y => by field_simp; ring) x

theorem abs_log_le_add_inv {x : ℝ} (hx : 0 < x) : |Real.log x| ≤ x + x⁻¹ := by
  have h1 := Real.log_le_sub_one_of_pos hx
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 hx)
  rw [Real.log_inv] at h2
  have := inv_pos.2 hx
  rw [abs_le]; constructor <;> linarith

/-- Backward derivative of the entropy-form integrand `m r - e log e`, where `r` is the
smoothing of an arbitrary jet `G`. -/
theorem backward_entropy {G : ℕ → ℝ → ℝ} (hg : Jet g) (hlow : PosLow (g 0)) (hG : Jet G)
    (m : ℝ) {a x v : ℝ} (hv : v ∈ Icc 0 a) :
    HasDerivWithinAt (fun w => heat (a - w)
        (fun y => m * hfam G 0 w y - hfam g 0 w y * Real.log (hfam g 0 w y)) x)
      (heat (a - v) (fun y => hfam g 1 v y ^ 2 * (hfam g 0 v y)⁻¹ / 2) x) (Icc 0 a) v := by
  have d0 : ∀ w y, HasDerivAt (hfam g 0 w) (hfam g 1 w y) y := fun w y =>
    hfam_deriv hg (by norm_num) w y
  have d1 : ∀ w y, HasDerivAt (hfam g 1 w) (hfam g 2 w y) y := fun w y =>
    hfam_deriv hg (by norm_num) w y
  have d2 : ∀ w y, HasDerivAt (hfam g 2 w) (hfam g 3 w y) y := fun w y =>
    hfam_deriv hg (by norm_num) w y
  have r0 : ∀ w y, HasDerivAt (hfam G 0 w) (hfam G 1 w y) y := fun w y =>
    hfam_deriv hG (by norm_num) w y
  have r1 : ∀ w y, HasDerivAt (hfam G 1 w) (hfam G 2 w y) y := fun w y =>
    hfam_deriv hG (by norm_num) w y
  have r2 : ∀ w y, HasDerivAt (hfam G 2 w) (hfam G 3 w y) y := fun w y =>
    hfam_deriv hG (by norm_num) w y
  have dE := hfam_inv_deriv hg hlow
  have hp := hfam_pos hg hlow
  have dL : ∀ w y, HasDerivAt (fun y => Real.log (hfam g 0 w y))
      (hfam g 1 w y * (hfam g 0 w y)⁻¹) y := fun w y => by
    simpa [div_eq_mul_inv] using (d0 w y).log (hp w y).ne'
  have U0 := hfam_uexp hg (j := 0) (by norm_num) a
  have U1 := hfam_uexp hg (j := 1) (by norm_num) a
  have U2 := hfam_uexp hg (j := 2) (by norm_num) a
  have U3 := hfam_uexp hg (j := 3) (by norm_num) a
  have V0 := hfam_uexp hG (j := 0) (by norm_num) a
  have V2 := hfam_uexp hG (j := 2) (by norm_num) a
  have V3 := hfam_uexp hG (j := 3) (by norm_num) a
  have UE := hfam_inv_uexp hg hlow a
  have UL : UExp (Icc 0 a) (fun w y => Real.log (hfam g 0 w y)) :=
    (U0.add UE).of_le fun w _ y => (abs_log_le_add_inv (hp w y)).trans (le_abs_self _)
  have C0 := hfam_cont hg (j := 0) (by norm_num)
  have C1 := hfam_cont hg (j := 1) (by norm_num)
  have C2 := hfam_cont hg (j := 2) (by norm_num)
  have D2 := hfam_cont hG (j := 2) (by norm_num)
  have CE := hfam_inv_cont hg hlow
  have CL : Continuous (fun p : ℝ × ℝ => Real.log (hfam g 0 p.1 p.2)) :=
    C0.log fun p => (hp p.1 p.2).ne'
  have t0 : ∀ w ∈ Icc 0 a, ∀ y, HasDerivWithinAt (fun u => hfam g 0 u y)
      (hfam g 2 w y / 2) (Icc 0 a) w := fun w hw y => hfam_time hg (j := 0) (by norm_num) hw y
  have s0 : ∀ w ∈ Icc 0 a, ∀ y, HasDerivWithinAt (fun u => hfam G 0 u y)
      (hfam G 2 w y / 2) (Icc 0 a) w := fun w hw y => hfam_time hG (j := 0) (by norm_num) hw y
  have h2c : Continuous (fun p : ℝ × ℝ =>
      m * hfam G 2 p.1 p.2 - hfam g 2 p.1 p.2 * Real.log (hfam g 0 p.1 p.2) -
      hfam g 1 p.1 p.2 ^ 2 * (hfam g 0 p.1 p.2)⁻¹ - hfam g 2 p.1 p.2) := by fun_prop
  refine (hasDerivWithinAt_heat_backward hv
    (h := fun w y => m * hfam G 0 w y - hfam g 0 w y * Real.log (hfam g 0 w y))
    (h₁ := fun w y => m * hfam G 1 w y - hfam g 1 w y * Real.log (hfam g 0 w y) -
      hfam g 1 w y)
    (h₂ := fun w y => m * hfam G 2 w y - hfam g 2 w y * Real.log (hfam g 0 w y) -
      hfam g 1 w y ^ 2 * (hfam g 0 w y)⁻¹ - hfam g 2 w y)
    (h₃ := fun w y => m * hfam G 3 w y - hfam g 3 w y * Real.log (hfam g 0 w y) -
      3 * hfam g 1 w y * hfam g 2 w y * (hfam g 0 w y)⁻¹ +
      hfam g 1 w y ^ 3 * (hfam g 0 w y)⁻¹ ^ 2 - hfam g 3 w y)
    (hv' := fun w y => m * hfam G 2 w y / 2 - hfam g 2 w y / 2 * Real.log (hfam g 0 w y) -
      hfam g 2 w y / 2)
    (fun w _ y => ?_) (fun w _ y => ?_) (fun w _ y => ?_) (by uexp_tac) (by uexp_tac)
    (by uexp_tac) (by uexp_tac) (fun y w hw => ?_) (Continuous.continuousOn (by fun_prop))
    (fun y => (h2c.comp (Continuous.prodMk_left y)).continuousWithinAt)).congr_deriv ?_
  · convert! ((r0 w y).const_mul m).sub ((d0 w y).mul (dL w y)) using 1
    have := (hp w y).ne'
    field_simp; ring
  · convert! (((r1 w y).const_mul m).sub ((d1 w y).mul (dL w y))).sub (d1 w y) using 1
    ring
  · convert! (((((r2 w y).const_mul m).sub ((d2 w y).mul (dL w y))).sub
      (((d1 w y).pow 2).mul (dE w y))).sub (d2 w y)) using 1
    pi_norm; ring
  · have := ((s0 w hw y).const_mul m).sub ((t0 w hw y).mul ((t0 w hw y).log (hp w y).ne'))
    convert! this using 1
    have := (hp w y).ne'
    field_simp
    ring
  · exact heat_congr (fun y => by ring) x

/-- Backward derivative of `u₁²` for the smoothing `u` of an arbitrary jet. -/
theorem backward_gradSq_linear {f : ℕ → ℝ → ℝ} (hf : Jet f) {a x v : ℝ} (hv : v ∈ Icc 0 a) :
    HasDerivWithinAt (fun w => heat (a - w) (fun y => hfam f 1 w y ^ 2) x)
      (heat (a - v) (fun y => -(hfam f 2 v y ^ 2)) x) (Icc 0 a) v := by
  have d1 : ∀ w y, HasDerivAt (hfam f 1 w) (hfam f 2 w y) y := fun w y =>
    hfam_deriv hf (by norm_num) w y
  have d2 : ∀ w y, HasDerivAt (hfam f 2 w) (hfam f 3 w y) y := fun w y =>
    hfam_deriv hf (by norm_num) w y
  have d3 : ∀ w y, HasDerivAt (hfam f 3 w) (hfam f 4 w y) y := fun w y =>
    hfam_deriv hf (by norm_num) w y
  have U1 := hfam_uexp hf (j := 1) (by norm_num) a
  have U2 := hfam_uexp hf (j := 2) (by norm_num) a
  have U3 := hfam_uexp hf (j := 3) (by norm_num) a
  have U4 := hfam_uexp hf (j := 4) (by norm_num) a
  have C1 := hfam_cont hf (j := 1) (by norm_num)
  have C2 := hfam_cont hf (j := 2) (by norm_num)
  have C3 := hfam_cont hf (j := 3) (by norm_num)
  have t1 : ∀ w ∈ Icc 0 a, ∀ y, HasDerivWithinAt (fun u => hfam f 1 u y)
      (hfam f 3 w y / 2) (Icc 0 a) w := fun w hw y => hfam_time hf (j := 1) (by norm_num) hw y
  have h2c : Continuous (fun p : ℝ × ℝ =>
      2 * hfam f 2 p.1 p.2 ^ 2 + 2 * hfam f 1 p.1 p.2 * hfam f 3 p.1 p.2) := by fun_prop
  refine (hasDerivWithinAt_heat_backward hv
    (h := fun w y => hfam f 1 w y ^ 2)
    (h₁ := fun w y => 2 * hfam f 1 w y * hfam f 2 w y)
    (h₂ := fun w y => 2 * hfam f 2 w y ^ 2 + 2 * hfam f 1 w y * hfam f 3 w y)
    (h₃ := fun w y => 6 * hfam f 2 w y * hfam f 3 w y + 2 * hfam f 1 w y * hfam f 4 w y)
    (hv' := fun w y => hfam f 1 w y * hfam f 3 w y)
    (fun w _ y => ?_) (fun w _ y => ?_) (fun w _ y => ?_) (by uexp_tac) (by uexp_tac)
    (by uexp_tac) (by uexp_tac) (fun y w hw => ?_) (Continuous.continuousOn (by fun_prop))
    (fun y => (h2c.comp (Continuous.prodMk_left y)).continuousWithinAt)).congr_deriv ?_
  · convert! (d1 w y).pow 2 using 1; ring
  · convert! ((d1 w y).const_mul 2).mul (d2 w y) using 1; ring
  · convert! (((d2 w y).pow 2).const_mul 2).add (((d1 w y).const_mul 2).mul (d3 w y)) using 1
    ring
  · convert! (t1 w hw y).pow 2 using 1; ring
  · exact heat_congr (fun y => by ring) x

/-- Backward derivative of `w - u²` (half a variance), for arbitrary jets `f` and `F`. -/
theorem backward_variance {f F : ℕ → ℝ → ℝ} (hf : Jet f) (hF : Jet F) {a x v : ℝ}
    (hv : v ∈ Icc 0 a) :
    HasDerivWithinAt (fun w => heat (a - w) (fun y => hfam F 0 w y - hfam f 0 w y ^ 2) x)
      (heat (a - v) (fun y => hfam f 1 v y ^ 2) x) (Icc 0 a) v := by
  have d0 : ∀ w y, HasDerivAt (hfam f 0 w) (hfam f 1 w y) y := fun w y =>
    hfam_deriv hf (by norm_num) w y
  have d1 : ∀ w y, HasDerivAt (hfam f 1 w) (hfam f 2 w y) y := fun w y =>
    hfam_deriv hf (by norm_num) w y
  have d2 : ∀ w y, HasDerivAt (hfam f 2 w) (hfam f 3 w y) y := fun w y =>
    hfam_deriv hf (by norm_num) w y
  have e0 : ∀ w y, HasDerivAt (hfam F 0 w) (hfam F 1 w y) y := fun w y =>
    hfam_deriv hF (by norm_num) w y
  have e1 : ∀ w y, HasDerivAt (hfam F 1 w) (hfam F 2 w y) y := fun w y =>
    hfam_deriv hF (by norm_num) w y
  have e2 : ∀ w y, HasDerivAt (hfam F 2 w) (hfam F 3 w y) y := fun w y =>
    hfam_deriv hF (by norm_num) w y
  have U0 := hfam_uexp hf (j := 0) (by norm_num) a
  have U1 := hfam_uexp hf (j := 1) (by norm_num) a
  have U2 := hfam_uexp hf (j := 2) (by norm_num) a
  have U3 := hfam_uexp hf (j := 3) (by norm_num) a
  have V0 := hfam_uexp hF (j := 0) (by norm_num) a
  have V2 := hfam_uexp hF (j := 2) (by norm_num) a
  have V3 := hfam_uexp hF (j := 3) (by norm_num) a
  have C0 := hfam_cont hf (j := 0) (by norm_num)
  have C1 := hfam_cont hf (j := 1) (by norm_num)
  have C2 := hfam_cont hf (j := 2) (by norm_num)
  have D2 := hfam_cont hF (j := 2) (by norm_num)
  have t0 : ∀ w ∈ Icc 0 a, ∀ y, HasDerivWithinAt (fun u => hfam f 0 u y)
      (hfam f 2 w y / 2) (Icc 0 a) w := fun w hw y => hfam_time hf (j := 0) (by norm_num) hw y
  have s0 : ∀ w ∈ Icc 0 a, ∀ y, HasDerivWithinAt (fun u => hfam F 0 u y)
      (hfam F 2 w y / 2) (Icc 0 a) w := fun w hw y => hfam_time hF (j := 0) (by norm_num) hw y
  have h2c : Continuous (fun p : ℝ × ℝ => hfam F 2 p.1 p.2 - 2 * hfam f 1 p.1 p.2 ^ 2 -
      2 * hfam f 0 p.1 p.2 * hfam f 2 p.1 p.2) := by fun_prop
  refine (hasDerivWithinAt_heat_backward hv
    (h := fun w y => hfam F 0 w y - hfam f 0 w y ^ 2)
    (h₁ := fun w y => hfam F 1 w y - 2 * hfam f 0 w y * hfam f 1 w y)
    (h₂ := fun w y => hfam F 2 w y - 2 * hfam f 1 w y ^ 2 - 2 * hfam f 0 w y * hfam f 2 w y)
    (h₃ := fun w y => hfam F 3 w y - 6 * hfam f 1 w y * hfam f 2 w y -
      2 * hfam f 0 w y * hfam f 3 w y)
    (hv' := fun w y => hfam F 2 w y / 2 - hfam f 0 w y * hfam f 2 w y)
    (fun w _ y => ?_) (fun w _ y => ?_) (fun w _ y => ?_) (by uexp_tac) (by uexp_tac)
    (by uexp_tac) (by uexp_tac) (fun y w hw => ?_) (Continuous.continuousOn (by fun_prop))
    (fun y => (h2c.comp (Continuous.prodMk_left y)).continuousWithinAt)).congr_deriv ?_
  · convert! (e0 w y).sub ((d0 w y).pow 2) using 1; ring
  · convert! (e1 w y).sub (((d0 w y).const_mul 2).mul (d1 w y)) using 1; ring
  · convert! ((e2 w y).sub (((d1 w y).pow 2).const_mul 2)).sub
      (((d0 w y).const_mul 2).mul (d2 w y)) using 1
    ring
  · convert! (s0 w hw y).sub ((t0 w hw y).pow 2) using 1; ring
  · exact heat_congr (fun y => by ring) x

end Fam

end Heat

end

end SpinGlass.Aristotle
