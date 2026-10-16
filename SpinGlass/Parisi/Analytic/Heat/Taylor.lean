import SpinGlass.Parisi.Analytic.Heat.Basic

/-!
# Heat Taylor analytic tools

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

/-! ## Taylor remainders and the short-time expansion -/

theorem abs_le_of_hasDerivAt_abs_le_aux {G g : ℝ → ℝ} {M : ℝ} {n : ℕ}
    (hG0 : G 0 = 0) (hd : ∀ u, HasDerivAt G (g u) u) {w : ℝ} (hw : 0 ≤ w)
    (hb : ∀ u ∈ Icc 0 w, |g u| ≤ M * |u| ^ n) :
    |G w| ≤ M * |w| ^ (n + 1) / (n + 1) := by
  have key : ∀ σ : ℝ, |σ| ≤ 1 → σ * G w ≤ M * w ^ (n + 1) / (n + 1) := by
    intro σ hσ
    set φ : ℝ → ℝ := fun u => σ * G u - M * u ^ (n + 1) / (n + 1)
    have hφd : ∀ u, HasDerivAt φ (σ * g u - M * u ^ n) u := by
      intro u
      have := ((hd u).const_mul σ).sub (((hasDerivAt_pow (n + 1) u).const_mul M).div_const
        ((n : ℝ) + 1))
      convert! this using 1
      push_cast
      field_simp
    have hφc : Continuous φ := continuous_iff_continuousAt.2 fun u => (hφd u).continuousAt
    have := antitoneOn_of_deriv_nonpos (convex_Icc 0 w) hφc.continuousOn
      (fun u _ => (hφd u).differentiableAt.differentiableWithinAt)
      (by
        rw [interior_Icc]
        intro u hu
        rw [(hφd u).deriv]
        have h1 := hb u (Ioo_subset_Icc_self hu)
        rw [abs_of_pos hu.1] at h1
        have h2 : σ * g u ≤ |g u| := by
          calc σ * g u ≤ |σ * g u| := le_abs_self _
            _ = |σ| * |g u| := abs_mul _ _
            _ ≤ 1 * |g u| := mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
            _ = |g u| := one_mul _
        linarith)
      ⟨le_rfl, hw⟩ ⟨hw, le_rfl⟩ hw
    simp only [φ, hG0, mul_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, not_false_eq_true, zero_pow, zero_div, sub_zero] at this
    linarith
  rw [abs_of_nonneg hw, abs_le]
  constructor
  · have := key (-1) (by norm_num); linarith
  · have := key 1 (by norm_num); linarith

/-- Integrating a derivative bound `|g u| ≤ M |u|^n` from `0`. -/
theorem abs_le_of_hasDerivAt_abs_le {G g : ℝ → ℝ} {M : ℝ} {n : ℕ}
    (hG0 : G 0 = 0) (hd : ∀ u, HasDerivAt G (g u) u) {w : ℝ}
    (hb : ∀ u ∈ uIcc 0 w, |g u| ≤ M * |u| ^ n) :
    |G w| ≤ M * |w| ^ (n + 1) / (n + 1) := by
  rcases le_total 0 w with hw | hw
  · exact abs_le_of_hasDerivAt_abs_le_aux hG0 hd hw fun u hu => hb u (by
      rw [uIcc_of_le hw]; exact hu)
  · have := abs_le_of_hasDerivAt_abs_le_aux (G := fun u => G (-u)) (g := fun u => -g (-u))
      (n := n) (by simpa using hG0)
      (fun u => by convert! (hd (-u)).comp u (hasDerivAt_neg u) using 1 <;> simp)
      (w := -w) (by linarith) (fun u hu => by
        rw [abs_neg, ← abs_neg u]
        exact hb (-u) (by rw [uIcc_of_ge hw]; constructor <;> linarith [hu.1, hu.2]))
    simpa using this

/-- Second-order Taylor remainder controlled by an exponential-type third derivative. -/
theorem abs_taylor3_le {f f₁ f₂ f₃ : ℝ → ℝ} (h₁ : ∀ y, HasDerivAt f (f₁ y) y)
    (h₂ : ∀ y, HasDerivAt f₁ (f₂ y) y) (h₃ : ∀ y, HasDerivAt f₂ (f₃ y) y) {C K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ y, |f₃ y| ≤ C * Real.exp (K * |y|)) (y w : ℝ) :
    |f (y + w) - f y - w * f₁ y - w ^ 2 / 2 * f₂ y| ≤
      C * Real.exp (K * (|y| + |w|)) * |w| ^ 3 / 6 := by
  have hC := nonneg_of_exp_bound hb
  set M := C * Real.exp (K * (|y| + |w|))
  have hM : 0 ≤ M := by positivity
  have hsub : ∀ u ∈ uIcc 0 w, uIcc 0 u ⊆ uIcc 0 w := fun u hu =>
    uIcc_subset_uIcc left_mem_uIcc hu
  have habs : ∀ u ∈ uIcc 0 w, |u| ≤ |w| := fun u hu => by
    simpa using abs_sub_left_of_mem_uIcc hu
  have hb3 : ∀ u ∈ uIcc 0 w, |f₃ (y + u)| ≤ M * |u| ^ 0 := by
    intro u hu
    rw [pow_zero, mul_one]
    refine (hb _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC)
    have := abs_add_le y u
    have := habs u hu
    nlinarith
  have s2 : ∀ u ∈ uIcc 0 w, |f₂ (y + u) - f₂ y| ≤ M * |u| ^ 1 := by
    intro u hu
    have := abs_le_of_hasDerivAt_abs_le (G := fun u => f₂ (y + u) - f₂ y)
      (g := fun u => f₃ (y + u)) (n := 0) (by simp)
      (fun u => by
        convert! ((h₃ (y + u)).comp u
          ((hasDerivAt_id u).const_add y)).sub_const (f₂ y) using 1 <;> simp)
      (fun u' hu' => hb3 u' (hsub u hu hu'))
    simpa using this
  have s1 : ∀ u ∈ uIcc 0 w, |f₁ (y + u) - f₁ y - u * f₂ y| ≤ (M / 2) * |u| ^ 2 := by
    intro u hu
    have := abs_le_of_hasDerivAt_abs_le (G := fun u => f₁ (y + u) - f₁ y - u * f₂ y)
      (g := fun u => f₂ (y + u) - f₂ y) (n := 1) (by simp)
      (fun u => by
        have := (((h₂ (y + u)).comp u ((hasDerivAt_id u).const_add y)).sub_const (f₁ y)).sub
          ((hasDerivAt_id u).mul_const (f₂ y))
        convert! this using 1 <;> simp) (fun u' hu' => s2 u' (hsub u hu hu'))
    refine this.trans_eq ?_
    push_cast; ring
  have := abs_le_of_hasDerivAt_abs_le
    (G := fun u => f (y + u) - f y - u * f₁ y - u ^ 2 / 2 * f₂ y)
    (g := fun u => f₁ (y + u) - f₁ y - u * f₂ y) (n := 2) (by simp)
    (fun u => by
      have := ((((h₁ (y + u)).comp u ((hasDerivAt_id u).const_add y)).sub_const (f y)).sub
        ((hasDerivAt_id u).mul_const (f₁ y))).sub (((hasDerivAt_pow 2 u).div_const 2).mul_const
          (f₂ y))
      convert! this using 1; simp) s1 (w := w)
  convert! this using 1; push_cast; ring

theorem integral_sq_std : ∫ z, z ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have := variance_of_integral_eq_zero (X := id) (μ := gaussianReal 0 1) aemeasurable_id
    (by simp [integral_id_gaussianReal (μ := (0 : ℝ)) (v := 1)])
  rw [variance_id_gaussianReal] at this
  simpa using this.symm

theorem integral_id_std : ∫ z, z ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal

theorem integrable_pow_abs_mul_exp_std (n : ℕ) (c : ℝ) :
    Integrable (fun z : ℝ => |z| ^ n * Real.exp (c * |z|)) (gaussianReal 0 1) := by
  refine ((integrable_exp_abs_gaussian (c + 1) 1).const_mul (n.factorial : ℝ)).mono'
    (by fun_prop) (.of_forall fun z => ?_)
  have h := Real.pow_div_factorial_le_exp |z| (abs_nonneg z) n
  rw [div_le_iff₀ (by positivity)] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), add_mul, one_mul, Real.exp_add]
  calc |z| ^ n * Real.exp (c * |z|) ≤ Real.exp |z| * n.factorial * Real.exp (c * |z|) := by gcongr
    _ = _ := by ring

/-- The constant in the short-time expansion. -/
noncomputable def taylorConst (K a : ℝ) : ℝ :=
  (∫ z, |z| ^ 3 * Real.exp (K * Real.sqrt a * |z|) ∂(gaussianReal 0 1)) / 6

theorem taylorConst_nonneg (K a : ℝ) : 0 ≤ taylorConst K a :=
  div_nonneg (integral_nonneg fun _ => by positivity) (by norm_num)

/-- Short-time expansion of the heat operator: `heat δ f = f + δ f'' / 2 + O(δ^{3/2})`. -/
theorem heat_short_time {f f₁ f₂ f₃ : ℝ → ℝ} (h₁ : ∀ y, HasDerivAt f (f₁ y) y)
    (h₂ : ∀ y, HasDerivAt f₁ (f₂ y) y) (h₃ : ∀ y, HasDerivAt f₂ (f₃ y) y) {C K : ℝ}
    (hK : 0 ≤ K) (hb₀ : ∀ y, |f y| ≤ C * Real.exp (K * |y|))
    (hb₃ : ∀ y, |f₃ y| ≤ C * Real.exp (K * |y|)) {δ a : ℝ} (hδ : 0 ≤ δ) (hδa : δ ≤ a)
    (y : ℝ) :
    |heat δ f y - f y - δ / 2 * f₂ y| ≤
      C * taylorConst K a * (δ * Real.sqrt δ) * Real.exp (K * |y|) := by
  have hf : Continuous f := continuous_iff_continuousAt.2 fun y => (h₁ y).continuousAt
  have hC := nonneg_of_exp_bound hb₀
  set s := Real.sqrt δ
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = δ := Real.sq_sqrt hδ
  have hsa : s ≤ Real.sqrt a := Real.sqrt_le_sqrt hδa
  set γ := gaussianReal (0 : ℝ) 1
  have hiz : Integrable (fun z : ℝ => z) γ := (memLp_id_gaussianReal 1).integrable le_rfl
  have hiz2 : Integrable (fun z : ℝ => z ^ 2) γ :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hF := integrable_affine hf hb₀ y s 1
  have hL : Integrable (fun z : ℝ => (s * z) * f₁ y) γ := (hiz.const_mul s).mul_const _
  have hQ : Integrable (fun z : ℝ => (s * z) ^ 2 / 2 * f₂ y) γ :=
    ((hiz2.const_mul (s ^ 2 / 2 * f₂ y))).congr (.of_forall fun z => by simp only; ring)
  have i1 : ∫ z, (s * z) * f₁ y ∂γ = 0 := by
    have : (fun z : ℝ => (s * z) * f₁ y) = fun z => (s * f₁ y) * z := by funext z; ring
    rw [this, integral_const_mul, integral_id_std, mul_zero]
  have i2 : ∫ z, (s * z) ^ 2 / 2 * f₂ y ∂γ = δ / 2 * f₂ y := by
    have : (fun z : ℝ => (s * z) ^ 2 / 2 * f₂ y) = fun z => (s ^ 2 / 2 * f₂ y) * z ^ 2 := by
      funext z; ring
    rw [this, integral_const_mul, integral_sq_std, hs2, mul_one]
  have hmain : heat δ f y - f y - δ / 2 * f₂ y =
      ∫ z, (f (y + s * z) - f y - (s * z) * f₁ y - (s * z) ^ 2 / 2 * f₂ y) ∂γ := by
    have hA : Integrable (fun z => f (y + s * z) - f y) γ := hF.sub (integrable_const _)
    have hB : Integrable (fun z => f (y + s * z) - f y - (s * z) * f₁ y) γ := hA.sub hL
    rw [heat_eq_std δ hf, integral_sub hB hQ, integral_sub hA hL,
      integral_sub hF (integrable_const _),
      integral_const, i1, i2]
    simp [s]
  rw [hmain]
  refine (abs_integral_le_integral_abs).trans ?_
  calc (∫ z, |f (y + s * z) - f y - (s * z) * f₁ y - (s * z) ^ 2 / 2 * f₂ y| ∂γ)
      ≤ ∫ z, C * Real.exp (K * |y|) * (δ * s) / 6 *
          (|z| ^ 3 * Real.exp (K * Real.sqrt a * |z|)) ∂γ := by
        refine integral_mono_of_nonneg (.of_forall fun _ => abs_nonneg _)
          ((integrable_pow_abs_mul_exp_std 3 _).const_mul _) (.of_forall fun z => ?_)
        refine (abs_taylor3_le h₁ h₂ h₃ hK hb₃ y (s * z)).trans ?_
        rw [abs_mul, abs_of_nonneg hs, mul_pow, mul_add, Real.exp_add]
        have e1 : Real.exp (K * (s * |z|)) ≤ Real.exp (K * Real.sqrt a * |z|) := by
          refine Real.exp_le_exp.2 ?_
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsa hK) (abs_nonneg _)
        have e2 : s ^ 3 = δ * s := by rw [pow_succ, hs2]
        rw [e2]
        have : 0 ≤ δ * s := by positivity
        calc C * (Real.exp (K * |y|) * Real.exp (K * (s * |z|))) * (δ * s * |z| ^ 3) / 6
            ≤ C * (Real.exp (K * |y|) * Real.exp (K * Real.sqrt a * |z|)) *
                (δ * s * |z| ^ 3) / 6 := by gcongr
          _ = _ := by ring
    _ = C * taylorConst K a * (δ * s) * Real.exp (K * |y|) := by
        rw [integral_const_mul, taylorConst]; ring

/-! ## Backward differentiation in the variance -/

theorem UExp.abs {S : Set ℝ} {h : ℝ → ℝ → ℝ} (hh : UExp S h) : UExp S (fun v y => |h v y|) :=
  hh.of_le fun _ _ _ => by rw [abs_abs]

end Heat

end

end SpinGlass.Aristotle
