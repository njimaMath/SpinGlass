import SpinGlass.Parisi.Analytic.Heat.Backward
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Heat Jet analytic tools

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

/-!
# Heat-semigroup identities behind the Gaussian split

Four-jets of functions of exponential type, the forward heat equation for their Gaussian
smoothings, and the backward variance derivatives of the specific integrands that appear in
the split mass response and the squared-gradient moment.
-/

/-- Exponential type of a single function. -/
abbrev ExpT (f : ℝ → ℝ) : Prop := UExp univ (fun _ => f)

theorem ExpT.bound {f : ℝ → ℝ} (hf : ExpT f) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ y, |f y| ≤ C * Real.exp (K * |y|) := by
  obtain ⟨C, K, hC, hK, h⟩ := UExp.nonneg hf
  exact ⟨C, K, hC, hK, fun y => h 0 trivial y⟩

/-- A four-jet: `d 0` with four successive derivatives, all of exponential type. -/
structure Jet (d : ℕ → ℝ → ℝ) : Prop where
  hasDeriv : ∀ j < 4, ∀ y, HasDerivAt (d j) (d (j + 1) y) y
  cont : Continuous (d 4)
  expT : ∀ j ≤ 4, ExpT (d j)

namespace Jet

variable {d : ℕ → ℝ → ℝ}

theorem continuous (hd : Jet d) {j : ℕ} (hj : j ≤ 4) : Continuous (d j) := by
  rcases lt_or_eq_of_le hj with h | rfl
  · exact continuous_iff_continuousAt.2 fun y => (hd.hasDeriv j h y).continuousAt
  · exact hd.cont

theorem heat_hasDerivAt (hd : Jet d) {j : ℕ} (hj : j < 4) (t y : ℝ) :
    HasDerivAt (heat t (d j)) (heat t (d (j + 1)) y) y := by
  obtain ⟨C₁, K₁, -, -, h₁⟩ := (hd.expT j hj.le).bound
  obtain ⟨C₂, K₂, -, -, h₂⟩ := (hd.expT (j + 1) hj).bound
  obtain ⟨C, K, -, -, h⟩ := ((hd.expT j hj.le).abs.add (hd.expT (j + 1) hj).abs).nonneg
  refine hasDerivAt_heat t (hd.hasDeriv j hj) (hd.continuous hj) (C := C) (K := K)
    (fun y => ?_) (fun y => ?_) y
  · have := h 0 trivial y
    rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (d (j + 1) y)]
  · have := h 0 trivial y
    rw [abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg (d j y)]

theorem continuous_heat (hd : Jet d) {j : ℕ} (hj : j ≤ 4) :
    Continuous (fun p : ℝ × ℝ => heat p.1 (d j) p.2) := by
  obtain ⟨C, K, -, -, h⟩ := (hd.expT j hj).bound
  exact Heat.continuous_heat (hd.continuous hj) h

theorem uexp_heat (hd : Jet d) {j : ℕ} (hj : j ≤ 4) (a : ℝ) :
    UExp (Icc 0 a) (fun t y => heat t (d j) y) := by
  obtain ⟨C, K, -, -, h⟩ := (hd.expT j hj).bound
  exact (Heat.uexp_heat (hd.continuous hj) h a).mono fun _ ht => ht.2

end Jet

theorem heat_neg (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : heat t (fun y => -f y) x = -heat t f x := by
  simp [heat, integral_neg]

theorem heat_const_mul (t c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    heat t (fun y => c * f y) x = c * heat t f x := by
  simp [heat, integral_const_mul]

theorem heat_div_const (t c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    heat t (fun y => f y / c) x = heat t f x / c := by
  simp [heat, integral_div]

theorem heat_congr {t : ℝ} {f g : ℝ → ℝ} (h : ∀ y, f y = g y) (x : ℝ) :
    heat t f x = heat t g x := by
  rw [show f = g from funext h]

/-- The forward heat equation in the variance, including the endpoint `t = 0`. -/
theorem hasDerivWithinAt_heat_time {f f₁ f₂ f₃ : ℝ → ℝ} (h₁ : ∀ y, HasDerivAt f (f₁ y) y)
    (h₂ : ∀ y, HasDerivAt f₁ (f₂ y) y) (h₃ : ∀ y, HasDerivAt f₂ (f₃ y) y)
    (hb : ExpT f) (hb₂ : ExpT f₂) (hb₃ : ExpT f₃) {a t : ℝ} (ht : t ∈ Icc 0 a) (y : ℝ) :
    HasDerivWithinAt (fun s => heat s f y) (heat t f₂ y / 2) (Icc 0 a) t := by
  have hv : a - t ∈ Icc 0 a := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have key := hasDerivWithinAt_heat_backward (a := a) (x := y) hv
    (h := fun _ => f) (h₁ := fun _ => f₁) (h₂ := fun _ => f₂) (h₃ := fun _ => f₃)
    (hv' := fun _ _ => 0) (fun _ _ => h₁) (fun _ _ => h₂) (fun _ _ => h₃)
    (hb.mono (subset_univ _)) (hb₂.mono (subset_univ _)) (hb₃.mono (subset_univ _))
    (UExp.const 0) (fun _ _ _ => hasDerivWithinAt_const _ _ _) continuousOn_const
    (fun _ => continuousWithinAt_const)
  have hmap : MapsTo (fun s => a - s) (Icc 0 a) (Icc 0 a) := fun s hs =>
    ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hφ : HasDerivWithinAt (fun s => a - s) (-1) (Icc 0 a) t :=
    ((hasDerivAt_id t).const_sub a).hasDerivWithinAt
  have := key.comp t hφ hmap
  simp only [Function.comp_def, sub_sub_cancel, zero_sub] at this
  convert! this using 1
  rw [heat_neg, heat_div_const]; ring

namespace Jet

variable {d : ℕ → ℝ → ℝ}

theorem heat_time (hd : Jet d) {j : ℕ} (hj : j ≤ 1) {a t : ℝ} (ht : t ∈ Icc 0 a) (y : ℝ) :
    HasDerivWithinAt (fun s => heat s (d j) y) (heat t (d (j + 2)) y / 2) (Icc 0 a) t :=
  hasDerivWithinAt_heat_time (hd.hasDeriv j (by omega)) (hd.hasDeriv (j + 1) (by omega))
    (hd.hasDeriv (j + 2) (by omega)) (hd.expT j (by omega)) (hd.expT (j + 2) (by omega))
    (hd.expT (j + 3) (by omega)) ht y

end Jet

/-- Leibniz products of four-jets. -/
def jetMul (d e : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun y => d 0 y * e 0 y
  | 1 => fun y => d 1 y * e 0 y + d 0 y * e 1 y
  | 2 => fun y => d 2 y * e 0 y + 2 * (d 1 y * e 1 y) + d 0 y * e 2 y
  | 3 => fun y => d 3 y * e 0 y + 3 * (d 2 y * e 1 y) + 3 * (d 1 y * e 2 y) + d 0 y * e 3 y
  | _ => fun y => d 4 y * e 0 y + 4 * (d 3 y * e 1 y) + 6 * (d 2 y * e 2 y) +
      4 * (d 1 y * e 3 y) + d 0 y * e 4 y

theorem ExpT.mul {f g : ℝ → ℝ} (hf : ExpT f) (hg : ExpT g) : ExpT (fun y => f y * g y) :=
  UExp.mul hf hg

theorem ExpT.add {f g : ℝ → ℝ} (hf : ExpT f) (hg : ExpT g) : ExpT (fun y => f y + g y) :=
  UExp.add hf hg

theorem ExpT.const_mul {f : ℝ → ℝ} (hf : ExpT f) (c : ℝ) : ExpT (fun y => c * f y) :=
  UExp.const_mul hf c

theorem Jet.mul {d e : ℕ → ℝ → ℝ} (hd : Jet d) (he : Jet e) : Jet (jetMul d e) := by
  have D := hd.hasDeriv
  have E := he.hasDeriv
  refine ⟨fun j hj y => ?_, ?_, fun j hj => ?_⟩
  · interval_cases j
    · convert! (D 0 (by norm_num) y).mul (E 0 (by norm_num) y) using 1
    · convert! ((D 1 (by norm_num) y).mul (E 0 (by norm_num) y)).add
        ((D 0 (by norm_num) y).mul (E 1 (by norm_num) y)) using 1
      simp only [jetMul]; ring
    · convert! (((D 2 (by norm_num) y).mul (E 0 (by norm_num) y)).add
        (((D 1 (by norm_num) y).mul (E 1 (by norm_num) y)).const_mul 2)).add
        ((D 0 (by norm_num) y).mul (E 2 (by norm_num) y)) using 1
      simp only [jetMul]; ring
    · convert! ((((D 3 (by norm_num) y).mul (E 0 (by norm_num) y)).add
        (((D 2 (by norm_num) y).mul (E 1 (by norm_num) y)).const_mul 3)).add
        (((D 1 (by norm_num) y).mul (E 2 (by norm_num) y)).const_mul 3)).add
        ((D 0 (by norm_num) y).mul (E 3 (by norm_num) y)) using 1
      simp only [jetMul]; ring
  · have c := fun j (hj : j ≤ 4) => hd.continuous hj
    have c' := fun j (hj : j ≤ 4) => he.continuous hj
    simp only [jetMul]
    have := c 0 (by norm_num); have := c 1 (by norm_num); have := c 2 (by norm_num)
    have := c 3 (by norm_num); have := c 4 le_rfl
    have := c' 0 (by norm_num); have := c' 1 (by norm_num); have := c' 2 (by norm_num)
    have := c' 3 (by norm_num); have := c' 4 le_rfl
    fun_prop
  · have b := fun j (hj : j ≤ 4) => hd.expT j hj
    have b' := fun j (hj : j ≤ 4) => he.expT j hj
    interval_cases j <;> simp only [jetMul]
    · exact (b 0 (by norm_num)).mul (b' 0 (by norm_num))
    · exact ((b 1 (by norm_num)).mul (b' 0 (by norm_num))).add
        ((b 0 (by norm_num)).mul (b' 1 (by norm_num)))
    · exact (((b 2 (by norm_num)).mul (b' 0 (by norm_num))).add
        (((b 1 (by norm_num)).mul (b' 1 (by norm_num))).const_mul 2)).add
        ((b 0 (by norm_num)).mul (b' 2 (by norm_num)))
    · exact ((((b 3 (by norm_num)).mul (b' 0 (by norm_num))).add
        (((b 2 (by norm_num)).mul (b' 1 (by norm_num))).const_mul 3)).add
        (((b 1 (by norm_num)).mul (b' 2 (by norm_num))).const_mul 3)).add
        ((b 0 (by norm_num)).mul (b' 3 (by norm_num)))
    · exact (((((b 4 le_rfl).mul (b' 0 (by norm_num))).add
        (((b 3 (by norm_num)).mul (b' 1 (by norm_num))).const_mul 4)).add
        (((b 2 (by norm_num)).mul (b' 2 (by norm_num))).const_mul 6)).add
        (((b 1 (by norm_num)).mul (b' 3 (by norm_num))).const_mul 4)).add
        ((b 0 (by norm_num)).mul (b' 4 le_rfl))

/-! ## Smoothed families -/

/-- The smoothed family `(w, y) ↦ heat w (g j) y` of the `j`-th jet component. -/
noncomputable def hfam (g : ℕ → ℝ → ℝ) (j : ℕ) (w y : ℝ) : ℝ := heat w (g j) y

/-- A positive lower envelope of exponential type. -/
def PosLow (f : ℝ → ℝ) : Prop :=
  ∃ c L : ℝ, 0 < c ∧ 0 ≤ L ∧ ∀ y, c * Real.exp (-(L * |y|)) ≤ f y

macro "uexp_tac" : tactic => `(tactic| repeat (first
  | assumption
  | apply UExp.add
  | apply UExp.sub
  | apply UExp.neg
  | apply UExp.mul
  | apply UExp.pow
  | apply UExp.div_const
  | apply UExp.const))

macro "pi_norm" : tactic => `(tactic| (try simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply,
  Pi.sub_apply, Pi.inv_apply, Pi.neg_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul]))

section Fam

variable {g : ℕ → ℝ → ℝ}

theorem hfam_deriv (hg : Jet g) {j : ℕ} (hj : j < 4) (w y : ℝ) :
    HasDerivAt (hfam g j w) (hfam g (j + 1) w y) y := hg.heat_hasDerivAt hj w y

theorem hfam_time (hg : Jet g) {j : ℕ} (hj : j ≤ 1) {a w : ℝ} (hw : w ∈ Icc 0 a) (y : ℝ) :
    HasDerivWithinAt (fun u => hfam g j u y) (hfam g (j + 2) w y / 2) (Icc 0 a) w :=
  hg.heat_time hj hw y

theorem hfam_cont (hg : Jet g) {j : ℕ} (hj : j ≤ 4) :
    Continuous (fun p : ℝ × ℝ => hfam g j p.1 p.2) := hg.continuous_heat hj

theorem hfam_uexp (hg : Jet g) {j : ℕ} (hj : j ≤ 4) (a : ℝ) : UExp (Icc 0 a) (hfam g j) :=
  hg.uexp_heat hj a

theorem hfam_lower (hg : Jet g) (hlow : PosLow (g 0)) (a : ℝ) :
    ∃ c L : ℝ, 0 < c ∧ 0 ≤ L ∧ ∀ w ≤ a, ∀ y, c * Real.exp (-(L * |y|)) ≤ hfam g 0 w y := by
  obtain ⟨c, L, hc, hL, hl⟩ := hlow
  obtain ⟨C, K, -, -, hb⟩ := (hg.expT 0 (by norm_num)).bound
  obtain ⟨c', hc', h⟩ := heat_lower (hg.continuous (by norm_num)) hb hc hL hl a
  exact ⟨c', L, hc', hL, h⟩

theorem hfam_pos (hg : Jet g) (hlow : PosLow (g 0)) (w y : ℝ) : 0 < hfam g 0 w y := by
  obtain ⟨c, L, hc, -, h⟩ := hfam_lower hg hlow w
  exact lt_of_lt_of_le (by positivity) (h w le_rfl y)

theorem hfam_inv_uexp (hg : Jet g) (hlow : PosLow (g 0)) (a : ℝ) :
    UExp (Icc 0 a) (fun w y => (hfam g 0 w y)⁻¹) := by
  obtain ⟨c, L, hc, hL, h⟩ := hfam_lower hg hlow a
  refine ⟨c⁻¹, L, fun w hw y => ?_⟩
  have hp := hfam_pos hg hlow w y
  rw [abs_of_pos (inv_pos.2 hp)]
  calc (hfam g 0 w y)⁻¹ ≤ (c * Real.exp (-(L * |y|)))⁻¹ := inv_anti₀ (by positivity) (h w hw.2 y)
    _ = c⁻¹ * Real.exp (L * |y|) := by rw [mul_inv, ← Real.exp_neg, neg_neg]

theorem hfam_inv_cont (hg : Jet g) (hlow : PosLow (g 0)) :
    Continuous (fun p : ℝ × ℝ => (hfam g 0 p.1 p.2)⁻¹) :=
  (hfam_cont hg (by norm_num)).inv₀ fun p => (hfam_pos hg hlow p.1 p.2).ne'

theorem hfam_inv_deriv (hg : Jet g) (hlow : PosLow (g 0)) (w y : ℝ) :
    HasDerivAt (fun y => (hfam g 0 w y)⁻¹) (-(hfam g 1 w y) * (hfam g 0 w y)⁻¹ ^ 2) y := by
  have := (hfam_deriv hg (j := 0) (by norm_num) w y).inv (hfam_pos hg hlow w y).ne'
  convert! this using 1
  field_simp

theorem continuousWithinAt_of_joint {F : ℝ → ℝ → ℝ} (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (y : ℝ) (s : Set ℝ) (v : ℝ) : ContinuousWithinAt (fun w => F w y) s v :=
  (hF.comp (Continuous.prodMk_left y)).continuousWithinAt

end Fam

/-! ## Concrete jets -/

/-- The derivatives of a `C⁴` function with bounded derivatives of orders one to four form a
four-jet; the function itself has linear growth. -/
theorem jet_iteratedDeriv {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C) :
    Jet (fun j => iteratedDeriv j A) := by
  have hd : ∀ j < 4, ∀ y, HasDerivAt (iteratedDeriv j A) (iteratedDeriv (j + 1) A y) y := by
    intro j hj y
    rw [iteratedDeriv_succ]
    exact ((hA.differentiable_iteratedDeriv j (by exact_mod_cast hj)) y).hasDerivAt
  refine ⟨hd, hA.continuous_iteratedDeriv 4 le_rfl, fun j hj => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · refine ⟨|A 0| + |C|, 1, fun _ _ y => ?_⟩
    have hmv := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := A) (f' := iteratedDeriv 1 A) (C := C)
      (fun u _ => by
        have := (hd 0 (by norm_num) u).hasDerivWithinAt (s := univ)
        simpa only [iteratedDeriv_zero, zero_add] using this)
      (fun u _ => by rw [Real.norm_eq_abs]; exact hb 1 (by simp) u) (mem_univ 0) (mem_univ y)
    simp only [iteratedDeriv_zero, Real.norm_eq_abs, sub_zero] at hmv ⊢
    have h1 : |y| + 1 ≤ Real.exp |y| := Real.add_one_le_exp _
    have h2 : 1 ≤ Real.exp |y| := Real.one_le_exp (abs_nonneg _)
    have := abs_sub_abs_le_abs_sub (A y) (A 0)
    have hC : C ≤ |C| := le_abs_self C
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb 1 (by simp) 0)
    rw [one_mul]
    nlinarith [abs_nonneg (A 0), abs_nonneg y, abs_nonneg C]
  · exact ⟨C, 0, fun _ _ y => by
      simpa using hb j (Finset.mem_Icc.2 ⟨hj0, hj⟩) y⟩

/-- The four-jet of `exp (m * f)`. -/
noncomputable def expJet (m : ℝ) (d : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun y => Real.exp (m * d 0 y)
  | 1 => fun y => m * d 1 y * Real.exp (m * d 0 y)
  | 2 => fun y => (m * d 2 y + m ^ 2 * d 1 y ^ 2) * Real.exp (m * d 0 y)
  | 3 => fun y => (m * d 3 y + 3 * m ^ 2 * d 1 y * d 2 y + m ^ 3 * d 1 y ^ 3) *
      Real.exp (m * d 0 y)
  | _ => fun y => (m * d 4 y + 4 * m ^ 2 * d 1 y * d 3 y + 3 * m ^ 2 * d 2 y ^ 2 +
      6 * m ^ 3 * d 1 y ^ 2 * d 2 y + m ^ 4 * d 1 y ^ 4) * Real.exp (m * d 0 y)

theorem expT_exp_of_linear {f : ℝ → ℝ} {α β : ℝ} (hlin : ∀ y, |f y| ≤ α + β * |y|)
    (m : ℝ) : ExpT (fun y => Real.exp (m * f y)) := by
  refine ⟨Real.exp (|m| * α), |m| * β, fun _ _ y => ?_⟩
  rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_left (hlin y) (abs_nonneg m)
  have := neg_abs_le (m * f y)
  have := le_abs_self (m * f y)
  rw [abs_mul] at *
  nlinarith

theorem posLow_exp_of_linear {f : ℝ → ℝ} {α β : ℝ} (hβ : 0 ≤ β)
    (hlin : ∀ y, |f y| ≤ α + β * |y|) (m : ℝ) : PosLow (fun y => Real.exp (m * f y)) := by
  refine ⟨Real.exp (-(|m| * α)), |m| * β, Real.exp_pos _, mul_nonneg (abs_nonneg _) hβ,
    fun y => ?_⟩
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := mul_le_mul_of_nonneg_left (hlin y) (abs_nonneg m)
  have := neg_abs_le (m * f y)
  rw [abs_mul] at *
  nlinarith

theorem Jet.exp {d : ℕ → ℝ → ℝ} (hd : Jet d) {α β : ℝ}
    (hlin : ∀ y, |d 0 y| ≤ α + β * |y|) (m : ℝ) : Jet (expJet m d) := by
  have D := hd.hasDeriv
  have hE : ∀ y, HasDerivAt (fun y => Real.exp (m * d 0 y)) (m * d 1 y * Real.exp (m * d 0 y)) y :=
    fun y => by
      convert! ((D 0 (by norm_num) y).const_mul m).exp using 1; ring
  have UE := expT_exp_of_linear hlin m
  have b := fun j (hj : j ≤ 4) => hd.expT j hj
  have b1 := b 1 (by norm_num); have b2 := b 2 (by norm_num); have b3 := b 3 (by norm_num)
  have b4 := b 4 le_rfl
  refine ⟨fun j hj y => ?_, ?_, fun j hj => ?_⟩
  · interval_cases j
    · exact hE y
    · convert! ((D 1 (by norm_num) y).const_mul m).mul (hE y) using 1
      simp only [expJet]; ring
    · convert! (((D 2 (by norm_num) y).const_mul m).add
        (((D 1 (by norm_num) y).pow 2).const_mul (m ^ 2))).mul (hE y) using 1
      simp only [expJet]; pi_norm; ring
    · convert! ((((D 3 (by norm_num) y).const_mul m).add
        ((((D 1 (by norm_num) y).const_mul (3 * m ^ 2)).mul (D 2 (by norm_num) y)))).add
        (((D 1 (by norm_num) y).pow 3).const_mul (m ^ 3))).mul (hE y) using 1
      simp only [expJet]; pi_norm; ring
  · have c := fun j (hj : j ≤ 4) => hd.continuous hj
    have := c 0 (by norm_num); have := c 1 (by norm_num); have := c 2 (by norm_num)
    have := c 3 (by norm_num); have := c 4 le_rfl
    simp only [expJet]
    fun_prop
  · interval_cases j <;> simp only [expJet] <;> uexp_tac

theorem linear_bound_of_iteratedDeriv {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C) :
    0 ≤ C ∧ ∀ y, |A y| ≤ |A 0| + C * |y| := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb 1 (by simp) 0)
  refine ⟨hC0, fun y => ?_⟩
  have hd : ∀ u, HasDerivAt A (iteratedDeriv 1 A u) u := fun u => by
    rw [iteratedDeriv_one]
    exact ((hA.differentiable (by norm_num)) u).hasDerivAt
  have hmv := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := A) (f' := iteratedDeriv 1 A) (C := C) (fun u _ => (hd u).hasDerivWithinAt)
    (fun u _ => by rw [Real.norm_eq_abs]; exact hb 1 (by simp) u) (mem_univ 0) (mem_univ y)
  simp only [Real.norm_eq_abs, sub_zero] at hmv
  have := abs_sub_abs_le_abs_sub (A y) (A 0)
  linarith

end Heat

end

end SpinGlass.Aristotle
