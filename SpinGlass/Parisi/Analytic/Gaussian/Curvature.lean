import SpinGlass.Parisi.Analytic.Lipschitz
import SpinGlass.Parisi.Analytic.Gaussian.Differentiation
import SpinGlass.Parisi.Analytic.Hyperbolic
import SpinGlass.Parisi.Analytic.Mass.Basic

/-!
# Gaussian Curvature analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

/-- Exponential moment bound behind the denominator in (14.282): Gaussian integration by
parts along the scaling `s ↦ x + s z` with `|A'| ≤ 1` and `|A''| ≤ 1`. -/
theorem integral_exp_mul_comp_add_le {A : ℝ → ℝ} (hA : ContDiff ℝ 2 A)
    (hfirst : ∀ x, |deriv A x| ≤ 1) (hsecond : ∀ x, |deriv (deriv A) x| ≤ 1)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (v : ℝ≥0) (x : ℝ) :
    ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v ≤ Real.exp (m * A x + v) := by
  obtain ⟨hm0, hm1⟩ := hm
  have hA1 : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hA2 : ContDiff ℝ 1 (deriv A) := (contDiff_succ_iff_deriv.1 hA).2.2
  have hA2d : Differentiable ℝ (deriv A) := hA2.differentiable one_ne_zero
  have hA2c : Continuous (deriv (deriv A)) := hA2.continuous_deriv le_rfl
  have hA1c : Continuous (deriv A) := hA2d.continuous
  have hAc : Continuous A := hA1.continuous
  have hlip := abs_sub_le_of_abs_deriv_le_one hA1 hfirst
  have henv : ∀ s z : ℝ, Real.exp (m * A (x + s * z)) ≤
      Real.exp (|A x|) * Real.exp (|s| * |z|) := by
    intro s z
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 := hlip (x + s * z) x
    rw [add_sub_cancel_left, abs_mul] at h1
    have h2 : m * A (x + s * z) ≤ |A (x + s * z)| := by
      calc m * A (x + s * z) ≤ m * |A (x + s * z)| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) hm0
        _ ≤ 1 * |A (x + s * z)| := mul_le_mul_of_nonneg_right hm1 (abs_nonneg _)
        _ = _ := one_mul _
    linarith [abs_sub_abs_le_abs_sub (A (x + s * z)) (A x)]
  set h : ℝ → ℝ := fun s => ∫ z, Real.exp (m * A (x + s * z)) ∂gaussianReal 0 v with hh
  set h' : ℝ → ℝ := fun s =>
    ∫ z, m * deriv A (x + s * z) * z * Real.exp (m * A (x + s * z)) ∂gaussianReal 0 v
  have hmeas : ∀ s, Continuous fun z => Real.exp (m * A (x + s * z)) := fun s => by fun_prop
  have hint : ∀ s, Integrable (fun z => Real.exp (m * A (x + s * z))) (gaussianReal 0 v) :=
    fun s => integrable_gaussianReal_of_abs_le_exp (hmeas s).aestronglyMeasurable fun z => by
      rw [abs_of_pos (Real.exp_pos _)]; exact henv s z
  have hpos : ∀ s, 0 < h s := fun s => integral_exp_pos (hint s)
  have hderiv : ∀ s, HasDerivAt h (h' s) s := by
    intro s
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s one_pos)
      (F := fun s z => Real.exp (m * A (x + s * z)))
      (F' := fun s z => m * deriv A (x + s * z) * z * Real.exp (m * A (x + s * z)))
      (bound := fun z => Real.exp (|A x|) * Real.exp ((|s| + 2) * |z|))
      (.of_forall fun s => (hmeas s).aestronglyMeasurable) (hint s)
      (by fun_prop : Continuous _).aestronglyMeasurable
      (.of_forall fun z t ht => ?_)
      ((integrable_gaussian_exp_abs _ v).const_mul _)
      (.of_forall fun z t _ => ?_)).2
    · rw [Metric.mem_ball, Real.dist_eq] at ht
      have ht' : |t| ≤ |s| + 1 := by linarith [abs_sub_abs_le_abs_sub t s]
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hm0]
      have hz : |z| ≤ Real.exp |z| := by linarith [Real.add_one_le_exp |z|, abs_nonneg z]
      calc m * |deriv A (x + t * z)| * |z| * Real.exp (m * A (x + t * z))
          ≤ 1 * 1 * Real.exp |z| * (Real.exp (|A x|) * Real.exp ((|s| + 1) * |z|)) := by
            gcongr
            · exact hfirst _
            · exact (henv t z).trans (by gcongr)
        _ = _ := by
          rw [one_mul, one_mul, mul_left_comm, ← Real.exp_add]; congr 2; ring
    · have hl := ((hasDerivAt_id t).mul_const z).const_add x
      have := (((hA1 _).hasDerivAt.comp t hl).const_mul m).exp
      convert! this using 1
      simp; ring
  set f' : ℝ → ℝ → ℝ := fun s z => (m * deriv (deriv A) (x + s * z) * s +
      m ^ 2 * deriv A (x + s * z) ^ 2 * s) * Real.exp (m * A (x + s * z))
  have hz : ∀ z : ℝ, |z| ≤ Real.exp |z| := fun z => by
    linarith [Real.add_one_le_exp |z|, abs_nonneg z]
  have hf'bd : ∀ s z, |m * deriv (deriv A) (x + s * z) * s +
      m ^ 2 * deriv A (x + s * z) ^ 2 * s| ≤ 2 * |s| := by
    intro s z
    refine (abs_add_le _ _).trans ?_
    simp only [abs_mul, abs_pow, abs_of_nonneg hm0]
    have a1 := hsecond (x + s * z)
    have a2 : |deriv A (x + s * z)| ^ 2 ≤ 1 := by
      nlinarith [hfirst (x + s * z), abs_nonneg (deriv A (x + s * z))]
    have hm2 : m ^ 2 ≤ 1 := by nlinarith
    have b1 : m * |deriv (deriv A) (x + s * z)| ≤ 1 := by
      nlinarith [abs_nonneg (deriv (deriv A) (x + s * z))]
    have b2 : m ^ 2 * |deriv A (x + s * z)| ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (deriv A (x + s * z))]
    nlinarith [abs_nonneg s]
  have hintf' : ∀ s, Integrable (f' s) (gaussianReal 0 v) := fun s =>
    integrable_gaussianReal_of_abs_le_exp (C := 2 * |s| * Real.exp |A x|) (c := |s|)
      (by fun_prop : Continuous _).aestronglyMeasurable fun z => by
        simp only [f']
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact (mul_le_mul (hf'bd s z) (henv s z) (Real.exp_pos _).le (by positivity)).trans_eq
          (by ring)
  have hstein : ∀ s, h' s = v * ∫ z, f' s z ∂gaussianReal 0 v := by
    intro s
    have hl : ∀ z, HasDerivAt (fun z => x + s * z) s z := fun z => by
      simpa using ((hasDerivAt_id z).const_mul s).const_add x
    have hf : ∀ z, HasDerivAt (fun z => m * deriv A (x + s * z) * Real.exp (m * A (x + s * z)))
        (f' s z) z := by
      intro z
      have h1 := ((hA2d _).hasDerivAt.comp z (hl z)).const_mul m
      have h2 := (((hA1 _).hasDerivAt.comp z (hl z)).const_mul m).exp
      convert! h1.mul h2 using 1
      simp only [f', Function.comp_def]; ring
    have hb := henv s
    rw [← integral_mul_gaussianReal hf _ _ (hintf' s)]
    · exact integral_congr_ae (.of_forall fun z => by simp only; ring)
    · refine integrable_gaussianReal_of_abs_le_exp (C := Real.exp |A x|) (c := |s|)
        (by fun_prop : Continuous _).aestronglyMeasurable fun z => ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hm0, abs_of_pos (Real.exp_pos _)]
      calc m * |deriv A (x + s * z)| * Real.exp (m * A (x + s * z))
          ≤ 1 * 1 * (Real.exp |A x| * Real.exp (|s| * |z|)) := by
            gcongr
            · exact hfirst _
            · exact hb z
        _ = _ := by ring
    · refine integrable_gaussianReal_of_abs_le_exp (C := Real.exp |A x|) (c := |s| + 1)
        (by fun_prop : Continuous _).aestronglyMeasurable fun z => ?_
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hm0, abs_of_pos (Real.exp_pos _)]
      calc |z| * (m * |deriv A (x + s * z)| * Real.exp (m * A (x + s * z)))
          ≤ Real.exp |z| * (1 * 1 * (Real.exp |A x| * Real.exp (|s| * |z|))) := by
            gcongr
            · exact hz z
            · exact hfirst _
            · exact hb z
        _ = _ := by
          rw [one_mul, one_mul, mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hle : ∀ s ∈ Icc (0 : ℝ) 1, h' s ≤ 2 * v * s * h s := by
    rintro s ⟨hs0, -⟩
    have hI : ∫ z, f' s z ∂gaussianReal 0 v ≤
        ∫ z, 2 * s * Real.exp (m * A (x + s * z)) ∂gaussianReal 0 v := by
      refine integral_mono (hintf' s) ((hint s).const_mul _) fun z => ?_
      have := hf'bd s z
      rw [abs_of_nonneg hs0] at this
      exact mul_le_mul_of_nonneg_right (le_abs_self _ |>.trans this) (Real.exp_pos _).le
    rw [integral_const_mul] at hI
    rw [hstein]
    calc (v : ℝ) * ∫ z, f' s z ∂gaussianReal 0 v ≤ v * (2 * s * h s) :=
          mul_le_mul_of_nonneg_left hI v.2
      _ = _ := by ring
  set k : ℝ → ℝ := fun s => Real.log (h s) - v * s ^ 2
  have hk : ∀ s, HasDerivAt k (h' s / h s - v * (2 * s)) s := fun s => by
    convert! ((hderiv s).log (hpos s).ne').sub
      ((hasDerivAt_pow 2 s).const_mul (v : ℝ)) using 1 <;> simp
  have hanti : AntitoneOn k (Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      (fun s _ => (hk s).continuousAt.continuousWithinAt)
      (fun s _ => (hk s).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [interior_Icc] at hs
    rw [(hk s).deriv, sub_nonpos, div_le_iff₀ (hpos s)]
    linarith [hle s (Ioo_subset_Icc_self hs)]
  have h10 := hanti (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one
  have h0 : h 0 = Real.exp (m * A x) := by simp [h]
  have h1 : h 1 = ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v := by simp [h]
  simp only [k, h0, Real.log_exp] at h10
  rw [← h1, ← Real.exp_log (hpos 1)]
  exact Real.exp_le_exp.2 (by linarith)

/-- Bounded continuous weights against the tilt `exp (m A (x + z))` are Gaussian integrable. -/
theorem integrable_mul_exp_comp_add {A w : ℝ → ℝ} (hA : Differentiable ℝ A)
    (hfirst : ∀ x, |deriv A x| ≤ 1) (hw : Continuous w) (hw1 : ∀ z, |w z| ≤ 1)
    {m : ℝ} (hm : 0 ≤ m) (v : ℝ≥0) (x : ℝ) :
    Integrable (fun z => w z * Real.exp (m * A (x + z))) (gaussianReal 0 v) := by
  have hAc := hA.continuous
  refine integrable_gaussianReal_of_abs_le_exp (C := Real.exp (m * |A x|)) (c := m)
    (by fun_prop : Continuous _).aestronglyMeasurable fun z => ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  have h1 := abs_sub_le_of_abs_deriv_le_one hA hfirst (x + z) x
  rw [add_sub_cancel_left] at h1
  have h2 : m * A (x + z) ≤ m * |A x| + m * |z| := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans
      (by linarith [abs_sub_abs_le_abs_sub (A (x + z)) (A x)])) hm
  calc |w z| * Real.exp (m * A (x + z)) ≤ 1 * Real.exp (m * |A x| + m * |z|) := by
        gcongr
        · exact hw1 z
    _ = _ := one_mul _

/-- Numerator estimate in (14.282): convexity of `A` and (14.281) under the Gaussian. -/
theorem integral_deriv_deriv_mul_exp_lower {A : ℝ → ℝ} (hA : ContDiff ℝ 2 A) {α m : ℝ}
    (hα : 0 ≤ α) (hm : 0 ≤ m)
    (hfirst : ∀ x, |deriv A x| ≤ 1) (hsecond : ∀ x, |deriv (deriv A) x| ≤ 1)
    (hlower : ∀ x, α / Real.cosh x ^ 2 ≤ deriv (deriv A) x) (v : ℝ≥0) (x : ℝ) :
    α * Real.exp (-(v : ℝ)) / Real.cosh x ^ 2 * Real.exp (m * A x) ≤
      ∫ z, deriv (deriv A) (x + z) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v := by
  have hA1 : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hA2 : ContDiff ℝ 1 (deriv A) := (contDiff_succ_iff_deriv.1 hA).2.2
  have hA2d : Differentiable ℝ (deriv A) := hA2.differentiable one_ne_zero
  have hA2c : Continuous (deriv (deriv A)) := hA2.continuous_deriv le_rfl
  have hmono : Monotone (deriv A) := monotone_of_deriv_nonneg hA2d fun y =>
    (div_nonneg hα (sq_nonneg _)).trans (hlower y)
  have htangent : ∀ z, A x + deriv A x * z ≤ A (x + z) := by
    intro z
    rcases le_total 0 z with hz | hz
    · have := (convex_Ici x).mul_sub_le_image_sub_of_le_deriv hA1.continuous.continuousOn
        hA1.differentiableOn (C := deriv A x) (fun y hy => by
          rw [interior_Ici] at hy; exact hmono (le_of_lt hy)) x self_mem_Ici (x + z)
        (by simpa using hz) (by linarith)
      rw [add_sub_cancel_left] at this; linarith
    · have := (convex_Iic x).image_sub_le_mul_sub_of_deriv_le hA1.continuous.continuousOn
        hA1.differentiableOn (C := deriv A x) (fun y hy => by
          rw [interior_Iic] at hy; exact hmono (le_of_lt hy)) (x + z) (by simpa using hz) x
        self_mem_Iic (by linarith)
      rw [sub_add_cancel_left] at this; linarith
  set t := Real.tanh x
  set c := m * deriv A x - 2 * t
  have hpt : ∀ z, α / Real.cosh x ^ 2 * Real.exp (m * A x) * Real.exp (c * z - z ^ 2) ≤
      deriv (deriv A) (x + z) * Real.exp (m * A (x + z)) := by
    intro z
    have h1 : α * (Real.exp (-2 * z * t - z ^ 2) / Real.cosh x ^ 2) ≤
        deriv (deriv A) (x + z) := by
      refine (mul_le_mul_of_nonneg_left (inv_cosh_sq_add_lower x z) hα).trans ?_
      rw [mul_one_div]; exact hlower _
    have h2 : Real.exp (m * (A x + deriv A x * z)) ≤ Real.exp (m * A (x + z)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (htangent z) hm)
    calc α / Real.cosh x ^ 2 * Real.exp (m * A x) * Real.exp (c * z - z ^ 2)
        = α / Real.cosh x ^ 2 * Real.exp (m * A x + (c * z - z ^ 2)) := by
          rw [Real.exp_add]; ring
      _ = α * (Real.exp (-2 * z * t - z ^ 2) / Real.cosh x ^ 2) *
            Real.exp (m * (A x + deriv A x * z)) := by
          have e : Real.exp (m * A x + (c * z - z ^ 2)) = Real.exp (-2 * z * t - z ^ 2) *
              Real.exp (m * (A x + deriv A x * z)) := by
            rw [← Real.exp_add]; congr 1; simp only [c]; ring
          rw [e]; ring
      _ ≤ _ := mul_le_mul h1 h2 (Real.exp_pos _).le (le_trans (by positivity) h1)
  have hint1 : Integrable (fun z => Real.exp (c * z - z ^ 2)) (gaussianReal 0 v) := by
    refine Integrable.of_bound (C := Real.exp (c ^ 2 / 4)) (by fun_prop)
      (.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (z - c / 2)])
  calc α * Real.exp (-(v : ℝ)) / Real.cosh x ^ 2 * Real.exp (m * A x)
      = α / Real.cosh x ^ 2 * Real.exp (m * A x) * Real.exp (-(v : ℝ)) := by ring
    _ ≤ α / Real.cosh x ^ 2 * Real.exp (m * A x) *
          ∫ z, Real.exp (c * z - z ^ 2) ∂gaussianReal 0 v := by
        gcongr
        exact integral_gaussian_exp_linear_sub_sq_lower c v
    _ = ∫ z, α / Real.cosh x ^ 2 * Real.exp (m * A x) * Real.exp (c * z - z ^ 2)
          ∂gaussianReal 0 v := (integral_const_mul _ _).symm
    _ ≤ _ := integral_mono (hint1.const_mul _)
        (integrable_mul_exp_comp_add hA1 hfirst (hA2c.comp (by fun_prop)) (fun z => hsecond _)
          hm v x) hpt

/-- Single-layer propagation behind (14.279). This uses concrete Gaussian
integration and the centered mass transform, rather than an assumed moment bound. -/
theorem gaussian_mass_curvature_lower {A : ℝ → ℝ} {α m : ℝ}
    (hA : ContDiff ℝ 2 A) (hα : 0 ≤ α) (hm : m ∈ Icc (0 : ℝ) 1)
    (hfirst : ∀ x, |deriv A x| ≤ 1)
    (hsecond : ∀ x, deriv (deriv A) x ≤ 1)
    (hlower : ∀ x, α / Real.cosh x ^ 2 ≤ deriv (deriv A) x)
    (v : ℝ≥0) (x : ℝ) :
    α * Real.exp (-2 * (v : ℝ)) / Real.cosh x ^ 2 ≤
      deriv (deriv (fun y => massTransform (gaussianReal 0 v) (fun z => A (y + z)) m)) x := by
  have hA1 : Differentiable ℝ A := hA.differentiable (by norm_num)
  have hA2 : ContDiff ℝ 1 (deriv A) := (contDiff_succ_iff_deriv.1 hA).2.2
  have hA2d : Differentiable ℝ (deriv A) := hA2.differentiable one_ne_zero
  have hA2c : Continuous (deriv (deriv A)) := hA2.continuous_deriv le_rfl
  have hA1c : Continuous (deriv A) := hA2d.continuous
  have habs2 : ∀ x, |deriv (deriv A) x| ≤ 1 := fun x => abs_le.2
    ⟨by linarith [(div_nonneg hα (sq_nonneg (Real.cosh x))).trans (hlower x)], hsecond x⟩
  have hlip := abs_sub_le_of_abs_deriv_le_one hA1 hfirst
  have hAgrowth : ∀ y, |A y| ≤ |A 0| + |y| := fun y => by
    have := hlip y 0
    rw [sub_zero] at this
    linarith [abs_sub_abs_le_abs_sub (A y) (A 0)]
  have hexp1 : ∀ y : ℝ, 1 ≤ Real.exp (1 * |y|) := fun y =>
    Real.one_le_exp (by rw [one_mul]; exact abs_nonneg y)
  have hnum := integral_deriv_deriv_mul_exp_lower hA hα hm.1 hfirst habs2 hlower v x
  have hv : Real.exp (-2 * (v : ℝ)) ≤ Real.exp (-(v : ℝ)) :=
    Real.exp_le_exp.2 (by linarith [NNReal.coe_nonneg v])
  rcases eq_or_lt_of_le hm.1 with rfl | hmpos
  · have hU : (fun y => massTransform (gaussianReal 0 v) (fun z => A (y + z)) 0) =
        fun y => ∫ z, A (y + z) ∂gaussianReal 0 v := by
      ext y; simp [massTransform]
    have hd1 : ∀ y, HasDerivAt (fun y => ∫ z, A (y + z) ∂gaussianReal 0 v)
        (∫ z, deriv A (y + z) ∂gaussianReal 0 v) y := fun y =>
      hasDerivAt_integral_gaussian_add (C := |A 0| + 1) (c := 1) (fun y => (hA1 y).hasDerivAt)
        hA1c zero_le_one (fun y => by
          have h1 := Real.add_one_le_exp (1 * |y|)
          rw [one_mul] at h1 ⊢
          nlinarith [hAgrowth y, mul_le_mul_of_nonneg_left (Real.one_le_exp (abs_nonneg y))
            (abs_nonneg (A 0))])
        (fun y => by nlinarith [hfirst y, hexp1 y, abs_nonneg (A 0)]) y
    have hd2 := hasDerivAt_integral_gaussian_add (v := v) (C := 1) (c := 1)
      (fun y => (hA2d y).hasDerivAt) hA2c zero_le_one (fun y => by nlinarith [hfirst y, hexp1 y])
      (fun y => by nlinarith [habs2 y, hexp1 y]) x
    rw [hU, funext fun y => (hd1 y).deriv, hd2.deriv]
    simp only [zero_mul, Real.exp_zero, mul_one] at hnum
    calc α * Real.exp (-2 * (v : ℝ)) / Real.cosh x ^ 2
        ≤ α * Real.exp (-(v : ℝ)) / Real.cosh x ^ 2 := by gcongr
      _ ≤ _ := hnum
  have hm0 : m ≠ 0 := hmpos.ne'
  set E : ℝ → ℝ := fun y => Real.exp (m * A y) with hE
  set g1 : ℝ → ℝ := fun y => m * deriv A y * E y with hg1
  set g2 : ℝ → ℝ := fun y => (m * deriv (deriv A) y + m ^ 2 * deriv A y ^ 2) * E y with hg2
  have hEb : ∀ y, E y ≤ Real.exp |A 0| * Real.exp (1 * |y|) := fun y => by
    rw [one_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : m * A y ≤ |A y| := by
      calc m * A y ≤ m * |A y| := mul_le_mul_of_nonneg_left (le_abs_self _) hm.1
        _ ≤ 1 * |A y| := mul_le_mul_of_nonneg_right hm.2 (abs_nonneg _)
        _ = |A y| := one_mul _
    linarith [hAgrowth y]
  have hC : 0 ≤ Real.exp |A 0| * Real.exp (1 * |(0 : ℝ)|) := by positivity
  have hdE : ∀ y, HasDerivAt E (g1 y) y := fun y => by
    have := (((hA1 y).hasDerivAt.const_mul m).exp)
    convert! this using 1; simp only [hg1, hE]; ring
  have hdg1 : ∀ y, HasDerivAt g1 (g2 y) y := fun y => by
    have := ((hA2d y).hasDerivAt.const_mul m).mul (hdE y)
    convert! this using 1
    simp only [hg2, hg1]; ring
  have hm2 : m ^ 2 ≤ 1 := by nlinarith [hm.1, hm.2]
  have hEpos : ∀ y, 0 < E y := fun y => Real.exp_pos _
  have hef : ∀ y : ℝ, 0 < Real.exp |A 0| * Real.exp (1 * |y|) := fun y => by positivity
  have bE : ∀ y, |E y| ≤ 2 * Real.exp |A 0| * Real.exp (1 * |y|) := fun y => by
    rw [abs_of_pos (Real.exp_pos _)]; nlinarith [hEb y, Real.exp_pos |A 0|, hexp1 y]
  have bg1 : ∀ y, |g1 y| ≤ 2 * Real.exp |A 0| * Real.exp (1 * |y|) := fun y => by
    simp only [hg1, abs_mul, abs_of_pos hmpos, abs_of_pos (hEpos y)]
    have h1 : m * |deriv A y| ≤ 1 := by nlinarith [hfirst y, abs_nonneg (deriv A y), hm.2]
    calc m * |deriv A y| * E y ≤ 1 * E y :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ _ := by nlinarith [hEb y, hef y]
  have bg2 : ∀ y, |g2 y| ≤ 2 * Real.exp |A 0| * Real.exp (1 * |y|) := fun y => by
    simp only [hg2, abs_mul, abs_of_pos (hEpos y)]
    have h1 : |m * deriv (deriv A) y + m ^ 2 * deriv A y ^ 2| ≤ 2 := by
      refine (abs_add_le _ _).trans ?_
      simp only [abs_mul, abs_pow, abs_of_pos hmpos]
      have a2 : |deriv A y| ^ 2 ≤ 1 := by nlinarith [hfirst y, abs_nonneg (deriv A y)]
      have b1 : m * |deriv (deriv A) y| ≤ 1 * 1 :=
        mul_le_mul hm.2 (habs2 y) (abs_nonneg _) zero_le_one
      have b2 : m ^ 2 * |deriv A y| ^ 2 ≤ 1 * 1 := mul_le_mul hm2 a2 (sq_nonneg _) zero_le_one
      linarith
    calc |m * deriv (deriv A) y + m ^ 2 * deriv A y ^ 2| * E y ≤ 2 * E y :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ _ := by nlinarith [hEb y, hef y]
  have hAc := hA1.continuous
  have hcE : Continuous E := by fun_prop
  have hcg2 : Continuous g2 := by fun_prop
  set F : ℝ → ℝ := fun y => ∫ z, E (y + z) ∂gaussianReal 0 v with hF
  set F1 : ℝ → ℝ := fun y => ∫ z, g1 (y + z) ∂gaussianReal 0 v with hF1
  set F2 : ℝ → ℝ := fun y => ∫ z, g2 (y + z) ∂gaussianReal 0 v with hF2
  have hdF : ∀ y, HasDerivAt F (F1 y) y := fun y =>
    hasDerivAt_integral_gaussian_add hdE (by fun_prop) zero_le_one bE bg1 y
  have hdF1 : HasDerivAt F1 (F2 x) x :=
    hasDerivAt_integral_gaussian_add hdg1 hcg2 zero_le_one bg1 bg2 x
  have hiE : ∀ y, Integrable (fun z => E (y + z)) (gaussianReal 0 v) := fun y => by
    simpa using integrable_mul_exp_comp_add (w := fun _ => (1 : ℝ)) hA1 hfirst continuous_const
      (fun _ => by norm_num) hm.1 v y
  have hFpos : ∀ y, 0 < F y := fun y => integral_exp_pos (hiE y)
  have hU : (fun y => massTransform (gaussianReal 0 v) (fun z => A (y + z)) m) =
      fun y => Real.log (F y) / m := by
    ext y; simp [massTransform, hm0, logLaplace, hF, hE]
  have hdU : deriv (fun y => Real.log (F y) / m) = fun y => F1 y / F y / m :=
    funext fun y => (((hdF y).log (hFpos y).ne').div_const m).deriv
  have hd2 : HasDerivAt (fun y => F1 y / F y / m) ((F2 x * F x - F1 x * F1 x) / F x ^ 2 / m) x :=
    (hdF1.div (hdF x) (hFpos x).ne').div_const m
  rw [hU, hdU, hd2.deriv]
  set Z := F x
  set P := ∫ z, deriv A (x + z) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v
  set Q := ∫ z, deriv A (x + z) ^ 2 * Real.exp (m * A (x + z)) ∂gaussianReal 0 v
  set N := ∫ z, deriv (deriv A) (x + z) * Real.exp (m * A (x + z)) ∂gaussianReal 0 v
  have iP := integrable_mul_exp_comp_add (w := fun z => deriv A (x + z)) hA1 hfirst
    (by fun_prop)
    (fun z => hfirst (x + z)) hm.1 v x
  have iQ := integrable_mul_exp_comp_add (w := fun z => deriv A (x + z) ^ 2) hA1 hfirst
    (by fun_prop) (fun z => by
      rw [abs_pow]; nlinarith [hfirst (x + z), abs_nonneg (deriv A (x + z))]) hm.1 v x
  have iN := integrable_mul_exp_comp_add (w := fun z => deriv (deriv A) (x + z)) hA1 hfirst
    (by fun_prop)
    (fun z => habs2 (x + z)) hm.1 v x
  have hF1x : F1 x = m * P := by
    rw [← integral_const_mul]
    exact integral_congr_ae (.of_forall fun z => by simp only [hg1, hE]; ring)
  have hF2x : F2 x = m * N + m ^ 2 * Q := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iN.const_mul _)
      (iQ.const_mul _)]
    exact integral_congr_ae (.of_forall fun z => by simp only [hg2, hE]; ring)
  have hZpos : 0 < Z := hFpos x
  have hCS : P ^ 2 ≤ Q * Z := by
    have h0 : 0 ≤ ∫ z, (deriv A (x + z) * Z - P) ^ 2 * Real.exp (m * A (x + z))
        ∂gaussianReal 0 v :=
      integral_nonneg fun z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    have hexp : ∫ z, (deriv A (x + z) * Z - P) ^ 2 * Real.exp (m * A (x + z))
        ∂gaussianReal 0 v = Z ^ 2 * Q - 2 * Z * P * P + P ^ 2 * Z := by
      have e : (fun z => (deriv A (x + z) * Z - P) ^ 2 * Real.exp (m * A (x + z))) =
          fun z => Z ^ 2 * (deriv A (x + z) ^ 2 * Real.exp (m * A (x + z))) -
            2 * Z * P * (deriv A (x + z) * Real.exp (m * A (x + z))) +
            P ^ 2 * E (x + z) := by
        ext z; simp only [hE]; ring
      rw [e, integral_add ?_ ((hiE x).const_mul _),
        integral_sub (iQ.const_mul _) (iP.const_mul _), integral_const_mul, integral_const_mul,
        integral_const_mul]
      exact (iQ.const_mul _).sub (iP.const_mul _)
    rw [hexp] at h0
    nlinarith
  have hden : Z ≤ Real.exp (m * A x + v) := integral_exp_mul_comp_add_le hA hfirst habs2 hm v x
  set K := α * Real.exp (-(v : ℝ)) / Real.cosh x ^ 2 * Real.exp (m * A x)
  have hK0 : 0 ≤ K := by positivity
  have hK : α * Real.exp (-2 * (v : ℝ)) / Real.cosh x ^ 2 = K / Real.exp (m * A x + v) := by
    simp only [K]
    rw [show -2 * (v : ℝ) = -(v : ℝ) - v by ring, Real.exp_sub, Real.exp_add]
    field_simp
  calc α * Real.exp (-2 * (v : ℝ)) / Real.cosh x ^ 2 = K / Real.exp (m * A x + v) := hK
    _ ≤ K / Z := div_le_div_of_nonneg_left hK0 hZpos hden
    _ ≤ N / Z := div_le_div_of_nonneg_right hnum hZpos.le
    _ ≤ N / Z + m * (Q * Z - P ^ 2) / Z ^ 2 :=
        le_add_of_nonneg_right (div_nonneg (mul_nonneg hm.1 (by linarith)) (sq_nonneg _))
    _ = _ := by
        rw [hF1x, hF2x]
        field_simp
        ring

end

end SpinGlass.Aristotle
