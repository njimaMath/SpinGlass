import SpinGlass.Parisi.Analytic.Gaussian.Integrability
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Heat Basic analytic tools

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
# Gaussian heat semigroup calculus

Search tag: `PARISI_LB_HEAT`. Namespace: `SpinGlass.Aristotle.Heat`.
Consumer: the concrete single-layer split formulas in `PARISI_LB_SPLIT`.

General tools about the Gaussian smoothing operator
`heat t f x = ∫ f (x + z) d𝒩(0, t)` acting on continuous functions of exponential type:
integrability, continuity in `(t, x)`, differentiation in `x`, the semigroup law,
a short-time expansion, and a backward differentiation formula in the variance for
time-dependent integrands.
-/

/-- Gaussian smoothing with variance `t` (negative variances are clamped to zero). -/
noncomputable def heat (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, f (x + z) ∂(gaussianReal 0 t.toNNReal)

/-- Uniform exponential-type bound for a family of functions on a parameter set. -/
def UExp (S : Set ℝ) (h : ℝ → ℝ → ℝ) : Prop :=
  ∃ C K : ℝ, ∀ v ∈ S, ∀ y, |h v y| ≤ C * Real.exp (K * |y|)

section UExp

variable {S : Set ℝ} {h g : ℝ → ℝ → ℝ}

theorem UExp.nonneg (hh : UExp S h) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ v ∈ S, ∀ y, |h v y| ≤ C * Real.exp (K * |y|) := by
  obtain ⟨C, K, hb⟩ := hh
  refine ⟨max C 0, max K 0, le_max_right _ _, le_max_right _ _, fun v hv y => ?_⟩
  refine (hb v hv y).trans ?_
  rcases le_total 0 C with hC | hC
  · rw [max_eq_left hC]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))) hC
  · exact (mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le).trans (by positivity)

theorem UExp.mono (hh : UExp S h) {T : Set ℝ} (hT : T ⊆ S) : UExp T h := by
  obtain ⟨C, K, hb⟩ := hh
  exact ⟨C, K, fun v hv => hb v (hT hv)⟩

theorem UExp.of_le (hh : UExp S h) (hle : ∀ v ∈ S, ∀ y, |g v y| ≤ |h v y|) : UExp S g := by
  obtain ⟨C, K, hb⟩ := hh
  exact ⟨C, K, fun v hv y => (hle v hv y).trans (hb v hv y)⟩

theorem UExp.const (c : ℝ) : UExp S (fun _ _ => c) :=
  ⟨|c|, 0, fun _ _ _ => by simp⟩

theorem UExp.add (hh : UExp S h) (hg : UExp S g) : UExp S (fun v y => h v y + g v y) := by
  obtain ⟨C₁, K₁, hC₁, hK₁, h₁⟩ := hh.nonneg
  obtain ⟨C₂, K₂, hC₂, hK₂, h₂⟩ := hg.nonneg
  refine ⟨C₁ + C₂, K₁ + K₂, fun v hv y => ?_⟩
  have e₁ : Real.exp (K₁ * |y|) ≤ Real.exp ((K₁ + K₂) * |y|) :=
    Real.exp_le_exp.2 (by nlinarith [abs_nonneg y])
  have e₂ : Real.exp (K₂ * |y|) ≤ Real.exp ((K₁ + K₂) * |y|) :=
    Real.exp_le_exp.2 (by nlinarith [abs_nonneg y])
  calc |h v y + g v y| ≤ |h v y| + |g v y| := abs_add_le _ _
    _ ≤ C₁ * Real.exp (K₁ * |y|) + C₂ * Real.exp (K₂ * |y|) := add_le_add (h₁ v hv y) (h₂ v hv y)
    _ ≤ C₁ * Real.exp ((K₁ + K₂) * |y|) + C₂ * Real.exp ((K₁ + K₂) * |y|) := by gcongr
    _ = (C₁ + C₂) * Real.exp ((K₁ + K₂) * |y|) := by ring

theorem UExp.neg (hh : UExp S h) : UExp S (fun v y => -h v y) :=
  hh.of_le fun _ _ _ => by rw [abs_neg]

theorem UExp.sub (hh : UExp S h) (hg : UExp S g) : UExp S (fun v y => h v y - g v y) := by
  simpa [sub_eq_add_neg] using hh.add hg.neg

theorem UExp.mul (hh : UExp S h) (hg : UExp S g) : UExp S (fun v y => h v y * g v y) := by
  obtain ⟨C₁, K₁, hC₁, hK₁, h₁⟩ := hh.nonneg
  obtain ⟨C₂, K₂, hC₂, hK₂, h₂⟩ := hg.nonneg
  refine ⟨C₁ * C₂, K₁ + K₂, fun v hv y => ?_⟩
  rw [abs_mul]
  calc |h v y| * |g v y| ≤ (C₁ * Real.exp (K₁ * |y|)) * (C₂ * Real.exp (K₂ * |y|)) :=
        mul_le_mul (h₁ v hv y) (h₂ v hv y) (abs_nonneg _) (by positivity)
    _ = C₁ * C₂ * Real.exp ((K₁ + K₂) * |y|) := by
        rw [add_mul, Real.exp_add]; ring

theorem UExp.const_mul (hh : UExp S h) (c : ℝ) : UExp S (fun v y => c * h v y) :=
  (UExp.const c).mul hh

theorem UExp.mul_const (hh : UExp S h) (c : ℝ) : UExp S (fun v y => h v y * c) :=
  hh.mul (UExp.const c)

theorem UExp.div_const (hh : UExp S h) (c : ℝ) : UExp S (fun v y => h v y / c) := by
  simpa [div_eq_mul_inv] using hh.mul_const c⁻¹

theorem UExp.pow (hh : UExp S h) (n : ℕ) : UExp S (fun v y => h v y ^ n) := by
  induction n with
  | zero => simpa using UExp.const (S := S) 1
  | succ n ih => simpa [pow_succ] using ih.mul hh

end UExp

/-! ## Gaussian integrability and the standard-normal representation -/

theorem integrable_exp_abs_gaussian (c : ℝ) (v : ℝ≥0) :
    Integrable (fun z : ℝ => Real.exp (c * |z|)) (gaussianReal 0 v) :=
  integrable_gaussian_exp_abs c v

theorem exp_abs_affine_le {K : ℝ} (hK : 0 ≤ K) (x s z : ℝ) :
    Real.exp (K * |x + s * z|) ≤ Real.exp (K * |x|) * Real.exp (K * |s| * |z|) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : |x + s * z| ≤ |x| + |s| * |z| := (abs_add_le _ _).trans (by rw [abs_mul])
  nlinarith

/-- A continuous function of exponential type composed with an affine map is integrable
against any centered Gaussian. -/
theorem integrable_affine {f : ℝ → ℝ} (hf : Continuous f) {C K : ℝ}
    (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|)) (x s : ℝ) (v : ℝ≥0) :
    Integrable (fun z => f (x + s * z)) (gaussianReal 0 v) := by
  obtain ⟨C', K', hC', hK', hb'⟩ := UExp.nonneg (S := univ) (h := fun _ => f) ⟨C, K, fun _ _ => hb⟩
  refine ((integrable_exp_abs_gaussian (K' * |s|) v).const_mul (C' * Real.exp (K' * |x|))).mono'
    (by fun_prop) (.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  calc |f (x + s * z)| ≤ C' * Real.exp (K' * |x + s * z|) := hb' 0 trivial _
    _ ≤ C' * (Real.exp (K' * |x|) * Real.exp (K' * |s| * |z|)) := by
        gcongr; exact exp_abs_affine_le hK' x s z
    _ = C' * Real.exp (K' * |x|) * Real.exp (K' * |s| * |z|) := by ring

theorem integrable_shift {f : ℝ → ℝ} (hf : Continuous f) {C K : ℝ}
    (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|)) (x : ℝ) (v : ℝ≥0) :
    Integrable (fun z => f (x + z)) (gaussianReal 0 v) := by
  simpa using integrable_affine hf hb x 1 v

theorem gaussianReal_map_sqrt (t : ℝ) :
    (gaussianReal 0 1).map (fun z => Real.sqrt t * z) = gaussianReal 0 t.toNNReal := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp only [NNReal.coe_mk, mul_one, Real.coe_toNNReal']
    rcases le_total 0 t with ht | ht
    · rw [Real.sq_sqrt ht, max_eq_left ht]
    · rw [Real.sqrt_eq_zero'.2 ht, max_eq_right ht]; simp

/-- Representation of `heat` through a standard Gaussian. Valid for every real `t`. -/
theorem heat_eq_std (t : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    heat t f x = ∫ z, f (x + Real.sqrt t * z) ∂(gaussianReal 0 1) := by
  rw [heat, ← gaussianReal_map_sqrt t, integral_map (by fun_prop)
    (by fun_prop : Continuous fun z => f (x + z)).aestronglyMeasurable]

theorem heat_zero {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) : heat 0 f x = f x := by
  rw [heat_eq_std 0 hf]; simp

/-- Dominated convergence for standard-Gaussian integrals of affinely moving integrands. -/
theorem tendsto_integral_std {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {q : ι → ℝ → ℝ} {k : ℝ → ℝ} {x s : ι → ℝ} {x₀ s₀ : ℝ}
    (hx : Tendsto x l (𝓝 x₀)) (hs : Tendsto s l (𝓝 s₀))
    (hmeas : ∀ᶠ i in l, AEStronglyMeasurable (fun z => q i (x i + s i * z)) (gaussianReal 0 1))
    (hbd : ∃ C K : ℝ, ∀ᶠ i in l, ∀ y, |q i y| ≤ C * Real.exp (K * |y|))
    (hlim : ∀ z, Tendsto (fun i => q i (x i + s i * z)) l (𝓝 (k (x₀ + s₀ * z)))) :
    Tendsto (fun i => ∫ z, q i (x i + s i * z) ∂(gaussianReal 0 1)) l
      (𝓝 (∫ z, k (x₀ + s₀ * z) ∂(gaussianReal 0 1))) := by
  obtain ⟨C, K, hbd⟩ := hbd
  set K' := max K 0
  have hK' : 0 ≤ K' := le_max_right _ _
  set C' := max C 0
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z => C' * Real.exp (K' * (|x₀| + 1)) * Real.exp (K' * (|s₀| + 1) * |z|)) hmeas ?_
    ((integrable_exp_abs_gaussian _ 1).const_mul _) (.of_forall hlim)
  have hx1 : ∀ᶠ i in l, |x i| ≤ |x₀| + 1 := by
    filter_upwards [(Metric.tendsto_nhds.1 hx) 1 one_pos] with i hi
    rw [Real.dist_eq] at hi
    linarith [abs_sub_abs_le_abs_sub (x i) x₀]
  have hs1 : ∀ᶠ i in l, |s i| ≤ |s₀| + 1 := by
    filter_upwards [(Metric.tendsto_nhds.1 hs) 1 one_pos] with i hi
    rw [Real.dist_eq] at hi
    linarith [abs_sub_abs_le_abs_sub (s i) s₀]
  filter_upwards [hbd, hx1, hs1] with i hi hxi hsi
  refine .of_forall fun z => ?_
  rw [Real.norm_eq_abs]
  have h1 : |q i (x i + s i * z)| ≤ C' * Real.exp (K' * |x i + s i * z|) := by
    refine (hi _).trans ?_
    rcases le_total 0 C with hC | hC
    · exact mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))) (by positivity)
        (le_max_right _ _)
    · exact (mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le).trans (by positivity)
  refine h1.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have : |x i + s i * z| ≤ |x i| + |s i| * |z| := (abs_add_le _ _).trans (by rw [abs_mul])
  have : |s i| * |z| ≤ (|s₀| + 1) * |z| := mul_le_mul_of_nonneg_right hsi (abs_nonneg _)
  nlinarith

/-- Joint continuity of the heat operator in the variance and the base point. -/
theorem continuous_heat {f : ℝ → ℝ} (hf : Continuous f) {C K : ℝ}
    (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|)) :
    Continuous (fun p : ℝ × ℝ => heat p.1 f p.2) := by
  have : (fun p : ℝ × ℝ => heat p.1 f p.2) =
      fun p => ∫ z, f (p.2 + Real.sqrt p.1 * z) ∂(gaussianReal 0 1) := by
    funext p; exact heat_eq_std _ hf _
  rw [this, continuous_iff_continuousAt]
  intro p
  refine tendsto_integral_std (q := fun _ => f) (x := fun p : ℝ × ℝ => p.2)
    (s := fun p : ℝ × ℝ => Real.sqrt p.1) continuous_snd.continuousAt
    (Real.continuous_sqrt.comp continuous_fst).continuousAt
    (.of_forall fun _ => (by fun_prop : Continuous _).aestronglyMeasurable)
    ⟨C, K, .of_forall fun _ => hb⟩ fun z => ?_
  exact (hf.comp (continuous_snd.add
    ((Real.continuous_sqrt.comp continuous_fst).mul continuous_const))).continuousAt

/-- Differentiation of the heat operator in the base point. -/
theorem hasDerivAt_heat (t : ℝ) {f f₁ : ℝ → ℝ} (hd : ∀ y, HasDerivAt f (f₁ y) y)
    (hf₁ : Continuous f₁) {C K : ℝ} (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|))
    (hb₁ : ∀ y, |f₁ y| ≤ C * Real.exp (K * |y|)) (x : ℝ) :
    HasDerivAt (heat t f) (heat t f₁ x) x := by
  have hf : Continuous f := continuous_iff_continuousAt.2 fun y => (hd y).continuousAt
  have e1 : heat t f = fun x => ∫ z, f (x + Real.sqrt t * z) ∂(gaussianReal 0 1) := by
    funext x; exact heat_eq_std t hf x
  rw [e1, heat_eq_std t hf₁]
  obtain ⟨C', K', hC', hK', hb'⟩ :=
    UExp.nonneg (S := univ) (h := fun _ => f₁) ⟨C, K, fun _ _ => hb₁⟩
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds x one_pos)
    (F := fun x z => f (x + Real.sqrt t * z)) (F' := fun x z => f₁ (x + Real.sqrt t * z))
    (bound := fun z => C' * Real.exp (K' * (|x| + 1)) * Real.exp (K' * |Real.sqrt t| * |z|))
    (.of_forall fun _ => (by fun_prop : Continuous _).aestronglyMeasurable)
    (integrable_affine hf hb x _ 1) (by fun_prop : Continuous _).aestronglyMeasurable
    (.of_forall fun z y hy => ?_) ((integrable_exp_abs_gaussian _ 1).const_mul _)
    (.of_forall fun z y _ => ?_)).2
  · rw [Real.norm_eq_abs]
    refine (hb' 0 trivial _).trans ?_
    have hy' : |y| ≤ |x| + 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hy; linarith [abs_sub_abs_le_abs_sub y x]
    calc C' * Real.exp (K' * |y + Real.sqrt t * z|)
        ≤ C' * (Real.exp (K' * |y|) * Real.exp (K' * |Real.sqrt t| * |z|)) := by
          gcongr; exact exp_abs_affine_le hK' _ _ _
      _ ≤ C' * (Real.exp (K' * (|x| + 1)) * Real.exp (K' * |Real.sqrt t| * |z|)) := by
          gcongr
      _ = _ := by ring
  · convert! (hd (y + Real.sqrt t * z)).comp y
      ((hasDerivAt_id y).add_const _) using 1 <;> simp

/-- The semigroup law of Gaussian smoothing. -/
theorem heat_heat {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {f : ℝ → ℝ} (hf : Continuous f)
    {C K : ℝ} (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|)) (x : ℝ) :
    heat s (heat t f) x = heat (s + t) f x := by
  have hconv : gaussianReal 0 (s + t).toNNReal =
      gaussianReal 0 s.toNNReal ∗ gaussianReal 0 t.toNNReal := by
    rw [gaussianReal_conv_gaussianReal, Real.toNNReal_add hs ht, add_zero]
  have hint : Integrable (fun z => f (x + z))
      (gaussianReal 0 s.toNNReal ∗ gaussianReal 0 t.toNNReal) := by
    rw [← hconv]; exact integrable_shift hf hb x _
  rw [heat, heat, hconv, integral_conv hint]
  simp only [heat, add_assoc]

theorem nonneg_of_exp_bound {f : ℝ → ℝ} {C K : ℝ} (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|)) :
    0 ≤ C := by
  have := (abs_nonneg _).trans (hb 0)
  simpa using this

/-- Exponential-type bounds are preserved by the heat operator, uniformly in bounded time. -/
theorem abs_heat_le {f : ℝ → ℝ} (hf : Continuous f) {C K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|)) {t a : ℝ} (hta : t ≤ a) (x : ℝ) :
    |heat t f x| ≤ C * (∫ z, Real.exp (K * Real.sqrt a * |z|) ∂(gaussianReal 0 1)) *
      Real.exp (K * |x|) := by
  have hC := nonneg_of_exp_bound hb
  rw [heat_eq_std t hf]
  refine (abs_integral_le_integral_abs).trans ?_
  calc (∫ z, |f (x + Real.sqrt t * z)| ∂(gaussianReal 0 1))
      ≤ ∫ z, C * Real.exp (K * |x|) * Real.exp (K * Real.sqrt a * |z|) ∂(gaussianReal 0 1) := by
        refine integral_mono (integrable_affine hf hb x _ 1).abs
          ((integrable_exp_abs_gaussian _ 1).const_mul _) fun z => ?_
        refine (hb _).trans ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hC
        refine (exp_abs_affine_le hK x _ z).trans ?_
        gcongr
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt hta
    _ = _ := by rw [integral_const_mul]; ring

theorem uexp_heat {f : ℝ → ℝ} (hf : Continuous f) {C K : ℝ}
    (hb : ∀ y, |f y| ≤ C * Real.exp (K * |y|)) (a : ℝ) :
    UExp (Iic a) (fun t y => heat t f y) := by
  obtain ⟨C', K', _, hK', hb'⟩ := UExp.nonneg (S := univ) (h := fun _ => f) ⟨C, K, fun _ _ => hb⟩
  exact ⟨_, _, fun t ht y => abs_heat_le hf hK' (hb' 0 trivial) ht y⟩

/-- A positive lower envelope survives Gaussian smoothing, uniformly in bounded time. -/
theorem heat_lower {g : ℝ → ℝ} (hg : Continuous g) {C K : ℝ}
    (hb : ∀ y, |g y| ≤ C * Real.exp (K * |y|)) {c L : ℝ} (hc : 0 < c) (hL : 0 ≤ L)
    (hlow : ∀ y, c * Real.exp (-(L * |y|)) ≤ g y) (a : ℝ) :
    ∃ c' > 0, ∀ t ≤ a, ∀ y, c' * Real.exp (-(L * |y|)) ≤ heat t g y := by
  set I := ∫ z, Real.exp (-(L * Real.sqrt a) * |z|) ∂(gaussianReal 0 1)
  have hI : 0 < I := integral_exp_pos (integrable_exp_abs_gaussian _ 1)
  refine ⟨c * I, mul_pos hc hI, fun t ht y => ?_⟩
  rw [heat_eq_std t hg]
  calc c * I * Real.exp (-(L * |y|))
      = ∫ z, c * Real.exp (-(L * |y|)) * Real.exp (-(L * Real.sqrt a) * |z|)
          ∂(gaussianReal 0 1) := by rw [integral_const_mul]; ring
    _ ≤ ∫ z, g (y + Real.sqrt t * z) ∂(gaussianReal 0 1) := by
        refine integral_mono ((integrable_exp_abs_gaussian _ 1).const_mul _)
          (integrable_affine hg hb y _ 1) fun z => ?_
        refine le_trans ?_ (hlow _)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hc.le
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have h1 : |y + Real.sqrt t * z| ≤ |y| + Real.sqrt a * |z| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          gcongr
        nlinarith

end Heat

end

end SpinGlass.Aristotle
