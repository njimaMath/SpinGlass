import SpinGlass.Parisi.Analytic.Lipschitz
import SpinGlass.Parisi.Analytic.Mass.Bounds
import SpinGlass.Parisi.Analytic.Heat.Split

/-!
# Gaussian Split analytic tools

Generic analytic lemmas used by the Parisi development.
Public names remain in `SpinGlass.Aristotle`;
`SpinGlass.Parisi.Analytic` is the analytic entry point.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

/-! ## Gaussian split identities behind U

Search tag: `PARISI_LB_SPLIT`. Keywords: Cole-Hopf, inserted mass, mixed derivative,
variance split, squared gradient, dissipation, U concavity, one-sided endpoints.

Consumers: (14.208)-(14.211), followed by (14.240)-(14.248). These local definitions
spell out the Gaussian integrals so the claims do not depend on the project's
Cole-Hopf API. The variance interval is closed and derivatives at its endpoints
are taken within that interval. Later bridges must identify these expressions
with the concrete recursion and propagate them through its earlier layers.
-/

/-- Gaussian specialization of `massTransform`. `Real.toNNReal` clamps variance;
the split lemmas therefore use derivatives within the admissible variance interval. -/
def gaussianLayer (m v : ℝ) (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  massTransform (gaussianReal 0 (Real.toNNReal v)) (fun z => A (x + z)) m

/-- Local inserted-mass response, corresponding to Delta in (14.208).
The inner mass varies while the outer mass and total variance remain fixed. -/
def splitMassResponse (m a : ℝ) (A : ℝ → ℝ) (x v : ℝ) : ℝ :=
  deriv (fun b => gaussianLayer m (a - v) (gaussianLayer b v A) x) m

/-- Tilted square of the j-th spatial derivative after Gaussian smoothing.
Use j=1 for the response derivative and j=2 for its negative curvature. -/
def splitSpatialMoment (j : ℕ) (m a : ℝ) (A : ℝ → ℝ) (x v : ℝ) : ℝ :=
  tiltedMean (gaussianReal 0 (Real.toNNReal (a - v)))
    (fun z => gaussianLayer m v A (x + z))
    (fun z => (iteratedDeriv j (gaussianLayer m v A) (x + z)) ^ 2) m

/-- A Gaussian layer with zero variance is the identity. -/
theorem gaussianLayer_zero_var (m : ℝ) (A : ℝ → ℝ) : gaussianLayer m 0 A = A := by
  ext x
  simp [gaussianLayer, gaussianReal_zero_var, massTransform_dirac]

/-- Differentiating the inserted mass at a zero-length interval gives zero. -/
theorem splitMassResponse_zero (m a : ℝ) (A : ℝ → ℝ) (x : ℝ) :
    splitMassResponse m a A x 0 = 0 := by
  simp [splitMassResponse, gaussianLayer_zero_var]


/-! ### Heat-semigroup form of the split quantities -/

section SplitGlue

open Heat

theorem gaussianLayer_eq_log {m : ℝ} (hm : m ≠ 0) (v : ℝ) (A : ℝ → ℝ) :
    gaussianLayer m v A = fun y => Real.log (heat v (fun u => Real.exp (m * A u)) y) / m := by
  funext y; simp [gaussianLayer, massTransform, hm, logLaplace, heat]

theorem gaussianLayer_zero_mass (v : ℝ) (A : ℝ → ℝ) : gaussianLayer 0 v A = heat v A := by
  funext y; simp [gaussianLayer, massTransform, heat]

theorem hfam_expJet_zero (m v : ℝ) (A : ℝ → ℝ) :
    hfam (expJet m (fun j => iteratedDeriv j A)) 0 v = heat v (fun u => Real.exp (m * A u)) := by
  funext y; simp [hfam, expJet]

theorem hfam_iteratedDeriv_zero (v : ℝ) (A : ℝ → ℝ) :
    hfam (fun j => iteratedDeriv j A) 0 v = heat v A := by
  funext y; simp [hfam]

theorem deriv_log_hfam {g : ℕ → ℝ → ℝ} (hg : Jet g) (hlow : PosLow (g 0)) (m v : ℝ) :
    deriv (fun y => Real.log (hfam g 0 v y) / m) =
      fun y => hfam g 1 v y / hfam g 0 v y / m := by
  funext y
  exact (((hfam_deriv hg (j := 0) (by norm_num) v y).log
    (hfam_pos hg hlow v y).ne').div_const m).deriv

theorem deriv_ratio_hfam {g : ℕ → ℝ → ℝ} (hg : Jet g) (hlow : PosLow (g 0)) (m v : ℝ) :
    deriv (fun y => hfam g 1 v y / hfam g 0 v y / m) =
      fun y => (hfam g 2 v y * hfam g 0 v y - hfam g 1 v y * hfam g 1 v y) /
        hfam g 0 v y ^ 2 / m := by
  funext y
  exact (((hfam_deriv hg (j := 1) (by norm_num) v y).div
    (hfam_deriv hg (j := 0) (by norm_num) v y) (hfam_pos hg hlow v y).ne').div_const m).deriv

theorem deriv_hfam {g : ℕ → ℝ → ℝ} (hg : Jet g) {j : ℕ} (hj : j < 4) (v : ℝ) :
    deriv (hfam g j v) = hfam g (j + 1) v := by
  funext y; exact (hfam_deriv hg hj v y).deriv

theorem heat_hfam_zero {g : ℕ → ℝ → ℝ} (hg : Jet g) {a v : ℝ} (hv : v ∈ Icc 0 a) (x : ℝ) :
    heat (a - v) (hfam g 0 v) x = heat a (g 0) x := by
  obtain ⟨C, K, -, -, hb⟩ := (hg.expT 0 (by norm_num)).bound
  have := heat_heat (s := a - v) (t := v) (by linarith [hv.2]) hv.1
    (hg.continuous (by norm_num)) hb x
  rw [sub_add_cancel] at this
  exact this

theorem heat_pos_of_posLow {g : ℕ → ℝ → ℝ} (hg : Jet g) (hlow : PosLow (g 0)) (a x : ℝ) :
    0 < heat a (g 0) x := hfam_pos hg hlow a x

/-- Heat form of the squared-gradient moment at positive mass. -/
theorem splitSpatialMoment_one_eq {m a : ℝ} (hm : m ≠ 0) {A : ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    (hg : Jet g) (hlow : PosLow (g 0))
    (hlay : ∀ v, gaussianLayer m v A = fun y => Real.log (hfam g 0 v y) / m)
    {v : ℝ} (hv : v ∈ Icc 0 a) (x : ℝ) :
    splitSpatialMoment 1 m a A x v = 1 / m ^ 2 *
      heat (a - v) (fun y => hfam g 1 v y ^ 2 * (hfam g 0 v y)⁻¹) x / heat a (g 0) x := by
  have hp := hfam_pos hg hlow v
  have hE : ∀ y, Real.exp (m * (Real.log (hfam g 0 v y) / m)) = hfam g 0 v y := fun y => by
    rw [show m * (Real.log (hfam g 0 v y) / m) = Real.log (hfam g 0 v y) by field_simp,
      Real.exp_log (hp y)]
  unfold splitSpatialMoment tiltedMean
  rw [hlay v, iteratedDeriv_one, deriv_log_hfam hg hlow]
  have num : heat (a - v) (fun y => (hfam g 1 v y / hfam g 0 v y / m) ^ 2 *
      Real.exp (m * (Real.log (hfam g 0 v y) / m))) x = 1 / m ^ 2 *
      heat (a - v) (fun y => hfam g 1 v y ^ 2 * (hfam g 0 v y)⁻¹) x := by
    rw [← heat_const_mul]
    refine heat_congr (fun y => ?_) x
    rw [hE]; have := (hp y).ne'; field_simp
  have den : heat (a - v) (fun y => Real.exp (m * (Real.log (hfam g 0 v y) / m))) x =
      heat a (g 0) x := by
    rw [heat_congr hE]; exact heat_hfam_zero hg hv x
  exact congrArg₂ (· / ·) num den

/-- Heat form of the squared-curvature moment at positive mass. -/
theorem splitSpatialMoment_two_eq {m a : ℝ} (hm : m ≠ 0) {A : ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    (hg : Jet g) (hlow : PosLow (g 0))
    (hlay : ∀ v, gaussianLayer m v A = fun y => Real.log (hfam g 0 v y) / m)
    {v : ℝ} (hv : v ∈ Icc 0 a) (x : ℝ) :
    splitSpatialMoment 2 m a A x v = 1 / m ^ 2 *
      heat (a - v) (fun y => (hfam g 2 v y * hfam g 0 v y - hfam g 1 v y ^ 2) ^ 2 *
        (hfam g 0 v y)⁻¹ ^ 3) x / heat a (g 0) x := by
  have hp := hfam_pos hg hlow v
  have hE : ∀ y, Real.exp (m * (Real.log (hfam g 0 v y) / m)) = hfam g 0 v y := fun y => by
    rw [show m * (Real.log (hfam g 0 v y) / m) = Real.log (hfam g 0 v y) by field_simp,
      Real.exp_log (hp y)]
  unfold splitSpatialMoment tiltedMean
  rw [hlay v, iteratedDeriv_succ, iteratedDeriv_one, deriv_log_hfam hg hlow,
    deriv_ratio_hfam hg hlow]
  have num : heat (a - v) (fun y => ((hfam g 2 v y * hfam g 0 v y - hfam g 1 v y *
      hfam g 1 v y) / hfam g 0 v y ^ 2 / m) ^ 2 *
      Real.exp (m * (Real.log (hfam g 0 v y) / m))) x = 1 / m ^ 2 *
      heat (a - v) (fun y => (hfam g 2 v y * hfam g 0 v y - hfam g 1 v y ^ 2) ^ 2 *
        (hfam g 0 v y)⁻¹ ^ 3) x := by
    rw [← heat_const_mul]
    refine heat_congr (fun y => ?_) x
    rw [hE]; have := (hp y).ne'; field_simp
  have den : heat (a - v) (fun y => Real.exp (m * (Real.log (hfam g 0 v y) / m))) x =
      heat a (g 0) x := by
    rw [heat_congr hE]; exact heat_hfam_zero hg hv x
  exact congrArg₂ (· / ·) num den

/-- Heat form of the spatial moments at zero mass. -/
theorem splitSpatialMoment_zero_mass_eq {a : ℝ} {A : ℝ → ℝ} (hJ : Jet (fun j => iteratedDeriv j A))
    {j : ℕ} (hj : j = 1 ∨ j = 2) (x v : ℝ) :
    splitSpatialMoment j 0 a A x v =
      heat (a - v) (fun y => hfam (fun j => iteratedDeriv j A) j v y ^ 2) x := by
  have hlay : gaussianLayer 0 v A = hfam (fun j => iteratedDeriv j A) 0 v := by
    rw [gaussianLayer_zero_mass, hfam_iteratedDeriv_zero]
  have hder : iteratedDeriv j (gaussianLayer 0 v A) = hfam (fun j => iteratedDeriv j A) j v := by
    rw [hlay]
    rcases hj with rfl | rfl
    · rw [iteratedDeriv_one, deriv_hfam hJ (by norm_num)]
    · rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_hfam hJ (by norm_num),
        deriv_hfam hJ (by norm_num)]
  unfold splitSpatialMoment tiltedMean
  rw [hder]
  simp only [zero_mul, Real.exp_zero, mul_one, integral_const, probReal_univ, smul_eq_mul,
    div_one]
  rfl

/-- Uniform mass bounds for the inner Gaussian layer. -/
theorem gaussianLayer_mass_bounds {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C) (v : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y,
      (∀ b ∈ Ioo (-3 : ℝ) 3, DifferentiableAt ℝ (fun b => gaussianLayer b v A y) b) ∧
      (∀ b ∈ Icc (-2 : ℝ) 2, |deriv (fun b => gaussianLayer b v A y) b| ≤ M) ∧
      (∀ b ∈ Icc (-2 : ℝ) 2, |gaussianLayer b v A y - A y| ≤ M) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb 1 (by simp) 0)
  obtain ⟨M, hM, h⟩ := massTransform_deriv_bound (μ := gaussianReal 0 v.toNNReal)
    (Y := fun z => C * |z|) (by fun_prop) (fun z => by positivity)
    (fun k => by simpa [mul_assoc] using integrable_gaussian_exp_abs (k * C) v.toNNReal)
  refine ⟨M, hM, fun y => ?_⟩
  exact h (fun z => A (y + z)) (A y) (hA.continuous.comp (continuous_const_add y)).measurable
    (fun z => lipschitz_of_iteratedDeriv hA hb y z)

theorem continuous_gaussianLayer {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C) (b v : ℝ) :
    Continuous (gaussianLayer b v A) := by
  have hJ := Heat.jet_iteratedDeriv hA hb
  obtain ⟨hC0, hlin⟩ := Heat.linear_bound_of_iteratedDeriv hA hb
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [gaussianLayer_zero_mass, ← hfam_iteratedDeriv_zero]
    exact (Heat.hfam_cont hJ (j := 0) (by norm_num)).comp (Continuous.prodMk_right v)
  · have hlin' : ∀ y, |(fun j => iteratedDeriv j A) 0 y| ≤ |A 0| + C * |y| := by simpa using hlin
    have hg := hJ.exp hlin' b
    have hlow := Heat.posLow_exp_of_linear hC0 hlin' b
    rw [gaussianLayer_eq_log hb0, ← hfam_expJet_zero]
    exact (((Heat.hfam_cont hg (j := 0) (by norm_num)).comp (Continuous.prodMk_right v)).log
      fun y => (Heat.hfam_pos hg hlow v y).ne').div_const b

/-- Heat form of the split mass response at zero mass: half a smoothed variance. -/
theorem splitMassResponse_zero_mass_eq {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C) (a x v : ℝ) :
    splitMassResponse 0 a A x v = heat (a - v) (fun y => 1 / 2 *
      (hfam (jetMul (fun j => iteratedDeriv j A) (fun j => iteratedDeriv j A)) 0 v y -
        hfam (fun j => iteratedDeriv j A) 0 v y ^ 2)) x := by
  have hJ := jet_iteratedDeriv hA hb
  obtain ⟨hC0, hlin⟩ := linear_bound_of_iteratedDeriv hA hb
  obtain ⟨M, hM, hB⟩ := gaussianLayer_mass_bounds hA hb v
  set F := jetMul (fun j => iteratedDeriv j A) (fun j => iteratedDeriv j A)
  have hF := hJ.mul hJ
  set ψ : ℝ → ℝ := fun y => 1 / 2 *
    (hfam F 0 v y - hfam (fun j => iteratedDeriv j A) 0 v y ^ 2)
  have hψc : Continuous ψ := by
    have h1 := (hfam_cont hF (j := 0) (by norm_num)).comp (Continuous.prodMk_right v)
    have h2 := (hfam_cont hJ (j := 0) (by norm_num)).comp (Continuous.prodMk_right v)
    exact continuous_const.mul (h1.sub (h2.pow 2))
  have hψ : ∀ y, deriv (fun b => gaussianLayer b v A y) 0 = ψ y := by
    intro y
    have hint : Integrable (fun z => Real.exp (1 * |A (y + z)|)) (gaussianReal 0 v.toNNReal) := by
      refine ((integrable_gaussian_exp_abs C v.toNNReal).const_mul (Real.exp |A y|)).mono'
        ((continuous_const.mul (hA.continuous.comp (continuous_const_add y)).abs).rexp
          |>.aestronglyMeasurable) (.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add, one_mul]
      refine Real.exp_le_exp.2 ?_
      have := lipschitz_of_iteratedDeriv hA hb y z
      have := abs_sub_abs_le_abs_sub (A (y + z)) (A y)
      linarith
    have := hasDerivAt_massTransform_zero (μ := gaussianReal 0 v.toNNReal)
      (X := fun z => A (y + z)) (hA.continuous.comp (continuous_const_add y)).measurable
      one_pos hint
    rw [show (fun b => gaussianLayer b v A y) = massTransform (gaussianReal 0 v.toNNReal)
      (fun z => A (y + z)) from rfl, this.deriv]
    simp only [ψ, F, hfam, jetMul, heat, iteratedDeriv_zero]
    ring_nf
  unfold splitMassResponse
  simp only [gaussianLayer_zero_mass]
  have key : HasDerivAt (fun b => ∫ z, gaussianLayer b v A (x + z) ∂gaussianReal 0 (a - v).toNNReal)
      (∫ z, deriv (fun b => gaussianLayer b v A (x + z)) 0 ∂gaussianReal 0 (a - v).toNNReal) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds (0 : ℝ) one_pos)
      (F' := fun b z => deriv (fun b => gaussianLayer b v A (x + z)) b) (bound := fun _ => M)
      (.of_forall fun b => ((continuous_gaussianLayer hA hb b v).comp
        (continuous_const_add x)).aestronglyMeasurable) ?_ ?_
      (.of_forall fun z b hb' => ?_) (integrable_const M) (.of_forall fun z b hb' => ?_)).2
    · refine ((integrable_gaussian_exp_abs 1 _).const_mul (|A 0| + C * |x| + M + C)).mono'
        ((continuous_gaussianLayer hA hb 0 v).comp (continuous_const_add x)).aestronglyMeasurable
        (.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, Function.comp_apply]
      have h1 := (hB (x + z)).2.2 0 ⟨by norm_num, by norm_num⟩
      have h2 := hlin (x + z)
      have h3 : |x + z| ≤ |x| + |z| := abs_add_le x z
      have h4 : |z| + 1 ≤ Real.exp (1 * |z|) := by rw [one_mul]; exact Real.add_one_le_exp _
      have h5 := abs_sub_abs_le_abs_sub (gaussianLayer 0 v A (x + z)) (A (x + z))
      have h6 : 1 ≤ Real.exp (1 * |z|) := by linarith [abs_nonneg z]
      have h7 : 0 ≤ |A 0| + C * |x| + M := by positivity
      have h8 : (|A 0| + C * |x| + M) * 1 ≤ (|A 0| + C * |x| + M) * Real.exp (1 * |z|) :=
        mul_le_mul_of_nonneg_left h6 h7
      have h9 : C * |z| ≤ C * Real.exp (1 * |z|) := mul_le_mul_of_nonneg_left (by linarith) hC0
      have h10 : C * |x + z| ≤ C * (|x| + |z|) := mul_le_mul_of_nonneg_left h3 hC0
      nlinarith [abs_nonneg z, abs_nonneg x]
    · exact (hψc.comp (continuous_const_add x)).aestronglyMeasurable.congr
        (.of_forall fun z => (hψ (x + z)).symm)
    · rw [Real.norm_eq_abs]
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hb'
      exact (hB (x + z)).2.1 b ⟨by linarith [(abs_lt.1 hb').1], by linarith [(abs_lt.1 hb').2]⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hb'
      exact ((hB (x + z)).1 b ⟨by linarith [(abs_lt.1 hb').1], by
        linarith [(abs_lt.1 hb').2]⟩).hasDerivAt
  rw [show (fun b => heat (a - v) (gaussianLayer b v A) x) =
    fun b => ∫ z, gaussianLayer b v A (x + z) ∂gaussianReal 0 (a - v).toNNReal from rfl, key.deriv]
  exact congrArg _ (funext fun z => hψ (x + z))

/-- Heat form of the split mass response at positive mass. -/
theorem splitMassResponse_pos_mass_eq {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C) {m a v : ℝ}
    (hm : m ∈ Icc (0 : ℝ) 1) (hm0 : m ≠ 0) (hv : v ∈ Icc 0 a) (x : ℝ) :
    splitMassResponse m a A x v = 1 / m ^ 2 *
      heat (a - v) (fun y => m * hfam (jetMul (fun j => iteratedDeriv j A)
        (expJet m (fun j => iteratedDeriv j A))) 0 v y -
        hfam (expJet m (fun j => iteratedDeriv j A)) 0 v y *
          Real.log (hfam (expJet m (fun j => iteratedDeriv j A)) 0 v y)) x /
      heat a (expJet m (fun j => iteratedDeriv j A) 0) x := by
  have hJ := jet_iteratedDeriv hA hb
  obtain ⟨hC0, hlin⟩ := linear_bound_of_iteratedDeriv hA hb
  have hlin' : ∀ y, |(fun j => iteratedDeriv j A) 0 y| ≤ |A 0| + C * |y| := by simpa using hlin
  have hg : Jet (expJet m (fun j => iteratedDeriv j A)) := hJ.exp hlin' m
  have hlow : PosLow (expJet m (fun j => iteratedDeriv j A) 0) := posLow_exp_of_linear hC0 hlin' m
  have hG : Jet (jetMul (fun j => iteratedDeriv j A) (expJet m (fun j => iteratedDeriv j A))) :=
    hJ.mul hg
  obtain ⟨M, hM, hB⟩ := gaussianLayer_mass_bounds hA hb v
  set g := expJet m (fun j => iteratedDeriv j A) with hgdef
  set e := hfam g 0 v with hedef
  set G := hfam (jetMul (fun j => iteratedDeriv j A) g) 0 v with hGdef
  have he : ∀ y, 0 < e y := hfam_pos hg hlow v
  have hec : Continuous e := (hfam_cont hg (j := 0) (by norm_num)).comp (Continuous.prodMk_right v)
  have hGc : Continuous G :=
    (hfam_cont hG (j := 0) (by norm_num)).comp (Continuous.prodMk_right v)
  have hlay : gaussianLayer m v A = fun y => Real.log (e y) / m := by
    rw [gaussianLayer_eq_log hm0, ← hfam_expJet_zero]
  have hE : ∀ y, Real.exp (m * gaussianLayer m v A y) = e y := by
    intro y; rw [hlay]; simp only; rw [mul_div_cancel₀ _ hm0, Real.exp_log (he y)]
  set ψ : ℝ → ℝ := fun y => (m * (G y / e y) - Real.log (e y)) / m ^ 2 with hψdef
  have hψc : Continuous ψ :=
    (((continuous_const.mul (hGc.div hec fun y => (he y).ne')).sub
      (hec.log fun y => (he y).ne')).div_const _)
  have hψ : ∀ y, HasDerivAt (fun b => gaussianLayer b v A y) (ψ y) m := by
    intro y
    have hint : Integrable (fun z => Real.exp (2 * |A (y + z)|)) (gaussianReal 0 v.toNNReal) := by
      refine ((integrable_gaussian_exp_abs (2 * C) v.toNNReal).const_mul
        (Real.exp (2 * |A y|))).mono'
        ((continuous_const.mul (hA.continuous.comp (continuous_const_add y)).abs).rexp
          |>.aestronglyMeasurable) (.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := lipschitz_of_iteratedDeriv hA hb y z
      have := abs_sub_abs_le_abs_sub (A (y + z)) (A y)
      nlinarith
    have h := hasDerivAt_massTransform (μ := gaussianReal 0 v.toNNReal)
      (X := fun z => A (y + z)) (hA.continuous.comp (continuous_const_add y)).measurable
      (a := 2) (by rw [abs_of_nonneg hm.1]; linarith [hm.2]) hm0 hint
    convert! h using 1
  have hK : ∀ b ∈ Icc (-2 : ℝ) 2, ∀ z, Real.exp (m * gaussianLayer b v A (x + z)) ≤
      Real.exp (|A 0| + C * |x| + M) * Real.exp (C * |z|) := by
    intro b hb' z
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 := (hB (x + z)).2.2 b hb'
    have h2 := hlin (x + z)
    have h3 : C * |x + z| ≤ C * (|x| + |z|) := mul_le_mul_of_nonneg_left (abs_add_le x z) hC0
    have h5 := abs_sub_abs_le_abs_sub (gaussianLayer b v A (x + z)) (A (x + z))
    have h6 : m * gaussianLayer b v A (x + z) ≤ |gaussianLayer b v A (x + z)| := by
      have := le_abs_self (gaussianLayer b v A (x + z))
      have := abs_nonneg (gaussianLayer b v A (x + z))
      have := neg_abs_le (gaussianLayer b v A (x + z))
      nlinarith [hm.1, hm.2]
    linarith
  have hball : ∀ b ∈ Metric.ball m 1, b ∈ Icc (-2 : ℝ) 2 ∧ b ∈ Ioo (-3 : ℝ) 3 := by
    intro b hb'
    rw [Metric.mem_ball, Real.dist_eq] at hb'
    have := abs_lt.1 hb'
    exact ⟨⟨by linarith [hm.1], by linarith [hm.2]⟩, ⟨by linarith [hm.1], by linarith [hm.2]⟩⟩
  have key : HasDerivAt (fun b => ∫ z, Real.exp (m * gaussianLayer b v A (x + z))
        ∂gaussianReal 0 (a - v).toNNReal)
      (∫ z, m * deriv (fun b => gaussianLayer b v A (x + z)) m *
        Real.exp (m * gaussianLayer m v A (x + z)) ∂gaussianReal 0 (a - v).toNNReal) m := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds m one_pos)
      (F' := fun b z => m * deriv (fun b => gaussianLayer b v A (x + z)) b *
        Real.exp (m * gaussianLayer b v A (x + z)))
      (bound := fun z => M * (Real.exp (|A 0| + C * |x| + M) * Real.exp (C * |z|)))
      (.of_forall fun b => (continuous_const.mul ((continuous_gaussianLayer hA hb b v).comp
        (continuous_const_add x))).rexp.aestronglyMeasurable) ?_ ?_
      (.of_forall fun z b hb' => ?_) ?_ (.of_forall fun z b hb' => ?_)).2
    · refine ((integrable_gaussian_exp_abs C _).const_mul
        (Real.exp (|A 0| + C * |x| + M))).mono'
        (continuous_const.mul ((continuous_gaussianLayer hA hb m v).comp
          (continuous_const_add x))).rexp.aestronglyMeasurable (.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hK m ⟨by linarith [hm.1], by linarith [hm.2]⟩ z
    · refine ((by fun_prop : Continuous fun z => m * ψ (x + z) * e (x + z))
        |>.aestronglyMeasurable).congr (.of_forall fun z => ?_)
      simp only
      rw [(hψ (x + z)).deriv, hE]
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hm.1, abs_of_pos (Real.exp_pos _)]
      have h1 := (hB (x + z)).2.1 b (hball b hb').1
      have h2 := hK b (hball b hb').1 z
      have h3 : m * |deriv (fun b => gaussianLayer b v A (x + z)) b| ≤ M := by
        nlinarith [abs_nonneg (deriv (fun b => gaussianLayer b v A (x + z)) b), hm.1, hm.2]
      calc m * |deriv (fun b => gaussianLayer b v A (x + z)) b| *
            Real.exp (m * gaussianLayer b v A (x + z))
          ≤ M * Real.exp (m * gaussianLayer b v A (x + z)) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 hM
    · exact ((integrable_gaussian_exp_abs C _).const_mul _).const_mul _
    · have := (((hB (x + z)).1 b (hball b hb').2).hasDerivAt.const_mul m).exp
      convert! this using 1; ring
  have hI : (∫ z, Real.exp (m * gaussianLayer m v A (x + z)) ∂gaussianReal 0 (a - v).toNNReal) =
      heat a (g 0) x := by
    rw [← heat_hfam_zero hg hv x]
    exact integral_congr_ae (.of_forall fun z => hE (x + z))
  have hIpos : 0 < heat a (g 0) x := heat_pos_of_posLow hg hlow a x
  have hfun : (fun b => gaussianLayer m (a - v) (gaussianLayer b v A) x) =
      fun b => Real.log (∫ z, Real.exp (m * gaussianLayer b v A (x + z))
        ∂gaussianReal 0 (a - v).toNNReal) / m := by
    funext b; rw [gaussianLayer_eq_log hm0]; rfl
  unfold splitMassResponse
  rw [hfun, ((key.log (by rw [hI]; exact hIpos.ne')).div_const m).deriv, hI]
  have hnum : (∫ z, m * deriv (fun b => gaussianLayer b v A (x + z)) m *
        Real.exp (m * gaussianLayer m v A (x + z)) ∂gaussianReal 0 (a - v).toNNReal) =
      1 / m * heat (a - v) (fun y => m * G y - e y * Real.log (e y)) x := by
    rw [← heat_const_mul]
    refine integral_congr_ae (.of_forall fun z => ?_)
    simp only
    rw [(hψ (x + z)).deriv, hE, hψdef]
    have := (he (x + z)).ne'
    field_simp
  rw [hnum]
  field_simp

end SplitGlue

/-- Concrete mixed mass/variance formula (14.209); includes m=0 and both endpoints. -/
theorem hasDerivWithinAt_splitMassResponse {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hbound : ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C)
    {m a v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivWithinAt (splitMassResponse m a A x)
      (splitSpatialMoment 1 m a A x v / 2) (Icc (0 : ℝ) a) v := by
  open Heat in
  · obtain ⟨C, hb⟩ := hbound
    have hJ := jet_iteratedDeriv hA hb
    obtain ⟨hC0, hlin⟩ := linear_bound_of_iteratedDeriv hA hb
    rcases eq_or_ne m 0 with rfl | hm0
    · have h := (backward_variance (x := x) hJ (hJ.mul hJ) hv).const_mul (1 / 2)
      refine (h.congr_of_mem (fun w _ => ?_) hv).congr_deriv ?_
      · rw [splitMassResponse_zero_mass_eq hA hb, heat_const_mul]
      · rw [splitSpatialMoment_zero_mass_eq hJ (Or.inl rfl)]; ring
    · have hlin' : ∀ y, |(fun j => iteratedDeriv j A) 0 y| ≤ |A 0| + C * |y| := by simpa using hlin
      have hg : Jet (expJet m (fun j => iteratedDeriv j A)) := hJ.exp hlin' m
      have hlow : PosLow (expJet m (fun j => iteratedDeriv j A) 0) :=
        posLow_exp_of_linear hC0 hlin' m
      have h := ((backward_entropy (x := x) hg hlow (hJ.mul hg) m hv).const_mul
        (1 / m ^ 2)).div_const (heat a (expJet m (fun j => iteratedDeriv j A) 0) x)
      refine (h.congr_of_mem (fun w hw => ?_) hv).congr_deriv ?_
      · rw [splitMassResponse_pos_mass_eq hA hb hm hm0 hw]
      · have hlay : ∀ v, gaussianLayer m v A =
            fun y => Real.log (hfam (expJet m (fun j => iteratedDeriv j A)) 0 v y) / m := by
          intro v; rw [gaussianLayer_eq_log hm0, ← hfam_expJet_zero]
        rw [splitSpatialMoment_one_eq hm0 hg hlow hlay hv,
          show (fun y => hfam (expJet m (fun j => iteratedDeriv j A)) 1 v y ^ 2 *
            (hfam (expJet m (fun j => iteratedDeriv j A)) 0 v y)⁻¹ / 2) = fun y => 1 / 2 *
            (hfam (expJet m (fun j => iteratedDeriv j A)) 1 v y ^ 2 *
            (hfam (expJet m (fun j => iteratedDeriv j A)) 0 v y)⁻¹) from funext fun y => by ring,
          heat_const_mul]
        ring

/-- Dissipation of the concrete squared-gradient moment, yielding (14.211). -/
theorem hasDerivWithinAt_splitSpatialMoment {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hbound : ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C)
    {m a v : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a)
    (hv : v ∈ Icc (0 : ℝ) a) (x : ℝ) :
    HasDerivWithinAt (splitSpatialMoment 1 m a A x)
      (-splitSpatialMoment 2 m a A x v) (Icc (0 : ℝ) a) v := by
  obtain ⟨C, hC⟩ := hbound
  have hJ := Heat.jet_iteratedDeriv hA hC
  obtain ⟨hC0, hlin⟩ := Heat.linear_bound_of_iteratedDeriv hA hC
  rcases eq_or_ne m 0 with rfl | hm0
  · have key := Heat.backward_gradSq_linear hJ (x := x) hv
    refine (key.congr_of_mem (fun w _ => splitSpatialMoment_zero_mass_eq hJ (Or.inl rfl) x w)
      hv).congr_deriv ?_
    rw [splitSpatialMoment_zero_mass_eq hJ (Or.inr rfl), Heat.heat_neg]
  · have hlin' : ∀ y, |(fun j => iteratedDeriv j A) 0 y| ≤ |A 0| + C * |y| := by simpa using hlin
    have hg := hJ.exp hlin' m
    have hlow : Heat.PosLow (Heat.expJet m (fun j => iteratedDeriv j A) 0) :=
      Heat.posLow_exp_of_linear hC0 hlin' m
    have hlay : ∀ v, gaussianLayer m v A = fun y =>
        Real.log (Heat.hfam (Heat.expJet m (fun j => iteratedDeriv j A)) 0 v y) / m := fun v => by
      rw [gaussianLayer_eq_log hm0, hfam_expJet_zero]
    have key := ((Heat.backward_gradSq hg hlow (x := x) hv).const_mul (1 / m ^ 2)).div_const
      (Heat.heat a (Heat.expJet m (fun j => iteratedDeriv j A) 0) x)
    refine (key.congr_of_mem (fun w hw => splitSpatialMoment_one_eq hm0 hg hlow hlay hw x)
      hv).congr_deriv ?_
    rw [splitSpatialMoment_two_eq hm0 hg hlow hlay hv x, Heat.heat_neg]
    ring

/-- Concavity needed for U, before averaging against the earlier recursion weights. -/
theorem concaveOn_splitMassResponse {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hbound : ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ y, |iteratedDeriv j A y| ≤ C)
    {m a : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) (ha : 0 < a) (x : ℝ) :
    ConcaveOn ℝ (Icc (0 : ℝ) a) (splitMassResponse m a A x) := by
  have h1 := fun v (hv : v ∈ Icc (0 : ℝ) a) =>
    hasDerivWithinAt_splitMassResponse hA hbound hm ha hv x
  have h2 := fun v (hv : v ∈ Icc (0 : ℝ) a) =>
    hasDerivWithinAt_splitSpatialMoment hA hbound hm ha hv x
  have hint : interior (Icc (0 : ℝ) a) = Ioo 0 a := interior_Icc
  have hS2 : ∀ v, 0 ≤ splitSpatialMoment 2 m a A x v := fun v =>
    div_nonneg (integral_nonneg fun z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (integral_nonneg fun z => (Real.exp_pos _).le)
  have hanti : AntitoneOn (splitSpatialMoment 1 m a A x) (Icc (0 : ℝ) a) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 a)
      (fun v hv => (h2 v hv).continuousWithinAt) ?_ ?_
    · rw [hint]
      exact fun v hv => ((h2 v (Ioo_subset_Icc_self hv)).hasDerivAt
        (Icc_mem_nhds hv.1 hv.2)).differentiableAt.differentiableWithinAt
    · rw [hint]
      intro v hv
      rw [((h2 v (Ioo_subset_Icc_self hv)).hasDerivAt (Icc_mem_nhds hv.1 hv.2)).deriv]
      linarith [hS2 v]
  refine AntitoneOn.concaveOn_of_deriv (convex_Icc 0 a)
    (fun v hv => (h1 v hv).continuousWithinAt) ?_ ?_
  · rw [hint]
    exact fun v hv => ((h1 v (Ioo_subset_Icc_self hv)).hasDerivAt
      (Icc_mem_nhds hv.1 hv.2)).differentiableAt.differentiableWithinAt
  · rw [hint]
    intro u hu w hw huw
    rw [((h1 u (Ioo_subset_Icc_self hu)).hasDerivAt (Icc_mem_nhds hu.1 hu.2)).deriv,
      ((h1 w (Ioo_subset_Icc_self hw)).hasDerivAt (Icc_mem_nhds hw.1 hw.2)).deriv]
    have := hanti (Ioo_subset_Icc_self hu) (Ioo_subset_Icc_self hw) huw
    linarith


end

end SpinGlass.Aristotle
