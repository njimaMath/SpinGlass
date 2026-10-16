import SpinGlass.Parisi.Analytic.Lipschitz
import SpinGlass.Parisi.Variational.ParisiMassDerivative
import SpinGlass.Parisi.Analytic.Gaussian.Split

/-!
# Spatial regularity for the concrete Parisi recursion

Fourth-order spatial regularity is needed by the variance-response identities
(14.209)-(14.211). The lemmas here connect the finite derivative families and
Gaussian smoothing in the analytic library to the project's Cole-Hopf layers.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- A finite family of actual derivatives agrees with iterated differentiation. -/
theorem iteratedDeriv_eq_of_derivative_family {d : ℕ → ℝ → ℝ} {n : ℕ}
    (hd : ∀ j < n, ∀ x, HasDerivAt (d j) (d (j + 1) x) x) :
    ∀ j ≤ n, iteratedDeriv j (d 0) = d j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      rw [iteratedDeriv_succ, ih (by omega)]
      exact funext fun x => (hd j (by omega) x).deriv

/-- Continuous final derivative and a finite derivative family imply `Cⁿ`. -/
theorem contDiff_of_finite_derivative_family {d : ℕ → ℝ → ℝ} {n : ℕ}
    (hd : ∀ j < n, ∀ x, HasDerivAt (d j) (d (j + 1) x) x)
    (hc : Continuous (d n)) : ContDiff ℝ n (d 0) := by
  have heq := iteratedDeriv_eq_of_derivative_family hd
  apply contDiff_nat_iff_iteratedDeriv.2
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [heq j hj]
    rcases lt_or_eq_of_le hj with hlt | rfl
    · exact continuous_iff_continuousAt.2 fun x => (hd j hlt x).continuousAt
    · exact hc
  · rw [heq j hj.le]
    exact fun x => (hd j hj x).differentiableAt

/-- The analytic Gaussian four-jet gives concrete fourth-order smoothness. -/
theorem contDiff_four_heat_of_jet {d : ℕ → ℝ → ℝ} (hd : Aristotle.Heat.Jet d) (v : ℝ) :
    ContDiff ℝ 4 (Aristotle.Heat.heat v (d 0)) := by
  apply contDiff_of_finite_derivative_family
    (d := fun j => Aristotle.Heat.heat v (d j))
    (fun j hj x => hd.heat_hasDerivAt hj v x)
  change Continuous (fun x => Aristotle.Heat.heat v (d 4) x)
  simpa only [Function.comp_def, id_eq] using
    (hd.continuous_heat (j := 4) le_rfl).comp
      ((continuous_const (y := v)).prodMk continuous_id)

/-- Identify the concrete Cole-Hopf layer with the analytic Gaussian layer. -/
theorem coleHopf_eq_gaussianLayer (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ) :
    coleHopf m v A = Aristotle.gaussianLayer m (v : ℝ) A := by
  funext x
  simpa only [Aristotle.gaussianLayer, Real.toNNReal_coe] using
    coleHopf_eq_massTransform m v A x

/-- Fourth-order smoothness of an actual Cole-Hopf layer, including zero
mass and zero variance. This is an intermediate regularity lemma; the input
derivative bounds must be supplied by the actual suffix recursion. -/
theorem contDiff_four_coleHopf {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hbound : ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j A x| ≤ C)
    (m : ℝ) (v : ℝ≥0) : ContDiff ℝ 4 (coleHopf m v A) := by
  have hJ := Aristotle.Heat.jet_iteratedDeriv hA hbound
  rw [coleHopf_eq_gaussianLayer]
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Aristotle.gaussianLayer_zero_mass]
    simpa only [iteratedDeriv_zero] using contDiff_four_heat_of_jet hJ (v : ℝ)
  · obtain ⟨hC, hlin⟩ := Aristotle.Heat.linear_bound_of_iteratedDeriv hA hbound
    have hlin' : ∀ x, |iteratedDeriv 0 A x| ≤ |A 0| + C * |x| := by
      simpa only [iteratedDeriv_zero] using hlin
    have hE := hJ.exp hlin' m
    have hec : ContDiff ℝ 4
        (Aristotle.Heat.heat (v : ℝ) (fun x => Real.exp (m * A x))) := by
      simpa only [Aristotle.Heat.expJet, iteratedDeriv_zero] using
        contDiff_four_heat_of_jet hE (v : ℝ)
    have hp : ∀ x, 0 < Aristotle.Heat.heat (v : ℝ) (fun y => Real.exp (m * A y)) x := by
      intro x
      simpa only [Aristotle.Heat.hfam, Aristotle.Heat.expJet, iteratedDeriv_zero] using
        Aristotle.Heat.hfam_pos hE (Aristotle.Heat.posLow_exp_of_linear hC hlin' m) (v : ℝ) x
    rw [Aristotle.gaussianLayer_eq_log hm]
    exact (hec.log (fun x => (hp x).ne')).div_const m

/-- The actual log-cosh terminal is smooth to every order. -/
theorem contDiff_parisiLogCoshTerminal (h : ℝ) (n : ℕ) :
    ContDiff ℝ n (parisiLogCoshTerminal h) := by
  exact (Real.contDiff_cosh.comp (contDiff_const.add contDiff_id)).log
    (fun x => (Real.cosh_pos (h + x)).ne')

private def SpatiallyBounded (f : ℝ → ℝ) : Prop := ∃ C : ℝ, ∀ x, |f x| ≤ C

private theorem spatiallyBounded_const (c : ℝ) : SpatiallyBounded (fun _ : ℝ => c) :=
  ⟨|c|, fun _ => le_rfl⟩

private theorem spatiallyBounded_add {f g : ℝ → ℝ}
    (hf : SpatiallyBounded f) (hg : SpatiallyBounded g) :
    SpatiallyBounded (fun x => f x + g x) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  exact ⟨C + D, fun x => (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩

private theorem spatiallyBounded_sub {f g : ℝ → ℝ}
    (hf : SpatiallyBounded f) (hg : SpatiallyBounded g) :
    SpatiallyBounded (fun x => f x - g x) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨C + D, fun x => ?_⟩
  simpa only [sub_eq_add_neg, abs_neg] using
    (abs_add_le (f x) (-g x)).trans (by simpa only [abs_neg] using add_le_add (hC x) (hD x))

private theorem spatiallyBounded_neg {f : ℝ → ℝ} (hf : SpatiallyBounded f) :
    SpatiallyBounded (fun x => -f x) := by
  obtain ⟨C, hC⟩ := hf
  exact ⟨C, fun x => by simpa only [abs_neg] using hC x⟩

private theorem spatiallyBounded_mul {f g : ℝ → ℝ}
    (hf : SpatiallyBounded f) (hg : SpatiallyBounded g) :
    SpatiallyBounded (fun x => f x * g x) := by
  obtain ⟨C, hC⟩ := hf
  obtain ⟨D, hD⟩ := hg
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine ⟨C * D, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC x) (hD x) (abs_nonneg _) hC0

private theorem spatiallyBounded_pow {f : ℝ → ℝ} (hf : SpatiallyBounded f) (n : ℕ) :
    SpatiallyBounded (fun x => f x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using spatiallyBounded_const 1
  | succ n ih => simpa only [pow_succ] using spatiallyBounded_mul ih hf

private theorem spatiallyBounded_div_const {f : ℝ → ℝ} (hf : SpatiallyBounded f) (c : ℝ) :
    SpatiallyBounded (fun x => f x / c) := by
  simpa only [div_eq_mul_inv] using spatiallyBounded_mul hf (spatiallyBounded_const c⁻¹)

private theorem exists_common_spatial_bound {d : ℕ → ℝ → ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, SpatiallyBounded (d j)) :
    ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ x, |d j x| ≤ C := by
  let K : ℕ → ℝ := fun j => if hj : j ∈ Finset.Icc 1 4 then (hb j hj).choose else 0
  refine ⟨∑ j ∈ Finset.Icc 1 4, |K j|, fun j hj x => ?_⟩
  have hK : |d j x| ≤ K j := by
    simpa only [K, dite_eq_left hj] using (hb j hj).choose_spec x
  exact hK.trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun i _ => abs_nonneg (K i)) hj))

private noncomputable def expDerivativeFactor (m : ℝ) (d : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | 1 => fun x => m * d 1 x
  | 2 => fun x => m * d 2 x + m ^ 2 * d 1 x ^ 2
  | 3 => fun x => m * d 3 x + 3 * m ^ 2 * d 1 x * d 2 x + m ^ 3 * d 1 x ^ 3
  | _ => fun x => m * d 4 x + 4 * m ^ 2 * d 1 x * d 3 x + 3 * m ^ 2 * d 2 x ^ 2 +
      6 * m ^ 3 * d 1 x ^ 2 * d 2 x + m ^ 4 * d 1 x ^ 4

private theorem expJet_eq_factor (m : ℝ) (d : ℕ → ℝ → ℝ) (j : ℕ) (x : ℝ) :
    Aristotle.Heat.expJet m d j x =
      expDerivativeFactor m d j x * Real.exp (m * d 0 x) := by
  rcases j with _ | j
  · simp only [Aristotle.Heat.expJet, expDerivativeFactor, one_mul]
  · rcases j with _ | j
    · rfl
    · rcases j with _ | j
      · rfl
      · rcases j with _ | j <;> rfl

private theorem spatiallyBounded_expDerivativeFactor {d : ℕ → ℝ → ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, SpatiallyBounded (d j)) (m : ℝ)
    {j : ℕ} (hj : j ∈ Finset.Icc 1 4) : SpatiallyBounded (expDerivativeFactor m d j) := by
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide)
  have h4 := hb 4 (by decide)
  obtain ⟨hj0, hj4⟩ := Finset.mem_Icc.1 hj
  interval_cases j <;> simp only [expDerivativeFactor] <;>
    repeat' first | assumption | apply spatiallyBounded_const | apply spatiallyBounded_add |
      apply spatiallyBounded_mul

private theorem continuous_expDerivativeFactor {d : ℕ → ℝ → ℝ}
    (hc : ∀ j ≤ 4, Continuous (d j)) (m : ℝ) {j : ℕ} (hj : j ≤ 4) :
    Continuous (expDerivativeFactor m d j) := by
  have h1 := hc 1 (by omega)
  have h2 := hc 2 (by omega)
  have h3 := hc 3 (by omega)
  have h4 := hc 4 le_rfl
  interval_cases j <;> simp only [expDerivativeFactor] <;> fun_prop

/-- Ratios of smoothed exponential derivatives are bounded in space. The
normalization is the actual Cole-Hopf tilt, whose integral equals one. -/
theorem exists_bound_heat_expJet_ratio {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j A x| ≤ C)
    {m : ℝ} (hm : m ≠ 0) (v : ℝ≥0) {j : ℕ} (hj : j ∈ Finset.Icc 1 4) :
    ∃ K : ℝ, ∀ x,
      |Aristotle.Heat.heat (v : ℝ) (Aristotle.Heat.expJet m (fun i => iteratedDeriv i A) j) x /
        Aristotle.Heat.heat (v : ℝ) (fun y => Real.exp (m * A y)) x| ≤ K := by
  have hB : ∀ i ∈ Finset.Icc 1 4, SpatiallyBounded (iteratedDeriv i A) :=
    fun i hi => ⟨C, hb i hi⟩
  let P := expDerivativeFactor m (fun i => iteratedDeriv i A) j
  obtain ⟨K, hK⟩ := spatiallyBounded_expDerivativeFactor hB m hj
  have hPc : Continuous P := continuous_expDerivativeFactor
    (fun i hi => hA.continuous_iteratedDeriv i (by exact_mod_cast hi)) m (Finset.mem_Icc.1 hj).2
  have hAm := hA.continuous.measurable
  have hAlip := Aristotle.lipschitz_of_iteratedDeriv hA hb
  have hLip : ∀ x y, |A y - A x| ≤ C * |y - x| := by
    intro x y
    simpa only [show x + (y - x) = y by ring] using hAlip x (y - x)
  have hAg := HasLinearGrowth.of_lipschitz hLip
  refine ⟨K, fun x => ?_⟩
  have heq :
      Aristotle.Heat.heat (v : ℝ) (Aristotle.Heat.expJet m (fun i => iteratedDeriv i A) j) x /
        Aristotle.Heat.heat (v : ℝ) (fun y => Real.exp (m * A y)) x =
      ∫ z, P (x + z) * coleHopfQ m v A x z ∂gaussianReal 0 v := by
    simp only [Aristotle.Heat.heat, Real.toNNReal_coe]
    rw [← integral_div]
    apply integral_congr_ae
    refine .of_forall fun z => ?_
    change Aristotle.Heat.expJet m (fun i => iteratedDeriv i A) j (x + z) /
      (∫ w, Real.exp (m * A (x + w)) ∂gaussianReal 0 v) =
      P (x + z) * coleHopfQ m v A x z
    rw [expJet_eq_factor, coleHopfQ_eq hAg hAm hm]
    simp only [iteratedDeriv_zero, P, mul_div_assoc]
  rw [heq]
  exact abs_integral_mul_coleHopfQ_le hAg hAm hm hPc.measurable hK v x

private noncomputable def logDerivativeFamily (B : ℝ → ℝ) (m : ℝ)
    (R : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => B
  | 1 => fun x => R 1 x / m
  | 2 => fun x => (R 2 x - R 1 x ^ 2) / m
  | 3 => fun x => (R 3 x - 3 * R 1 x * R 2 x + 2 * R 1 x ^ 3) / m
  | _ => fun x => (R 4 x - 4 * R 1 x * R 3 x - 3 * R 2 x ^ 2 +
      12 * R 1 x ^ 2 * R 2 x - 6 * R 1 x ^ 4) / m

private theorem hasDerivAt_logDerivativeFamily {B : ℝ → ℝ} {m : ℝ} {R : ℕ → ℝ → ℝ}
    (hB : ∀ x, HasDerivAt B (R 1 x / m) x)
    (hR : ∀ j < 4, ∀ x, HasDerivAt (R j) (R (j + 1) x - R j x * R 1 x) x) :
    ∀ j < 4, ∀ x, HasDerivAt (logDerivativeFamily B m R j)
      (logDerivativeFamily B m R (j + 1) x) x := by
  intro j hj x
  have h1 := hR 1 (by omega) x
  have h2 := hR 2 (by omega) x
  have h3 := hR 3 (by omega) x
  interval_cases j
  · exact hB x
  · convert! h1.div_const m using 1 <;> simp only [logDerivativeFamily] <;> ring
  · convert! (h2.sub (h1.pow 2)).div_const m using 1 <;>
      simp only [logDerivativeFamily] <;> ring
  · convert! ((h3.sub ((h1.mul h2).const_mul 3)).add ((h1.pow 3).const_mul 2)).div_const m
      using 1 <;> (try funext y) <;>
      simp only [logDerivativeFamily, Pi.mul_apply, Pi.add_apply,
        Pi.sub_apply, Pi.pow_apply] <;> ring

private theorem spatiallyBounded_logDerivativeFamily {B : ℝ → ℝ} {m : ℝ} {R : ℕ → ℝ → ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, SpatiallyBounded (R j)) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 4) : SpatiallyBounded (logDerivativeFamily B m R j) := by
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide)
  have h4 := hb 4 (by decide)
  obtain ⟨hj1, hj4⟩ := Finset.mem_Icc.1 hj
  interval_cases j <;> simp only [logDerivativeFamily] <;>
    repeat' first | assumption | apply spatiallyBounded_div_const | apply spatiallyBounded_const |
      apply spatiallyBounded_add | apply spatiallyBounded_sub | apply spatiallyBounded_neg |
      apply spatiallyBounded_mul

/-- Bounded spatial derivatives of orders one through four survive an actual
Cole-Hopf layer, including zero mass and zero variance. The bound here is
existential for a fixed input and mass; no parameter-uniform Taylor claim is made. -/
theorem exists_bound_iteratedDeriv_coleHopf_four {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j A x| ≤ C)
    (m : ℝ) (v : ℝ≥0) :
    ∃ K : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j (coleHopf m v A) x| ≤ K := by
  have hJ := Aristotle.Heat.jet_iteratedDeriv hA hb
  rcases eq_or_ne m 0 with rfl | hm
  · have heq := iteratedDeriv_eq_of_derivative_family (n := 4)
      (d := fun j => Aristotle.Heat.heat (v : ℝ) (iteratedDeriv j A))
      (fun j hj x => hJ.heat_hasDerivAt hj (v : ℝ) x)
    simp only [iteratedDeriv_zero] at heq
    rw [coleHopf_eq_gaussianLayer, Aristotle.gaussianLayer_zero_mass]
    refine ⟨C, fun j hj x => ?_⟩
    rw [heq j (Finset.mem_Icc.1 hj).2]
    have hi := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 v)
      (f := fun z => iteratedDeriv j A (x + z)) (C := C)
      (.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb j hj (x + z))
    simpa only [Aristotle.Heat.heat, Real.toNNReal_coe, Real.norm_eq_abs,
      probReal_univ, mul_one] using hi
  · obtain ⟨hC, hlin⟩ := Aristotle.Heat.linear_bound_of_iteratedDeriv hA hb
    have hAg : HasLinearGrowth A := ⟨|A 0|, C, hC, hlin⟩
    have hAm := hA.continuous.measurable
    have hlin' : ∀ x, |iteratedDeriv 0 A x| ≤ |A 0| + C * |x| := by
      simpa only [iteratedDeriv_zero] using hlin
    have hE := hJ.exp hlin' m
    let H : ℕ → ℝ → ℝ := fun j =>
      Aristotle.Heat.heat (v : ℝ) (Aristotle.Heat.expJet m (fun i => iteratedDeriv i A) j)
    let R : ℕ → ℝ → ℝ := fun j x => H j x / H 0 x
    have hH0 : H 0 = fun x => ∫ z, Real.exp (m * A (x + z)) ∂gaussianReal 0 v := by
      funext x
      simp only [H, Aristotle.Heat.heat, Aristotle.Heat.expJet, iteratedDeriv_zero,
        Real.toNNReal_coe]
    have hp : ∀ x, 0 < H 0 x := by
      rw [hH0]
      exact integral_exp_mul_comp_add_pos hAg hAm m v
    have hHd : ∀ j < 4, ∀ x, HasDerivAt (H j) (H (j + 1) x) x :=
      fun j hj x => hE.heat_hasDerivAt hj (v : ℝ) x
    have hRd : ∀ j < 4, ∀ x, HasDerivAt (R j) (R (j + 1) x - R j x * R 1 x) x := by
      intro j hj x
      convert! (hHd j hj x).fun_div (hHd 0 (by omega) x) (hp x).ne' using 1
      dsimp only [R]
      field_simp [(hp x).ne']
    have hfun : coleHopf m v A = fun x => Real.log (H 0 x) / m := by
      rw [coleHopf_eq_gaussianLayer, Aristotle.gaussianLayer_eq_log hm]
      simp only [H, Aristotle.Heat.expJet, iteratedDeriv_zero]
    have hBd : ∀ x, HasDerivAt (coleHopf m v A) (R 1 x / m) x := by
      rw [hfun]
      exact fun x => ((hHd 0 (by omega) x).log (hp x).ne').div_const m
    have hd := hasDerivAt_logDerivativeFamily hBd hRd
    have heq := iteratedDeriv_eq_of_derivative_family hd
    have hRb : ∀ j ∈ Finset.Icc 1 4, SpatiallyBounded (R j) := by
      intro j hj
      have hbound := exists_bound_heat_expJet_ratio hA hb hm v hj
      simpa only [SpatiallyBounded, R, H, Aristotle.Heat.expJet, iteratedDeriv_zero] using hbound
    obtain ⟨K, hK⟩ := exists_common_spatial_bound
      (fun j hj => spatiallyBounded_logDerivativeFamily hRb hj)
    refine ⟨K, fun j hj x => ?_⟩
    have hj' := Finset.mem_Icc.1 hj
    have he := heq j hj'.2
    change iteratedDeriv j (coleHopf m v A) = logDerivativeFamily (coleHopf m v A) m R j at he
    rw [he]
    exact hK j hj x

/-- The first two spatial derivatives have bounds uniform in the Gaussian
variance. This bound is local to one layer; its input constant may depend on
the fixed suffix and is not the parameter-uniform mass Taylor bound. -/
theorem iteratedDeriv_coleHopf_one_two_bounds {A : ℝ → ℝ} (hA : ContDiff ℝ 4 A) {C : ℝ}
    (hb : ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j A x| ≤ C)
    (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    |iteratedDeriv 1 (coleHopf m v A) x| ≤ C ∧
      |iteratedDeriv 2 (coleHopf m v A) x| ≤ C + 2 * |m| * C ^ 2 := by
  have hJ := Aristotle.Heat.jet_iteratedDeriv hA hb
  have hA0 : ∀ y, HasDerivAt A (iteratedDeriv 1 A y) y := by
    simpa only [iteratedDeriv_zero] using hJ.hasDeriv 0 (by norm_num)
  have hA1 : ∀ y, HasDerivAt (iteratedDeriv 1 A) (iteratedDeriv 2 A y) y :=
    hJ.hasDeriv 1 (by norm_num)
  have hC1 := hb 1 (by norm_num)
  have hC2 := hb 2 (by norm_num)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC1 0)
  have hAg := HasLinearGrowth.of_bounded_deriv hA0 hC1
  have hA1g := HasExpGrowth.of_bounded hC1
  have hA2g := HasExpGrowth.of_bounded hC2
  have hA1c := hJ.continuous (j := 1) (by norm_num)
  have hA2c := hJ.continuous (j := 2) (by norm_num)
  rcases eq_or_ne m 0 with rfl | hm
  · have hfun : coleHopf 0 v A = Aristotle.Heat.heat (v : ℝ) A := by
      funext y
      simp only [coleHopf_zero, Aristotle.Heat.heat, Real.toNNReal_coe]
    have heq := iteratedDeriv_eq_of_derivative_family
      (fun j hj y => hJ.heat_hasDerivAt hj (v : ℝ) y)
    have hh : ∀ j ∈ Finset.Icc 1 4,
        |iteratedDeriv j (coleHopf 0 v A) x| ≤ C := by
      intro j hj
      rw [hfun]
      change |iteratedDeriv j (Aristotle.Heat.heat (v : ℝ) (iteratedDeriv 0 A)) x| ≤ C
      rw [heq j (Finset.mem_Icc.1 hj).2]
      have h := norm_integral_le_of_norm_le_const
        (μ := gaussianReal 0 v) (f := fun z => iteratedDeriv j A (x + z))
        (.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb j hj (x + z))
      simpa only [Aristotle.Heat.heat, Real.toNNReal_coe, probReal_univ,
        mul_one, Real.norm_eq_abs] using h
    exact ⟨hh 1 (by norm_num), by simpa using hh 2 (by norm_num)⟩
  · let B1 : ℝ → ℝ := fun y => ∫ z, iteratedDeriv 1 A (y + z) *
        coleHopfQ m v A y z ∂gaussianReal 0 v
    have hd : ∀ y, HasDerivAt (coleHopf m v A) (B1 y) y := fun y =>
      hasDerivAt_coleHopf hA0 hAg hA1g hA1c.measurable hm v y
    have hder : iteratedDeriv 1 (coleHopf m v A) = B1 := by
      rw [iteratedDeriv_one]
      exact funext fun y => (hd y).deriv
    have hb1 : ∀ y, |B1 y| ≤ C := fun y =>
      abs_integral_mul_coleHopfQ_le hAg hA.continuous.measurable hm
        hA1c.measurable hC1 v y
    have hdd := hasDerivAt_integral_deriv_mul_coleHopfQ hA0 hA1
      hAg hA1g hA2g hA2c.measurable hm v x
    have hI := abs_integral_deriv2_coleHopfQ_le hA0 hA1 hA2c hC1 hC2 hm v x
    refine ⟨by rw [hder]; exact hb1 x, ?_⟩
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, hder, hdd.deriv]
    have hs : |B1 x| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hb1 x) 2
    calc
      _ ≤ |∫ z, (iteratedDeriv 2 A (x + z) + m * iteratedDeriv 1 A (x + z) ^ 2) *
          coleHopfQ m v A x z ∂gaussianReal 0 v| + |m * B1 x ^ 2| := abs_sub _ _
      _ ≤ (C + |m| * C ^ 2) + |m| * C ^ 2 := by
        rw [abs_mul, abs_pow]
        exact add_le_add hI (mul_le_mul_of_nonneg_left hs (abs_nonneg _))
      _ = C + 2 * |m| * C ^ 2 := by ring

private noncomputable def terminalDerivativeFamily (h : ℝ) : ℕ → ℝ → ℝ
  | 0 => parisiLogCoshTerminal h
  | 1 => parisiLogCoshTerminalDeriv h
  | 2 => parisiLogCoshTerminalDeriv2 h
  | 3 => fun x => -2 * Real.tanh (h + x) * (1 - Real.tanh (h + x) ^ 2)
  | _ => fun x => -2 + 8 * Real.tanh (h + x) ^ 2 - 6 * Real.tanh (h + x) ^ 4

private theorem hasDerivAt_terminalDerivativeFamily (h : ℝ) :
    ∀ j < 4, ∀ x, HasDerivAt (terminalDerivativeFamily h j)
      (terminalDerivativeFamily h (j + 1) x) x := by
  intro j hj x
  have hT : HasDerivAt (fun y => Real.tanh (h + y)) (1 - Real.tanh (h + x) ^ 2) x :=
    hasDerivAt_parisiLogCoshTerminalDeriv h x
  interval_cases j
  · exact hasDerivAt_parisiLogCoshTerminal h x
  · exact hasDerivAt_parisiLogCoshTerminalDeriv h x
  · convert! (hasDerivAt_const x (1 : ℝ)).sub (hT.pow 2) using 1 <;>
      simp only [terminalDerivativeFamily, parisiLogCoshTerminalDeriv2] <;> ring
  · convert! (hT.const_mul (-2)).mul
      ((hasDerivAt_const x (1 : ℝ)).sub (hT.pow 2)) using 1 <;>
      (try funext y) <;>
      simp only [terminalDerivativeFamily, Pi.sub_apply, Pi.pow_apply,
        Pi.mul_apply, Pi.add_apply] <;> ring

/-- The first four spatial derivatives of the actual log-cosh terminal are
bounded. The third and fourth derivatives are explicit polynomials in tanh. -/
theorem exists_bound_iteratedDeriv_parisiLogCoshTerminal_four (h : ℝ) :
    ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j (parisiLogCoshTerminal h) x| ≤ C := by
  have hT : SpatiallyBounded (fun x => Real.tanh (h + x)) :=
    ⟨1, fun x => (abs_parisiLogCoshTerminalDeriv_lt_one h x).le⟩
  have hB : ∀ j ∈ Finset.Icc 1 4, SpatiallyBounded (terminalDerivativeFamily h j) := by
    intro j hj
    obtain ⟨hj1, hj4⟩ := Finset.mem_Icc.1 hj
    interval_cases j <;>
      simp only [terminalDerivativeFamily, parisiLogCoshTerminalDeriv, parisiLogCoshTerminalDeriv2] <;>
      repeat' first | assumption | apply spatiallyBounded_const | apply spatiallyBounded_add |
        apply spatiallyBounded_sub | apply spatiallyBounded_neg | apply spatiallyBounded_mul
  obtain ⟨C, hC⟩ := exists_common_spatial_bound hB
  have heq := iteratedDeriv_eq_of_derivative_family (hasDerivAt_terminalDerivativeFamily h)
  refine ⟨C, fun j hj x => ?_⟩
  have he := heq j (Finset.mem_Icc.1 hj).2
  change iteratedDeriv j (parisiLogCoshTerminal h) = terminalDerivativeFamily h j at he
  rw [he]
  exact hC j hj x

/-- Actual finite Cole-Hopf recursion preserves fourth-order spatial regularity
and bounded derivatives, even when some masses or variances vanish. -/
theorem coleHopfIterate_spatial_regular_four {j : ℕ}
    (ms : Fin j → ℝ) (vs : Fin j → ℝ≥0) {A : ℝ → ℝ}
    (hA : ContDiff ℝ 4 A)
    (hb : ∃ C : ℝ, ∀ i ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv i A x| ≤ C) :
    ContDiff ℝ 4 (coleHopfIterate j ms vs A) ∧
      ∃ K : ℝ, ∀ i ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv i (coleHopfIterate j ms vs A) x| ≤ K := by
  induction j with
  | zero => exact ⟨hA, hb⟩
  | succ j ih =>
      obtain ⟨hB, C, hC⟩ := ih (Fin.tail ms) (Fin.tail vs)
      rw [coleHopfIterate_succ]
      exact ⟨contDiff_four_coleHopf hB hC (ms 0) (vs 0),
        exists_bound_iteratedDeriv_coleHopf_four hB hC (ms 0) (vs 0)⟩

/-- The concrete Parisi suffix satisfies the fourth-order regularity and
bounded-derivative hypotheses of the variance-response formulas (14.209)-(14.211).
These properties are derived from the recursion rather than assumed. -/
theorem parisiQSuffix_spatial_regular_four (ξ : ℝ → ℝ) (h : ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (r : Fin (k + 1)) :
    ContDiff ℝ 4 (parisiQSuffix ξ h ms qs r) ∧
      ∃ C : ℝ, ∀ j ∈ Finset.Icc 1 4, ∀ x, |iteratedDeriv j (parisiQSuffix ξ h ms qs r) x| ≤ C :=
  coleHopfIterate_spatial_regular_four (parisiQSuffixMasses ms r) (parisiQSuffixVars ξ qs r)
    (contDiff_parisiLogCoshTerminal h 4) (exists_bound_iteratedDeriv_parisiLogCoshTerminal_four h)

end SpinGlass
