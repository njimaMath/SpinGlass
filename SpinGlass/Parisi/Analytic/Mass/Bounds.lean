import SpinGlass.Parisi.Analytic.Mass.Derivatives

/-!
# Uniform bounds for the logarithmic Laplace layer

A common centered exponential envelope controls the tilted moments, the first
and second mass derivatives, and the centered value. The estimates include zero
mass and provide the single-layer analytic input for the bounds around (14.265).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped BigOperators ENNReal NNReal

namespace SpinGlass.Aristotle

noncomputable section

/-- Tilted polynomial moments are controlled by a nonnegative envelope, uniformly for
masses in `[0, 1]`. -/
theorem abs_tiltedMean_pow_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : ∀ᵐ ω ∂μ, |X ω| ≤ Y ω)
    (hint : Integrable (fun ω => Real.exp (2 * Y ω)) μ) {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (k : ℕ) :
    |tiltedMean μ X (fun ω => X ω ^ k) m| ≤
      (∫ ω, Y ω ^ k * Real.exp (Y ω) ∂μ) / ∫ ω, Real.exp (-Y ω) ∂μ := by
  obtain ⟨hm0, hm1⟩ := hm
  have hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω := hXY.mono fun ω h => (abs_nonneg _).trans h
  have iY : ∀ j : ℕ, Integrable (fun ω => Y ω ^ j * Real.exp (Y ω)) μ := fun j => by
    refine (hint.const_mul (j.factorial : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [hY0] with ω hω
    have h := Real.pow_div_factorial_le_exp (Y ω) hω j
    rw [div_le_iff₀ (by positivity)] at h
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity),
      show 2 * Y ω = Y ω + Y ω by ring, Real.exp_add]
    calc Y ω ^ j * Real.exp (Y ω) ≤ Real.exp (Y ω) * j.factorial * Real.exp (Y ω) := by gcongr
      _ = _ := by ring
  have ieY : Integrable (fun ω => Real.exp (-Y ω)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [hY0] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hle : ∀ᵐ ω ∂μ, m * X ω ≤ Y ω ∧ -Y ω ≤ m * X ω := by
    filter_upwards [hXY, hY0] with ω h h0
    have h1 : |m * X ω| ≤ Y ω := by
      rw [abs_mul, abs_of_nonneg hm0]
      nlinarith [abs_nonneg (X ω)]
    exact ⟨(le_abs_self _).trans h1, by linarith [neg_abs_le (m * X ω)]⟩
  have hbound : ∀ᵐ ω ∂μ, ‖X ω ^ k * Real.exp (m * X ω)‖ ≤ Y ω ^ k * Real.exp (Y ω) := by
    filter_upwards [hXY, hle] with ω h h'
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h k) (Real.exp_le_exp.2 h'.1)
      (Real.exp_pos _).le (pow_nonneg ((abs_nonneg _).trans h) k)
  have iN : Integrable (fun ω => X ω ^ k * Real.exp (m * X ω)) μ :=
    (iY k).mono' (by fun_prop) hbound
  have iZ : Integrable (fun ω => Real.exp (m * X ω)) μ := by
    refine (iY 0).mono' (by fun_prop) ?_
    filter_upwards [hle] with ω h
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_zero, one_mul]
    exact Real.exp_le_exp.2 h.1
  have hZ : ∫ ω, Real.exp (-Y ω) ∂μ ≤ ∫ ω, Real.exp (m * X ω) ∂μ :=
    integral_mono_ae ieY iZ (hle.mono fun ω h => Real.exp_le_exp.2 h.2)
  have hZ0 : 0 < ∫ ω, Real.exp (-Y ω) ∂μ := integral_exp_pos ieY
  have hN : |∫ ω, X ω ^ k * Real.exp (m * X ω) ∂μ| ≤ ∫ ω, Y ω ^ k * Real.exp (Y ω) ∂μ :=
    abs_integral_le_integral_abs.trans (integral_mono_ae iN.abs (iY k) (hbound.mono
      fun ω h => by simpa [Real.norm_eq_abs] using h))
  rw [tiltedMean, abs_div, abs_of_pos (hZ0.trans_le hZ)]
  exact div_le_div₀ ((abs_nonneg _).trans hN) hN hZ0 hZ

/-- The second mass derivative of a layer is bounded by any bound on the tilted third cumulant
over `[0, 1]`, including at zero mass. -/
theorem abs_deriv_deriv_massTransform_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hXY : ∀ᵐ ω ∂μ, |X ω| ≤ Y ω)
    (hint : Integrable (fun ω => Real.exp (2 * Y ω)) μ) {K : ℝ}
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, |tiltedMean μ X (fun ω => X ω ^ 3) t -
        3 * tiltedMean μ X (fun ω => X ω ^ 2) t * tiltedMean μ X X t +
        2 * tiltedMean μ X X t ^ 3| ≤ K)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1) :
    |deriv (deriv (massTransform μ X)) m| ≤ K := by
  have hint2 : Integrable (fun ω => Real.exp (2 * |X ω|)) μ := by
    refine hint.mono' (by fun_prop) ?_
    filter_upwards [hXY] with ω h
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 ⟨le_rfl, zero_le_one⟩)
  have hana := analyticOnNhd_massTransform hX hint2
  have hgc : ContinuousOn (deriv (deriv (massTransform μ X))) (Ioo (-2) 2) :=
    hana.deriv.deriv.continuousOn
  have hpos : ∀ m ∈ Ioc (0 : ℝ) 1, |deriv (deriv (massTransform μ X)) m| ≤ K := by
    rintro m ⟨hm0, hm1⟩
    have hm2 : |m| < 2 := by rw [abs_of_pos hm0]; linarith
    rw [(hasDerivAt_massTransform_deriv hX hm2 hm0.ne' hint2).deriv]
    set φ : ℝ → ℝ := fun t => t ^ 2 * (tiltedMean μ X (fun ω => X ω ^ 2) t -
      tiltedMean μ X X t ^ 2) - 2 * t * tiltedMean μ X X t + 2 * logLaplace μ X t
    have hφ : ∀ t, |t| < 2 → HasDerivAt φ (t ^ 2 * (tiltedMean μ X (fun ω => X ω ^ 3) t -
        3 * tiltedMean μ X (fun ω => X ω ^ 2) t * tiltedMean μ X X t +
        2 * tiltedMean μ X X t ^ 3)) t := by
      intro t ht
      have h1 := hasDerivAt_tiltedVariance hX ht hint2
      have h2 := hasDerivAt_tiltedMean_self hX ht hint2
      have h3 := hasDerivAt_logLaplace hX ht hint2
      convert! (((hasDerivAt_pow 2 t).mul h1).sub (((hasDerivAt_id t).const_mul 2).mul h2)).add
        (h3.const_mul 2) using 1
      simp only [id, Nat.cast_ofNat]; ring
    have hφ0 : φ 0 = 0 := by simp [φ, logLaplace]
    have hmvt := (convex_Icc 0 m).norm_image_sub_le_of_norm_hasDerivWithin_le (f := φ)
      (C := K * m ^ 2) (fun t ht => (hφ t (by
        rw [abs_of_nonneg ht.1]; linarith [ht.2])).hasDerivWithinAt) (fun t ht => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg t), mul_comm]
        exact mul_le_mul (hK t ⟨ht.1, ht.2.trans hm1⟩) (pow_le_pow_left₀ ht.1 ht.2 2)
          (sq_nonneg _) hK0) ⟨le_rfl, hm0.le⟩ ⟨hm0.le, le_rfl⟩
    rw [hφ0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hm0] at hmvt
    have e : (tiltedMean μ X (fun ω => X ω ^ 2) m - tiltedMean μ X X m ^ 2) / m -
        2 * tiltedMean μ X X m / m ^ 2 + 2 * logLaplace μ X m / m ^ 3 = φ m / m ^ 3 := by
      simp only [φ]; field_simp
    rw [e, abs_div, abs_of_pos (pow_pos hm0 3), div_le_iff₀ (pow_pos hm0 3)]
    linarith
  rcases eq_or_lt_of_le hm.1 with rfl | hm0
  · have hc : ContinuousAt (deriv (deriv (massTransform μ X))) 0 :=
      hgc.continuousAt (Ioo_mem_nhds (by norm_num) (by norm_num))
    have ht : Tendsto (fun t => |deriv (deriv (massTransform μ X)) t|) (𝓝[>] (0 : ℝ))
        (𝓝 |deriv (deriv (massTransform μ X)) 0|) :=
      hc.tendsto.abs.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
    exact hpos t ⟨ht.1, ht.2.le⟩
  · exact hpos m ⟨hm0, hm.2⟩

/-- Uniform mass Taylor constants from a common centered envelope, including mass
zero. The constant is independent of X and its additive center c. This is the
single-layer analytic input for the uniform bounds around (14.265). -/
theorem uniform_mass_second_derivative_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY : Measurable Y) (hYnonneg : ∀ᵐ ω ∂μ, 0 ≤ Y ω)
    (hint : Integrable (fun ω => Real.exp (2 * Y ω)) μ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (X : Ω → ℝ) (c : ℝ), Measurable X →
      (∀ᵐ ω ∂μ, |X ω - c| ≤ Y ω) →
      ContDiffOn ℝ 2 (massTransform μ X) (Icc (0 : ℝ) 1) ∧
        ∀ m ∈ Icc (0 : ℝ) 1, |deriv (deriv (massTransform μ X)) m| ≤ M := by
  set B : ℕ → ℝ := fun k => (∫ ω, Y ω ^ k * Real.exp (Y ω) ∂μ) / ∫ ω, Real.exp (-Y ω) ∂μ
  have hB0 : ∀ k, 0 ≤ B k := fun k => div_nonneg
    (integral_nonneg_of_ae (hYnonneg.mono fun ω h => by positivity))
    (integral_nonneg fun ω => (Real.exp_pos _).le)
  set K := B 3 + 3 * B 2 * B 1 + 2 * B 1 ^ 3
  have hK0 : 0 ≤ K := by have := hB0 1; have := hB0 2; have := hB0 3; positivity
  refine ⟨K + 1, by linarith, fun X c hX hXc => ?_⟩
  set X' : Ω → ℝ := fun ω => X ω - c
  have hX' : Measurable X' := hX.sub_const c
  have hint2 : Integrable (fun ω => Real.exp (2 * |X' ω|)) μ := by
    refine hint.mono' (by fun_prop) ?_
    filter_upwards [hXc] with ω h
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith)
  have hX'i : Integrable X' μ := by
    simpa using integrable_pow_mul_exp_of_exp_abs hX' (m := 0) (by norm_num) hint2 1
  have heq : EqOn (massTransform μ X) (fun m => massTransform μ X' m + c) (Ioo (-2) 2) := by
    intro m hm
    have := massTransform_add_const hX' hX'i
      (by simpa using integrable_pow_mul_exp_of_exp_abs hX' (abs_lt.2 hm) hint2 0) c
    simpa [X'] using this
  have hana := analyticOnNhd_massTransform hX' hint2
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-2) 2 := fun m hm => ⟨by linarith [hm.1], by linarith [hm.2]⟩
  refine ⟨((hana.contDiffOn_of_completeSpace.add contDiffOn_const).mono hsub).congr
    fun m hm => heq (hsub hm), fun m hm => ?_⟩
  have hev : massTransform μ X =ᶠ[𝓝 m] fun y => massTransform μ X' y + c :=
    heq.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds (hsub hm))
  have hd : deriv (massTransform μ X) =ᶠ[𝓝 m] deriv (massTransform μ X') := by
    filter_upwards [hev.eventuallyEq_nhds] with y hy
    rw [hy.deriv_eq, deriv_add_const]
  rw [hd.deriv_eq]
  refine (abs_deriv_deriv_massTransform_le (K := K) hX' hXc hint
    (fun t ht => ?_) hm).trans (by linarith)
  have hb := abs_tiltedMean_pow_le hX' hY hXc hint ht
  have h1 : |tiltedMean μ X' X' t| ≤ B 1 := by
    have := hb 1
    rwa [show (fun ω => X' ω ^ 1) = X' from funext fun ω => pow_one _] at this
  have h2 : |tiltedMean μ X' (fun ω => X' ω ^ 2) t| ≤ B 2 := hb 2
  have h3 : |tiltedMean μ X' (fun ω => X' ω ^ 3) t| ≤ B 3 := hb 3
  calc _ ≤ |tiltedMean μ X' (fun ω => X' ω ^ 3) t| +
        3 * |tiltedMean μ X' (fun ω => X' ω ^ 2) t| * |tiltedMean μ X' X' t| +
        2 * |tiltedMean μ X' X' t| ^ 3 := by
        refine (abs_add_le _ _).trans ?_
        refine add_le_add ((abs_sub _ _).trans ?_) ?_
        · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
        · rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ K := by
        have := abs_nonneg (tiltedMean μ X' X' t)
        have := abs_nonneg (tiltedMean μ X' (fun ω => X' ω ^ 2) t)
        simp only [K]
        gcongr

/-- A layer is nonexpansive for uniformly close inputs, including zero mass. -/
theorem abs_massTransform_sub_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X μ) (hYi : Integrable Y μ) {m c : ℝ}
    (hm : 0 ≤ m) (hc : 0 ≤ c)
    (hXe : Integrable (fun ω => Real.exp (m * X ω)) μ)
    (hYe : Integrable (fun ω => Real.exp (m * Y ω)) μ)
    (hclose : ∀ᵐ ω ∂μ, |X ω - Y ω| ≤ c) :
    |massTransform μ X m - massTransform μ Y m| ≤ c := by
  unfold massTransform
  split_ifs with hm0
  · rw [← integral_sub hXi hYi]
    refine abs_integral_le_integral_abs.trans ?_
    calc (∫ ω, |X ω - Y ω| ∂μ) ≤ ∫ _, c ∂μ :=
          integral_mono_ae (hXi.sub hYi).abs (integrable_const c) hclose
      _ = c := by simp
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  have key : ∀ X Y : Ω → ℝ, Integrable (fun ω => Real.exp (m * X ω)) μ →
      Integrable (fun ω => Real.exp (m * Y ω)) μ → (∀ᵐ ω ∂μ, X ω - Y ω ≤ c) →
      logLaplace μ X m / m - logLaplace μ Y m / m ≤ c := by
    intro X Y hXe hYe h
    have hXp := integral_exp_pos hXe
    have hYp := integral_exp_pos hYe
    rw [← sub_div, div_le_iff₀ hmpos, logLaplace, logLaplace, sub_le_iff_le_add,
      ← Real.log_exp (c * m), ← Real.log_mul (Real.exp_pos _).ne' hYp.ne']
    refine Real.log_le_log hXp ?_
    rw [← integral_const_mul]
    refine integral_mono_ae hXe (hYe.const_mul _) (h.mono fun ω hω => ?_)
    dsimp only
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  rw [abs_sub_le_iff]
  exact ⟨key X Y hXe hYe (hclose.mono fun ω h => (abs_le.1 h).2),
    key Y X hYe hXe (hclose.mono fun ω h => by linarith [(abs_le.1 h).1])⟩

/-- Uniform bounds on the first mass derivative and on the centred layer, for all inputs with
a common centred envelope, and masses in `[-2, 2]`. -/
theorem massTransform_deriv_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hint : ∀ k : ℝ, Integrable (fun ω => Real.exp (k * Y ω)) μ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (X : Ω → ℝ) (c : ℝ), Measurable X → (∀ ω, |X ω - c| ≤ Y ω) →
      (∀ b ∈ Ioo (-3 : ℝ) 3, DifferentiableAt ℝ (massTransform μ X) b) ∧
      (∀ b ∈ Icc (-2 : ℝ) 2, |deriv (massTransform μ X) b| ≤ M) ∧
      (∀ b ∈ Icc (-2 : ℝ) 2, |massTransform μ X b - c| ≤ M) := by
  have hYi1 : Integrable Y μ := (hint 1).mono' hY.aestronglyMeasurable (.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hY0 ω), one_mul]; linarith [Real.add_one_le_exp (Y ω)])
  have hYi2 : Integrable (fun ω => Y ω ^ 2) μ :=
    ((hint 1).const_mul 2).mono' (hY.pow_const 2).aestronglyMeasurable (.of_forall fun ω => by
      have := Real.pow_div_factorial_le_exp (Y ω) (hY0 ω) 2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul]
      norm_num [Nat.factorial] at this; linarith)
  have hexp : ∀ (X : Ω → ℝ) (c k : ℝ), Measurable X → (∀ ω, |X ω - c| ≤ 2 * Y ω) → 0 ≤ k →
      Integrable (fun ω => Real.exp (k * |X ω|)) μ := by
    intro X c k hX hXc hk
    refine ((hint (2 * k)).const_mul (Real.exp (k * |c|))).mono' (by fun_prop)
      (.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : |X ω| ≤ |c| + 2 * Y ω := by
      have := abs_sub_abs_le_abs_sub (X ω) c; linarith [hXc ω]
    nlinarith
  obtain ⟨M₁, hM₁, hunif⟩ := uniform_mass_second_derivative_bound (μ := μ)
    (Y := fun ω => 2 * Y ω) (hY.const_mul 2) (.of_forall fun ω => by linarith [hY0 ω])
    (by refine (hint 4).congr (.of_forall fun ω => ?_); simp only; ring_nf)
  set B₀ := ((∫ ω, (2 * Y ω) ^ 2 ∂μ) + (∫ ω, 2 * Y ω ∂μ) ^ 2) / 2
  have hB₀ : 0 ≤ B₀ := by
    have : 0 ≤ ∫ ω, (2 * Y ω) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    positivity
  have stepB : ∀ (X : Ω → ℝ) (c : ℝ), Measurable X → (∀ ω, |X ω - c| ≤ 2 * Y ω) →
      ∀ s ∈ Icc (0 : ℝ) 1, |deriv (massTransform μ X) s| ≤ B₀ + M₁ := by
    intro X c hX hXc s hs
    have hana := analyticOnNhd_massTransform hX (hexp X c 3 hX hXc (by norm_num))
    have h0 := hasDerivAt_massTransform_zero hX one_pos
      (by simpa using hexp X c 1 hX hXc (by norm_num))
    have hXi : ∀ j : ℕ, Integrable (fun ω => X ω ^ j) μ := fun j => by
      simpa using integrable_pow_mul_exp_of_exp_abs hX (m := 0) (a := 1) (by simp)
        (by simpa using hexp X c 1 hX hXc (by norm_num)) j
    have hX1 : Integrable X μ := by simpa using hXi 1
    have hb0 : |deriv (massTransform μ X) 0| ≤ B₀ := by
      rw [h0.deriv]
      have hsq : (fun ω => (X ω - c) ^ 2) = fun ω => X ω ^ 2 - 2 * c * X ω + c ^ 2 := by
        funext ω; ring
      have i1 : Integrable (fun ω => X ω ^ 2 - 2 * c * X ω) μ := (hXi 2).sub (hX1.const_mul _)
      have iZ2 : Integrable (fun ω => (X ω - c) ^ 2) μ := by
        rw [hsq]; exact i1.add (integrable_const _)
      have hZ2 : ∫ ω, (X ω - c) ^ 2 ∂μ = (∫ ω, X ω ^ 2 ∂μ) - 2 * c * (∫ ω, X ω ∂μ) + c ^ 2 := by
        rw [hsq, integral_add i1 (integrable_const _),
          integral_sub (hXi 2) (hX1.const_mul _), integral_const_mul, integral_const]
        simp
      have hZ1 : ∫ ω, (X ω - c) ∂μ = (∫ ω, X ω ∂μ) - c := by
        rw [integral_sub hX1 (integrable_const _), integral_const]; simp
      have hup : ∫ ω, (X ω - c) ^ 2 ∂μ ≤ ∫ ω, (2 * Y ω) ^ 2 ∂μ := by
        refine integral_mono iZ2
          ((hYi2.const_mul 4).congr (.of_forall fun ω => by simp only; ring)) fun ω => ?_
        have := hXc ω
        have h0 : 0 ≤ |X ω - c| := abs_nonneg _
        calc (X ω - c) ^ 2 = |X ω - c| ^ 2 := (sq_abs _).symm
          _ ≤ (2 * Y ω) ^ 2 := pow_le_pow_left₀ h0 this 2
      have hlow : 0 ≤ ∫ ω, (X ω - c) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
      have hZabs : |∫ ω, (X ω - c) ∂μ| ≤ ∫ ω, 2 * Y ω ∂μ :=
        (abs_integral_le_integral_abs).trans (integral_mono (hX1.sub (integrable_const c)).abs
          (hYi1.const_mul 2) fun ω => hXc ω)
      have hZsq : (∫ ω, (X ω - c) ∂μ) ^ 2 ≤ (∫ ω, 2 * Y ω ∂μ) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hZabs 2
      have hsq0 : 0 ≤ (∫ ω, (X ω - c) ∂μ) ^ 2 := sq_nonneg _
      have key : (∫ ω, X ω ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2 =
          (∫ ω, (X ω - c) ^ 2 ∂μ) - (∫ ω, (X ω - c) ∂μ) ^ 2 := by rw [hZ2, hZ1]; ring
      rw [key, abs_le]
      simp only [B₀]
      constructor <;> nlinarith
    have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
      (f := deriv (massTransform μ X)) (C := M₁)
      (fun u hu => (hana u ⟨by linarith [hu.1], by linarith [hu.2]⟩).deriv.differentiableAt)
      (fun u hu => by rw [Real.norm_eq_abs]; exact (hunif X c hX (.of_forall hXc)).2 u hu)
      ⟨le_rfl, zero_le_one⟩ hs
    simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1] at hmvt
    have := abs_sub_abs_le_abs_sub (deriv (massTransform μ X) s) (deriv (massTransform μ X) 0)
    nlinarith [hs.2]
  have stepC : ∀ (X : Ω → ℝ) (c : ℝ), Measurable X → (∀ ω, |X ω - c| ≤ 2 * Y ω) →
      ∀ s ∈ Icc (-1 : ℝ) 1, |deriv (massTransform μ X) s| ≤ B₀ + M₁ := by
    intro X c hX hXc s hs
    rcases le_total 0 s with h | h
    · exact stepB X c hX hXc s ⟨h, hs.2⟩
    · have hX' : Measurable (fun ω => -X ω) := hX.neg
      have hXc' : ∀ ω, |-X ω - -c| ≤ 2 * Y ω := fun ω => by
        rw [show -X ω - -c = -(X ω - c) by ring, abs_neg]; exact hXc ω
      have hana := analyticOnNhd_massTransform hX' (hexp _ _ 3 hX' hXc' (by norm_num))
      have hd : HasDerivAt (fun s => -massTransform μ (fun ω => -X ω) (-s))
          (deriv (massTransform μ (fun ω => -X ω)) (-s)) s := by
        have := (((hana (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩).differentiableAt
          |>.hasDerivAt).comp s (hasDerivAt_neg s)).neg
        convert! this using 1 <;> simp
      have hfun : massTransform μ X = fun s => -massTransform μ (fun ω => -X ω) (-s) :=
        funext (massTransform_neg_mass μ X)
      rw [hfun, hd.deriv]
      exact stepB _ _ hX' hXc' (-s) ⟨by linarith, by linarith [hs.1]⟩
  set M := (B₀ + M₁) / 4 + (B₀ + M₁) / 2 + ∫ ω, Y ω ∂μ
  have hYint0 : 0 ≤ ∫ ω, Y ω ∂μ := integral_nonneg hY0
  refine ⟨M, by positivity, fun X c hX hXc => ?_⟩
  have hXc2 : ∀ ω, |X ω - c| ≤ 2 * Y ω := fun ω => by linarith [hXc ω, hY0 ω]
  have hana := analyticOnNhd_massTransform hX (hexp X c 3 hX hXc2 (by norm_num))
  have hdiff : ∀ b ∈ Ioo (-3 : ℝ) 3, DifferentiableAt ℝ (massTransform μ X) b :=
    fun b hb => (hana b hb).differentiableAt
  have hderiv : ∀ b ∈ Icc (-2 : ℝ) 2, |deriv (massTransform μ X) b| ≤ (B₀ + M₁) / 4 := by
    intro b hb
    have h2X : Measurable (fun ω => 2 * X ω) := hX.const_mul 2
    have h2Xc : ∀ ω, |2 * X ω - 2 * c| ≤ 2 * Y ω := fun ω => by
      rw [show 2 * X ω - 2 * c = 2 * (X ω - c) by ring, abs_mul, abs_two]
      linarith [hXc ω]
    have hana2 := analyticOnNhd_massTransform h2X (hexp _ _ 3 h2X h2Xc (by norm_num))
    have hd : HasDerivAt (fun b => massTransform μ (fun ω => 2 * X ω) (b / 2) / 2)
        (deriv (massTransform μ (fun ω => 2 * X ω)) (b / 2) / 4) b := by
      have := ((((hana2 (b / 2) ⟨by linarith [hb.1], by linarith [hb.2]⟩).differentiableAt
        |>.hasDerivAt).comp b ((hasDerivAt_id b).div_const 2)).div_const 2)
      convert! this using 1; simp; ring
    have hfun : massTransform μ X = fun b => massTransform μ (fun ω => 2 * X ω) (b / 2) / 2 :=
      funext (massTransform_scale_two μ X)
    rw [hfun, hd.deriv, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact div_le_div_of_nonneg_right (stepC _ _ h2X h2Xc (b / 2)
      ⟨by linarith [hb.1], by linarith [hb.2]⟩) (by norm_num)
  have hB : 0 ≤ (B₀ + M₁) / 4 := by positivity
  refine ⟨hdiff, fun b hb => (hderiv b hb).trans (by simp only [M]; linarith), fun b hb => ?_⟩
  have hmvt := (convex_Icc (-2 : ℝ) 2).norm_image_sub_le_of_norm_deriv_le
    (f := massTransform μ X) (C := (B₀ + M₁) / 4) (x := 0)
    (fun u hu => hdiff u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (fun u hu => by rw [Real.norm_eq_abs]; exact hderiv u hu) ⟨by norm_num, by norm_num⟩ hb
  simp only [Real.norm_eq_abs, sub_zero] at hmvt
  have h0 : massTransform μ X 0 = ∫ ω, X ω ∂μ := by simp [massTransform]
  have hX1 : Integrable X μ := by
    simpa using integrable_pow_mul_exp_of_exp_abs hX (m := 0) (a := 1) (by simp)
      (by simpa using hexp X c 1 hX hXc2 (by norm_num)) 1
  have hc : |massTransform μ X 0 - c| ≤ ∫ ω, Y ω ∂μ := by
    rw [h0, show (∫ ω, X ω ∂μ) - c = ∫ ω, (X ω - c) ∂μ by
      rw [integral_sub hX1 (integrable_const c), integral_const]; simp]
    exact (abs_integral_le_integral_abs).trans (integral_mono (hX1.sub (integrable_const c)).abs
      hYi1 fun ω => hXc ω)
  have hbabs : |b| ≤ 2 := abs_le.2 ⟨hb.1, hb.2⟩
  calc |massTransform μ X b - c|
      ≤ |massTransform μ X b - massTransform μ X 0| + |massTransform μ X 0 - c| := by
        have := abs_sub_le (massTransform μ X b) (massTransform μ X 0) c; linarith
    _ ≤ (B₀ + M₁) / 4 * |b| + ∫ ω, Y ω ∂μ := add_le_add hmvt hc
    _ ≤ M := by simp only [M]; nlinarith

end

end SpinGlass.Aristotle
