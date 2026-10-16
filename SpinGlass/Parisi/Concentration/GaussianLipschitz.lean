import Common.Mathlib.Probability.Distributions.Gaussian_Concentration
import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateCovariance
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Gaussian concentration for finite-dimensional Lipschitz observables

The logarithmic tilted mass is controlled by a deterministic Lipschitz
estimate. Smooth convolution preserves that constant, and Fatou's lemma
passes the Gaussian exponential bound to the original observable.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Convolution

namespace SpinGlass

/-- A fixed sub-Gaussian parameter is preserved under almost everywhere
convergence. Integrability of the limiting exponential follows from Fatou. -/
theorem hasSubgaussianMGF_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {Xn : ℕ → Ω → ℝ} {c : ℝ≥0}
    (hX : AEStronglyMeasurable X μ) (hn : ∀ n, HasSubgaussianMGF (Xn n) c μ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Xn n ω) atTop (𝓝 (X ω))) :
    HasSubgaussianMGF X c μ := by
  have hbound (s : ℝ) :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (s * X ω)) ∂μ) ≤
        ENNReal.ofReal (Real.exp (c * s ^ 2 / 2)) := by
    have heq : (fun ω => ENNReal.ofReal (Real.exp (s * X ω))) =ᵐ[μ]
        fun ω => liminf (fun n => ENNReal.ofReal (Real.exp (s * Xn n ω))) atTop := by
      filter_upwards [hlim] with ω hω
      exact ((ENNReal.continuous_ofReal.tendsto _).comp
        ((Real.continuous_exp.tendsto _).comp (tendsto_const_nhds.mul hω))).liminf_eq.symm
    rw [lintegral_congr_ae heq]
    refine (lintegral_liminf_le' (fun n =>
      ((hn n).integrable_exp_mul s).aemeasurable.ennreal_ofReal)).trans ?_
    apply liminf_le_of_frequently_le'
    apply Filter.Eventually.frequently
    filter_upwards [] with n
    rw [← ofReal_integral_eq_lintegral_ofReal ((hn n).integrable_exp_mul s)
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal ((hn n).mgf_le s)
  have hint (s : ℝ) : Integrable (fun ω => Real.exp (s * X ω)) μ := by
    refine ⟨Real.continuous_exp.comp_aestronglyMeasurable (hX.const_mul s), ?_⟩
    exact (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)).2
      ((hbound s).trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hint, fun s => ?_⟩
  have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound s)
  rw [← ofReal_integral_eq_lintegral_ofReal (hint s)
    (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg fun _ => Real.exp_nonneg _),
    ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hb
  exact hb

/-- Averaging translations against a normalized nonnegative bump preserves
the Lipschitz constant, including constant functions. -/
theorem lipschitzWith_normed_bump_convolution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ρ : Measure E) [ρ.IsAddHaarMeasure] (φ : ContDiffBump (0 : E))
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (φ.normed ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ρ] f) := by
  have hi : ConvolutionExists (φ.normed ρ) f (ContinuousLinearMap.lsmul ℝ ℝ) ρ :=
    φ.hasCompactSupport_normed.convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.continuous_normed
      (hf.continuous.locallyIntegrable (μ := ρ))
  change ∀ x, Integrable (fun z => φ.normed ρ z * f (x - z)) ρ at hi
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  change |(∫ z, φ.normed ρ z * f (x - z) ∂ρ) -
    ∫ z, φ.normed ρ z * f (y - z) ∂ρ| ≤ L * dist x y
  rw [← integral_sub (hi x) (hi y)]
  calc
    |∫ z, φ.normed ρ z * f (x - z) - φ.normed ρ z * f (y - z) ∂ρ|
        ≤ ∫ z, |φ.normed ρ z * f (x - z) - φ.normed ρ z * f (y - z)| ∂ρ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, φ.normed ρ z * (L * dist x y) ∂ρ := by
      apply integral_mono ((hi x).sub (hi y)).abs (φ.integrable_normed.mul_const _)
      intro z
      dsimp only [Pi.sub_apply]
      rw [← mul_sub, abs_mul, abs_of_nonneg (φ.nonneg_normed z)]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed z)
      simpa only [← Real.dist_eq, dist_sub_right] using hf.dist_le_mul (x - z) (y - z)
    _ = L * dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]

/-- The Gaussian concentration theorem for a Lipschitz functional on a
finite-dimensional Hilbert space. No derivative of the observable is assumed. -/
theorem hasSubgaussianMGF_gaussian_sub_integral_of_lipschitz
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {ν : Measure H} [IsGaussian ν] (hmean : (∫ x : H, x ∂ν) = 0)
    {f : H → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂ν)
      (‖covarianceOperator ν‖ * (L : ℝ) ^ 2).toNNReal ν := by
  let ρ : Measure H := Measure.addHaar
  let φ (n : ℕ) : ContDiffBump (0 : H) :=
    ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1),
      half_pos (by positivity), half_lt_self (by positivity)⟩
  let g (n : ℕ) : H → ℝ := φ n |>.normed ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, ρ] f
  let F (n : ℕ) (x : H) : ℝ := g n x - g n 0
  have hgLip (n : ℕ) : LipschitzWith L (g n) :=
    lipschitzWith_normed_bump_convolution ρ (φ n) hf
  have hgSmooth (n : ℕ) : ContDiff ℝ 1 (g n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _
      (φ n).contDiff_normed (hf.continuous.locallyIntegrable (μ := ρ))
  have hFLip (n : ℕ) : LipschitzWith L (F n) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [F, dist_sub_right] using (hgLip n).dist_le_mul x y
  have hFSmooth (n : ℕ) : ContDiff ℝ 1 (F n) := (hgSmooth n).sub contDiff_const
  have hgLim (x : H) : Tendsto (fun n => g n x) atTop (𝓝 (f x)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous
      tendsto_one_div_add_atTop_nhds_zero_nat hf.continuous x
  have hFLim (x : H) : Tendsto (fun n => F n x) atTop (𝓝 (f x - f 0)) :=
    (hgLim x).sub (hgLim 0)
  have hnorm : Integrable (fun x : H => (L : ℝ) * ‖x‖) ν :=
    (IsGaussian.integrable_id (μ := ν)).norm.const_mul L
  have hFbound (n : ℕ) (x : H) : ‖F n x‖ ≤ (L : ℝ) * ‖x‖ := by
    simpa only [F, Real.norm_eq_abs, Real.dist_eq, dist_zero_right] using
      (hgLip n).dist_le_mul x 0
  have hfint : Integrable f ν := by
    apply (hnorm.add (integrable_const ‖f 0‖)).mono' hf.continuous.aestronglyMeasurable
    filter_upwards [] with x
    have hb := hf.dist_le_mul x 0
    rw [Real.dist_eq, dist_zero_right] at hb
    calc
      ‖f x‖ ≤ ‖f x - f 0‖ + ‖f 0‖ := norm_le_norm_sub_add _ _
      _ ≤ (L : ℝ) * ‖x‖ + ‖f 0‖ := by
        exact add_le_add (by simpa only [Real.norm_eq_abs] using hb) le_rfl
  have hmeanLim : Tendsto (fun n => ∫ x, F n x ∂ν) atTop
      (𝓝 (∫ x, f x ∂ν - f 0)) := by
    have hh := tendsto_integral_of_dominated_convergence _
      (fun n => (hFLip n).continuous.aestronglyMeasurable) hnorm
      (fun n => Filter.Eventually.of_forall (hFbound n))
      (Filter.Eventually.of_forall hFLim)
    simpa only [integral_sub hfint (integrable_const _), integral_const,
      probReal_univ, one_smul] using hh
  apply hasSubgaussianMGF_of_ae_tendsto
    (X := fun x => f x - ∫ y, f y ∂ν)
    (Xn := fun n x => F n x - ∫ y, F n y ∂ν)
    (hf.continuous.sub continuous_const).aestronglyMeasurable
  · intro n
    exact IsGaussian.hasSubgaussianMGF_sub_integral_of_norm_fderiv_le hmean
      (hFSmooth n) (fun _ => norm_fderiv_le_of_lipschitz ℝ (hFLip n))
  · filter_upwards [] with x
    have he : (f x - f 0) - ((∫ y, f y ∂ν) - f 0) = f x - ∫ y, f y ∂ν := by ring
    simpa only [he] using (hFLim x).sub hmeanLim

/-- Increasing the variance proxy preserves an exponential-moment bound. -/
theorem hasSubgaussianMGF_mono {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {c d : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hcd : c ≤ d) : HasSubgaussianMGF X d μ := by
  refine ⟨h.integrable_exp_mul, fun s => (h.mgf_le s).trans ?_⟩
  apply Real.exp_le_exp.2
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcd) (sq_nonneg s)) (by norm_num)

/-- The dimension-free standard Gaussian form, also valid on the zero
space. The variance proxy is exactly the square of the Lipschitz constant. -/
theorem hasSubgaussianMGF_stdGaussian_sub_integral_of_lipschitz
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {f : H → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂stdGaussian H)
      (L ^ 2) (stdGaussian H) := by
  have hcov : covarianceOperator (stdGaussian H) = ContinuousLinearMap.id ℝ H := by
    ext x
    apply ext_inner_right ℝ
    intro y
    rw [← covarianceBilin_eq_inner_covarianceOperator IsGaussian.memLp_two_id
      integral_id_stdGaussian, covarianceBilin_stdGaussian]
    rfl
  have h := hasSubgaussianMGF_gaussian_sub_integral_of_lipschitz integral_id_stdGaussian hf
  apply hasSubgaussianMGF_mono h
  rw [hcov]
  apply Real.toNNReal_le_iff_le_coe.2
  simpa only [NNReal.coe_pow, one_mul] using
    mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := H))
      (sq_nonneg (L : ℝ))

end SpinGlass
