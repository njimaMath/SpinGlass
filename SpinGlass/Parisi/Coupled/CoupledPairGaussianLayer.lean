import SpinGlass.Parisi.Coupled.CoupledCanonicalGaussianColumns

/-!
# Gaussian integral representations of actual paired layers

Common, antisymmetric and independent Cole-Hopf layers use their concrete
two-coordinate Gaussian laws. The positive-mass exponential identity and
the genuine mass-zero expectation identity provide the one-layer bridges
for the finite cascade recursion transport.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

theorem PairUnitLipschitz.continuous_uncurry {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) :
    Continuous (Function.uncurry F) := by
  have hl : LipschitzWith 2 (Function.uncurry F) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change |F p.1 p.2 - F q.1 q.2| ≤ (2 : ℝ) * dist p q
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    have hh := hF q.1 q.2 p.1 p.2
    linarith [le_max_left |p.1 - q.1| |p.2 - q.2|,
      le_max_right |p.1 - q.1| |p.2 - q.2|]
  exact hl.continuous

theorem PairUnitLipschitz.abs_shift_le {F : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (x y : ℝ) (z : ℝ × ℝ) :
    |F (x + z.1) (y + z.2)| ≤ |F x y| + 2 * ‖z‖ := by
  have hh := hF x y (x + z.1) (y + z.2)
  simp only [add_sub_cancel_left] at hh
  have hfst : |z.1| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le z
  have hsnd : |z.2| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le z
  have htriangle : |F (x + z.1) (y + z.2)| ≤
      |F x y| + |F (x + z.1) (y + z.2) - F x y| := by
    calc
      _ = |F x y + (F (x + z.1) (y + z.2) - F x y)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  linarith

theorem PairUnitLipschitz.integrable_shift_gaussian_prod {F : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (v : ℝ≥0) (x y : ℝ) :
    Integrable (fun z : ℝ × ℝ => F (x + z.1) (y + z.2))
      ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
  have hm : Measurable (fun z : ℝ × ℝ => F (x + z.1) (y + z.2)) :=
    (hF.continuous_uncurry.comp
      (show Continuous (fun z : ℝ × ℝ => (x + z.1, y + z.2)) by fun_prop)).measurable
  apply IsGaussian.integrable_of_abs_le_mul_one_add_norm_pow hm
    (C := |F x y| + 2) (m := 1) (by positivity)
  intro z
  have hh := hF.abs_shift_le x y z
  simp only [pow_one]
  nlinarith [norm_nonneg z, abs_nonneg (F x y)]

theorem PairUnitLipschitz.integrable_exp_shift_gaussian_prod {F : ℝ → ℝ → ℝ}
    (hF : PairUnitLipschitz F) (m : ℝ) (v : ℝ≥0) (x y : ℝ) :
    Integrable (fun z : ℝ × ℝ => Real.exp (m * F (x + z.1) (y + z.2)))
      ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
  have hm : Measurable (fun z : ℝ × ℝ => Real.exp (m * F (x + z.1) (y + z.2))) :=
    (hF.continuous_uncurry.comp
      (show Continuous (fun z : ℝ × ℝ => (x + z.1, y + z.2)) by fun_prop)).measurable.const_mul m |>.exp
  apply ((IsGaussian.integrable_exp_mul_norm
    (μ := (gaussianReal 0 v).prod (gaussianReal 0 v)) (2 * |m|)).const_mul
      (Real.exp (|m| * |F x y|))).mono' hm.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hh := mul_le_mul_of_nonneg_left (hF.abs_shift_le x y z) (abs_nonneg m)
  have hmF : m * F (x + z.1) (y + z.2) ≤ |m| * |F (x + z.1) (y + z.2)| := by
    simpa only [abs_mul] using le_abs_self (m * F (x + z.1) (y + z.2))
  nlinarith

theorem integral_pi_gaussianReal_two_eq_prod (v : ℝ≥0) (f : ℝ × ℝ → ℝ) :
    (∫ z : Fin 2 → ℝ, f (z 0, z 1) ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 v)) =
      ∫ z, f z ∂(gaussianReal 0 v).prod (gaussianReal 0 v) := by
  exact (measurePreserving_piFinTwo (fun _ : Fin 2 => gaussianReal 0 v)).integral_comp' f

theorem integral_pi_gaussianReal_two_apply (v : ℝ≥0) (i : Fin 2)
    {f : ℝ → ℝ} (hf : Measurable f) :
    (∫ z : Fin 2 → ℝ, f (z i) ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 v)) =
      ∫ z, f z ∂gaussianReal 0 v := by
  have hmap := (measurePreserving_eval (μ := fun _ : Fin 2 => gaussianReal 0 v) i).map_eq
  calc
    _ = ∫ z, f z ∂(Measure.pi (fun _ : Fin 2 => gaussianReal 0 v)).map (Function.eval i) :=
      (integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by rw [hmap]

def PairColeHopfKind.gaussianFactor : PairColeHopfKind → Fin 2 → Fin 2 → ℝ
  | .independent => couplingFactorSgn 1 0 0
  | .common => couplingFactorSgn 1 1 0
  | .antisymmetric => couplingFactorSgn (-1) 1 0

def pairGaussianShift (kind : PairColeHopfKind) (z : Fin 2 → ℝ) : ℝ × ℝ :=
  match kind with
  | .independent => (z 0, z 1)
  | .common => (z 0, z 0)
  | .antisymmetric => (z 0, -z 0)

theorem pairGaussianShift_eq_factor (kind : PairColeHopfKind) (z : Fin 2 → ℝ) :
    pairGaussianShift kind z =
      (∑ j, kind.gaussianFactor 0 j * z j, ∑ j, kind.gaussianFactor 1 j * z j) := by
  cases kind <;>
    simp [pairGaussianShift, PairColeHopfKind.gaussianFactor, couplingFactorSgn, Fin.sum_univ_two]

theorem ParisiCanonicalPiece.gaussianFactor_eq_kind {k : ℕ} (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (e : ParisiCanonicalPiece k) :
    e.gaussianFactor negative r p = (e.kind negative r p).gaussianFactor := rfl

/-- The exact positive-mass exponential identity for all three actual
two-coordinate Gaussian layers, as used in the finite paired cascade. -/
theorem exp_mul_pairColeHopfOperator_eq_gaussian_integral
    {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) (p : PairColeHopfLevel)
    (hm : p.mass ≠ 0) (x y : ℝ) :
    Real.exp (p.mass * pairColeHopfOperator p F x y) =
      ∫ z : Fin 2 → ℝ,
        Real.exp (p.mass * F (x + (pairGaussianShift p.kind z).1)
          (y + (pairGaussianShift p.kind z).2))
        ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 p.variance) := by
  cases hk : p.kind with
  | independent =>
    simp only [pairColeHopfOperator, hk, pairGaussianShift]
    rw [integral_pi_gaussianReal_two_eq_prod p.variance
        (fun z : ℝ × ℝ => Real.exp (p.mass * F (x + z.1) (y + z.2))),
      integral_prod _ (hF.integrable_exp_shift_gaussian_prod p.mass p.variance x y)]
    exact exp_mul_independentPairColeHopf hF hm p.variance x y
  | common =>
    simp only [pairColeHopfOperator, hk, pairGaussianShift]
    have hmF : Measurable (fun z => Real.exp (p.mass * F (x + z) (y + z))) :=
      (hF.continuous_uncurry.comp
        (show Continuous (fun z : ℝ => (x + z, y + z)) by fun_prop)).measurable.const_mul p.mass |>.exp
    rw [integral_pi_gaussianReal_two_apply p.variance 0 hmF]
    simpa only [one_mul] using exp_mul_correlatedPairColeHopf hF
      (η := 1) (by norm_num) hm p.variance x y
  | antisymmetric =>
    simp only [pairColeHopfOperator, hk, pairGaussianShift]
    have hmF : Measurable (fun z => Real.exp (p.mass * F (x + z) (y + -z))) :=
      (hF.continuous_uncurry.comp
        (show Continuous (fun z : ℝ => (x + z, y + -z)) by fun_prop)).measurable.const_mul p.mass |>.exp
    rw [integral_pi_gaussianReal_two_apply p.variance 0 hmF]
    simpa only [neg_one_mul] using exp_mul_correlatedPairColeHopf hF
      (η := -1) (by norm_num) hm p.variance x y

/-- The mass-zero layer is its actual Gaussian expectation.
This identity never applies the positive-mass cascade at zero. -/
theorem pairColeHopfOperator_zero_eq_gaussian_integral
    {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) (p : PairColeHopfLevel)
    (hm : p.mass = 0) (x y : ℝ) :
    pairColeHopfOperator p F x y =
      ∫ z : Fin 2 → ℝ, F (x + (pairGaussianShift p.kind z).1)
        (y + (pairGaussianShift p.kind z).2)
        ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 p.variance) := by
  cases hk : p.kind with
  | independent =>
    simp only [pairColeHopfOperator, hk, hm, pairGaussianShift]
    rw [integral_pi_gaussianReal_two_eq_prod p.variance
        (fun z : ℝ × ℝ => F (x + z.1) (y + z.2)),
      integral_prod _ (hF.integrable_shift_gaussian_prod p.variance x y)]
    exact independentPairColeHopf_zero p.variance F x y
  | common =>
    simp only [pairColeHopfOperator, hk, hm, correlatedPairColeHopf, coleHopf_zero,
      zero_add, one_mul, pairGaussianShift]
    have hmF : Measurable (fun z => F (x + z) (y + z)) :=
      (hF.continuous_uncurry.comp
        (show Continuous (fun z : ℝ => (x + z, y + z)) by fun_prop)).measurable
    exact (integral_pi_gaussianReal_two_apply p.variance 0 hmF).symm
  | antisymmetric =>
    simp only [pairColeHopfOperator, hk, hm, correlatedPairColeHopf, coleHopf_zero,
      zero_add, neg_one_mul, pairGaussianShift]
    have hmF : Measurable (fun z => F (x + z) (y + -z)) :=
      (hF.continuous_uncurry.comp
        (show Continuous (fun z : ℝ => (x + z, y + -z)) by fun_prop)).measurable
    exact (integral_pi_gaussianReal_two_apply p.variance 0 hmF).symm

theorem integrable_exp_mul_pairGaussianShift
    {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) (p : PairColeHopfLevel)
    (hm : p.mass ≠ 0) (x y : ℝ) :
    Integrable (fun z : Fin 2 → ℝ =>
      Real.exp (p.mass * F (x + (pairGaussianShift p.kind z).1)
        (y + (pairGaussianShift p.kind z).2)))
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 p.variance)) := by
  apply Integrable.of_integral_ne_zero
  rw [← exp_mul_pairColeHopfOperator_eq_gaussian_integral hF p hm x y]
  exact Real.exp_ne_zero _

/-- The positive-mass paired Gaussian layer in the ENNReal form
used by the actual cascade recursion. -/
theorem lintegral_exp_mul_pairGaussianShift
    {F : ℝ → ℝ → ℝ} (hF : PairUnitLipschitz F) (p : PairColeHopfLevel)
    (hm : p.mass ≠ 0) (x y : ℝ) :
    (∫⁻ z : Fin 2 → ℝ,
      ENNReal.ofReal (Real.exp (p.mass * F (x + (pairGaussianShift p.kind z).1)
        (y + (pairGaussianShift p.kind z).2)))
      ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 p.variance)) =
      ENNReal.ofReal (Real.exp (p.mass * pairColeHopfOperator p F x y)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_mul_pairGaussianShift hF p hm x y)
    (.of_forall fun z => (Real.exp_pos _).le)]
  rw [← exp_mul_pairColeHopfOperator_eq_gaussian_integral hF p hm x y]

end SpinGlass
