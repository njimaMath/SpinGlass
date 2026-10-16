import SpinGlass.Parisi.Coupled.CoupledGaussianCorrelation
import SpinGlass.FiniteGibbs.GaussianFieldCoords
import Common.Mathlib.Probability.Distributions.Gaussian.MultivariateUniqueness
import Common.Mathlib.Probability.PointProcess.CascadeTiltMeasure

/-!
# Concrete Gaussian laws for the two root fields

Linear images of independent Gaussian marks are identified by their
actual covariance kernels. In particular, two independent branches above
a common root have the common/antisymmetric law used by the heat estimate.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs Aristotle.Heat

/-- The law of any finite linear Gaussian mark family is determined by
its explicit covariance sum, including degenerate variances. -/
theorem map_pi_gaussianReal_linear_eq_multivariateGaussian
    {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
    (A : ι → J → ℝ) (vs : J → ℝ≥0) :
    (Measure.pi (fun j => gaussianReal 0 (vs j))).map
      (fun z => WithLp.toLp 2 (fun i => ∑ j, A i j * z j)) =
      multivariateGaussian 0 (fun i l => ∑ j, (vs j : ℝ) * A i j * A l j) := by
  let G := GaussianField.ofCoords A vs (WithLp.toLp 2)
    (by fun_prop) (P := Measure.pi (fun j => gaussianReal 0 (vs j))) rfl
  have : IsGaussian ((Measure.pi (fun j => gaussianReal 0 (vs j))).map
      (fun z => WithLp.toLp 2 (fun i => ∑ j, A i j * z j))) := G.isGaussian
  exact IsGaussian.eq_multivariateGaussian_of_inner_covarianceOperator _ G.mean0 fun i l => by
    rw [← std_basis_eq_single, ← std_basis_eq_single]
    exact G.cov_eq i l

/-- Two Gaussian linear realizations with equal covariance sums have
exactly the same joint law. -/
theorem map_pi_gaussianReal_linear_eq_of_covariance
    {ι J K : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (A : ι → J → ℝ) (vs : J → ℝ≥0) (B : ι → K → ℝ) (ws : K → ℝ≥0)
    (hcov : ∀ i l, (∑ j, (vs j : ℝ) * A i j * A l j) =
      ∑ j, (ws j : ℝ) * B i j * B l j) :
    (Measure.pi (fun j => gaussianReal 0 (vs j))).map
      (fun z => WithLp.toLp 2 (fun i => ∑ j, A i j * z j)) =
    (Measure.pi (fun j => gaussianReal 0 (ws j))).map
      (fun z => WithLp.toLp 2 (fun i => ∑ j, B i j * z j)) := by
  rw [map_pi_gaussianReal_linear_eq_multivariateGaussian,
    map_pi_gaussianReal_linear_eq_multivariateGaussian]
  congr 1
  exact funext fun i => funext fun l => hcov i l

/-- A common Gaussian root and two independent tails have the same
law as a common mark plus or minus an independent antisymmetric mark. -/
theorem map_gaussian_common_independent_eq_antithetic (p q : ℝ≥0) :
    (Measure.pi (fun j : Fin 3 => gaussianReal 0 (![p, q, q] j))).map
      (fun z => WithLp.toLp 2 (![z 0 + z 1, z 0 + z 2])) =
    (Measure.pi (fun j : Fin 2 => gaussianReal 0 (![p + q / 2, q / 2] j))).map
      (fun z => WithLp.toLp 2 (![z 0 + z 1, z 0 - z 1])) := by
  let A : Fin 2 → Fin 3 → ℝ := ![![1, 1, 0], ![1, 0, 1]]
  let B : Fin 2 → Fin 2 → ℝ := ![![1, 1], ![1, -1]]
  have hcov : ∀ i l, (∑ j : Fin 3, (![p, q, q] j : ℝ) * A i j * A l j) =
      ∑ j : Fin 2, (![p + q / 2, q / 2] j : ℝ) * B i j * B l j := by
    intro i l
    fin_cases i <;> fin_cases l <;>
      simp [A, B, Fin.sum_univ_succ, NNReal.coe_add, NNReal.coe_div] <;> ring
  have hA : (fun z : Fin 3 → ℝ => WithLp.toLp 2 (fun i => ∑ j, A i j * z j)) =
      fun z => WithLp.toLp 2 (![z 0 + z 1, z 0 + z 2]) := by
    funext z
    ext i
    fin_cases i <;> simp [A, Fin.sum_univ_succ]
  have hB : (fun z : Fin 2 → ℝ => WithLp.toLp 2 (fun i => ∑ j, B i j * z j)) =
      fun z => WithLp.toLp 2 (![z 0 + z 1, z 0 - z 1]) := by
    funext z
    ext i
    fin_cases i <;> simp [B, Fin.sum_univ_succ, sub_eq_add_neg]
  have hh := map_pi_gaussianReal_linear_eq_of_covariance A ![p, q, q] B ![p + q / 2, q / 2] hcov
  rw [hA, hB] at hh
  exact hh

/-- The heat correlation agrees with the actual square of the
conditional response above a common root. This identifies the baseline
used when comparing nonnegative and signed root covariances. -/
theorem gaussianFixedVarianceCorrelation_eq_square_heat {f : ℝ → ℝ}
    (hc : Continuous f) {C : ℝ} (hb : ∀ y, |f y| ≤ C) (p q : ℝ≥0) (x : ℝ) :
    gaussianFixedVarianceCorrelation ((p : ℝ) + q) ((q : ℝ) / 2) f x =
      heat p (fun y => heat q f y ^ 2) x := by
  have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hb 0)
  have hprod : ∀ y z, |f y * f z| ≤ C ^ 2 := fun y z => by
    rw [abs_mul]
    simpa only [pow_two] using mul_le_mul (hb y) (hb z) (abs_nonneg _) hC
  let F := fun z : EuclideanSpace ℝ (Fin 2) => f (x + z 0) * f (x + z 1)
  have hFc : Continuous F := by dsimp [F]; fun_prop
  have hi := integral_map
    (μ := Measure.pi (fun j : Fin 3 => gaussianReal 0 (![p, q, q] j)))
    (f := F) (by fun_prop : Measurable fun z : Fin 3 → ℝ =>
      WithLp.toLp 2 (![z 0 + z 1, z 0 + z 2])).aemeasurable hFc.aestronglyMeasurable
  have hj := integral_map
    (μ := Measure.pi (fun j : Fin 2 => gaussianReal 0 (![p + q / 2, q / 2] j)))
    (f := F) (by fun_prop : Measurable fun z : Fin 2 → ℝ =>
      WithLp.toLp 2 (![z 0 + z 1, z 0 - z 1])).aemeasurable hFc.aestronglyMeasurable
  rw [map_gaussian_common_independent_eq_antithetic] at hi
  have heq : (∫ z : Fin 3 → ℝ, f (x + (z 0 + z 1)) * f (x + (z 0 + z 2))
      ∂Measure.pi (fun j => gaussianReal 0 (![p, q, q] j))) =
      ∫ z : Fin 2 → ℝ, f (x + (z 0 + z 1)) * f (x + (z 0 - z 1))
        ∂Measure.pi (fun j => gaussianReal 0 (![p + q / 2, q / 2] j)) := hi.symm.trans hj
  have hleft : (∫ z : Fin 3 → ℝ, f (x + (z 0 + z 1)) * f (x + (z 0 + z 2))
      ∂Measure.pi (fun j => gaussianReal 0 (![p, q, q] j))) =
      heat p (fun y => heat q f y ^ 2) x := by
    have hint : Integrable (fun z : Fin 3 → ℝ =>
        f (x + (z 0 + z 1)) * f (x + (z 0 + z 2)))
        (Measure.pi (fun j => gaussianReal 0 (![p, q, q] j))) :=
      Integrable.of_bound (by fun_prop) (C ^ 2)
        (.of_forall fun z => by rw [Real.norm_eq_abs]; exact hprod _ _)
    rw [integral_pi_fin_succ _ hint]
    have htail : Fin.tail (fun j : Fin 3 => gaussianReal 0 (![p, q, q] j)) =
        fun _ : Fin 2 => gaussianReal 0 q := by
      funext j
      fin_cases j <;> rfl
    rw [htail]
    simp only [Fin.cons_zero, Matrix.cons_val_zero]
    unfold heat
    simp only [Real.toNNReal_coe]
    apply integral_congr_ae
    exact .of_forall fun y => by
      have h := integral_fintype_prod_eq_prod (μ := fun _ : Fin 2 => gaussianReal 0 q)
        (fun _ : Fin 2 => fun z : ℝ => f (x + y + z))
      change (∫ zs : Fin 2 → ℝ, f (x + (y + zs 0)) * f (x + (y + zs 1))
        ∂Measure.pi (fun _ => gaussianReal 0 q)) = _
      simpa only [Fin.prod_univ_two, add_assoc, pow_two] using h
  have hright : (∫ z : Fin 2 → ℝ, f (x + (z 0 + z 1)) * f (x + (z 0 - z 1))
      ∂Measure.pi (fun j => gaussianReal 0 (![p + q / 2, q / 2] j))) =
      gaussianFixedVarianceCorrelation ((p : ℝ) + q) ((q : ℝ) / 2) f x := by
    let e := MeasurableEquiv.finTwoArrow (α := ℝ)
    have hmp := (measurePreserving_finTwoArrow_vec (gaussianReal 0 (p + q / 2))
      (gaussianReal 0 (q / 2))).symm e
    have hμ : (fun j : Fin 2 => gaussianReal 0 (![p + q / 2, q / 2] j)) =
        ![gaussianReal 0 (p + q / 2), gaussianReal 0 (q / 2)] := by
      funext j
      fin_cases j <;> rfl
    rw [hμ, ← hmp.integral_comp']
    have hint : Integrable (fun z : ℝ × ℝ => f (x + (z.1 + z.2)) * f (x + (z.1 - z.2)))
        ((gaussianReal 0 (p + q / 2)).prod (gaussianReal 0 (q / 2))) :=
      Integrable.of_bound (by fun_prop) (C ^ 2)
        (.of_forall fun z => by rw [Real.norm_eq_abs]; exact hprod _ _)
    change (∫ z : ℝ × ℝ, f (x + (z.1 + z.2)) * f (x + (z.1 - z.2))
      ∂(gaussianReal 0 (p + q / 2)).prod (gaussianReal 0 (q / 2))) = _
    rw [integral_prod _ hint]
    have hvar : (((p : ℝ) + q - (q : ℝ) / 2).toNNReal) = p + q / 2 := by
      calc
        _ = ((p + q / 2 : ℝ≥0) : ℝ).toNNReal := congrArg Real.toNNReal (by
          simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat]
          ring)
        _ = _ := Real.toNNReal_coe
    have hqvar : ((q : ℝ) / 2).toNNReal = q / 2 := by
      simpa only [NNReal.coe_div, NNReal.coe_ofNat] using
        (show ((q / 2 : ℝ≥0) : ℝ).toNNReal = q / 2 from Real.toNNReal_coe)
    simp only [gaussianFixedVarianceCorrelation, heat, zero_add, hvar, hqvar]
    apply integral_congr_ae
    exact .of_forall fun y => integral_congr_ae (.of_forall fun z => by
      dsimp
      congr 2 <;> ring)
  exact hright.symm.trans (heq.symm.trans hleft)

/-- A signed driven root, a common auxiliary root and two independent
tails have the canonical common/antisymmetric Gaussian law. -/
theorem map_gaussian_signed_common_independent_eq_antithetic (d e v : ℝ≥0) :
    (Measure.pi (fun j : Fin 4 => gaussianReal 0 (![d, e, v, v] j))).map
      (fun z => WithLp.toLp 2 (![z 0 + z 1 + z 2, -z 0 + z 1 + z 3])) =
    (Measure.pi (fun j : Fin 2 => gaussianReal 0 (![e + v / 2, d + v / 2] j))).map
      (fun z => WithLp.toLp 2 (![z 0 + z 1, z 0 - z 1])) := by
  let A : Fin 2 → Fin 4 → ℝ := ![![1, 1, 1, 0], ![-1, 1, 0, 1]]
  let B : Fin 2 → Fin 2 → ℝ := ![![1, 1], ![1, -1]]
  have hcov : ∀ i l, (∑ j : Fin 4, (![d, e, v, v] j : ℝ) * A i j * A l j) =
      ∑ j : Fin 2, (![e + v / 2, d + v / 2] j : ℝ) * B i j * B l j := by
    intro i l
    fin_cases i <;> fin_cases l <;>
      simp [A, B, Fin.sum_univ_succ, NNReal.coe_add, NNReal.coe_div] <;> ring
  have hA : (fun z : Fin 4 → ℝ => WithLp.toLp 2 (fun i => ∑ j, A i j * z j)) =
      fun z => WithLp.toLp 2 (![z 0 + z 1 + z 2, -z 0 + z 1 + z 3]) := by
    funext z
    ext i
    fin_cases i <;> simp [A, Fin.sum_univ_succ] <;> ring
  have hB : (fun z : Fin 2 → ℝ => WithLp.toLp 2 (fun i => ∑ j, B i j * z j)) =
      fun z => WithLp.toLp 2 (![z 0 + z 1, z 0 - z 1]) := by
    funext z
    ext i
    fin_cases i <;> simp [B, Fin.sum_univ_succ, sub_eq_add_neg]
  have hh := map_pi_gaussianReal_linear_eq_of_covariance A ![d, e, v, v]
    B ![e + v / 2, d + v / 2] hcov
  rw [hA, hB] at hh
  exact hh

end SpinGlass
