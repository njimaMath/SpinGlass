import SpinGlass.Parisi.Coupled.CoupledRootSignedResponse

/-!
# Law of the signed driven and common auxiliary root

The normalized four-column root marks have the exact law of two independent
Gaussians of variances d and e, read as D+E and -D+E. The construction
includes either zero variance.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs Aristotle.Heat

noncomputable def signedRootVarianceShareMap (d e : ℝ≥0)
    (z : Fin 2 ⊕ Fin 2 → ℝ) : Fin 2 → ℝ := fun l =>
  ∑ j, (coupledDrivenVarianceFactor d e (couplingFactorSgn (-1) 1 0) +
    coupledAuxVarianceFactor d e (couplingFactorSgn 1 1 0)) l j * z j

theorem measurable_signedRootVarianceShareMap (d e : ℝ≥0) :
    Measurable (signedRootVarianceShareMap d e) := by
  unfold signedRootVarianceShareMap
  fun_prop

/-- The normalized signed root has exactly the prescribed driven and
auxiliary joint Gaussian law. -/
theorem map_pi_gaussianReal_signedRootVarianceShareMap (d e : ℝ≥0) :
    (Measure.pi (fun _ : Fin 2 ⊕ Fin 2 => gaussianReal 0 (d + e))).map
      (fun z => WithLp.toLp 2 (signedRootVarianceShareMap d e z)) =
    (Measure.pi (fun j : Fin 2 => gaussianReal 0 (![d, e] j))).map
      (fun z => WithLp.toLp 2 (![z 0 + z 1, -z 0 + z 1])) := by
  let A := coupledDrivenVarianceFactor d e (couplingFactorSgn (-1) 1 0) +
    coupledAuxVarianceFactor d e (couplingFactorSgn 1 1 0)
  let B : Fin 2 → Fin 2 → ℝ := ![![1, 1], ![-1, 1]]
  have hcov : ∀ l l', (∑ j : Fin 2 ⊕ Fin 2, ((d + e : ℝ≥0) : ℝ) * A l j * A l' j) =
      ∑ j : Fin 2, (![d, e] j : ℝ) * B l j * B l' j := by
    intro l l'
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    change ((d + e : ℝ≥0) : ℝ) * gram A l l' = _
    rw [gram_coupledVarianceFactors_add]
    fin_cases l <;> fin_cases l' <;>
      simp [gram, couplingFactorSgn, B, Fin.sum_univ_two]
  have hB : (fun z : Fin 2 → ℝ => WithLp.toLp 2 (fun i => ∑ j, B i j * z j)) =
      fun z => WithLp.toLp 2 (![z 0 + z 1, -z 0 + z 1]) := by
    funext z
    ext i
    fin_cases i <;> simp [B, Fin.sum_univ_two]
  have hh := map_pi_gaussianReal_linear_eq_of_covariance A (fun _ => d + e) B ![d, e] hcov
  rw [hB] at hh
  exact hh

/-- The joint Gaussian law transports every measurable two-field
observable, with no integrability premise on this law identity. -/
theorem integral_signedRootVarianceShare_eq {F : (Fin 2 → ℝ) → ℝ}
    (hF : Measurable F) (d e : ℝ≥0) :
    (∫ z, F (signedRootVarianceShareMap d e z)
      ∂Measure.pi (fun _ : Fin 2 ⊕ Fin 2 => gaussianReal 0 (d + e))) =
      ∫ z : Fin 2 → ℝ, F (![z 0 + z 1, -z 0 + z 1])
        ∂Measure.pi (fun j => gaussianReal 0 (![d, e] j)) := by
  have hm : Measurable (fun z : EuclideanSpace ℝ (Fin 2) => F (WithLp.ofLp z)) :=
    hF.comp (by fun_prop)
  have hi := integral_map
    (μ := Measure.pi (fun _ : Fin 2 ⊕ Fin 2 => gaussianReal 0 (d + e)))
    (f := fun z : EuclideanSpace ℝ (Fin 2) => F (WithLp.ofLp z))
    ((by fun_prop : Measurable (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2))).comp
      (measurable_signedRootVarianceShareMap d e)).aemeasurable
    hm.aestronglyMeasurable
  have hj := integral_map
    (μ := Measure.pi (fun j : Fin 2 => gaussianReal 0 (![d, e] j)))
    (f := fun z : EuclideanSpace ℝ (Fin 2) => F (WithLp.ofLp z))
    (by fun_prop : Measurable fun z : Fin 2 → ℝ =>
      WithLp.toLp 2 (![z 0 + z 1, -z 0 + z 1])).aemeasurable hm.aestronglyMeasurable
  simp only [Function.comp_def] at hi
  rw [map_pi_gaussianReal_signedRootVarianceShareMap] at hi
  exact hi.symm.trans hj

/-- The canonical two-mark law realizes the fixed-marginal heat
correlation exactly, including zero common or antisymmetric variance. -/
theorem integral_pi_gaussian_antithetic_eq_correlation {f : ℝ → ℝ}
    (hc : Continuous f) {C : ℝ} (hb : ∀ y, |f y| ≤ C) (p q : ℝ≥0) (x : ℝ) :
    (∫ z : Fin 2 → ℝ, f (x + (z 0 + z 1)) * f (x + (z 0 - z 1))
      ∂Measure.pi (fun j => gaussianReal 0 (![p, q] j))) =
      gaussianFixedVarianceCorrelation ((p : ℝ) + q) q f x := by
  have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hb 0)
  have hprod : ∀ y z, |f y * f z| ≤ C ^ 2 := fun y z => by
    rw [abs_mul]
    simpa only [pow_two] using mul_le_mul (hb y) (hb z) (abs_nonneg _) hC
  let e := MeasurableEquiv.finTwoArrow (α := ℝ)
  have hmp := (measurePreserving_finTwoArrow_vec (gaussianReal 0 p) (gaussianReal 0 q)).symm e
  have hμ : (fun j : Fin 2 => gaussianReal 0 (![p, q] j)) =
      ![gaussianReal 0 p, gaussianReal 0 q] := by funext j; fin_cases j <;> rfl
  rw [hμ, ← hmp.integral_comp']
  have hint : Integrable (fun z : ℝ × ℝ => f (x + (z.1 + z.2)) * f (x + (z.1 - z.2)))
      ((gaussianReal 0 p).prod (gaussianReal 0 q)) :=
    Integrable.of_bound (by fun_prop) (C ^ 2)
      (.of_forall fun z => by rw [Real.norm_eq_abs]; exact hprod _ _)
  change (∫ z : ℝ × ℝ, f (x + (z.1 + z.2)) * f (x + (z.1 - z.2))
    ∂(gaussianReal 0 p).prod (gaussianReal 0 q)) = _
  rw [integral_prod _ hint]
  simp only [gaussianFixedVarianceCorrelation, heat, zero_add, add_sub_cancel_right,
    Real.toNNReal_coe]
  exact integral_congr_ae (.of_forall fun y => integral_congr_ae (.of_forall fun z => by
    dsimp
    congr 2 <;> ring))

/-- Independent positive-level smoothing above the signed root gives
the same canonical Gaussian correlation of the unsmoothed response. -/
theorem integral_gaussian_signed_root_heat_eq_correlation {f : ℝ → ℝ}
    (hc : Continuous f) {C : ℝ} (hb : ∀ y, |f y| ≤ C) (d e v : ℝ≥0) (x : ℝ) :
    (∫ D, ∫ E, heat v f (x + D + E) * heat v f (x - D + E)
      ∂gaussianReal 0 e ∂gaussianReal 0 d) =
      gaussianFixedVarianceCorrelation ((d : ℝ) + e + v) ((d : ℝ) + v / 2) f x := by
  have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hb 0)
  have hprod : ∀ y z, |f y * f z| ≤ C ^ 2 := fun y z => by
    rw [abs_mul]
    simpa only [pow_two] using mul_le_mul (hb y) (hb z) (abs_nonneg _) hC
  let F := fun z : EuclideanSpace ℝ (Fin 2) => f (x + z 0) * f (x + z 1)
  have hFc : Continuous F := by dsimp [F]; fun_prop
  have hi := integral_map
    (μ := Measure.pi (fun j : Fin 4 => gaussianReal 0 (![d, e, v, v] j)))
    (f := F) (by fun_prop : Measurable fun z : Fin 4 → ℝ =>
      WithLp.toLp 2 (![z 0 + z 1 + z 2, -z 0 + z 1 + z 3])).aemeasurable hFc.aestronglyMeasurable
  have hj := integral_map
    (μ := Measure.pi (fun j : Fin 2 => gaussianReal 0 (![e + v / 2, d + v / 2] j)))
    (f := F) (by fun_prop : Measurable fun z : Fin 2 → ℝ =>
      WithLp.toLp 2 (![z 0 + z 1, z 0 - z 1])).aemeasurable hFc.aestronglyMeasurable
  rw [map_gaussian_signed_common_independent_eq_antithetic] at hi
  have heq : (∫ z : Fin 4 → ℝ, f (x + (z 0 + z 1 + z 2)) * f (x + (-z 0 + z 1 + z 3))
      ∂Measure.pi (fun j => gaussianReal 0 (![d, e, v, v] j))) =
      ∫ z : Fin 2 → ℝ, f (x + (z 0 + z 1)) * f (x + (z 0 - z 1))
        ∂Measure.pi (fun j => gaussianReal 0 (![e + v / 2, d + v / 2] j)) := hi.symm.trans hj
  have hint : Integrable (fun z : Fin 4 → ℝ =>
      f (x + (z 0 + z 1 + z 2)) * f (x + (-z 0 + z 1 + z 3)))
      (Measure.pi (fun j => gaussianReal 0 (![d, e, v, v] j))) :=
    Integrable.of_bound (by fun_prop) (C ^ 2)
      (.of_forall fun z => by rw [Real.norm_eq_abs]; exact hprod _ _)
  rw [integral_pi_fin_succ _ hint] at heq
  have htail : Fin.tail (fun j : Fin 4 => gaussianReal 0 (![d, e, v, v] j)) =
      fun j : Fin 3 => gaussianReal 0 (![e, v, v] j) := by funext j; fin_cases j <;> rfl
  simp only [Fin.cons_zero, Matrix.cons_val_zero] at heq
  rw [htail] at heq
  have hbranch (D : ℝ) : (∫ z : Fin 3 → ℝ,
      f (x + (D + z 0 + z 1)) * f (x + (-D + z 0 + z 2))
      ∂Measure.pi (fun j => gaussianReal 0 (![e, v, v] j))) =
      ∫ E, heat v f (x + D + E) * heat v f (x - D + E) ∂gaussianReal 0 e := by
    have hintD : Integrable (fun z : Fin 3 → ℝ =>
        f (x + (D + z 0 + z 1)) * f (x + (-D + z 0 + z 2)))
        (Measure.pi (fun j => gaussianReal 0 (![e, v, v] j))) :=
      Integrable.of_bound (by fun_prop) (C ^ 2)
        (.of_forall fun z => by rw [Real.norm_eq_abs]; exact hprod _ _)
    rw [integral_pi_fin_succ _ hintD]
    have ht : Fin.tail (fun j : Fin 3 => gaussianReal 0 (![e, v, v] j)) =
        fun _ : Fin 2 => gaussianReal 0 v := by funext j; fin_cases j <;> rfl
    rw [ht]
    simp only [Fin.cons_zero, Matrix.cons_val_zero]
    apply integral_congr_ae
    exact .of_forall fun E => by
      change (∫ z : Fin 2 → ℝ, f (x + (D + E + z 0)) * f (x + (-D + E + z 1))
        ∂Measure.pi (fun _ => gaussianReal 0 v)) = _
      have hh := integral_fintype_prod_eq_prod (μ := fun _ : Fin 2 => gaussianReal 0 v)
        (fun l : Fin 2 => fun z : ℝ => f ((![x + D + E, x - D + E] l) + z))
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hh
      simpa only [heat, Real.toNNReal_coe, add_assoc, sub_eq_add_neg] using hh
  change (∫ D, ∫ z : Fin 3 → ℝ,
    f (x + (D + z 0 + z 1)) * f (x + (-D + z 0 + z 2))
    ∂Measure.pi (fun j => gaussianReal 0 (![e, v, v] j)) ∂gaussianReal 0 d) = _ at heq
  simp_rw [hbranch] at heq
  rw [integral_pi_gaussian_antithetic_eq_correlation hc hb (e + v / 2) (d + v / 2) x] at heq
  have htotal : ((e + v / 2 : ℝ≥0) : ℝ) + (d + v / 2 : ℝ≥0) = (d : ℝ) + e + v := by
    simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat]
    ring
  have hanti : ((d + v / 2 : ℝ≥0) : ℝ) = (d : ℝ) + v / 2 := by simp
  rw [htotal, hanti] at heq
  exact heq

/-- Either signed root coordinate has variance d+e under the actual
independent driven/auxiliary product law. -/
theorem map_gaussianReal_prod_signed_sum (d e : ℝ≥0) (l : Fin 2) :
    ((gaussianReal 0 d).prod (gaussianReal 0 e)).map
      (fun z : ℝ × ℝ => (if l = 0 then z.1 else -z.1) + z.2) = gaussianReal 0 (d + e) := by
  let f := fun D : ℝ => if l = 0 then D else -D
  have hf : Measurable f := by dsimp [f]; split_ifs <;> fun_prop
  have hX : ((gaussianReal 0 d).prod (gaussianReal 0 e)).map
      (fun z : ℝ × ℝ => f z.1) = gaussianReal 0 d := by
    change ((gaussianReal 0 d).prod (gaussianReal 0 e)).map (f ∘ Prod.fst) = _
    rw [← Measure.map_map hf measurable_fst, measurePreserving_fst.map_eq]
    by_cases h : l = 0
    · simp [f, h]
    · simp [f, h, gaussianReal_map_neg]
  have hY : ((gaussianReal 0 d).prod (gaussianReal 0 e)).map
      (fun z : ℝ × ℝ => z.2) = gaussianReal 0 e := measurePreserving_snd.map_eq
  have hi : IndepFun (fun z : ℝ × ℝ => f z.1) (fun z : ℝ × ℝ => z.2)
      ((gaussianReal 0 d).prod (gaussianReal 0 e)) := indepFun_prod hf measurable_id
  have hh := gaussianReal_add_gaussianReal_of_indepFun hi hX hY
  have hfun : (fun z : ℝ × ℝ => f z.1) + (fun z : ℝ × ℝ => z.2) =
      fun z => (if l = 0 then z.1 else -z.1) + z.2 := by funext z; rfl
  rw [hfun, zero_add] at hh
  exact hh

/-- The normalized root transports directly to the independent
driven/auxiliary product, in the form consumed by the two-field recursion. -/
theorem integral_signedRootVarianceShare_eq_prod {F : (Fin 2 → ℝ) → ℝ}
    (hF : Measurable F) (d e : ℝ≥0) :
    (∫ z, F (signedRootVarianceShareMap d e z)
      ∂Measure.pi (fun _ : Fin 2 ⊕ Fin 2 => gaussianReal 0 (d + e))) =
      ∫ z : ℝ × ℝ, F (![z.1 + z.2, -z.1 + z.2]) ∂(gaussianReal 0 d).prod (gaussianReal 0 e) := by
  rw [integral_signedRootVarianceShare_eq hF d e]
  let equiv := MeasurableEquiv.finTwoArrow (α := ℝ)
  have hmp := (measurePreserving_finTwoArrow_vec (gaussianReal 0 d) (gaussianReal 0 e)).symm equiv
  have hμ : (fun j : Fin 2 => gaussianReal 0 (![d, e] j)) =
      ![gaussianReal 0 d, gaussianReal 0 e] := by funext j; fin_cases j <;> rfl
  rw [hμ, ← hmp.integral_comp']
  rfl

end SpinGlass
