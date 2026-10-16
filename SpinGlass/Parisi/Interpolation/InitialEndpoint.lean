import SpinGlass.Parisi.Interpolation.PressureIntegrability

/-!
# The initial interpolation endpoint

The actual time-zero pressure agrees with the original interpolation
bracket, including the terminal mass-one Gaussian normalization.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

variable {N k : ℕ}

theorem hamG_zero (h : Fin N → ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ)
    (x : Fin k → Fin N → ℝ) : hamG N k 0 h H z₀ x = coshG N k h z₀ x := by
  rw [hamG, coshG_eq]
  congr 1
  have he (σ : Config N) : -branchHamX N k 0 h H z₀ x σ =
      ∑ i, (-(h i + z₀ i + ∑ p, x p i)) * spin N σ i := by
    simp only [branchHamX, Real.sqrt_zero, zero_mul, sub_zero, Real.sqrt_one,
      one_mul, zero_add, spin, spinOf]
    rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [branchZX, he]
  rw [sum_exp_sum_spin]
  apply Finset.prod_congr rfl
  intro i _
  rw [neg_neg, add_comm, exp_add_exp_neg_eq_two_cosh]

/-- The root expectation of the actual time-zero recursion factors into
the one-site Parisi expectations, with the absorbed last level removed. -/
theorem integral_log_cascadeRec_hamG_zero
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (h : Fin N → ℝ) (H : EnergySpace N) :
    (∫ z₀, Real.log (cascadeRec k ms
      (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1)))
      (hamG N k 0 h H z₀)).toReal
      ∂Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0))) =
      (N : ℝ) * Real.log 2 + ∑ i,
        (parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h i + x))) -
          (parisiVar ξ qs (k + 1) : ℝ) / 2) := by
  simp_rw [show ∀ z₀, hamG N k 0 h H z₀ = coshG N k h z₀ from
    fun z₀ => funext (hamG_zero h H z₀)]
  change (∫ z₀, parisiRec k ms
    (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1)))
    (coshF N k h z₀) ∂_) = _
  simp_rw [parisiRec_coshF N k ms _ hpos hle]
  have hi : Integrable (fun z₀ : Fin N → ℝ => ∑ i,
      logCoshRec k ms (fun p => parisiVar ξ qs (p.val + 1)) (h i + z₀ i))
      (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0))) := by
    apply integrable_finsetSum
    intro i _
    exact ((measurePreserving_eval (μ := fun _ : Fin N =>
      gaussianReal 0 (parisiVar ξ qs 0)) i).integrable_comp
        ((measurable_logCoshRec k ms _).comp
          (measurable_const.add measurable_id)).aestronglyMeasurable).2
      (integrable_logCoshRec_add k ms _ hpos hle (h i) _)
  rw [integral_add (integrable_const _) hi, integral_const, probReal_univ, one_smul,
    integral_sum_logCoshRec N k ms _ hpos hle]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [parisiX₀_logCosh_eq k ξ (h i) ms qs hpos hle, add_sub_cancel_right]

theorem parisiInterpolationBracket_zero
    (μh : Measure ℝ) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) :
    parisiInterpolationBracket μh ξ ms qs 0 = Real.log 2 + randomFieldParisiX₀ μh ξ ms qs -
      (parisiVar ξ qs (k + 1) : ℝ) / 2 := by
  rw [parisiInterpolationBracket,
    parisiSplitBracket_eq_functional_add_correction μh ξ ms qs hm]
  simp only [parisiAuxTerminalVar, sub_zero, Real.toNNReal_one, one_mul]
  unfold randomFieldParisiFunctional parisiCorrection
  rw [Fin.sum_univ_eq_sum_range (fun p => mExt ms (p + 1) *
    (parisiTheta ξ (qExt qs (p + 2)) - parisiTheta ξ (qExt qs (p + 1))))]
  ring

/-- The initial identity in (14.108) with the actual i.i.d. field law. -/
theorem parisiInterpolationPressure_zero
    (hN : 0 < N) {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hS : (overlapCovMatrix N ξ).PosSemidef) :
    parisiInterpolationPressure N μh ξ ms qs 0 = parisiInterpolationBracket μh ξ ms qs 0 := by
  have hle (i) := (hm.2.2 i).le
  rw [parisiInterpolationPressure_eq_base_recursion μh ξ ms qs hS
    (by constructor <;> norm_num)]
  unfold parisiBaseDisorderFieldLaw
  rw [integral_prod_symm _ (integrable_parisiBaseLogPartition hμ ξ ms qs hm.2.1 hle hS
    (t := 0) (by constructor <;> norm_num))]
  have hignore (h : Fin N → ℝ) :
      (fun z : EnergySpace N × (Fin N → ℝ) => Real.log (cascadeRec k ms
        (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1)))
        (hamG N k 0 h z.1 z.2)).toReal) =
      fun z => Real.log (cascadeRec k ms
        (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1)))
        (hamG N k 0 h 0 z.2)).toReal := by
    funext z
    congr 3
    funext x
    rw [hamG_zero, hamG_zero]
  have hinner (h : Fin N → ℝ) :
      (∫ z : EnergySpace N × (Fin N → ℝ), Real.log (cascadeRec k ms
        (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1)))
        (hamG N k 0 h z.1 z.2)).toReal
        ∂(multivariateGaussian 0 (overlapCovMatrix N ξ)).prod
          (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0)))) =
      (N : ℝ) * Real.log 2 + ∑ i,
        (parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h i + x))) -
          (parisiVar ξ qs (k + 1) : ℝ) / 2) := by
    rw [hignore, integral_fun_snd (fun z₀ : Fin N → ℝ => Real.log (cascadeRec k ms
      (gaussianMarks N k (fun p => parisiVar ξ qs (p.val + 1)))
      (hamG N k 0 h 0 z₀)).toReal), probReal_univ, one_smul]
    exact integral_log_cascadeRec_hamG_zero ξ ms qs hm.2.1 hle h 0
  simp_rw [hinner]
  let X := fun h => parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))
  let v : ℝ := (parisiVar ξ qs (k + 1) : ℝ) / 2
  have hX : Integrable X μh := integrable_parisiX₀_logCosh hμ ξ ms qs hm.2.1 hle
  have hXi (i : Fin N) : Integrable (fun h : Fin N → ℝ => X (h i) - v)
      (externalFieldVecLaw N μh) :=
    (((measurePreserving_externalFieldVec_apply N μh i).integrable_comp
      hX.aestronglyMeasurable).2 hX).sub (integrable_const _)
  change (1 / (N : ℝ)) * (∫ h, (N : ℝ) * Real.log 2 + ∑ i, (X (h i) - v)
    ∂externalFieldVecLaw N μh) = _
  rw [integral_add (integrable_const _) (integrable_finsetSum _ (fun i _ => hXi i)),
    integral_const, probReal_univ, one_smul, integral_finsetSum _ (fun i _ => hXi i)]
  have hsingle (i : Fin N) :
      (∫ h, X (h i) - v ∂externalFieldVecLaw N μh) = randomFieldParisiX₀ μh ξ ms qs - v := by
    have hi : Integrable (fun h : Fin N → ℝ => X (h i)) (externalFieldVecLaw N μh) :=
      ((measurePreserving_externalFieldVec_apply N μh i).integrable_comp
        hX.aestronglyMeasurable).2 hX
    rw [integral_sub hi (integrable_const _),
      integral_externalFieldVec_apply N μh i X hX.aestronglyMeasurable,
      integral_const, probReal_univ, one_smul]
    rfl
  simp_rw [hsingle]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    parisiInterpolationBracket_zero μh ξ ms qs hm]
  dsimp only [v]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hn]
  ring

end SpinGlass
