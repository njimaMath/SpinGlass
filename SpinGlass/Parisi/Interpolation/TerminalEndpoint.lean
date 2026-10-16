import SpinGlass.Parisi.Interpolation.PressureLaw

/-!
# The terminal interpolation endpoint

At time one all auxiliary fields vanish, so the single-copy interpolation
is exactly the original finite-volume quenched free energy. A first moment
of the site law suffices for the joint integration and change of order.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ}

theorem hamG_one (h : Fin N → ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ)
    (x : Fin k → Fin N → ℝ) :
    hamG N k 1 h H z₀ x = ENNReal.ofReal (SpinGlass.Z N (H + siteExternalFieldEnergy N h)) := by
  simp [hamG, branchZX, branchHamX, SpinGlass.Z, siteExternalFieldEnergy]

/-- Joint integrability of the terminal free energy with its actual
interaction, root and field product law. -/
theorem integrable_terminalFreeEnergy_baseLaw
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) (qs : Fin (k + 1) → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef) :
    Integrable (fun z : (EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ) =>
      SpinGlass.free_energy_density N (z.1.1 + siteExternalFieldEnergy N z.2))
      (parisiBaseDisorderFieldLaw N μh ξ qs) := by
  have hH := ((GaussianField.ofMultivariateGaussian hS).integrable.comp_fst
    (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0)))).comp_fst
      (externalFieldVecLaw N μh)
  have hh := (integrable_siteExternalFieldEnergy N hμ).comp_snd
    ((multivariateGaussian 0 (overlapCovMatrix N ξ)).prod
      (Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0))))
  have hm : Measurable (fun z : (EnergySpace N × (Fin N → ℝ)) × (Fin N → ℝ) =>
      z.1.1 + siteExternalFieldEnergy N z.2) := by
    exact measurable_fst.fst.add ((continuous_siteExternalFieldEnergy N).measurable.comp
      measurable_snd)
  have hf := integrable_wFreeEnergy_of_integrable_norm (fun _ : Config N => (1 : ℝ))
    (fun _ => zero_le_one) ⟨(fun _ => true), one_ne_zero⟩ N hm (hH.add hh).norm
  simpa only [wFreeEnergy, wZ, one_mul, SpinGlass.free_energy_density, SpinGlass.Z,
    parisiBaseDisorderFieldLaw] using hf

/-- The terminal pressure in (14.109), with the i.i.d. quenched site law. -/
theorem parisiInterpolationPressure_one
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hS : (overlapCovMatrix N ξ).PosSemidef) :
    parisiInterpolationPressure N μh ξ ms qs 1 = iidFieldMixedPSpinFreeEnergy N μh ξ := by
  rw [parisiInterpolationPressure_eq_base_recursion μh ξ ms qs hS (by constructor <;> norm_num)]
  simp_rw [show ∀ (h : Fin N → ℝ) (H : EnergySpace N) (z₀ : Fin N → ℝ),
    hamG N k 1 h H z₀ = fun _ => ENNReal.ofReal
      (SpinGlass.Z N (H + siteExternalFieldEnergy N h)) from
        fun h H z₀ => funext (hamG_one h H z₀), cascadeRec_const k ms _ hpos,
    ENNReal.toReal_ofReal (SpinGlass.Z_pos N _).le]
  rw [← integral_const_mul]
  change (∫ z, SpinGlass.free_energy_density N (z.1.1 + siteExternalFieldEnergy N z.2)
    ∂parisiBaseDisorderFieldLaw N μh ξ qs) = _
  unfold parisiBaseDisorderFieldLaw
  rw [integral_prod_symm _ (integrable_terminalFreeEnergy_baseLaw hμ ξ qs hS)]
  unfold iidFieldMixedPSpinFreeEnergy siteFieldMixedPSpinFreeEnergy gaussField
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro h
  simpa only [probReal_univ, one_smul] using
    (integral_fun_fst (μ := multivariateGaussian 0 (overlapCovMatrix N ξ))
      (ν := Measure.pi (fun _ : Fin N => gaussianReal 0 (parisiVar ξ qs 0)))
      (fun H : EnergySpace N => SpinGlass.free_energy_density N (H + siteExternalFieldEnergy N h)))

end SpinGlass
