import SpinGlass.Parisi.Field.FieldContinuity

/-!
# Uniform continuity under a coupled change of the site-field law

A common scalar sample couples two site laws. Their expected absolute
difference controls both the finite-volume pressure and the Parisi
infimum, with constant one independent of volume and level count.
These are the law-approximation inputs for the random-field qualification
after Talagrand's equation (14.123).
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace SpinGlass

/-- Sitewise field changes have a volume-normalized absolute-sum
bound under the same Gaussian interaction law. -/
theorem abs_siteFieldMixedPSpinFreeEnergy_sub_le
    {N : ℕ} (hN : 0 < N) (ξ : ℝ → ℝ) (a b : Fin N → ℝ) :
    |siteFieldMixedPSpinFreeEnergy N ξ a - siteFieldMixedPSpinFreeEnergy N ξ b| ≤
      (1 / (N : ℝ)) * ∑ i, |a i - b i| := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpoint (H : EnergySpace N) (a b : Fin N → ℝ) :
      free_energy_density N (H + siteExternalFieldEnergy N a) ≤
        free_energy_density N (H + siteExternalFieldEnergy N b) +
          (1 / (N : ℝ)) * ∑ i, |a i - b i| := by
    apply free_energy_density_le_add_of_pointwise_bound hN
    intro σ
    have henergy : |siteExternalFieldEnergy N a σ - siteExternalFieldEnergy N b σ| ≤
        ∑ i, |a i - b i| := by
      change |(∑ i, a i * isingSpin (σ i)) - ∑ i, b i * isingSpin (σ i)| ≤ _
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ i, |a i * isingSpin (σ i) - b i * isingSpin (σ i)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [← sub_mul, abs_mul, abs_isingSpin_eq_one, mul_one]
    have hscale : (N : ℝ) * ((1 / (N : ℝ)) * ∑ i, |a i - b i|) =
        ∑ i, |a i - b i| := by field_simp
    rw [hscale]
    change -(H σ + siteExternalFieldEnergy N a σ) ≤
      -(H σ + siteExternalFieldEnergy N b σ) + _
    linarith [(abs_le.1 henergy).1]
  have hi (a : Fin N → ℝ) : Integrable
      (fun H : EnergySpace N => free_energy_density N (H + siteExternalFieldEnergy N a))
      (gaussField N (overlapCovMatrix N ξ)) := by
    simpa only [add_comm] using
      integrable_free_energy_density_add_gaussField (overlapCovMatrix N ξ)
        (siteExternalFieldEnergy N a)
  have hmean (a b : Fin N → ℝ) :
      siteFieldMixedPSpinFreeEnergy N ξ a ≤ siteFieldMixedPSpinFreeEnergy N ξ b +
        (1 / (N : ℝ)) * ∑ i, |a i - b i| := by
    have hh := integral_mono (hi a) ((hi b).add (integrable_const _))
      (fun H => hpoint H a b)
    simp only [Pi.add_apply] at hh
    rw [integral_add (hi b) (integrable_const _), integral_const,
      probReal_univ, one_smul] at hh
    exact hh
  apply abs_le.2
  constructor
  · have hh := hmean b a
    simp only [abs_sub_comm] at hh
    linarith
  · linarith [hmean a b]

/-- Applying the same measurable map independently at every site
gives precisely the product of the transformed scalar laws. -/
theorem measurePreserving_externalFieldVec_map (N : ℕ) {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {f : ℝ → ℝ} (hf : Measurable f) :
    MeasurePreserving (fun hVec : Fin N → ℝ => fun i => f (hVec i))
      (externalFieldVecLaw N μh) (externalFieldVecLaw N (μh.map f)) := by
  let : IsProbabilityMeasure (μh.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  exact ⟨measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i)),
    Measure.pi_map_pi (fun _ => hf.aemeasurable)⟩

/-- A common sample couples two i.i.d. field laws without changing
the quenched Gaussian interaction or sharing fields across distinct sites. -/
theorem abs_iidFieldMixedPSpinFreeEnergy_map_sub_le {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfi : Integrable f μh) (hgi : Integrable g μh)
    {N : ℕ} (hN : 0 < N) (ξ : ℝ → ℝ) (hS : (overlapCovMatrix N ξ).PosSemidef) :
    |iidFieldMixedPSpinFreeEnergy N (μh.map f) ξ -
      iidFieldMixedPSpinFreeEnergy N (μh.map g) ξ| ≤ ∫ h, |f h - g h| ∂μh := by
  let : IsProbabilityMeasure (μh.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  let : IsProbabilityMeasure (μh.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hfid : Integrable id (μh.map f) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hf.aemeasurable).2 hfi
  have hgid : Integrable id (μh.map g) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hg.aemeasurable).2 hgi
  have hF := integrable_siteFieldMixedPSpinFreeEnergy N hfid ξ hS
  have hG := integrable_siteFieldMixedPSpinFreeEnergy N hgid ξ hS
  have hmpf := measurePreserving_externalFieldVec_map N (μh := μh) hf
  have hmpg := measurePreserving_externalFieldVec_map N (μh := μh) hg
  have hFc := (hmpf.integrable_comp hF.aestronglyMeasurable).2 hF
  have hGc := (hmpg.integrable_comp hG.aestronglyMeasurable).2 hG
  have hFm : AEStronglyMeasurable (siteFieldMixedPSpinFreeEnergy N ξ)
      ((externalFieldVecLaw N μh).map (fun hVec i => f (hVec i))) := by
    rw [hmpf.map_eq]
    exact hF.aestronglyMeasurable
  have hGm : AEStronglyMeasurable (siteFieldMixedPSpinFreeEnergy N ξ)
      ((externalFieldVecLaw N μh).map (fun hVec i => g (hVec i))) := by
    rw [hmpg.map_eq]
    exact hG.aestronglyMeasurable
  have htransf := integral_map hmpf.measurable.aemeasurable hFm
  have htransg := integral_map hmpg.measurable.aemeasurable hGm
  rw [hmpf.map_eq] at htransf
  rw [hmpg.map_eq] at htransg
  simp only [Function.comp_def] at hFc hGc
  have hd : Integrable (fun h => |f h - g h|) μh := (hfi.sub hgi).abs
  have hdi (i : Fin N) : Integrable (fun hVec : Fin N → ℝ => |f (hVec i) - g (hVec i)|)
      (externalFieldVecLaw N μh) :=
    ((measurePreserving_externalFieldVec_apply N μh i).integrable_comp
      hd.aestronglyMeasurable).2 hd
  have hbound := (integrable_finsetSum Finset.univ (fun i _ => hdi i)).const_mul
    (1 / (N : ℝ))
  unfold iidFieldMixedPSpinFreeEnergy
  rw [htransf, htransg, ← integral_sub hFc hGc]
  calc
    _ ≤ ∫ hVec, |siteFieldMixedPSpinFreeEnergy N ξ (fun i => f (hVec i)) -
        siteFieldMixedPSpinFreeEnergy N ξ (fun i => g (hVec i))| ∂externalFieldVecLaw N μh :=
      abs_integral_le_integral_abs
    _ ≤ ∫ hVec, (1 / (N : ℝ)) * ∑ i, |f (hVec i) - g (hVec i)|
        ∂externalFieldVecLaw N μh := integral_mono (hFc.sub hGc).abs hbound
      (fun hVec => abs_siteFieldMixedPSpinFreeEnergy_sub_le hN ξ _ _)
    _ = ∫ h, |f h - g h| ∂μh := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => hdi i)]
      simp_rw [integral_externalFieldVec_apply N μh _ _ hd.aestronglyMeasurable]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← mul_assoc, one_div, inv_mul_cancel₀ (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0), one_mul]

/-- The variational value for a transformed law is the average
of the actual deterministic-field functional along that transformation. -/
theorem randomFieldParisiFunctional_map_eq_integral {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {f : ℝ → ℝ} (hf : Measurable f) (hfi : Integrable f μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    randomFieldParisiFunctional (μh.map f) ξ ms qs =
      ∫ h, parisiFunctional ξ (f h) ms qs ∂μh := by
  let : IsProbabilityMeasure (μh.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hid : Integrable id (μh.map f) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hf.aemeasurable).2 hfi
  rw [randomFieldParisiFunctional_eq_integral hid ξ ms qs hpos hle]
  exact integral_map hf.aemeasurable
    (integrable_parisiFunctional_externalField hid ξ ms qs hpos hle).aestronglyMeasurable

/-- The same scalar coupling controls every admissible Parisi
functional, uniformly in the number of levels and their parameters. -/
theorem abs_randomFieldParisiFunctional_map_sub_le {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfi : Integrable f μh) (hgi : Integrable g μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    |randomFieldParisiFunctional (μh.map f) ξ ms qs -
      randomFieldParisiFunctional (μh.map g) ξ ms qs| ≤ ∫ h, |f h - g h| ∂μh := by
  let : IsProbabilityMeasure (μh.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  let : IsProbabilityMeasure (μh.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hfid : Integrable id (μh.map f) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hf.aemeasurable).2 hfi
  have hgid : Integrable id (μh.map g) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hg.aemeasurable).2 hgi
  have hF := integrable_parisiFunctional_externalField hfid ξ ms qs hpos hle
  have hG := integrable_parisiFunctional_externalField hgid ξ ms qs hpos hle
  have hFc := (integrable_map_measure hF.aestronglyMeasurable hf.aemeasurable).1 hF
  have hGc := (integrable_map_measure hG.aestronglyMeasurable hg.aemeasurable).1 hG
  simp only [Function.comp_def] at hFc hGc
  rw [randomFieldParisiFunctional_map_eq_integral hf hfi ξ ms qs hpos hle,
    randomFieldParisiFunctional_map_eq_integral hg hgi ξ ms qs hpos hle,
    ← integral_sub hFc hGc]
  exact abs_integral_le_integral_abs.trans
    (integral_mono (hFc.sub hGc).abs (hfi.sub hgi).abs
      (fun h => abs_parisiFunctional_sub_field_le ξ ms qs hpos hle (f h) (g h)))

/-- Taking the infimum preserves the field-law perturbation bound.
No existence of a minimizing discrete parameter array is needed. -/
theorem randomFieldParisiInf_map_le_add {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfi : Integrable f μh) (hgi : Integrable g μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) :
    randomFieldParisiInf (μh.map f) ξ ≤
      randomFieldParisiInf (μh.map g) ξ + ∫ h, |f h - g h| ∂μh := by
  let : IsProbabilityMeasure (μh.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hbdd := bddBelow_randomFieldParisiSet_of_talagrand (μh.map f) hξ
  have hh : randomFieldParisiInf (μh.map f) ξ - (∫ h, |f h - g h| ∂μh) ≤
      sInf (randomFieldParisiSet (μh.map g) ξ) := by
    apply le_csInf (randomFieldParisiSet_nonempty (μh.map g) ξ)
    rintro y ⟨k, ms, qs, hsm, hpos, hlt, hmono, hq0, hq1, rfl⟩
    have hvalue := randomFieldParisiInf_le (μh.map f) ξ hbdd hsm hpos hlt hmono hq0 hq1
    have hdiff := (abs_le.1 (abs_randomFieldParisiFunctional_map_sub_le
      hf hg hfi hgi ξ ms qs hpos (fun i => (hlt i).le))).2
    linarith
  change randomFieldParisiInf (μh.map f) ξ - (∫ h, |f h - g h| ∂μh) ≤
    randomFieldParisiInf (μh.map g) ξ at hh
  linarith

/-- The Parisi infimum is one-Lipschitz for a common-sample coupling
of site laws with finite first moments, without additional profile regularity. -/
theorem abs_randomFieldParisiInf_map_sub_le {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfi : Integrable f μh) (hgi : Integrable g μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) :
    |randomFieldParisiInf (μh.map f) ξ - randomFieldParisiInf (μh.map g) ξ| ≤
      ∫ h, |f h - g h| ∂μh := by
  have hfg := randomFieldParisiInf_map_le_add hf hg hfi hgi hξ
  have hgf := randomFieldParisiInf_map_le_add hg hf hgi hfi hξ
  simp only [abs_sub_comm] at hgf
  exact abs_le.2 ⟨by linarith, by linarith⟩

end SpinGlass
