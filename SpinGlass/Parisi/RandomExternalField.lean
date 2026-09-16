/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.ParisiFunctional
import SpinGlass.MixedPSpinThermodynamicLimit
import SpinGlass.Parisi.GuerraBound
import SpinGlass.FiniteGibbs.GaussianFieldProd

/-!
# Quenched random external fields

This file records the law of the i.i.d. site variables in Talagrand, *Mean Field Models for Spin
Glasses*, Vol. II, Chapter 14.  The external field is kept separate from the Gaussian interaction
and cascade marks.  In particular, all replicas of one quenched system use the same point of
`Fin N → ℝ` sampled from `externalFieldVecLaw`.
-/

open MeasureTheory ProbabilityTheory

namespace SpinGlass

open FiniteGibbs

noncomputable section

/-- The same realized site field is used by both members of a coupled replica pair. -/
def sharedReplicaSiteField {N : ℕ} (hVec : Fin N → ℝ) : Fin N × Fin 2 → ℝ :=
  fun i => hVec i.1

lemma measurable_sharedReplicaSiteField (N : ℕ) :
    Measurable (sharedReplicaSiteField (N := N)) := by
  exact measurable_pi_lambda _ fun i => measurable_pi_apply i.1

/-- The external-field energy for one realized site vector. Replicas share this vector. -/
def siteExternalFieldEnergy (N : ℕ) (hVec : Fin N → ℝ) : EnergySpace N :=
  WithLp.toLp 2 (fun σ : Config N => ∑ i, hVec i * isingSpin (σ i))

@[simp] lemma siteExternalFieldEnergy_const (N : ℕ) (h : ℝ) :
    siteExternalFieldEnergy N (fun _ => h) = H_field N h := by
  ext σ
  simp [siteExternalFieldEnergy, H_field, magnetic_field_vector,
    magnetization_eq_magnetizationOf, magnetizationOf, spinOf, Finset.mul_sum]

/-- Finite-volume free energy conditional on a realized external-field vector. -/
def siteFieldMixedPSpinFreeEnergy (N : ℕ) (ξ : ℝ → ℝ) (hVec : Fin N → ℝ) : ℝ :=
  ∫ H, free_energy_density (N := N) (H + siteExternalFieldEnergy N hVec)
    ∂gaussField N (overlapCovMatrix N ξ)

@[simp] lemma siteFieldMixedPSpinFreeEnergy_const (N : ℕ) (ξ : ℝ → ℝ) (h : ℝ) :
    siteFieldMixedPSpinFreeEnergy N ξ (fun _ => h) = mixedPSpinFreeEnergy N ξ h := by
  simp [siteFieldMixedPSpinFreeEnergy, mixedPSpinFreeEnergy, gaussFreeEnergy, gaussField]

/-- The product law of the i.i.d. quenched external fields `(hᵢ)_{i ≤ N}`. -/
def externalFieldVecLaw (N : ℕ) (μh : Measure ℝ) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ : Fin N => μh

instance (N : ℕ) (μh : Measure ℝ) [IsProbabilityMeasure μh] :
    IsProbabilityMeasure (externalFieldVecLaw N μh) := by
  unfold externalFieldVecLaw
  infer_instance

/-- The coupled external-field law: independent sites with a shared field in both replicas. -/
def sharedReplicaExternalFieldLaw (N : ℕ) (μh : Measure ℝ) :
    Measure (Fin N × Fin 2 → ℝ) :=
  (externalFieldVecLaw N μh).map sharedReplicaSiteField

instance (N : ℕ) (μh : Measure ℝ) [IsProbabilityMeasure μh] :
    IsProbabilityMeasure (sharedReplicaExternalFieldLaw N μh) := by
  exact Measure.isProbabilityMeasure_map (measurable_sharedReplicaSiteField N).aemeasurable

/-- Quenched free energy with i.i.d. site fields, independent of the Gaussian interaction. -/
def iidFieldMixedPSpinFreeEnergy (N : ℕ) (μh : Measure ℝ) (ξ : ℝ → ℝ) : ℝ :=
  ∫ hVec, siteFieldMixedPSpinFreeEnergy N ξ hVec ∂externalFieldVecLaw N μh

/-- The SK model with the same general i.i.d. quenched site law. -/
def iidFieldSKFreeEnergy (N : ℕ) (μh : Measure ℝ) (β : ℝ) : ℝ :=
  iidFieldMixedPSpinFreeEnergy N μh (skCovXi β)

@[simp] lemma externalFieldVecLaw_dirac (N : ℕ) (h : ℝ) :
    externalFieldVecLaw N (Measure.dirac h) = Measure.dirac (fun _ : Fin N => h) := by
  classical
  apply Measure.pi_eq
  intro s hs
  by_cases hm : ∀ i, h ∈ s i
  · simp [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs),
      Measure.dirac_apply' _ (hs _), Set.mem_pi, hm]
  · obtain ⟨i, hi⟩ := not_forall.mp hm
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Measure.dirac_apply' _ (hs i), hi])]
    simp [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs), Set.mem_pi, hm]

@[simp] theorem iidFieldMixedPSpinFreeEnergy_dirac (N : ℕ) (ξ : ℝ → ℝ) (h : ℝ) :
    iidFieldMixedPSpinFreeEnergy N (Measure.dirac h) ξ = mixedPSpinFreeEnergy N ξ h := by
  simp [iidFieldMixedPSpinFreeEnergy]

@[simp] theorem iidFieldSKFreeEnergy_dirac (N : ℕ) (β h : ℝ) :
    iidFieldSKFreeEnergy N (Measure.dirac h) β = skFreeEnergy N β h := by
  simp [iidFieldSKFreeEnergy, skFreeEnergy_eq_mixedPSpinFreeEnergy]

/-- The coordinates are independent, in addition to having the common marginal law. -/
lemma iIndepFun_externalFieldVec (N : ℕ) (μh : Measure ℝ) [IsProbabilityMeasure μh] :
    iIndepFun (fun i : Fin N => Function.eval i) (externalFieldVecLaw N μh) := by
  exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- Every coordinate of the i.i.d. external-field vector has law `μh`. -/
lemma measurePreserving_externalFieldVec_apply (N : ℕ) (μh : Measure ℝ)
  [IsProbabilityMeasure μh] (i : Fin N) :
    MeasurePreserving (Function.eval i) (externalFieldVecLaw N μh) μh := by
  exact measurePreserving_eval (μ := fun _ : Fin N => μh) i

/-- Every coupled site coordinate still has the original site law. -/
lemma measurePreserving_sharedReplicaExternalField_apply (N : ℕ) (μh : Measure ℝ)
    [IsProbabilityMeasure μh] (i : Fin N) (l : Fin 2) :
    MeasurePreserving (Function.eval (i, l)) (sharedReplicaExternalFieldLaw N μh) μh := by
  refine ⟨measurable_pi_apply _, ?_⟩
  rw [sharedReplicaExternalFieldLaw, Measure.map_map (measurable_pi_apply _)
    (measurable_sharedReplicaSiteField N)]
  exact (measurePreserving_externalFieldVec_apply N μh i).map_eq

/-- Integration of a one-coordinate observable reduces to integration against the site law. -/
lemma integral_externalFieldVec_apply (N : ℕ) (μh : Measure ℝ) [IsProbabilityMeasure μh]
    (i : Fin N) (f : ℝ → ℝ) (hf : AEStronglyMeasurable f μh) :
    ∫ hVec, f (hVec i) ∂externalFieldVecLaw N μh = ∫ h, f h ∂μh := by
  let P := externalFieldVecLaw N μh
  have hmap : P.map (Function.eval i) = μh :=
    (measurePreserving_externalFieldVec_apply N μh i).map_eq
  have hf' : AEStronglyMeasurable f (P.map (Function.eval i)) := by
    rw [hmap]
    exact hf
  calc
    ∫ hVec, f (hVec i) ∂P = ∫ h, f h ∂P.map (Function.eval i) :=
      (integral_map (measurable_pi_apply i).aemeasurable hf').symm
    _ = ∫ h, f h ∂μh := by rw [hmap]

lemma siteExternalFieldEnergy_eq_sum (N : ℕ) (hVec : Fin N → ℝ) :
    siteExternalFieldEnergy N hVec =
      ∑ i, hVec i • WithLp.toLp 2 (fun σ : Config N => isingSpin (σ i)) := by
  unfold siteExternalFieldEnergy
  simp only [← WithLp.toLp_smul, ← WithLp.toLp_sum]
  congr 1
  ext σ
  simp [Finset.sum_apply]

lemma continuous_siteExternalFieldEnergy (N : ℕ) : Continuous (siteExternalFieldEnergy N) := by
  change Continuous (fun hVec => siteExternalFieldEnergy N hVec)
  simp_rw [siteExternalFieldEnergy_eq_sum]
  exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

/-- A finite first moment of the site law makes the realized field energy integrable. -/
lemma integrable_siteExternalFieldEnergy (N : ℕ) {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) :
    Integrable (siteExternalFieldEnergy N) (externalFieldVecLaw N μh) := by
  change Integrable (fun hVec => siteExternalFieldEnergy N hVec) _
  simp_rw [siteExternalFieldEnergy_eq_sum]
  refine integrable_finsetSum _ fun i _ => ?_
  exact (((measurePreserving_externalFieldVec_apply N μh i).integrable_comp
    measurable_id.aestronglyMeasurable).2 hμh).smul_const _

/-- Integrability of the finite-volume model follows from the first moment of the site law. -/
theorem integrable_siteFieldMixedPSpinFreeEnergy (N : ℕ) {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμh : Integrable (fun h : ℝ => h) μh) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) :
    Integrable (siteFieldMixedPSpinFreeEnergy N ξ) (externalFieldVecLaw N μh) := by
  let P := externalFieldVecLaw N μh
  let G := GaussianField.ofMultivariateGaussian hS
  have hg : Integrable (fun q : (Fin N → ℝ) × EnergySpace N =>
      q.2 + siteExternalFieldEnergy N q.1) (P.prod (gaussField N (overlapCovMatrix N ξ))) :=
    (G.integrable.comp_snd P).add ((integrable_siteExternalFieldEnergy N hμh).comp_fst _)
  have hm : Measurable (fun q : (Fin N → ℝ) × EnergySpace N =>
      q.2 + siteExternalFieldEnergy N q.1) :=
    measurable_snd.add ((continuous_siteExternalFieldEnergy N).measurable.comp measurable_fst)
  have hf := integrable_wFreeEnergy_of_integrable_norm (fun _ : Config N => (1 : ℝ))
    (fun _ => zero_le_one) ⟨(fun _ => true), one_ne_zero⟩ N hm hg.norm
  change Integrable (fun hVec => ∫ H, SpinGlass.free_energy_density N
    (H + siteExternalFieldEnergy N hVec) ∂gaussField N (overlapCovMatrix N ξ)) _
  simpa [wFreeEnergy, wZ,
    SpinGlass.free_energy_density, SpinGlass.Z, P] using hf.integral_prod_left

end

end SpinGlass
