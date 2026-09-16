/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
import SpinGlass.Parisi.GuerraParisi
import SpinGlass.Parisi.RandomExternalField

/-!
# The Parisi functional with a quenched random external field

Talagrand's `h` in Vol. II, (14.83) is a real random variable.  Consequently `X₀` in (14.84)
contains an outer expectation over `h` as well as the root Gaussian mark `z₀`.  This file adds
that probability layer around the conditional one-site recursion and proves the bound for
the actual i.i.d. site model.  No Gaussian
assumption is made on the external field; a finite first absolute moment is sufficient.

The normalization is exactly that of `SpinGlass.parisiFunctional`: `log 2 + X₀` followed by the
correction term in (14.88)/(14.89).
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

noncomputable section

variable {N k : ℕ}

/-- Talagrand's `X₀` in (14.84), including the quenched expectation over the external-field law. -/
def randomFieldParisiX₀ (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) : ℝ :=
  ∫ h, parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x))) ∂μh

/-- The discrete Parisi functional (14.89) for a general quenched external-field law. -/
def randomFieldParisiFunctional (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) : ℝ :=
  Real.log 2 + randomFieldParisiX₀ μh ξ ms qs
    - (1 / 2) * ∑ p ∈ Finset.range (k + 1),
        mExt ms (p + 1) *
          (parisiTheta ξ (qExt qs (p + 2)) - parisiTheta ξ (qExt qs (p + 1)))

/-! ## Constant-field compatibility -/

@[simp] theorem randomFieldParisiX₀_dirac (h : ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    randomFieldParisiX₀ (Measure.dirac h) ξ ms qs
      = parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x))) := by
  simp [randomFieldParisiX₀]

@[simp] theorem randomFieldParisiFunctional_dirac (h : ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    randomFieldParisiFunctional (Measure.dirac h) ξ ms qs = parisiFunctional ξ h ms qs := by
  simp [randomFieldParisiFunctional, parisiFunctional]

@[simp] theorem randomFieldParisiFunctional_zeroField (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    randomFieldParisiFunctional (Measure.dirac 0) ξ ms qs = parisiFunctional ξ 0 ms qs := by
  exact randomFieldParisiFunctional_dirac 0 ξ ms qs

/-! ## First-moment integrability -/

private lemma integrable_logCoshRec_add_prod {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) {k : ℕ} (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) (v₀ : ℝ≥0) :
    Integrable (fun q : ℝ × ℝ => logCoshRec k ms vs (q.1 + q.2))
      (μh.prod (gaussianReal 0 v₀)) := by
  have hsum : Integrable (fun q : ℝ × ℝ => q.1 + q.2)
      (μh.prod (gaussianReal 0 v₀)) :=
    (hμh.comp_fst _).add ((integrable_id_gaussianReal 0 v₀).comp_snd μh)
  have hbound : Integrable (fun q : ℝ × ℝ => |q.1 + q.2| + ∑ p, (vs p : ℝ) / 2)
      (μh.prod (gaussianReal 0 v₀)) := hsum.abs.add (integrable_const _)
  refine hbound.mono'
    ((measurable_logCoshRec k ms vs).comp
      (measurable_fst.add measurable_snd)).aestronglyMeasurable ?_
  filter_upwards [] with q
  rw [Real.norm_eq_abs, abs_of_nonneg (logCoshRec_nonneg k ms vs hpos _)]
  exact logCoshRec_le k ms vs hpos hle _

/-- The root-Gaussian average is integrable against a site law with finite first moment. -/
theorem integrable_integral_logCoshRec_externalField {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμh : Integrable (fun h : ℝ => h) μh)
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1) (v₀ : ℝ≥0) :
    Integrable (fun h => ∫ a, logCoshRec k ms vs (h + a) ∂gaussianReal 0 v₀) μh :=
  (integrable_logCoshRec_add_prod hμh ms vs hpos hle v₀).integral_prod_left

/-- The map `h ↦ X₀(h)` is measurable for admissible positive exponents. -/
theorem measurable_parisiX₀_logCosh (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    Measurable fun h => parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x))) := by
  let vs : Fin k → ℝ≥0 := fun p => parisiVar ξ qs (p.val + 1)
  let v₀ : ℝ≥0 := parisiVar ξ qs 0
  have hjoint : Measurable fun q : ℝ × ℝ => logCoshRec k ms vs (q.1 + q.2) :=
    (measurable_logCoshRec k ms vs).comp (measurable_fst.add measurable_snd)
  have hinter : Measurable fun h => ∫ a, logCoshRec k ms vs (h + a) ∂gaussianReal 0 v₀ :=
    hjoint.stronglyMeasurable.integral_prod_right'.measurable
  have heq : ∀ h, parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))
      = (∫ a, logCoshRec k ms vs (h + a) ∂gaussianReal 0 v₀)
        + (parisiVar ξ qs (k + 1) : ℝ) / 2 := by
    intro h
    exact parisiX₀_logCosh_eq k ξ h ms qs hpos hle
  rw [funext heq]
  exact hinter.add_const _

/-- A finite first absolute moment of `h` suffices to integrate Talagrand's `X₀`. -/
theorem integrable_parisiX₀_logCosh {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    Integrable (fun h => parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))) μh := by
  let vs : Fin k → ℝ≥0 := fun p => parisiVar ξ qs (p.val + 1)
  let v₀ : ℝ≥0 := parisiVar ξ qs 0
  have hjoint := integrable_logCoshRec_add_prod hμh ms vs hpos hle v₀
  have hinter : Integrable (fun h => ∫ a, logCoshRec k ms vs (h + a)
      ∂gaussianReal 0 v₀) μh := hjoint.integral_prod_left
  have htotal := hinter.add (integrable_const ((parisiVar ξ qs (k + 1) : ℝ) / 2))
  refine htotal.congr (Filter.Eventually.of_forall fun h => ?_)
  exact (parisiX₀_logCosh_eq k ξ h ms qs hpos hle).symm

/-- The random-field Parisi functional is integrable as an average of the deterministic one. -/
theorem integrable_parisiFunctional_externalField {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    Integrable (fun h => parisiFunctional ξ h ms qs) μh := by
  unfold parisiFunctional
  exact ((integrable_const _).add
    (integrable_parisiX₀_logCosh hμh ξ ms qs hpos hle)).sub (integrable_const _)

/-! ## Equivalent forms of the functional -/

/-- The law-level functional is the quenched average of the deterministic-field functional. -/
theorem randomFieldParisiFunctional_eq_integral {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ)
    (qs : Fin (k + 1) → ℝ) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    randomFieldParisiFunctional μh ξ ms qs = ∫ h, parisiFunctional ξ h ms qs ∂μh := by
  have hX := integrable_parisiX₀_logCosh hμh ξ ms qs hpos hle
  let X : ℝ → ℝ := fun h => parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))
  let C : ℝ := (1 / 2) * ∑ p ∈ Finset.range (k + 1),
    mExt ms (p + 1) *
      (parisiTheta ξ (qExt qs (p + 2)) - parisiTheta ξ (qExt qs (p + 1)))
  change Real.log 2 + (∫ h, X h ∂μh) - C = ∫ h, (Real.log 2 + X h) - C ∂μh
  have hXi : Integrable X μh := hX
  calc
    Real.log 2 + (∫ h, X h ∂μh) - C
        = (∫ h, Real.log 2 + X h ∂μh) - ∫ _h, C ∂μh := by
            rw [integral_add (integrable_const _) hXi, integral_const, integral_const]
            simp only [probReal_univ, one_smul]
    _ = ∫ h, (Real.log 2 + X h) - C ∂μh :=
      (integral_sub ((integrable_const _).add hXi) (integrable_const C)).symm

/-- Talagrand's summation-by-parts form (14.403), now with the quenched `X₀`. -/
theorem randomFieldParisiFunctional_eq_theta_sum (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) :
    randomFieldParisiFunctional μh ξ ms qs
      = Real.log 2 + randomFieldParisiX₀ μh ξ ms qs
        + (1 / 2) * ∑ p ∈ Finset.range (k + 1),
            parisiTheta ξ (qExt qs (p + 1)) * (mExt ms (p + 1) - mExt ms p)
        - (1 / 2) * parisiTheta ξ 1 := by
  have h := parisiFunctional_eq_theta_sum ξ 0 ms qs
  unfold parisiFunctional at h
  unfold randomFieldParisiFunctional
  linarith

/-! ## I.i.d. site-field model -/

/-- Averaging the site sum against the product law gives the one-site Parisi functional. -/
theorem integral_siteAverage_parisiFunctional {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (hN : 0 < N) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    (∫ hVec, (1 / (N : ℝ)) * ∑ i, parisiFunctional ξ (hVec i) ms qs
      ∂externalFieldVecLaw N μh) = randomFieldParisiFunctional μh ξ ms qs := by
  have hPF := integrable_parisiFunctional_externalField hμh ξ ms qs hpos hle
  have hi : ∀ i : Fin N, Integrable (fun hVec : Fin N → ℝ =>
      parisiFunctional ξ (hVec i) ms qs) (externalFieldVecLaw N μh) := fun i =>
    ((measurePreserving_externalFieldVec_apply N μh i).integrable_comp
      hPF.aestronglyMeasurable).2 hPF
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hi i]
  simp_rw [integral_externalFieldVec_apply N μh _ _ hPF.aestronglyMeasurable]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, one_div, inv_mul_cancel₀ (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0),
    one_mul]
  exact (randomFieldParisiFunctional_eq_integral hμh ξ ms qs hpos hle).symm

/-- Guerra's bound for independent, identically distributed quenched site fields.
A probability site law with finite first absolute moment suffices. -/
theorem iidFieldMixedPSpinFreeEnergy_le_randomFieldParisiFunctional
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (qs : Fin (k + 1) → ℝ) (ms : Fin k → ℝ)
    (h0 : deriv ξ 0 = 0)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (hq01 : ∀ r, qExt qs r ∈ Set.Icc (0 : ℝ) 1)
    (htan : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) :
    iidFieldMixedPSpinFreeEnergy N μh ξ ≤ randomFieldParisiFunctional μh ξ ms qs := by
  have hPF := integrable_parisiFunctional_externalField hμh ξ ms qs hpos (fun i => (hlt i).le)
  have hAvg : Integrable (fun hVec : Fin N → ℝ =>
      (1 / (N : ℝ)) * ∑ i, parisiFunctional ξ (hVec i) ms qs)
      (externalFieldVecLaw N μh) :=
    (integrable_finsetSum _ fun i _ =>
      ((measurePreserving_externalFieldVec_apply N μh i).integrable_comp
        hPF.aestronglyMeasurable).2 hPF).const_mul _
  rw [← integral_siteAverage_parisiFunctional hμh hN ξ ms qs hpos (fun i => (hlt i).le)]
  exact integral_mono (integrable_siteFieldMixedPSpinFreeEnergy N hμh ξ hS) hAvg fun hVec =>
    siteFieldMixedPSpinFreeEnergy_le_parisiFunctional N k hN ξ hS qs ms h0 hmono hq01
      htan hsm hpos hlt hVec

/-- The i.i.d. Guerra bound under convexity and differentiability of the covariance profile. -/
theorem iidFieldMixedPSpinFreeEnergy_le_randomFieldParisiFunctional_of_convexOn
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (hconv : ConvexOn ℝ Set.univ ξ)
    (hdiff : Differentiable ℝ ξ) (h0 : deriv ξ 0 = 0) (qs : Fin (k + 1) → ℝ)
    (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1)
    (ms : Fin k → ℝ) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1) :
    iidFieldMixedPSpinFreeEnergy N μh ξ ≤ randomFieldParisiFunctional μh ξ ms qs := by
  have hderiv : Monotone (deriv ξ) :=
    monotoneOn_univ.1 (hconv.monotoneOn_deriv fun x _ => hdiff x)
  refine iidFieldMixedPSpinFreeEnergy_le_randomFieldParisiFunctional hμh hN ξ hS qs ms h0
    (fun r hr => hderiv (qExt_le_succ hqmono hq0 hq1 hr))
    (fun r => qExt_mem_Icc hqmono hq0 hq1 r) (fun x _ q _ => ?_) hsm hpos hlt
  rw [mul_comm (x - q) (deriv ξ q)]
  exact hconv.add_deriv_mul_sub_le_univ hdiff q x

/-- Guerra's i.i.d. bound with repeated positive Parisi exponents. -/
theorem iidFieldMixedPSpinFreeEnergy_le_randomFieldParisiFunctional_of_monotone
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (qs : Fin (k + 1) → ℝ) (ms : Fin k → ℝ)
    (h0 : deriv ξ 0 = 0)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (hq01 : ∀ r, qExt qs r ∈ Set.Icc (0 : ℝ) 1)
    (htan : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (hmsm : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    iidFieldMixedPSpinFreeEnergy N μh ξ ≤ randomFieldParisiFunctional μh ξ ms qs := by
  have hPF := integrable_parisiFunctional_externalField hμh ξ ms qs hpos hle
  have hAvg : Integrable (fun hVec : Fin N → ℝ =>
      (1 / (N : ℝ)) * ∑ i, parisiFunctional ξ (hVec i) ms qs)
      (externalFieldVecLaw N μh) :=
    (integrable_finsetSum _ fun i _ =>
      ((measurePreserving_externalFieldVec_apply N μh i).integrable_comp
        hPF.aestronglyMeasurable).2 hPF).const_mul _
  rw [← integral_siteAverage_parisiFunctional hμh hN ξ ms qs hpos hle]
  exact integral_mono (integrable_siteFieldMixedPSpinFreeEnergy N hμh ξ hS) hAvg fun hVec =>
    siteFieldMixedPSpinFreeEnergy_le_parisiFunctional_of_monotone N k hN ξ hS qs ms h0 hmono hq01
      htan hmsm hpos hle hVec

/-- The i.i.d. Guerra bound under convexity and differentiability of the covariance profile. -/
theorem iidFieldMixedPSpinFreeEnergy_le_randomFieldParisiFunctional_of_convexOn_of_monotone
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (hconv : ConvexOn ℝ Set.univ ξ)
    (hdiff : Differentiable ℝ ξ) (h0 : deriv ξ 0 = 0) (qs : Fin (k + 1) → ℝ)
    (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1)
    (ms : Fin k → ℝ) (hmsm : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    iidFieldMixedPSpinFreeEnergy N μh ξ ≤ randomFieldParisiFunctional μh ξ ms qs := by
  have hderiv : Monotone (deriv ξ) :=
    monotoneOn_univ.1 (hconv.monotoneOn_deriv fun x _ => hdiff x)
  refine iidFieldMixedPSpinFreeEnergy_le_randomFieldParisiFunctional_of_monotone hμh hN ξ hS qs ms h0
    (fun r hr => hderiv (qExt_le_succ hqmono hq0 hq1 hr))
    (fun r => qExt_mem_Icc hqmono hq0 hq1 r) (fun x _ q _ => ?_) hmsm hpos hle
  rw [mul_comm (x - q) (deriv ξ q)]
  exact hconv.add_deriv_mul_sub_le_univ hdiff q x

/-- Guerra's bound for SK with a general i.i.d. field, including repeated exponents. -/
theorem iidFieldSKFreeEnergy_le_randomFieldParisiFunctional_of_monotone
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (hN : 0 < N) (β : ℝ)
    (qs : Fin (k + 1) → ℝ) (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0)
    (hq1 : qs (Fin.last k) ≤ 1) (ms : Fin k → ℝ) (hmsm : Monotone ms)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1) :
    iidFieldSKFreeEnergy N μh β ≤ randomFieldParisiFunctional μh (skCovXi β) ms qs :=
  iidFieldMixedPSpinFreeEnergy_le_randomFieldParisiFunctional_of_convexOn_of_monotone hμh hN
    (skCovXi β) (posSemidef_skCovMatrix N β) (convexOn_univ_skCovXi β)
    (differentiable_skCovXi β) (deriv_skCovXi_zero β) qs hqmono hq0 hq1 ms hmsm hpos hle

/-! ## Replica-symmetric check -/

/-- For `k = 0`, the quenched functional has Talagrand's replica-symmetric form: the outer
expectation is over `h`, while the inner expectation is over the independent root Gaussian mark. -/
theorem randomFieldParisiFunctional_zero {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (ξ : ℝ → ℝ) (ms : Fin 0 → ℝ)
    (qs : Fin 1 → ℝ) :
    randomFieldParisiFunctional μh ξ ms qs
      = Real.log 2
        + (∫ h, ∫ z, Real.log (Real.cosh (h + z))
            ∂gaussianReal 0 (parisiVar ξ qs 0) ∂μh)
        + (parisiVar ξ qs 1 : ℝ) / 2
        - (1 / 2) * (parisiTheta ξ 1 - parisiTheta ξ (qs 0)) := by
  let L : ℝ → ℝ := fun h => ∫ z, Real.log (Real.cosh (h + z))
    ∂gaussianReal 0 (parisiVar ξ qs 0)
  have hX := integrable_parisiX₀_logCosh hμh ξ ms qs
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  have hL : Integrable L μh := by
    have hsub := hX.sub (integrable_const ((parisiVar ξ qs 1 : ℝ) / 2))
    refine hsub.congr (Filter.Eventually.of_forall fun h => ?_)
    change parisiX₀ ξ ms qs (fun x => Real.log (Real.cosh (h + x)))
      - (parisiVar ξ qs 1 : ℝ) / 2 = L h
    rw [parisiX₀_logCosh_zero]
    simp only [L]
    ring
  unfold randomFieldParisiFunctional randomFieldParisiX₀
  rw [integral_congr_ae (Filter.Eventually.of_forall fun h =>
      parisiX₀_logCosh_zero ξ h ms qs),
    integral_add hL (integrable_const _), integral_const]
  simp only [probReal_univ, one_smul, L]
  rw [Finset.sum_range_one, mExt_of_zero_lt (by norm_num),
    qExt_of_le qs (by norm_num), qExt_succ_of_lt qs zero_lt_one, one_mul, Fin.zero_eta]
  ring

/-! ## Guerra's bound after averaging the external field

The statements in this section average the finite-volume free energy with a spatially constant
field `h` against `μh`.  The name is deliberately explicit: this is the law-level consequence of
the deterministic Guerra bound.  The genuinely i.i.d. site-field model uses
`externalFieldVecLaw`; it must not be identified with this averaged constant-field model.
-/

/-- Guerra's bound integrated against an external-field law.  No Gaussian assumption is imposed
on `μh`.  A finite first moment controls the Parisi side; integrability of the finite-volume side
is stated explicitly so this theorem applies to any realization of the model. -/
theorem integral_mixedPSpinFreeEnergy_le_randomFieldParisiFunctional
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (qs : Fin (k + 1) → ℝ) (ms : Fin k → ℝ)
    (h0 : deriv ξ 0 = 0)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (hq01 : ∀ r, qExt qs r ∈ Set.Icc (0 : ℝ) 1)
    (htan : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (hFE : Integrable (fun h => mixedPSpinFreeEnergy N ξ h) μh) :
    (∫ h, mixedPSpinFreeEnergy N ξ h ∂μh)
      ≤ randomFieldParisiFunctional μh ξ ms qs := by
  have hPF : Integrable (fun h => parisiFunctional ξ h ms qs) μh :=
    integrable_parisiFunctional_externalField hμh ξ ms qs hpos (fun i => (hlt i).le)
  have hpoint : ∀ h, mixedPSpinFreeEnergy N ξ h ≤ parisiFunctional ξ h ms qs := fun h =>
    mixedPSpinFreeEnergy_le_parisiFunctional N k hN ξ hS qs ms h0 hmono hq01 htan
      hsm hpos hlt h
  rw [randomFieldParisiFunctional_eq_integral hμh ξ ms qs hpos (fun i => (hlt i).le)]
  exact integral_mono hFE hPF hpoint

/-- The averaged random-field bound under convexity and differentiability of the covariance
profile. -/
theorem integral_mixedPSpinFreeEnergy_le_randomFieldParisiFunctional_of_convexOn
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (hconv : ConvexOn ℝ Set.univ ξ)
    (hdiff : Differentiable ℝ ξ) (h0 : deriv ξ 0 = 0) (qs : Fin (k + 1) → ℝ)
    (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1)
    (ms : Fin k → ℝ) (hsm : StrictMono ms) (hpos : ∀ i, 0 < ms i)
    (hlt : ∀ i, ms i < 1)
    (hFE : Integrable (fun h => mixedPSpinFreeEnergy N ξ h) μh) :
    (∫ h, mixedPSpinFreeEnergy N ξ h ∂μh)
      ≤ randomFieldParisiFunctional μh ξ ms qs := by
  have hPF : Integrable (fun h => parisiFunctional ξ h ms qs) μh :=
    integrable_parisiFunctional_externalField hμh ξ ms qs hpos (fun i => (hlt i).le)
  rw [randomFieldParisiFunctional_eq_integral hμh ξ ms qs hpos (fun i => (hlt i).le)]
  exact integral_mono hFE hPF fun h =>
    mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn N k hN ξ hS hconv hdiff h0
      qs hqmono hq0 hq1 ms hsm hpos hlt h

/-- Guerra's averaged random-field bound for nondecreasing Parisi exponents. -/
theorem integral_mixedPSpinFreeEnergy_le_randomFieldParisiFunctional_of_monotone
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (qs : Fin (k + 1) → ℝ) (ms : Fin k → ℝ)
    (h0 : deriv ξ 0 = 0)
    (hmono : ∀ r, r ≤ k + 1 → deriv ξ (qExt qs r) ≤ deriv ξ (qExt qs (r + 1)))
    (hq01 : ∀ r, qExt qs r ∈ Set.Icc (0 : ℝ) 1)
    (htan : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      ξ q + (x - q) * deriv ξ q ≤ ξ x)
    (hmsm : Monotone ms) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hFE : Integrable (fun h => mixedPSpinFreeEnergy N ξ h) μh) :
    (∫ h, mixedPSpinFreeEnergy N ξ h ∂μh)
      ≤ randomFieldParisiFunctional μh ξ ms qs := by
  have hPF : Integrable (fun h => parisiFunctional ξ h ms qs) μh :=
    integrable_parisiFunctional_externalField hμh ξ ms qs hpos hle
  rw [randomFieldParisiFunctional_eq_integral hμh ξ ms qs hpos hle]
  exact integral_mono hFE hPF fun h =>
    mixedPSpinFreeEnergy_le_parisiFunctional_of_monotone N k hN ξ hS qs ms h0 hmono
      hq01 htan hmsm hpos hle h

/-- The averaged random-field bound under Talagrand's hypotheses, allowing repeated Parisi
exponents. -/
theorem integral_mixedPSpinFreeEnergy_le_randomFieldParisiFunctional_of_convexOn_of_monotone
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (hN : 0 < N) (ξ : ℝ → ℝ)
    (hS : (overlapCovMatrix N ξ).PosSemidef) (hconv : ConvexOn ℝ Set.univ ξ)
    (hdiff : Differentiable ℝ ξ) (h0 : deriv ξ 0 = 0) (qs : Fin (k + 1) → ℝ)
    (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0) (hq1 : qs (Fin.last k) ≤ 1)
    (ms : Fin k → ℝ) (hmsm : Monotone ms) (hpos : ∀ i, 0 < ms i)
    (hle : ∀ i, ms i ≤ 1)
    (hFE : Integrable (fun h => mixedPSpinFreeEnergy N ξ h) μh) :
    (∫ h, mixedPSpinFreeEnergy N ξ h ∂μh)
      ≤ randomFieldParisiFunctional μh ξ ms qs := by
  have hPF : Integrable (fun h => parisiFunctional ξ h ms qs) μh :=
    integrable_parisiFunctional_externalField hμh ξ ms qs hpos hle
  rw [randomFieldParisiFunctional_eq_integral hμh ξ ms qs hpos hle]
  exact integral_mono hFE hPF fun h =>
    mixedPSpinFreeEnergy_le_parisiFunctional_of_convexOn_of_monotone N k hN ξ hS
      hconv hdiff h0 qs hqmono hq0 hq1 ms hmsm hpos hle h

/-- The averaged random-field Guerra bound for the Sherrington-Kirkpatrick model. -/
theorem integral_skFreeEnergy_le_randomFieldParisiFunctional_of_monotone
    {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμh : Integrable (fun h : ℝ => h) μh) (hN : 0 < N) (β : ℝ)
    (qs : Fin (k + 1) → ℝ) (hqmono : Monotone qs) (hq0 : 0 ≤ qs 0)
    (hq1 : qs (Fin.last k) ≤ 1) (ms : Fin k → ℝ) (hmsm : Monotone ms)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (hFE : Integrable (fun h => skFreeEnergy N β h) μh) :
    (∫ h, skFreeEnergy N β h ∂μh)
      ≤ randomFieldParisiFunctional μh (skCovXi β) ms qs := by
  have hPF : Integrable (fun h => parisiFunctional (skCovXi β) h ms qs) μh :=
    integrable_parisiFunctional_externalField hμh (skCovXi β) ms qs hpos hle
  rw [randomFieldParisiFunctional_eq_integral hμh (skCovXi β) ms qs hpos hle]
  exact integral_mono hFE hPF fun h =>
    skFreeEnergy_le_parisiFunctional_of_monotone N k hN β h qs hqmono hq0 hq1 ms
      hmsm hpos hle

end

end SpinGlass
