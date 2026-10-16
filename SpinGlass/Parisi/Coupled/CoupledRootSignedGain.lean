import SpinGlass.Parisi.Coupled.CoupledSignedRootSite
import SpinGlass.Parisi.Coupled.CoupledSignedRootLaw

/-!
# Concrete signed-root coupling and its mass limit

The root fields read independent driven and auxiliary Gaussians as D+E
and -D+E. The positive inserted-mass conditional recursion is differentiated
under the actual probability field/root law. Its slope converges to the
canonical signed response of the unchanged Parisi recursion.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators

namespace SpinGlass

open Aristotle.Heat

def signedRootEffectiveField (h : ℝ) (z : ℝ × ℝ) : Fin 2 → ℝ :=
  ![h + z.1 + z.2, h - z.1 + z.2]

theorem measurable_signedRootEffectiveField :
    Measurable (fun hz : ℝ × (ℝ × ℝ) => signedRootEffectiveField hz.1 hz.2) := by
  unfold signedRootEffectiveField
  fun_prop

noncomputable def parisiRootSignedCouplingValue (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u m lam : ℝ) : ℝ :=
  let v := t * (deriv ξ (qs 0) - deriv ξ |u|)
  ∫ hz : ℝ × (ℝ × ℝ), independentPairSiteRec (parisiRootResponseMasses ms m)
    (parisiRootResponseVars ξ qs v) lam (signedRootEffectiveField hz.1 hz.2)
    ∂μh.prod ((gaussianReal 0 (parisiRootDrivenRootVar ξ qs t |u|)).prod
      (gaussianReal 0 (parisiAuxRootVar ξ qs t)))

noncomputable def parisiRootSignedCouplingMassMoment (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u m : ℝ) : ℝ :=
  let v := t * (deriv ξ (qs 0) - deriv ξ |u|)
  ∫ hz : ℝ × (ℝ × ℝ),
    deriv (coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs)) (signedRootEffectiveField hz.1 hz.2 0) *
    deriv (coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs)) (signedRootEffectiveField hz.1 hz.2 1)
    ∂μh.prod ((gaussianReal 0 (parisiRootDrivenRootVar ξ qs t |u|)).prod
      (gaussianReal 0 (parisiAuxRootVar ξ qs t)))

/-- Both effective root fields are integrable under a finite first
external-field moment, with no exponential field-moment requirement. -/
theorem integrable_signedRootEffectiveField {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (d e : ℝ≥0) (l : Fin 2) :
    Integrable (fun hz : ℝ × (ℝ × ℝ) => signedRootEffectiveField hz.1 hz.2 l)
      (μh.prod ((gaussianReal 0 d).prod (gaussianReal 0 e))) := by
  have hD : Integrable id (gaussianReal 0 d) := IsGaussian.integrable_id
  have hE : Integrable id (gaussianReal 0 e) := IsGaussian.integrable_id
  have hDr : Integrable (fun z : ℝ × ℝ => z.1) ((gaussianReal 0 d).prod (gaussianReal 0 e)) :=
    hD.comp_fst _
  have hEr : Integrable (fun z : ℝ × ℝ => z.2) ((gaussianReal 0 d).prod (gaussianReal 0 e)) :=
    hE.comp_snd _
  fin_cases l
  · exact ((hμ.comp_fst _).add (hDr.comp_snd _)).add (hEr.comp_snd _)
  · exact ((hμ.comp_fst _).sub (hDr.comp_snd _)).add (hEr.comp_snd _)

/-- The actual zero-coupling conditional recursion is integrable
before differentiating its external-field/root average. -/
theorem integrable_independentPairSiteRec_parisi_signed_root_zero
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1)
    (v : ℝ) (d e : ℝ≥0) :
    Integrable (fun hz : ℝ × (ℝ × ℝ) => independentPairSiteRec (parisiRootResponseMasses ms m)
      (parisiRootResponseVars ξ qs v) 0 (signedRootEffectiveField hz.1 hz.2))
      (μh.prod ((gaussianReal 0 d).prod (gaussianReal 0 e))) := by
  have hi (l : Fin 2) := integrable_coleHopf_comp_shift
    ((measurable_pi_apply l).comp measurable_signedRootEffectiveField)
    (integrable_signedRootEffectiveField hμ d e l)
    (parisiRootSuffix_spatial_regular_four ξ ms qs).1.continuous.measurable
    (abs_parisiRootSuffix_sub_le ξ ms qs) m v.toNNReal
  exact ((hi 0).add (hi 1)).congr (.of_forall fun hz =>
    (independentPairSiteRec_parisi_root_zero ξ ms qs hm hm0 hm1 v
      (signedRootEffectiveField hz.1 hz.2)).symm)

/-- The signed positive-mass coupling has its actual product-gradient
slope after the probability external-field/root average. -/
theorem hasDerivAt_parisiRootSignedCouplingValue_zero {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (t u : ℝ) :
    HasDerivAt (parisiRootSignedCouplingValue μh ξ ms qs t u m)
      (parisiRootSignedCouplingMassMoment μh ξ ms qs t u m) 0 := by
  let v := t * (deriv ξ (qs 0) - deriv ξ |u|)
  have hd := hasDerivAt_integral_independentPairSiteRec_zero
    (parisiRootResponseMasses ms m) (parisiRootResponseVars ξ qs v)
    (parisiRootResponseMasses_pos ms hm hm0) (parisiRootResponseMasses_le_one ms hm hm1)
    measurable_signedRootEffectiveField
    (integrable_independentPairSiteRec_parisi_signed_root_zero hμ ξ ms qs hm hm0 hm1 v
      (parisiRootDrivenRootVar ξ qs t |u|) (parisiAuxRootVar ξ qs t))
  unfold parisiRootSignedCouplingValue parisiRootSignedCouplingMassMoment
  simpa only [parisiRootResponseMasses, parisiRootResponseVars, coleHopfIterate_succ,
    Fin.cons_zero, Fin.tail_cons, parisiRootSuffix, v] using hd

/-- The signed coupling slope has a zero inserted-mass limit under
the actual probability external-field and independent root Gaussians. -/
theorem continuousAt_parisiRootSignedCouplingMassMoment_zero {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u : ℝ) :
    ContinuousAt (fun m => parisiRootSignedCouplingMassMoment μh ξ ms qs t u m) 0 := by
  obtain ⟨hA, C, hC⟩ := parisiRootSuffix_spatial_regular_four ξ ms qs
  have hs : ∀ y, |deriv (deriv (parisiRootSuffix ξ ms qs)) y| ≤ C := by
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero] using
      hC 2 (by decide)
  exact continuousAt_integral_pair_deriv_coleHopf_mass_zero measurable_signedRootEffectiveField
    (hA.of_le (by norm_num)) (abs_parisiRootSuffix_sub_le ξ ms qs) hs
    (t * (deriv ξ (qs 0) - deriv ξ |u|)).toNNReal

/-- The signed positive-mass slope is a bounded integrable observable
under its actual probability external-field/root law. -/
theorem integrable_parisiRootSignedCouplingGradientProduct {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u m : ℝ) :
    let v := t * (deriv ξ (qs 0) - deriv ξ |u|)
    Integrable (fun hz : ℝ × (ℝ × ℝ) =>
      deriv (coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs)) (signedRootEffectiveField hz.1 hz.2 0) *
      deriv (coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs)) (signedRootEffectiveField hz.1 hz.2 1))
      (μh.prod ((gaussianReal 0 (parisiRootDrivenRootVar ξ qs t |u|)).prod
        (gaussianReal 0 (parisiAuxRootVar ξ qs t)))) := by
  let v := t * (deriv ξ (qs 0) - deriv ξ |u|)
  let B := coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs)
  have hL : ∀ x y, |parisiRootSuffix ξ ms qs y - parisiRootSuffix ξ ms qs x| ≤ 1 * |y - x| := by
    simpa only [one_mul] using abs_parisiRootSuffix_sub_le ξ ms qs
  have hLip := lipschitzWith_toNNReal_of_abs_sub_le
    (abs_coleHopf_sub_le_of_lipschitz m
      (parisiRootSuffix_spatial_regular_four ξ ms qs).1.continuous.measurable hL v.toNNReal)
  have hB : ∀ x, |deriv B x| ≤ 1 := fun x => by
    simpa only [Real.norm_eq_abs, Real.toNNReal_one, NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := x) hLip
  apply Integrable.of_bound
    (((measurable_deriv B).comp ((measurable_pi_apply 0).comp measurable_signedRootEffectiveField)).mul
      ((measurable_deriv B).comp ((measurable_pi_apply 1).comp measurable_signedRootEffectiveField))).aestronglyMeasurable 1
  exact .of_forall fun hz => by
    change |deriv B (signedRootEffectiveField hz.1 hz.2 0) *
      deriv B (signedRootEffectiveField hz.1 hz.2 1)| ≤ 1
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hB _) (hB _) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- The zero-mass signed slope is exactly the canonical signed
response moment of the original recursion. -/
theorem parisiRootSignedCouplingMassMoment_zero {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hq : ParisiQAdmissible qs)
    {t u : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hu : |u| ≤ qs 0) :
    parisiRootSignedCouplingMassMoment μh ξ ms qs t u 0 = parisiRootSignedMoment μh ξ ms qs t u := by
  let a := deriv ξ (qs 0) - deriv ξ 0
  let b := deriv ξ |u| - deriv ξ 0
  let v := t * (deriv ξ (qs 0) - deriv ξ |u|)
  let d := parisiRootDrivenRootVar ξ qs t |u|
  let e := parisiAuxRootVar ξ qs t
  let A := parisiRootSuffix ξ ms qs
  have habs : |u| ∈ Icc (0 : ℝ) (qs 0) := ⟨abs_nonneg _, hu⟩
  have hv := parisi_root_time_variance_mem_Icc hξ qs hq ht habs
  have hde : d + e = (a - v).toNNReal := parisiRootDrivenRootVar_add_aux_eq hξ qs hq ht habs
  have hb : 0 ≤ b := sub_nonneg.2 (hξ.strictMonoOn_deriv.monotoneOn ⟨le_rfl, zero_le_one⟩
    ⟨abs_nonneg _, hu.trans (hq.mem_Icc 0).2⟩ (abs_nonneg _))
  have hd : (d : ℝ) = t * b := by
    simp only [d, parisiRootDrivenRootVar, parisiVar_splitParisiRootOverlap_root,
      NNReal.coe_mul, Real.coe_toNNReal _ ht.1]
    change t * (b.toNNReal : ℝ) = t * b
    rw [Real.coe_toNNReal _ hb]
  obtain ⟨hA, C, hC⟩ := parisiRootSuffix_spatial_regular_four ξ ms qs
  have hfirst : ∀ y, |deriv A y| ≤ 1 := by
    have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
      simpa only [one_mul] using abs_parisiRootSuffix_sub_le ξ ms qs
    intro y
    simpa only [Real.norm_eq_abs, Real.toNNReal_one, NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := y) (lipschitzWith_toNNReal_of_abs_sub_le hL)
  have hsecond : ∀ y, |deriv (deriv A) y| ≤ C := by
    simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_zero] using
      hC 2 (by decide)
  have hgrad (y : ℝ) : deriv (coleHopf 0 v.toNNReal A) y = heat v.toNNReal (deriv A) y := by
    simpa only [coleHopfQ_zero, mul_one, heat, Real.toNNReal_coe] using
      ((coleHopf_spatial_derivative_formulas (hA.of_le (by norm_num)) hfirst hsecond
        0 v.toNNReal).1 y).deriv
  have htotal : (d : ℝ) + e + v.toNNReal = a := by
    have hh := congrArg (fun z : ℝ≥0 => (z : ℝ)) hde
    rw [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.2 hv.2)] at hh
    rw [Real.coe_toNNReal _ hv.1]
    dsimp only [a, v] at hh ⊢
    linarith
  have hanti : (d : ℝ) + (v.toNNReal : ℝ) / 2 = t * (a + b) / 2 := by
    rw [hd, Real.coe_toNNReal _ hv.1]
    dsimp only [a, b, v]
    ring
  let F := fun hz : ℝ × (ℝ × ℝ) =>
    deriv (coleHopf 0 v.toNNReal A) (signedRootEffectiveField hz.1 hz.2 0) *
      deriv (coleHopf 0 v.toNNReal A) (signedRootEffectiveField hz.1 hz.2 1)
  have hi : Integrable F (μh.prod ((gaussianReal 0 d).prod (gaussianReal 0 e))) :=
    integrable_parisiRootSignedCouplingGradientProduct ξ ms qs t u 0
  unfold parisiRootSignedCouplingMassMoment parisiRootSignedMoment
  change (∫ hz, F hz ∂μh.prod ((gaussianReal 0 d).prod (gaussianReal 0 e))) =
    ∫ h, gaussianFixedVarianceCorrelation a (t * (a + b) / 2) (deriv A) h ∂μh
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact .of_forall fun h => by
    have hroot : Integrable (fun z : ℝ × ℝ => F (h, z)) ((gaussianReal 0 d).prod (gaussianReal 0 e)) := by
      have hB : ∀ y, |deriv (coleHopf 0 v.toNNReal A) y| ≤ 1 := by
        have hL : ∀ x y, |A y - A x| ≤ 1 * |y - x| := by
          simpa only [one_mul] using abs_parisiRootSuffix_sub_le ξ ms qs
        intro y
        simpa only [Real.norm_eq_abs, Real.toNNReal_one, NNReal.coe_one] using
          norm_deriv_le_of_lipschitz (x₀ := y) (lipschitzWith_toNNReal_of_abs_sub_le
            (abs_coleHopf_sub_le_of_lipschitz 0 hA.continuous.measurable hL v.toNNReal))
      apply Integrable.of_bound
        ((((measurable_deriv (coleHopf 0 v.toNNReal A)).comp
          ((measurable_pi_apply 0).comp (measurable_signedRootEffectiveField.comp
            (measurable_const.prodMk measurable_id)))).mul
          ((measurable_deriv (coleHopf 0 v.toNNReal A)).comp
            ((measurable_pi_apply 1).comp (measurable_signedRootEffectiveField.comp
              (measurable_const.prodMk measurable_id)))))).aestronglyMeasurable 1
      exact .of_forall fun z => by
        change |deriv (coleHopf 0 v.toNNReal A) (signedRootEffectiveField h z 0) *
          deriv (coleHopf 0 v.toNNReal A) (signedRootEffectiveField h z 1)| ≤ 1
        rw [abs_mul]
        simpa only [one_mul] using mul_le_mul (hB _) (hB _) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    change (∫ z : ℝ × ℝ, F (h, z) ∂(gaussianReal 0 d).prod (gaussianReal 0 e)) = _
    rw [integral_prod _ hroot]
    simp only [F, signedRootEffectiveField, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp_rw [hgrad]
    rw [integral_gaussian_signed_root_heat_eq_correlation (hA.continuous_deriv (by norm_num))
      hfirst d e v.toNNReal h, htotal, hanti]

/-- A fixed external field leaves both signed root coordinates
integrable under the independent Gaussian roots. -/
theorem integrable_signedRootEffectiveField_fixed (h : ℝ) (d e : ℝ≥0) (l : Fin 2) :
    Integrable (fun z : ℝ × ℝ => signedRootEffectiveField h z l)
      ((gaussianReal 0 d).prod (gaussianReal 0 e)) := by
  have hD : Integrable id (gaussianReal 0 d) := IsGaussian.integrable_id
  have hE : Integrable id (gaussianReal 0 e) := IsGaussian.integrable_id
  fin_cases l
  · exact ((integrable_const h).add (hD.comp_fst _)).add (hE.comp_snd _)
  · exact ((integrable_const h).sub (hD.comp_fst _)).add (hE.comp_snd _)

/-- Either effective field of a fixed signed root has the scalar
Gaussian marginal of variance d+e. -/
theorem integral_signedRootEffectiveField_eq_marginal {B : ℝ → ℝ} (hB : Measurable B)
    (h : ℝ) (d e : ℝ≥0) (l : Fin 2) :
    (∫ z : ℝ × ℝ, B (signedRootEffectiveField h z l)
      ∂(gaussianReal 0 d).prod (gaussianReal 0 e)) =
      ∫ z, B (h + z) ∂gaussianReal 0 (d + e) := by
  have hm : Measurable (fun z : ℝ × ℝ => (if l = 0 then z.1 else -z.1) + z.2) := by
    split_ifs <;> fun_prop
  have hi := integral_map (μ := (gaussianReal 0 d).prod (gaussianReal 0 e))
    (f := fun z => B (h + z)) hm.aemeasurable
    (hB.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  rw [map_gaussianReal_prod_signed_sum] at hi
  rw [hi]
  apply integral_congr_ae
  exact .of_forall fun z => by
    fin_cases l <;> simp [signedRootEffectiveField, sub_eq_add_neg, add_assoc]

/-- The signed positive-mass recursion has the same zero-coupling
value as the original scalar root insertion because both marginals agree. -/
theorem parisiRootSignedCouplingValue_zero {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t u m : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : |u| ≤ qs 0) (hm0 : 0 < m) (hm1 : m ≤ 1) :
    parisiRootSignedCouplingValue μh ξ ms qs t u m 0 =
      2 * parisiRootCouplingZeroValue μh ξ ms qs (t * (deriv ξ (qs 0) - deriv ξ |u|)) m := by
  let v := t * (deriv ξ (qs 0) - deriv ξ |u|)
  let d := parisiRootDrivenRootVar ξ qs t |u|
  let e := parisiAuxRootVar ξ qs t
  let A := parisiRootSuffix ξ ms qs
  let B := coleHopf m v.toNNReal A
  have hB : Measurable B := (lipschitzWith_toNNReal_of_abs_sub_le
    (abs_coleHopf_sub_le_of_lipschitz m
      (parisiRootSuffix_spatial_regular_four ξ ms qs).1.continuous.measurable
      (by simpa only [one_mul] using abs_parisiRootSuffix_sub_le ξ ms qs :
        ∀ x y, |A y - A x| ≤ 1 * |y - x|) v.toNNReal)).continuous.measurable
  have hi := integrable_independentPairSiteRec_parisi_signed_root_zero hμ ξ ms qs hm hm0 hm1 v d e
  have hzero (h : ℝ) (z : ℝ × ℝ) := independentPairSiteRec_parisi_root_zero ξ ms qs hm hm0 hm1 v
    (signedRootEffectiveField h z)
  unfold parisiRootSignedCouplingValue
  change (∫ hz : ℝ × (ℝ × ℝ), independentPairSiteRec (parisiRootResponseMasses ms m)
    (parisiRootResponseVars ξ qs v) 0 (signedRootEffectiveField hz.1 hz.2)
    ∂μh.prod ((gaussianReal 0 d).prod (gaussianReal 0 e))) = _
  rw [integral_prod _ hi]
  have hpoint (h : ℝ) : (∫ z : ℝ × ℝ, independentPairSiteRec (parisiRootResponseMasses ms m)
      (parisiRootResponseVars ξ qs v) 0 (signedRootEffectiveField h z)
      ∂(gaussianReal 0 d).prod (gaussianReal 0 e)) =
      2 * ∫ z, B (h + z) ∂gaussianReal 0 (d + e) := by
    have hiB (l : Fin 2) := integrable_coleHopf_comp_shift
      ((measurable_pi_apply l).comp (measurable_signedRootEffectiveField.comp
        (measurable_const.prodMk measurable_id)))
      (integrable_signedRootEffectiveField_fixed h d e l)
      (parisiRootSuffix_spatial_regular_four ξ ms qs).1.continuous.measurable
      (abs_parisiRootSuffix_sub_le ξ ms qs) m v.toNNReal
    simp_rw [hzero h]
    simp only [Function.comp_apply, id_eq] at hiB
    change (∫ z : ℝ × ℝ, B (signedRootEffectiveField h z 0) + B (signedRootEffectiveField h z 1)
      ∂(gaussianReal 0 d).prod (gaussianReal 0 e)) = _
    rw [integral_add (hiB 0) (hiB 1), integral_signedRootEffectiveField_eq_marginal hB h d e 0,
      integral_signedRootEffectiveField_eq_marginal hB h d e 1]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  have hde := parisiRootDrivenRootVar_add_aux_eq hξ qs hq ht ⟨abs_nonneg _, hu⟩
  change d + e = (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal at hde
  rw [hde]
  have hzg : Integrable id (gaussianReal 0 (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal) :=
    IsGaussian.integrable_id
  have hH := (hμ.comp_fst (gaussianReal 0 (deriv ξ (qs 0) - deriv ξ 0 - v).toNNReal)).add
    (hzg.comp_snd μh)
  have hiB := integrable_coleHopf_comp_shift (measurable_fst.add measurable_snd) hH
    (parisiRootSuffix_spatial_regular_four ξ ms qs).1.continuous.measurable
    (abs_parisiRootSuffix_sub_le ξ ms qs) m v.toNNReal
  unfold parisiRootCouplingZeroValue
  congr 1
  exact (integral_prod _ hiB).symm

/-- Integrability at zero coupling extends to every coupling under
the uniform one-Lipschitz bound of the actual conditional recursion. -/
theorem integrable_independentPairSiteRec_parisi_signed_root {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1) (v : ℝ) (d e : ℝ≥0) (lam : ℝ) :
    Integrable (fun hz : ℝ × (ℝ × ℝ) => independentPairSiteRec (parisiRootResponseMasses ms m)
      (parisiRootResponseVars ξ qs v) lam (signedRootEffectiveField hz.1 hz.2))
      (μh.prod ((gaussianReal 0 d).prod (gaussianReal 0 e))) := by
  let ns := parisiRootResponseMasses ms m
  let vs := parisiRootResponseVars ξ qs v
  have hpos := parisiRootResponseMasses_pos ms hm hm0
  have hle := parisiRootResponseMasses_le_one ms hm hm1
  have hi0 := integrable_independentPairSiteRec_parisi_signed_root_zero hμ ξ ms qs hm hm0 hm1 v d e
  have hid : Integrable (fun hz : ℝ × (ℝ × ℝ) =>
      independentPairSiteRec ns vs lam (signedRootEffectiveField hz.1 hz.2) -
        independentPairSiteRec ns vs 0 (signedRootEffectiveField hz.1 hz.2))
      (μh.prod ((gaussianReal 0 d).prod (gaussianReal 0 e))) := by
    apply Integrable.of_bound
      (((measurable_independentPairSiteRec ns vs lam).comp measurable_signedRootEffectiveField).sub
        ((measurable_independentPairSiteRec ns vs 0).comp measurable_signedRootEffectiveField)).aestronglyMeasurable |lam|
    exact .of_forall fun hz => by
      change |independentPairSiteRec ns vs lam (signedRootEffectiveField hz.1 hz.2) -
        independentPairSiteRec ns vs 0 (signedRootEffectiveField hz.1 hz.2)| ≤ |lam|
      simpa only [sub_zero] using abs_independentPairSiteRec_sub_le ns vs hpos hle
        (signedRootEffectiveField hz.1 hz.2) lam 0
  exact (hid.add hi0).congr (.of_forall fun _ => sub_add_cancel _ _)

/-- The actual signed coupling Taylor bound has its concrete
averaged product-gradient slope and uniform coefficient one half. -/
theorem parisiRootSignedCouplingValue_le_taylor {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) {m : ℝ} (hm0 : 0 < m) (hmr : m ≤ mExt ms 1) (t u lam : ℝ) :
    parisiRootSignedCouplingValue μh ξ ms qs t u m lam ≤
      parisiRootSignedCouplingValue μh ξ ms qs t u m 0 +
        parisiRootSignedCouplingMassMoment μh ξ ms qs t u m * lam + lam ^ 2 / 2 := by
  let v := t * (deriv ξ (qs 0) - deriv ξ |u|)
  let d := parisiRootDrivenRootVar ξ qs t |u|
  let e := parisiAuxRootVar ξ qs t
  let ns := parisiRootResponseMasses ms m
  let vs := parisiRootResponseVars ξ qs v
  have hm1 : m ≤ 1 := hmr.trans (mExt_le_one (fun i => (hm.2.2 i).le) _)
  have hpos := parisiRootResponseMasses_pos ms hm hm0
  have hle := parisiRootResponseMasses_le_one ms hm hm1
  let D := fun hz : ℝ × (ℝ × ℝ) =>
    deriv (coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs)) (signedRootEffectiveField hz.1 hz.2 0) *
      deriv (coleHopf m v.toNNReal (parisiRootSuffix ξ ms qs)) (signedRootEffectiveField hz.1 hz.2 1)
  have hiD : Integrable D (μh.prod ((gaussianReal 0 d).prod (gaussianReal 0 e))) :=
    integrable_parisiRootSignedCouplingGradientProduct ξ ms qs t u m
  have hi0 := integrable_independentPairSiteRec_parisi_signed_root_zero hμ ξ ms qs hm hm0 hm1 v d e
  have hiLam := integrable_independentPairSiteRec_parisi_signed_root hμ ξ ms qs hm hm0 hm1 v d e lam
  have hpoint (hz : ℝ × (ℝ × ℝ)) : independentPairSiteRec ns vs lam (signedRootEffectiveField hz.1 hz.2) ≤
      independentPairSiteRec ns vs 0 (signedRootEffectiveField hz.1 hz.2) + D hz * lam + lam ^ 2 / 2 := by
    have hh := independentPairSiteRec_le_taylor ns vs (parisiRootResponseMasses_monotone ms hm hmr)
      hpos hle (signedRootEffectiveField hz.1 hz.2) lam
    rw [← independentPairSiteRec_zero ns vs hpos hle] at hh
    simpa only [ns, vs, D, parisiRootResponseMasses, parisiRootResponseVars,
      coleHopfIterate_succ, Fin.cons_zero, Fin.tail_cons, parisiRootSuffix] using hh
  have hb := integral_mono hiLam ((hi0.add (hiD.mul_const lam)).add (integrable_const (lam ^ 2 / 2))) hpoint
  have ha := integral_add (hi0.add (hiD.mul_const lam)) (integrable_const (lam ^ 2 / 2))
  have hs := integral_add hi0 (hiD.mul_const lam)
  simp only [Pi.add_apply] at hb ha hs
  rw [ha, hs, integral_mul_const, integral_const, probReal_univ, one_smul] at hb
  exact hb

/-- Choosing coupling minus the concrete response gap gives the
signed one-site quadratic gain at every positive inserted mass. -/
theorem parisiRootSignedCouplingValue_le_gain {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    (hq : ParisiQAdmissible qs) {t u m : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : |u| ≤ qs 0) (hm0 : 0 < m) (hmr : m ≤ mExt ms 1) :
    let β := parisiRootSignedCouplingMassMoment μh ξ ms qs t u m - u
    parisiRootSignedCouplingValue μh ξ ms qs t u m (-β) + β * u ≤
      2 * parisiRootCouplingZeroValue μh ξ ms qs (t * (deriv ξ (qs 0) - deriv ξ |u|)) m - β ^ 2 / 2 := by
  have hm1 : m ≤ 1 := hmr.trans (mExt_le_one (fun i => (hm.2.2 i).le) _)
  have hb := parisiRootSignedCouplingValue_le_taylor hμ ξ ms qs hm hm0 hmr t u
    (-(parisiRootSignedCouplingMassMoment μh ξ ms qs t u m - u))
  rw [parisiRootSignedCouplingValue_zero hμ hξ ms qs hm hq ht hu hm0 hm1] at hb
  dsimp only at ⊢
  nlinarith

end SpinGlass
