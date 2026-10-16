import SpinGlass.Parisi.Coupled.CoupledRootSignedGain

/-!
# The actual normalized signed one-site comparison

The raw four-column one-site recursion in the separate-factor coupled
bound is the concrete signed-root recursion. Its equality is proved for
every coupling before using its slope, mass limit or Taylor gain.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

noncomputable def parisiRootSignedRawCouplingValue (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t u m lam : ℝ) : ℝ :=
  let d := parisiRootDrivenRootVar ξ qs t |u|
  let e := parisiAuxRootVar ξ qs t
  let ds := parisiRootDrivenVars ξ qs t |u|
  let es := parisiRootAuxVars ξ qs t
  randomFieldPairSiteY₀ μh (parisiRootResponseMasses ms m) (d + e) (fun i => ds i + es i)
    lam (coupledDrivenVarianceFactor d e (couplingFactorSgn (-1) 1 0) +
      coupledAuxVarianceFactor d e (couplingFactorSgn 1 1 0))
    (fun i => coupledDrivenVarianceFactor (ds i) (es i) (couplingFactorSgn (-1) 1 (i.val + 1)) +
      coupledAuxVarianceFactor (ds i) (es i) (couplingFactorSgn 1 1 (i.val + 1)))

/-- The actual four-column recursion transports to the signed-root
two-field recursion for every coupling, under the preserved field law. -/
theorem parisiRootSignedRawCouplingValue_eq {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {t u m : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hm0 : 0 < m) (hm1 : m ≤ 1) (lam : ℝ) :
    parisiRootSignedRawCouplingValue μh ξ ms qs t u m lam =
      parisiRootSignedCouplingValue μh ξ ms qs t u m lam := by
  let v := t * (deriv ξ (qs 0) - deriv ξ |u|)
  let d := parisiRootDrivenRootVar ξ qs t |u|
  let e := parisiAuxRootVar ξ qs t
  let ds := parisiRootDrivenVars ξ qs t |u|
  let es := parisiRootAuxVars ξ qs t
  let ns := parisiRootResponseMasses ms m
  let vs := parisiRootResponseVars ξ qs v
  let L₀ := coupledDrivenVarianceFactor d e (couplingFactorSgn (-1) 1 0) +
    coupledAuxVarianceFactor d e (couplingFactorSgn 1 1 0)
  have hK (η : ℝ) (i : Fin (k + 2)) : couplingFactorSgn η 1 (i.val + 1) =
      fun l j => if l = j then 1 else 0 := by
    unfold couplingFactorSgn
    rw [ite_eq_right (by omega)]
  have hvars : (fun i => ds i + es i) = vs := parisiRootDrivenVars_add_aux_eq ξ qs ht |u|
  have hi := integrable_independentPairSiteRec_parisi_signed_root hμ ξ ms qs hm hm0 hm1 v d e lam
  unfold parisiRootSignedRawCouplingValue randomFieldPairSiteY₀ parisiRootSignedCouplingValue
  change (∫ h, pairSiteY₀ ns (d + e) (fun i => ds i + es i) lam (fun _ => h) L₀
    (fun i => coupledDrivenVarianceFactor (ds i) (es i) (couplingFactorSgn (-1) 1 (i.val + 1)) +
      coupledAuxVarianceFactor (ds i) (es i) (couplingFactorSgn 1 1 (i.val + 1))) ∂μh) =
      ∫ hz, independentPairSiteRec ns vs lam (signedRootEffectiveField hz.1 hz.2)
        ∂μh.prod ((gaussianReal 0 d).prod (gaussianReal 0 e))
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact .of_forall fun h => by
    simp_rw [hK]
    rw [pairSiteY₀_varianceShare_independent_eq, hvars]
    let F := fun x : Fin 2 → ℝ => independentPairSiteRec ns vs lam (fun l => h + x l)
    have hF : Measurable F := (measurable_independentPairSiteRec ns vs lam).comp
      (by fun_prop : Measurable fun x : Fin 2 → ℝ => fun l => h + x l)
    change (∫ z, F (signedRootVarianceShareMap d e z)
      ∂Measure.pi (fun _ : Fin 2 ⊕ Fin 2 => gaussianReal 0 (d + e))) = _
    rw [integral_signedRootVarianceShare_eq_prod hF d e]
    apply integral_congr_ae
    exact .of_forall fun z => by
      have hfield : (fun l : Fin 2 => h + (![z.1 + z.2, -z.1 + z.2] l)) =
          signedRootEffectiveField h z := by
        funext l
        fin_cases l <;> simp [signedRootEffectiveField, sub_eq_add_neg, add_assoc]
      exact congrArg (independentPairSiteRec ns vs lam) hfield

/-- The normalized signed one-site value has the actual concrete
product-gradient slope at zero coupling. -/
theorem hasDerivAt_parisiRootSignedRawCouplingValue_zero {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμ : Integrable id μh) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms)
    {t u m : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hm0 : 0 < m) (hm1 : m ≤ 1) :
    HasDerivAt (parisiRootSignedRawCouplingValue μh ξ ms qs t u m)
      (parisiRootSignedCouplingMassMoment μh ξ ms qs t u m) 0 := by
  have he : parisiRootSignedRawCouplingValue μh ξ ms qs t u m =
      parisiRootSignedCouplingValue μh ξ ms qs t u m := funext fun lam =>
    parisiRootSignedRawCouplingValue_eq hμ ξ ms qs hm ht hm0 hm1 lam
  rw [he]
  exact hasDerivAt_parisiRootSignedCouplingValue_zero hμ ξ ms qs hm hm0 hm1 t u

end SpinGlass
