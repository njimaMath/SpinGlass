import SpinGlass.Parisi.Coupled.CoupledRootSignedGain
import SpinGlass.Parisi.Coupled.CoupledPairGaussianSite

/-!
# Continuity of the signed root comparison value

The two signed root expectations are genuine mass-zero Gaussian
operators. The inserted positive mass remains in the independent
suffix. The paired variance modulus therefore applies at arbitrary
coupling, including zero driven or auxiliary root variance.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

/-- The actual independent positive cascade is its concrete paired
list, at arbitrary effective fields and coupling. -/
theorem independentPairSiteRec_eq_pairColeHopfIterate {n : ℕ}
    (ns : Fin n → ℝ) (vs : Fin n → ℝ≥0) (hpos : ∀ i, 0 < ns i)
    (lam : ℝ) (x : Fin 2 → ℝ) :
    independentPairSiteRec ns vs lam x =
      pairColeHopfIterate (List.ofFn (fun i => ⟨ns i, vs i, .independent⟩))
        (pairSiteY lam) (x 0) (x 1) := by
  have he : independentPairSiteF lam x = fun zs : Fin n → Fin 2 → ℝ =>
      pairSiteY lam (x 0 + ∑ i, (pairGaussianShift .independent (zs i)).1)
        (x 1 + ∑ i, (pairGaussianShift .independent (zs i)).2) := by
    funext zs
    simp only [independentPairSiteF, pairSiteF, pairSiteMark_independent,
      pairGaussianShift]
  unfold independentPairSiteRec
  rw [he]
  exact parisiRec_pairGaussian_comp_add_sum
    (fun i => ⟨ns i, vs i, .independent⟩) hpos (pairUnitLipschitz_pairSiteY lam) _ _

noncomputable def parisiRootSignedPairLevels (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t s m : ℝ) : List PairColeHopfLevel :=
  ⟨0, parisiRootDrivenRootVar ξ qs t |s|, .antisymmetric⟩ ::
    ⟨0, parisiAuxRootVar ξ qs t, .common⟩ ::
      List.ofFn (fun i => ⟨parisiRootResponseMasses ms m i,
        parisiRootResponseVars ξ qs (t * (deriv ξ (qs 0) - deriv ξ |s|)) i,
          .independent⟩)

/-- The concrete signed product root law equals the two mass-zero
paired root expectations followed by its actual positive cascade. -/
theorem parisiRootSignedCouplingValue_eq_pairLevels
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1)
    (t s lam : ℝ) :
    parisiRootSignedCouplingValue μh ξ ms qs t s m lam =
      randomFieldPairColeHopfTerminalValue μh
        (parisiRootSignedPairLevels ξ ms qs t s m) (pairSiteY lam) := by
  let v := t * (deriv ξ (qs 0) - deriv ξ |s|)
  let d := parisiRootDrivenRootVar ξ qs t |s|
  let e := parisiAuxRootVar ξ qs t
  have hi := integrable_independentPairSiteRec_parisi_signed_root hμ ξ ms qs hm
    hm0 hm1 v d e lam
  unfold parisiRootSignedCouplingValue randomFieldPairColeHopfTerminalValue
  rw [integral_prod _ hi]
  apply integral_congr_ae (.of_forall fun h => ?_)
  have hD : Integrable id (Measure.dirac h) := by apply integrable_dirac; finiteness
  have hih := (integrable_independentPairSiteRec_parisi_signed_root hD ξ ms qs hm
    hm0 hm1 v d e lam).prod_right_ae
  have hprod : Integrable (fun z : ℝ × ℝ =>
      independentPairSiteRec (parisiRootResponseMasses ms m)
        (parisiRootResponseVars ξ qs v) lam (signedRootEffectiveField h z))
      ((gaussianReal 0 d).prod (gaussianReal 0 e)) := by
    simpa only [ae_dirac_eq, Filter.eventually_pure] using hih
  rw [integral_prod _ hprod]
  simp only [parisiRootSignedPairLevels, pairColeHopfIterate, pairColeHopfOperator,
    correlatedPairColeHopf, coleHopf_zero, zero_add, one_mul, neg_one_mul]
  apply integral_congr_ae (.of_forall fun z => ?_)
  apply integral_congr_ae (.of_forall fun w => ?_)
  rw [independentPairSiteRec_eq_pairColeHopfIterate _ _
    (parisiRootResponseMasses_pos ms hm hm0)]
  simp only [signedRootEffectiveField, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_eq_add_neg]
  rfl

/-- Every fixed signed overlap gives a continuous actual one-site
value as time varies, under only a finite first field moment. -/
theorem continuous_parisiRootSignedCouplingValue_time
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    (ξ : ℝ → ℝ) {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) {m : ℝ} (hm0 : 0 < m) (hm1 : m ≤ 1)
    (s lam : ℝ) :
    Continuous (fun t => parisiRootSignedCouplingValue μh ξ ms qs t s m lam) := by
  let l : List (Fin (k + 4)) := List.ofFn id
  let mass : Fin (k + 4) → ℝ := Fin.cons 0 (Fin.cons 0 (parisiRootResponseMasses ms m))
  let kind : Fin (k + 4) → PairColeHopfKind :=
    Fin.cons .antisymmetric (Fin.cons .common (fun _ => .independent))
  let variance (t : ℝ) : Fin (k + 4) → ℝ≥0 :=
    Fin.cons (parisiRootDrivenRootVar ξ qs t |s|) (Fin.cons (parisiAuxRootVar ξ qs t)
      (parisiRootResponseVars ξ qs (t * (deriv ξ (qs 0) - deriv ξ |s|))))
  have hvar (i : Fin (k + 4)) : Continuous (fun t => variance t i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [variance, Fin.cons_zero, parisiRootDrivenRootVar]
      exact continuous_real_toNNReal.mul_const _
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [variance, Fin.cons_succ, Fin.cons_zero, parisiAuxRootVar]
        exact (continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).mul_const _
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp only [variance, Fin.cons_succ, parisiRootResponseVars, Fin.cons_zero]
          exact continuous_real_toNNReal.comp (continuous_id.mul_const _)
        · simpa only [variance, Fin.cons_succ, parisiRootResponseVars] using
            (continuous_const : Continuous (fun _ : ℝ => parisiLevelVars ξ qs j))
  have hc := continuous_randomFieldPairColeHopfTerminalValue_of_continuous_variance hμ
    l mass kind variance hvar (pairUnitLipschitz_pairSiteY lam)
  have he (t : ℝ) : l.map (fun i => ⟨mass i, variance t i, kind i⟩) =
      parisiRootSignedPairLevels ξ ms qs t s m := by
    dsimp only [l]
    rw [List.map_ofFn, List.ofFn_succ]
    change _ :: List.ofFn _ = _ :: _
    congr 1
    rw [List.ofFn_succ]
    rfl
  simp_rw [he] at hc
  exact hc.congr (fun t =>
    (parisiRootSignedCouplingValue_eq_pairLevels hμ ξ ms qs hm hm0 hm1 t s lam).symm)

end SpinGlass
