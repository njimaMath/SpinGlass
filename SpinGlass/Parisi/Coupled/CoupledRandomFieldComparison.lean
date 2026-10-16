import SpinGlass.Parisi.Coupled.CoupledFieldPressure

/-!
# Finite-volume coupled comparisons under the i.i.d. field law

The actual constrained pressure is averaged over independent site fields,
with the same realized field in both replicas. Its integrability follows
from the coordinate field bound, and the one-site term is averaged by the
product-coordinate law. Only a finite first field moment is used here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The actual constrained split pressure with i.i.d. quenched fields,
independent of the disorder and root Gaussian marks. -/
noncomputable def randomFieldParisiSplitPressure {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (μh : Measure ℝ) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (es : Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0) : ℝ :=
  ∫ hVec, parisiSplitPressure ξ ms qs p t u G₀ es (sharedReplicaSiteField hVec)
    ∂externalFieldVecLaw N μh

/-- Integrability of an arbitrary one-site observable gives that of
its empirical site average under the independent product-coordinate law. -/
theorem integrable_externalFieldVec_siteAverage {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {F : ℝ → ℝ} (hF : Integrable F μh) (N : ℕ) :
    Integrable (fun hVec : Fin N → ℝ => (1 / (N : ℝ)) * ∑ i, F (hVec i))
      (externalFieldVecLaw N μh) := by
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i _
  exact ((measurePreserving_externalFieldVec_apply N μh i).integrable_comp
    hF.aestronglyMeasurable).2 hF

/-- The empirical site average has the original one-site law mean.
The normalization is valid for every positive volume. -/
theorem integral_externalFieldVec_siteAverage {μh : Measure ℝ} [IsProbabilityMeasure μh]
    {F : ℝ → ℝ} (hF : Integrable F μh) {N : ℕ} (hN : 0 < N) :
    (∫ hVec : Fin N → ℝ, (1 / (N : ℝ)) * ∑ i, F (hVec i) ∂externalFieldVecLaw N μh) =
      ∫ h, F h ∂μh := by
  have hi : ∀ i : Fin N, Integrable (fun hVec : Fin N → ℝ => F (hVec i))
      (externalFieldVecLaw N μh) := fun i =>
    ((measurePreserving_externalFieldVec_apply N μh i).integrable_comp
      hF.aestronglyMeasurable).2 hF
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hi i]
  simp_rw [integral_externalFieldVec_apply N μh _ _ hF.aestronglyMeasurable]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, one_div, inv_mul_cancel₀ (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0), one_mul]

/-- Every coupled one-site value for the actual positive split masses
is integrable under a probability field law of finite first moment. -/
theorem integrable_pairSiteY₀_parisiSplit_externalField {μh : Measure ℝ}
    [IsProbabilityMeasure μh] (hμ : Integrable id μh) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (ξ : ℝ → ℝ)
    (vs : Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0) (lam : ℝ) :
    Integrable (fun h : ℝ => pairSiteY₀
      (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)) (parisiVar ξ qs 0) vs lam (fun _ => h)
      (couplingFactorSgn 1 (p.val + 2) 0)
      (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))) μh := by
  have hpos := parisiResponseSplitMasses_pos ms p hm
  have hle := parisiResponseSplitMasses_le_one ms p hm
  have hY : Integrable (fun h : ℝ => pairSiteY₀
      (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)) (parisiVar ξ qs 0) vs 0 (fun _ => h)
      (couplingFactorSgn 1 (p.val + 2) 0)
      (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))) μh := by
    have hi := (integrable_integral_logCoshRec_externalField hμ
      (parisiResponseSplitMasses ms p) vs hpos hle (parisiVar ξ qs 0)).const_mul 2
    apply hi.congr (.of_forall fun h => ?_)
    have hh := pairSiteY₀_coupling_zero (parisiResponseSplitMasses ms p) hpos
      (parisiVar ξ qs 0) vs h (τ := p.val + 2) (by omega)
    simpa only [show p.val + 2 - 1 = p.val + 1 by omega] using hh.symm
  exact integrable_pairSiteY₀_commonField_of_integrable_at_zero
    (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)) (halveBelow_pos hpos _)
    (halveBelow_le_one hle _) (parisiVar ξ qs 0) vs
    (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) hY lam

/-- The concrete finite-volume comparison after averaging the i.i.d.
quenched site fields. The field fluctuation is not replaced by a deterministic
field, and no exponential-field integrability is assumed. -/
theorem randomFieldParisiSplitPressure_le_siteValue {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (es : Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiSplitPressure μh ξ ms qs p t u G₀ es ≤
      2 * Real.log 2 + randomFieldPairSiteY₀ μh
        (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)) (parisiVar ξ qs 0)
        (fun i => parisiDrivenSplitVars ξ qs p t u i + es i) lam
        (couplingFactorSgn 1 (p.val + 2) 0)
        (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) - lam * u -
          t * parisiCorrection ξ ms qs := by
  let F := fun h : ℝ => pairSiteY₀
    (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)) (parisiVar ξ qs 0)
    (fun i => parisiDrivenSplitVars ξ qs p t u i + es i) lam (fun _ => h)
    (couplingFactorSgn 1 (p.val + 2) 0)
    (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1))
  have hF : Integrable F μh := integrable_pairSiteY₀_parisiSplit_externalField hμ ms qs p hm ξ _ lam
  have hAvg := integrable_externalFieldVec_siteAverage hF N
  have hLeft := integrable_parisiSplitPressure_externalField hμ ξ ms qs p t u hm G₀ es hreach
  have hRhs : Integrable (fun hVec : Fin N → ℝ =>
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) - lam * u - t * parisiCorrection ξ ms qs)
      (externalFieldVecLaw N μh) :=
    (((integrable_const (2 * Real.log 2)).add hAvg).sub (integrable_const (lam * u))).sub
      (integrable_const (t * parisiCorrection ξ ms qs))
  have hb := integral_mono hLeft hRhs fun hVec =>
    parisiSplitPressure_le_siteValue hN hξ ms qs p hm hq ht hu G₀ es
      (sharedReplicaSiteField hVec) lam hreach
  have hmean : (∫ hVec : Fin N → ℝ,
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ i, F (hVec i) - lam * u - t * parisiCorrection ξ ms qs
      ∂externalFieldVecLaw N μh) =
      2 * Real.log 2 + (∫ h, F h ∂μh) - lam * u - t * parisiCorrection ξ ms qs := by
    have ha := integral_add (integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)) hAvg
    have hs := integral_sub ((integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)).add hAvg)
      (integrable_const (lam * u))
    have ht' := integral_sub
      (((integrable_const (μ := externalFieldVecLaw N μh) (2 * Real.log 2)).add hAvg).sub
        (integrable_const (lam * u))) (integrable_const (t * parisiCorrection ξ ms qs))
    simp only [Pi.add_apply, Pi.sub_apply] at ha hs ht'
    rw [ht', hs, ha, integral_externalFieldVec_siteAverage hF hN]
    simp only [integral_const, probReal_univ, one_smul]
  rw [hmean] at hb
  exact hb

/-- The law-level comparison with the actual inner auxiliary insertion. -/
theorem randomFieldParisiSplitPressure_inner_le_siteValue {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ)) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiSplitPressure μh ξ ms qs p t u G₀ (parisiInnerAuxSplitVars ξ qs p t) ≤
      2 * Real.log 2 + randomFieldPairSiteY₀ μh
        (halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)) (parisiVar ξ qs 0)
        (parisiResponseSplitVars ξ qs p (t * (deriv ξ (qExt qs (p.val + 2)) - deriv ξ u))) lam
        (couplingFactorSgn 1 (p.val + 2) 0)
        (fun i => couplingFactorSgn 1 (p.val + 2) (i.val + 1)) - lam * u -
          t * parisiCorrection ξ ms qs := by
  have hb := randomFieldParisiSplitPressure_le_siteValue hμ hN hξ ms qs p hm hq ht hu G₀
    (parisiInnerAuxSplitVars ξ qs p t) lam hreach
  simpa only [parisiDrivenSplitVars_add_innerAux_eq hξ qs p hq ht hu] using hb

/-- The law-level comparison with the actual mirror auxiliary insertion,
including the terminal old interval. -/
theorem randomFieldParisiSplitPressure_outer_le_siteValue {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ)) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiSplitPressure μh ξ ms qs p t u G₀ (parisiOuterAuxSplitVars ξ qs p t) ≤
      2 * Real.log 2 + parisiOuterCouplingValue μh ξ ms qs p t u lam - lam * u -
        t * parisiCorrection ξ ms qs := by
  have hb := randomFieldParisiSplitPressure_le_siteValue hμ hN hξ ms qs p hm hq ht hu G₀
    (parisiOuterAuxSplitVars ξ qs p t) lam hreach
  simpa only [parisiDrivenSplitVars_add_outerAux_eq hξ qs p hq ht hu,
    parisiOuterCouplingValue] using hb

/-- The matching split bracket before removal of the terminal
mass-one auxiliary Gaussian mark. Its normalization is explicit. -/
noncomputable def parisiSplitBracket (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ) : ℝ :=
  Real.log 2 + (∫ h, closedParisiX₀ ξ ms qs h ∂μh) - t * parisiCorrection ξ ms qs / 2

/-- The unnormalized split bracket is the original random-field
Parisi value plus its explicit time correction. -/
theorem parisiSplitBracket_eq_functional_add_correction (μh : Measure ℝ) (ξ : ℝ → ℝ)
    {k : ℕ} (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) (t : ℝ) :
    parisiSplitBracket μh ξ ms qs t = randomFieldParisiFunctional μh ξ ms qs +
      (1 - t) * parisiCorrection ξ ms qs / 2 := by
  have hh := closedRandomFieldParisiFunctional_eq μh ξ ms qs hm
  unfold closedRandomFieldParisiFunctional at hh
  rw [← Fin.sum_univ_eq_sum_range] at hh
  change Real.log 2 + (∫ h, closedParisiX₀ ξ ms qs h ∂μh) -
    (1 / 2) * parisiCorrection ξ ms qs = _ at hh
  dsimp only [parisiSplitBracket]
  nlinarith

/-- The concrete mirror finite-volume pressure gains the square of its
actual response gap after averaging the i.i.d. quenched fields. -/
theorem randomFieldParisiSplitPressure_outer_le_gain {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1))
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p) (qExt qs (p.val + 2)))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiSplitPressure μh ξ ms qs p t u G₀ (parisiOuterAuxSplitVars ξ qs p t) ≤
      2 * parisiSplitBracket μh ξ ms qs t - (parisiLeftResponseGap μh ξ ms qs p t u) ^ 2 / 2 := by
  have hb := randomFieldParisiSplitPressure_outer_le_siteValue hμ hN hξ ms qs p hm hq ht hu G₀
    (-parisiLeftResponseGap μh ξ ms qs p t u) hreach
  have hg := parisiOuterCouplingValue_le_gain hμ hξ ms qs p hm hq ht hu
  dsimp only at hg
  dsimp only [parisiSplitBracket]
  nlinarith

/-- The corresponding concrete finite-volume inner pressure gain for
each nonroot original interval. -/
theorem randomFieldParisiSplitPressure_inner_le_gain {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs) {t u : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (qs p.castSucc) (qs p.succ))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiSplitPressure μh ξ ms qs p.castSucc t u G₀
        (parisiInnerAuxSplitVars ξ qs p.castSucc t) ≤
      2 * parisiSplitBracket μh ξ ms qs t - (parisiRightResponseGap μh ξ ms qs p t u) ^ 2 / 2 := by
  have hR : qExt qs (p.castSucc.val + 2) = qs p.succ := qExt_succ_of_lt qs p.succ.isLt
  have hu' : u ∈ Icc (qs p.castSucc) (qExt qs (p.castSucc.val + 2)) := by rw [hR]; exact hu
  have hb := randomFieldParisiSplitPressure_inner_le_siteValue hμ hN hξ ms qs p.castSucc hm hq ht hu'
    G₀ (-parisiRightResponseGap μh ξ ms qs p t u) hreach
  rw [hR] at hb
  change randomFieldParisiSplitPressure μh ξ ms qs p.castSucc t u G₀
      (parisiInnerAuxSplitVars ξ qs p.castSucc t) ≤
    2 * Real.log 2 + parisiInnerCouplingValue μh ξ ms qs p t u
      (-parisiRightResponseGap μh ξ ms qs p t u) -
      (-parisiRightResponseGap μh ξ ms qs p t u) * u - t * parisiCorrection ξ ms qs at hb
  have hg := parisiInnerCouplingValue_le_gain hμ hξ ms qs p hm hq ht hu
  dsimp only at hg
  dsimp only [parisiSplitBracket]
  nlinarith

/-- The nearby nonroot main-estimate penalty for the explicit matching
split pressures. MIN tolerance and radius precede all volumes, probability
spaces, Gaussian realizations and times. Identification with the original
canonical auxiliary cascade and its terminal normalization remains separate. -/
theorem exists_uniform_randomFieldParisiSplitPressure_near_gap {μh : Measure ℝ}
    [IsProbabilityMeasure μh] {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (hμ : NondegenerateExternalFieldLaw μh) {t₀ : ℝ} (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ (k : ℕ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ),
        ParisiMAdmissible ms → IsRandomFieldParisiQMinimizer μh ξ ms qs →
        IsMinOn (fun x => closedRandomFieldParisiFunctional μh ξ x.1 x.2)
          (parisiParameterDomain k) (ms, qs) →
        randomFieldParisiFunctional μh ξ ms qs < randomFieldParisiInf μh ξ + ε →
        ∀ N : ℕ, 0 < N → ∀ (Ω : Type) [MeasurableSpace Ω]
          (Pm : Measure Ω) [IsProbabilityMeasure Pm], ∀ t ∈ Icc (0 : ℝ) t₀,
          ∀ G₀ : GaussianField (α := Config N) Pm
            (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ),
          (∀ p : Fin k, ∀ u ∈ Icc (qs p.castSucc) (qs p.succ), qs p.succ - u ≤ ρ →
            (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
            randomFieldParisiSplitPressure μh ξ ms qs p.castSucc t u G₀
                (parisiInnerAuxSplitVars ξ qs p.castSucc t) ≤
              2 * parisiSplitBracket μh ξ ms qs t - (1 - t₀) ^ 2 * (u - qs p.succ) ^ 2 / 32) ∧
          (∀ p : Fin (k + 1), ∀ u ∈ Icc (qs p) (qExt qs (p.val + 2)), u - qs p ≤ ρ →
            (∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) →
            randomFieldParisiSplitPressure μh ξ ms qs p t u G₀
                (parisiOuterAuxSplitVars ξ qs p t) ≤
              2 * parisiSplitBracket μh ξ ms qs t - (1 - t₀) ^ 2 * (u - qs p) ^ 2 / 32) := by
  obtain ⟨ε, hε, ρ, hρ, hgap⟩ := exists_uniform_parisi_critical_response_gap hξ hμ ht₀
  refine ⟨ε, hε, ρ, hρ, ?_⟩
  intro k ms qs hm hmin hfull hnear N hN Ω _ Pm _ t ht G₀
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2.le⟩
  have hresp := hgap k ms qs hm hmin hfull hnear t ht
  constructor
  · intro p u hu hdist hreach
    have hb := randomFieldParisiSplitPressure_inner_le_gain hμ.integrable_id hN hξ ms qs p hm hmin.1
      ht01 hu G₀ hreach
    have hg := hresp.2.1 p u hu hdist
    have hnonneg : 0 ≤ (1 - t₀) / 4 * (qs p.succ - u) :=
      mul_nonneg (by linarith [ht₀.2]) (sub_nonneg.2 hu.2)
    have hsquare := mul_self_le_mul_self hnonneg hg
    nlinarith
  · intro p u hu hdist hreach
    have hb := randomFieldParisiSplitPressure_outer_le_gain hμ.integrable_id hN hξ ms qs p hm hmin.1
      ht01 hu G₀ hreach
    have hg := hresp.2.2 p u hu hdist
    have hnonneg : 0 ≤ (1 - t₀) / 4 * (u - qs p) :=
      mul_nonneg (by linarith [ht₀.2]) (sub_nonneg.2 hu.1)
    have hsquare := mul_self_le_mul_self hnonneg (show
        (1 - t₀) / 4 * (u - qs p) ≤ -parisiLeftResponseGap μh ξ ms qs p t u by linarith)
    nlinarith

end SpinGlass
