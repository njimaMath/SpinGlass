import SpinGlass.Parisi.Coupled.CoupledCanonicalAuxiliary

/-!
# The original physical constrained pressure and its normalization

The split comparison pressure is identified with the original k-level
auxiliary cascade. Its additional mass-one field contributes precisely
the terminal variance to the pressure per site, as in (14.312).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- Auxiliary variances on the original positive masses, without the
extra terminal mass-one mark. -/
noncomputable def parisiAuxLevelVars (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (t : ℝ) : Fin k → ℝ≥0 :=
  fun i => (1 - t).toNNReal * parisiVar ξ qs (i.val + 1)

/-- The variance of the removable terminal auxiliary mark. -/
noncomputable def parisiAuxTerminalVar (ξ : ℝ → ℝ) {k : ℕ}
    (qs : Fin (k + 1) → ℝ) (t : ℝ) : ℝ≥0 :=
  (1 - t).toNNReal * parisiVar ξ qs (k + 1)

theorem halveBelow_parisiLevelMasses_eq_snoc {k r : ℕ} (ms : Fin k → ℝ) (hr : r ≤ k) :
    halveBelow r (parisiLevelMasses ms) = Fin.snoc (halveBelow r ms) 1 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [halveBelow, parisiLevelMasses, Fin.snoc_last, Fin.val_last]
    rw [ite_eq_right (by omega)]
  · simp only [halveBelow, parisiLevelMasses, Fin.snoc_castSucc, Fin.val_castSucc]

theorem parisiAuxFullVars_eq_snoc (ξ : ℝ → ℝ) {k : ℕ} (qs : Fin (k + 1) → ℝ) (t : ℝ) :
    (fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i) =
      Fin.snoc (parisiAuxLevelVars ξ qs t) (parisiAuxTerminalVar ξ qs t) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, parisiLevelVars, Fin.val_last, parisiAuxTerminalVar]
  · simp only [Fin.snoc_castSucc, parisiLevelVars, Fin.val_castSucc, parisiAuxLevelVars]

theorem parisiAuxFullFactors_eq_snoc (k τ : ℕ) :
    (fun i : Fin (k + 1) => couplingFactorSgn 1 τ (i.val + 1)) =
      Fin.snoc (fun i : Fin k => couplingFactorSgn 1 τ (i.val + 1))
        (couplingFactorSgn 1 τ (k + 1)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, Fin.val_last]
  · simp only [Fin.snoc_castSucc, Fin.val_castSucc]

/-- Terminal normalization for the original auxiliary cascade, with
the constrained partition sum and all earlier levels retained. -/
theorem log_cascadeRec_parisi_aux_eq {N k τ : ℕ} (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ)
    (hm : ParisiMAdmissible ms) (hτ : 1 ≤ τ) (hτk : τ ≤ k + 1)
    {c : (Fin 2 → Config N) → ℝ} (hc : ∀ σ, 0 ≤ c σ) (hcpos : ∃ σ, 0 < c σ)
    (H : EnergySpace N) (lam : ℝ) (a : Fin N × Fin 2 → ℝ) (z₀ : Fin N × Fin 2 → ℝ) :
    Real.log (cascadeRec (k + 1) (halveBelow (τ - 1) (parisiLevelMasses ms))
        (siteGaussianMarks (Fin N × Fin 2) _ (fun i => (1 - t).toNNReal * parisiLevelVars ξ qs i))
        (pairHamG N _ c H lam a (couplingFactorSgn 1 τ 0)
          (fun i => couplingFactorSgn 1 τ (i.val + 1)) z₀)).toReal =
      (N : ℝ) * parisiAuxTerminalVar ξ qs t +
        Real.log (cascadeRec k (halveBelow (τ - 1) ms)
          (siteGaussianMarks (Fin N × Fin 2) _ (parisiAuxLevelVars ξ qs t))
          (pairHamG N _ c H lam a (couplingFactorSgn 1 τ 0)
            (fun i => couplingFactorSgn 1 τ (i.val + 1)) z₀)).toReal := by
  rw [halveBelow_parisiLevelMasses_eq_snoc ms (by omega : τ - 1 ≤ k),
    parisiAuxFullVars_eq_snoc, parisiAuxFullFactors_eq_snoc]
  exact log_cascadeRec_pairHamG_snoc_terminal_eq (halveBelow (τ - 1) ms)
    (parisiAuxLevelVars ξ qs t) (halveBelow_pos hm.2.1 _)
    (halveBelow_le_one (fun i => (hm.2.2 i).le) _) hc hcpos H lam a
    (couplingFactorSgn 1 τ 0) (fun i => couplingFactorSgn 1 τ (i.val + 1))
    (couplingFactorSgn 1 τ (k + 1)) (gram_couplingFactorSgn_of_le hτk)
    z₀ (parisiAuxTerminalVar ξ qs t)

/-- The original physical two-replica pressure, with its k positive
mass levels and no terminal auxiliary mark. -/
noncomputable def parisiAuxPairPressure {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (τ : ℕ) (t u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ θ, Real.log (cascadeRec k (halveBelow (τ - 1) ms)
    (siteGaussianMarks (Fin N × Fin 2) _ (parisiAuxLevelVars ξ qs t))
    (pairHamG N _ (constraintR N u) (G₀.U θ.1) 0 a (couplingFactorSgn 1 τ 0)
      (fun i => couplingFactorSgn 1 τ (i.val + 1)) θ.2)).toReal
    ∂Pm.prod (rootMarksLaw N (J := Fin 2) (parisiAuxRootVar ξ qs t))

theorem integrable_log_cascadeRec_parisi_aux {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (τ : ℕ) (t u : ℝ)
    (hm : ParisiMAdmissible ms)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    Integrable (fun θ => Real.log (cascadeRec k (halveBelow (τ - 1) ms)
      (siteGaussianMarks (Fin N × Fin 2) _ (parisiAuxLevelVars ξ qs t))
      (pairHamG N _ (constraintR N u) (G₀.U θ.1) 0 a (couplingFactorSgn 1 τ 0)
        (fun i => couplingFactorSgn 1 τ (i.val + 1)) θ.2)).toReal)
      (Pm.prod (rootMarksLaw N (J := Fin 2) (parisiAuxRootVar ξ qs t))) := by
  have hi := integrable_log_cascadeRec_coupledG (parisiTimeProfile ξ t) u hreach G₀
    (halveBelow (τ - 1) ms) (halveBelow_pos hm.2.1 _)
    (halveBelow_le_one (fun i => (hm.2.2 i).le) _) (parisiAuxRootVar ξ qs t)
    (parisiAuxLevelVars ξ qs t) 0 (couplingFactorSgn 1 τ 0) 0
    (fun i => couplingFactorSgn 1 τ (i.val + 1)) a
  unfold coupledG at hi
  simpa only [sub_self, Real.sqrt_zero, Real.sqrt_one, zero_smul, one_smul,
    zero_add] using hi

/-- The mirror split pressure is the original physical pressure plus
the removable terminal variance, also for the terminal outer interval. -/
theorem parisiSplitPressure_outer_eq_original {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) {t : ℝ} (u : ℝ)
    (hm : ParisiMAdmissible ms) (ht : t ∈ Icc (0 : ℝ) 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiSplitPressure ξ ms qs p t u G₀ (parisiOuterAuxSplitVars ξ qs p t) a =
      parisiAuxPairPressure ξ ms qs (p.val + 1) t u G₀ a + parisiAuxTerminalVar ξ qs t := by
  rw [parisiSplitPressure_eq_auxiliary ξ ms qs p ht]
  unfold parisiAuxSplitPressure parisiAuxPairPressure
  have hrec (θ : Ω × (Fin N × Fin 2 → ℝ)) :=
    cascadeRec_parisi_outer_aux_eq ξ ms qs p t hm (constraintR N u) (G₀.U θ.1) 0 a θ.2
  simp_rw [hrec]
  have hcpos : ∃ σ, 0 < constraintR N u σ :=
    hreach.elim fun σ hσ => ⟨σ, constraintR_pos_of_overlap_eq N hσ⟩
  have hlog (θ : Ω × (Fin N × Fin 2 → ℝ)) :=
    log_cascadeRec_parisi_aux_eq (τ := p.val + 1) ξ ms qs t hm (by omega) (by omega)
      (constraintR_nonneg N u) hcpos (G₀.U θ.1) 0 a θ.2
  simp only [Nat.add_sub_cancel] at hlog
  simp_rw [hlog]
  have hi := integrable_log_cascadeRec_parisi_aux ξ ms qs (p.val + 1) t u hm G₀ a hreach
  simp only [Nat.add_sub_cancel] at hi ⊢
  rw [integral_add (integrable_const _) hi,
    integral_const, probReal_univ, one_smul]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- The nonroot inner split has the same terminal normalization at
the original right-endpoint replica prefix. -/
theorem parisiSplitPressure_inner_eq_original {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) {t : ℝ} (u : ℝ)
    (hm : ParisiMAdmissible ms) (ht : t ∈ Icc (0 : ℝ) 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiSplitPressure ξ ms qs p.castSucc t u G₀ (parisiInnerAuxSplitVars ξ qs p.castSucc t) a =
      parisiAuxPairPressure ξ ms qs (p.val + 2) t u G₀ a + parisiAuxTerminalVar ξ qs t := by
  rw [parisiSplitPressure_eq_auxiliary ξ ms qs p.castSucc ht]
  unfold parisiAuxSplitPressure parisiAuxPairPressure
  have hrec (θ : Ω × (Fin N × Fin 2 → ℝ)) :=
    cascadeRec_parisi_inner_aux_eq ξ ms qs p.castSucc t hm (constraintR N u) (G₀.U θ.1) 0 a θ.2
  simp_rw [hrec]
  have hcpos : ∃ σ, 0 < constraintR N u σ :=
    hreach.elim fun σ hσ => ⟨σ, constraintR_pos_of_overlap_eq N hσ⟩
  have hlog (θ : Ω × (Fin N × Fin 2 → ℝ)) :=
    log_cascadeRec_parisi_aux_eq (τ := p.val + 2) ξ ms qs t hm (by omega) (by omega)
      (constraintR_nonneg N u) hcpos (G₀.U θ.1) 0 a θ.2
  have hi := integrable_log_cascadeRec_parisi_aux ξ ms qs (p.val + 2) t u hm G₀ a hreach
  simp only [Fin.val_castSucc, show p.val + 2 - 1 = p.val + 1 by omega] at hlog hi ⊢
  simp_rw [hlog]
  rw [integral_add (integrable_const _) hi, integral_const, probReal_univ, one_smul]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- Averaging the original auxiliary pressure over i.i.d. site
fields, with the same site realization in both replicas. -/
noncomputable def randomFieldParisiAuxPairPressure {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (μh : Measure ℝ) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (τ : ℕ) (t u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ)) : ℝ :=
  ∫ hVec, parisiAuxPairPressure ξ ms qs τ t u G₀ (sharedReplicaSiteField hVec)
    ∂externalFieldVecLaw N μh

theorem randomFieldParisiAuxPairPressure_outer_eq {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (hN : 0 < N) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) {t : ℝ} (u : ℝ)
    (hm : ParisiMAdmissible ms) (ht : t ∈ Icc (0 : ℝ) 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 1) t u G₀ =
      randomFieldParisiSplitPressure μh ξ ms qs p t u G₀ (parisiOuterAuxSplitVars ξ qs p t) -
        parisiAuxTerminalVar ξ qs t := by
  have hp (hVec : Fin N → ℝ) :
      parisiAuxPairPressure ξ ms qs (p.val + 1) t u G₀ (sharedReplicaSiteField hVec) =
        parisiSplitPressure ξ ms qs p t u G₀ (parisiOuterAuxSplitVars ξ qs p t)
          (sharedReplicaSiteField hVec) - parisiAuxTerminalVar ξ qs t := by
    have hh := parisiSplitPressure_outer_eq_original hN ξ ms qs p u hm ht G₀
      (sharedReplicaSiteField hVec) hreach
    linarith
  unfold randomFieldParisiAuxPairPressure randomFieldParisiSplitPressure
  simp_rw [hp]
  rw [integral_sub (integrable_parisiSplitPressure_externalField hμ ξ ms qs p t u hm G₀
    (parisiOuterAuxSplitVars ξ qs p t) hreach) (integrable_const _),
    integral_const, probReal_univ, one_smul]

theorem randomFieldParisiAuxPairPressure_inner_eq {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] {μh : Measure ℝ} [IsProbabilityMeasure μh]
    (hμ : Integrable id μh) (hN : 0 < N) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin k) {t : ℝ} (u : ℝ)
    (hm : ParisiMAdmissible ms) (ht : t ∈ Icc (0 : ℝ) 1)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (p.val + 2) t u G₀ =
      randomFieldParisiSplitPressure μh ξ ms qs p.castSucc t u G₀
        (parisiInnerAuxSplitVars ξ qs p.castSucc t) - parisiAuxTerminalVar ξ qs t := by
  have hp (hVec : Fin N → ℝ) :
      parisiAuxPairPressure ξ ms qs (p.val + 2) t u G₀ (sharedReplicaSiteField hVec) =
        parisiSplitPressure ξ ms qs p.castSucc t u G₀ (parisiInnerAuxSplitVars ξ qs p.castSucc t)
          (sharedReplicaSiteField hVec) - parisiAuxTerminalVar ξ qs t := by
    have hh := parisiSplitPressure_inner_eq_original hN ξ ms qs p u hm ht G₀
      (sharedReplicaSiteField hVec) hreach
    linarith
  unfold randomFieldParisiAuxPairPressure randomFieldParisiSplitPressure
  simp_rw [hp]
  rw [integral_sub (integrable_parisiSplitPressure_externalField hμ ξ ms qs p.castSucc t u hm G₀
    (parisiInnerAuxSplitVars ξ qs p.castSucc t) hreach) (integrable_const _),
    integral_const, probReal_univ, one_smul]

/-- The original interpolation bracket after the terminal mass-one
Gaussian normalization in (14.312). -/
noncomputable def parisiInterpolationBracket (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (t : ℝ) : ℝ :=
  parisiSplitBracket μh ξ ms qs t - (parisiAuxTerminalVar ξ qs t : ℝ) / 2

theorem parisiInterpolationBracket_one (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (hm : ParisiMAdmissible ms) :
    parisiInterpolationBracket μh ξ ms qs 1 = randomFieldParisiFunctional μh ξ ms qs := by
  rw [parisiInterpolationBracket, parisiSplitBracket_eq_functional_add_correction μh ξ ms qs hm]
  simp only [parisiAuxTerminalVar, sub_self, Real.toNNReal_zero, zero_mul, NNReal.coe_zero,
    zero_div, sub_zero, add_zero]

end SpinGlass
