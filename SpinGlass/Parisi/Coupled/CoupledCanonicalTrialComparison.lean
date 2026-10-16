import SpinGlass.Parisi.Coupled.CoupledCanonicalCouplingComparison
import SpinGlass.Parisi.Coupled.CoupledOverlapTangentDefect

/-!
# Canonical pressure comparison at a fixed trial overlap

The trial overlap determines the Gaussian path, while the realized overlap
determines the constraint. Their difference contributes the explicit tangent
defect in (14.147). The resulting scalar bound is continuous in time and
realized overlap, even though the constrained finite-volume pressure need
not be continuous in its constraint. This is the local witness interface
for the compact argument following Proposition 14.8.7.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

noncomputable def parisiCanonicalTrialPressure {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t v u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∫ θ, Real.log
    (cascadeRec (parisiCanonicalPositivePieces ms r p).length
      (parisiCanonicalPositiveMasses ms r p)
      (siteGaussianMarks (Fin N × ParisiCanonicalColumns ms r p) _ (fun _ => 1))
      (coupledG N u a
        (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t v)
        (parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t v)
        (parisiCanonicalDrivenFactor ξ ms qs negative r p t v)
        (parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t v)
        (parisiTimeProfile ξ t) G₀ 1 θ)).toReal
    ∂Pm.prod (rootMarksLaw N (J := ParisiCanonicalColumns ms r p) 1)

theorem parisiCanonicalTrialPressure_eq_original {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    (hN : 0 < N) (ξ : ℝ → ℝ) (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (t v u : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiCanonicalTrialPressure ξ ms qs negative r p t v u G₀ a =
      parisiAuxPairPressure ξ ms qs (r.val + 1) t u G₀ a + parisiAuxTerminalVar ξ qs t := by
  have hi := integral_log_cascadeRec_parisiCanonical_auxiliary_eq Pm ξ ms qs hm negative r p t v
    (constraintR N u) G₀.U G₀.measU 0 a
  unfold parisiCanonicalTrialPressure coupledG
  simp only [sub_self, Real.sqrt_zero, Real.sqrt_one, zero_smul, one_smul, zero_add]
  rw [hi]
  have hcpos : ∃ σ, 0 < constraintR N u σ :=
    hreach.elim fun σ hσ => ⟨σ, constraintR_pos_of_overlap_eq N hσ⟩
  have hlog (θ : Ω × (Fin N × Fin 2 → ℝ)) :=
    log_cascadeRec_parisi_aux_eq (τ := r.val + 1) ξ ms qs t hm (by omega) (by omega)
      (constraintR_nonneg N u) hcpos (G₀.U θ.1) 0 a θ.2
  have hint := integrable_log_cascadeRec_parisi_aux ξ ms qs (r.val + 1) t u hm G₀ a hreach
  unfold parisiAuxPairPressure
  simp only [Nat.add_sub_cancel] at hlog hint ⊢
  simp_rw [hlog]
  rw [integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- The canonical Gaussian path at a trial magnitude bounds the
physical pressure at any realizable overlap, with its exact tangent defect. -/
theorem parisiCanonicalTrialPressure_le_siteValue {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {t v : ℝ} (u : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1)))
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (a : Fin N × Fin 2 → ℝ) (lam : ℝ)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    parisiCanonicalTrialPressure ξ ms qs negative r p t v u G₀ a ≤
      2 * Real.log 2 + (1 / (N : ℝ)) * ∑ j, pairSiteY₀
        (parisiCanonicalPositiveMasses ms r p) 1 (fun _ => 1) lam (fun l => a (j, l))
        (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t v +
          parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t v)
        (fun i => parisiCanonicalDrivenFactor ξ ms qs negative r p t v i +
          parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t v i) -
        lam * u - t * parisiCorrection ξ ms qs +
          t * parisiOverlapTangentDefect ξ (if negative then -v else v) u := by
  have hpos := parisiCanonicalPositiveMasses_pos ms hm r p
  have hle := parisiCanonicalPositiveMasses_le_one ms hm r p
  have hmono := parisiCanonicalPositiveMasses_monotone ms r p
  have hb := coupled_bound'_of_monotone N hN (parisiTimeProfile ξ t)
    (parisiCanonicalCompressedRho ms qs negative r p v) u
    (parisiCanonicalCompressedRho_zero ms qs negative r p v)
    (S := Icc (-1 : ℝ) 1) (parisiCanonicalCompressedRho_mem_Icc ms qs hq negative r p hv)
    (fun x _ q hq' => parisiTimeProfile_tangent_line_le_signed hξ ht.1 hq' x)
    (deriv_parisiTimeProfile_zero hξ t) G₀ 1 (fun _ => 1)
    (J₁ := canonicalDrivenColumns (ParisiCanonicalColumnHalf ms r p))
    (L₀ := parisiCanonicalDrivenRootFactor ξ ms qs negative r p t v)
    (L₀' := parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t v)
    (L := parisiCanonicalDrivenFactor ξ ms qs negative r p t v)
    (L' := parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t v)
    (fun l l' => by
      simpa only [NNReal.coe_one, one_mul] using
        gram_parisiCanonicalDrivenRootFactor hξ ms qs hm hq negative r p ht.1 hv l l')
    (fun i l l' => by
      simpa only [NNReal.coe_one, one_mul] using
        gram_parisiCanonicalDrivenFactor hξ ms qs hm hq negative r p ht.1 hv i l l')
    (fun l j hj => canonicalLeftColumn_zero_of_not_mem _ l j hj)
    (fun i l j hj => canonicalLeftColumn_zero_of_not_mem _ l j hj)
    (fun l j hj => canonicalRightColumn_zero_of_mem _ l j hj)
    (fun i l j hj => canonicalRightColumn_zero_of_mem _ l j hj)
    a lam (parisiCanonicalPositiveMasses ms r p) hmono hpos hle hreach
  rw [integral_parisiRec_pairCoshF_siteField N _ hpos hle,
    coupledLevelSum_parisiCanonical_compressed_eq_correction hξ ms qs hm hq negative r p t hv] at hb
  have hv1 : v ≤ 1 := hv.2.trans (qExt_mem_Icc hq.monotone hq.2.1 hq.2.2 (p.val + 1)).2
  simp only [parisiCanonicalCompressedRho_terminal ms qs negative r p hv1] at hb
  rw [pairDiagDefect_overlapMatrix_eq, parisiOverlapTangentDefect_timeProfile] at hb
  exact hb

noncomputable def parisiCanonicalTrialGap (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (v lam t u : ℝ) : ℝ :=
  2 * (∫ h, closedParisiX₀ ξ ms qs h ∂μh) + lam * u -
    parisiCanonicalSiteValue μh ξ ms qs negative r p t v lam -
      t * parisiOverlapTangentDefect ξ (if negative then -v else v) u

theorem parisiCanonicalTrialGap_at_trial_eq (μh : Measure ℝ) (ξ : ℝ → ℝ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) (v lam t : ℝ) :
    parisiCanonicalTrialGap μh ξ ms qs negative r p v lam t (if negative then -v else v) =
      parisiCanonicalCouplingGap μh ξ ms qs negative r p t v lam := by
  simp only [parisiCanonicalTrialGap, parisiCanonicalCouplingGap, parisiOverlapTangentDefect,
    sub_self, zero_mul, sub_zero, mul_zero]

/-- Each fixed admissible trial gives a continuous scalar witness
on the full time/realized-overlap plane. This makes no continuity claim
about the constrained finite-volume pressure itself. -/
theorem continuous_parisiCanonicalTrialGap_time_overlap
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ) {k : ℕ}
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (negative : Bool)
    (r : Fin (k + 1)) (p : Fin (k + 2)) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) (lam : ℝ) :
    Continuous (fun x : ℝ × ℝ =>
      parisiCanonicalTrialGap μh ξ ms qs negative r p v lam x.1 x.2) := by
  have hsite : Continuous (fun x : ℝ × ℝ =>
      parisiCanonicalSiteValue μh ξ ms qs negative r p x.1 v lam) := by
    apply continuousOn_univ.1
    exact (continuousOn_parisiCanonicalSiteValue_time_overlap hμ hξ ms qs negative r p lam).comp
      (continuous_fst.prodMk (continuous_const (y := v))).continuousOn (fun _ _ => ⟨mem_univ _, hv⟩)
  have hξc : Continuous ξ := continuousOn_univ.1 (hξ.convex.continuousOn isOpen_univ)
  unfold parisiCanonicalTrialGap parisiOverlapTangentDefect
  exact ((continuous_const.add (continuous_snd.const_mul lam)).sub hsite).sub
    (continuous_fst.mul (((hξc.comp continuous_snd).sub continuous_const).sub
      ((continuous_snd.sub continuous_const).mul continuous_const)))

/-- A fixed admissible trial bounds the original physical pressure
at every realizable overlap under the actual i.i.d. field law. Its scalar
gap is continuous even as the realized constraint changes. -/
theorem randomFieldParisiAuxPairPressure_le_canonicalTrialGap {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (hN : 0 < N)
    {ξ : ℝ → ℝ} (hξ : TalagrandXiCondition ξ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ)
    (hm : ParisiMAdmissible ms) (hq : ParisiQAdmissible qs)
    (negative : Bool) (r : Fin (k + 1)) (p : Fin (k + 2)) {t v : ℝ} (u : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (qExt qs p.val) (qExt qs (p.val + 1))) (lam : ℝ)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u G₀ ≤
      2 * parisiInterpolationBracket μh ξ ms qs t -
        parisiCanonicalTrialGap μh ξ ms qs negative r p v lam t u := by
  let F := fun h => pairColeHopfIterate (parisiCanonicalPairLevels ξ ms qs negative r p t v)
    (pairSiteY lam) h h
  let C : ℝ := 2 * Real.log 2 - lam * u - t * parisiCorrection ξ ms qs +
    t * parisiOverlapTangentDefect ξ (if negative then -v else v) u - parisiAuxTerminalVar ξ qs t
  have hF : Integrable F μh := integrable_pairColeHopfIterate_terminal_externalField hμ _
    (pairUnitLipschitz_pairSiteY lam)
  have hAvg := integrable_externalFieldVec_siteAverage hF N
  have hLeft := integrable_parisiAuxPairPressure_externalField hμ hN ξ ms qs hm r ht u G₀ hreach
  have hRhs : Integrable (fun hVec : Fin N → ℝ => C + (1 / (N : ℝ)) * ∑ i, F (hVec i))
      (externalFieldVecLaw N μh) := (integrable_const C).add hAvg
  have hb := integral_mono hLeft hRhs (fun hVec => by
    have hp := parisiCanonicalTrialPressure_le_siteValue hN hξ ms qs hm hq negative r p u ht hv G₀
      (sharedReplicaSiteField hVec) lam hreach
    have hsite (i : Fin N) : pairSiteY₀ (parisiCanonicalPositiveMasses ms r p) 1 (fun _ => 1) lam
        (fun l => sharedReplicaSiteField hVec (i, l))
        (parisiCanonicalDrivenRootFactor ξ ms qs negative r p t v +
          parisiCanonicalAuxiliaryRootFactor ξ ms qs negative r p t v)
        (fun j => parisiCanonicalDrivenFactor ξ ms qs negative r p t v j +
          parisiCanonicalAuxiliaryFactor ξ ms qs negative r p t v j) = F (hVec i) :=
      pairSiteY₀_parisiCanonical_eq ξ ms qs hm negative r p t v lam (fun _ => hVec i)
    simp_rw [hsite] at hp
    rw [parisiCanonicalTrialPressure_eq_original hN ξ ms qs hm negative r p t v u G₀
      (sharedReplicaSiteField hVec) hreach] at hp
    dsimp only [C]
    linarith)
  have hmean : (∫ hVec : Fin N → ℝ, C + (1 / (N : ℝ)) * ∑ i, F (hVec i)
      ∂externalFieldVecLaw N μh) = C + ∫ h, F h ∂μh := by
    have ha := integral_add (integrable_const (μ := externalFieldVecLaw N μh) C) hAvg
    rw [ha, integral_externalFieldVec_siteAverage hF hN]
    simp only [integral_const, probReal_univ, one_smul]
  rw [hmean] at hb
  change randomFieldParisiAuxPairPressure μh ξ ms qs (r.val + 1) t u G₀ ≤ _ at hb
  unfold parisiInterpolationBracket parisiSplitBracket parisiCanonicalTrialGap
    parisiCanonicalSiteValue randomFieldPairColeHopfTerminalValue
  dsimp only [C, F] at hb
  linarith

end SpinGlass
