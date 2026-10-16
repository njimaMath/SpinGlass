import SpinGlass.Parisi.Coupled.CoupledParisiComparison
import SpinGlass.Parisi.Field.RandomExternalField

/-!
# Field differences and integrability of the actual coupled pressure

Changing the realized quenched site field changes the logarithmic constrained
cascade pressure by a deterministic sum of coordinate differences. This
supplies its field-law integrability without exponential moments of that law.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

/-- The total coordinate difference of two realized replica site fields. -/
def replicaSiteFieldDistance {N : ℕ} (a b : Fin N × Fin 2 → ℝ) : ℝ :=
  ∑ l : Fin 2, ∑ i : Fin N, |a (i, l) - b (i, l)|

theorem replicaSiteFieldDistance_comm {N : ℕ} (a b : Fin N × Fin 2 → ℝ) :
    replicaSiteFieldDistance a b = replicaSiteFieldDistance b a := by
  simp only [replicaSiteFieldDistance, abs_sub_comm]

theorem replicaSiteFieldDistance_nonneg {N : ℕ} (a b : Fin N × Fin 2 → ℝ) :
    0 ≤ replicaSiteFieldDistance a b :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The coupled branch Hamiltonian changes by at most the total
coordinate field difference, uniformly in disorder and all Gaussian marks. -/
theorem abs_pairBranchHamX_sub_field_le {N k : ℕ} {J : Type*} [Fintype J]
    (H : EnergySpace N) (lam : ℝ) (a b : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) (σ : Fin 2 → Config N) :
    |pairBranchHamX N k H lam a K₀ K z₀ x σ - pairBranchHamX N k H lam b K₀ K z₀ x σ| ≤
      replicaSiteFieldDistance a b := by
  have he : pairBranchHamX N k H lam a K₀ K z₀ x σ - pairBranchHamX N k H lam b K₀ K z₀ x σ =
      ∑ l : Fin 2, ∑ i : Fin N, isingSpin (σ l i) * (a (i, l) - b (i, l)) := by
    unfold pairBranchHamX
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [he]
  calc
    _ ≤ ∑ l : Fin 2, |∑ i : Fin N, isingSpin (σ l i) * (a (i, l) - b (i, l))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l : Fin 2, ∑ i : Fin N, |isingSpin (σ l i) * (a (i, l) - b (i, l))| :=
      Finset.sum_le_sum fun l _ => Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_isingSpin_eq_one, one_mul, replicaSiteFieldDistance]

/-- The branch partition functions obey the same multiplicative field
comparison, before any cascade or Gaussian averages. -/
theorem pairHamG_field_le_exp_mul {N k : ℕ} {J : Type*} [Fintype J]
    {c : (Fin 2 → Config N) → ℝ} (hc : ∀ σ, 0 ≤ c σ)
    (H : EnergySpace N) (lam : ℝ) (a b : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    (z₀ : Fin N × J → ℝ) (x : Fin k → Fin N × J → ℝ) :
    pairHamG N k c H lam a K₀ K z₀ x ≤
      ENNReal.ofReal (Real.exp (replicaSiteFieldDistance a b)) * pairHamG N k c H lam b K₀ K z₀ x := by
  unfold pairHamG
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  unfold pairBranchZX
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  have hh := abs_pairBranchHamX_sub_field_le H lam a b K₀ K z₀ x σ
  have hex : Real.exp (-pairBranchHamX N k H lam a K₀ K z₀ x σ) ≤
      Real.exp (replicaSiteFieldDistance a b) * Real.exp (-pairBranchHamX N k H lam b K₀ K z₀ x σ) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith [(abs_le.1 hh).1]
  have hm := mul_le_mul_of_nonneg_left hex (hc σ)
  nlinarith

/-- A pointwise multiplicative comparison passes through a positive
finite cascade and then through the logarithm. -/
theorem log_cascadeRec_sub_le_of_exp_mul_le {T : Type*} [MeasurableSpace T] {k : ℕ}
    (ms : Fin k → ℝ) (μs : Fin k → Measure T) [∀ i, IsProbabilityMeasure (μs i)]
    (hpos : ∀ i, 0 < ms i) {F G : (Fin k → T) → ℝ≥0∞}
    (hFm : Measurable F) (hGm : Measurable G) (hFp : ∀ x, 0 < F x) (hGp : ∀ x, 0 < G x)
    (hFfin : cascadeRec k ms μs F ≠ ∞) (hGfin : cascadeRec k ms μs G ≠ ∞)
    (C : ℝ) (hFG : ∀ x, F x ≤ ENNReal.ofReal (Real.exp C) * G x) :
    Real.log (cascadeRec k ms μs F).toReal - Real.log (cascadeRec k ms μs G).toReal ≤ C := by
  have hrec := cascadeRec_mono k ms μs hFG (fun i => (hpos i).le)
  rw [cascadeRec_const_mul k ms μs hGm hpos] at hrec
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGfin) hrec
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal
  have hFpReal := ENNReal.toReal_pos (cascadeRec_pos k ms μs hFm hFp hpos).ne' hFfin
  have hGpReal := ENNReal.toReal_pos (cascadeRec_pos k ms μs hGm hGp hpos).ne' hGfin
  have hlog := Real.log_le_log hFpReal hreal
  rw [Real.log_mul (Real.exp_pos _).ne' hGpReal.ne', Real.log_exp] at hlog
  linarith

/-- The actual constrained logarithmic cascade inherits the coordinate
field bound. Its constant does not depend on the number of cascade levels. -/
theorem abs_log_cascadeRec_pairHamG_sub_field_le {N k : ℕ} {J : Type*} [Fintype J]
    {c : (Fin 2 → Config N) → ℝ} (hc : ∀ σ, 0 ≤ c σ) (hcpos : ∃ σ, 0 < c σ)
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (H : EnergySpace N) (lam : ℝ) (a b : Fin N × Fin 2 → ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (z₀ : Fin N × J → ℝ) :
    |Real.log (cascadeRec k ms (siteGaussianMarks (Fin N × J) k vs)
        (pairHamG N k c H lam a K₀ K z₀)).toReal -
      Real.log (cascadeRec k ms (siteGaussianMarks (Fin N × J) k vs)
        (pairHamG N k c H lam b K₀ K z₀)).toReal| ≤ replicaSiteFieldDistance a b := by
  have hupper (a b : Fin N × Fin 2 → ℝ) :
      Real.log (cascadeRec k ms (siteGaussianMarks (Fin N × J) k vs)
          (pairHamG N k c H lam a K₀ K z₀)).toReal -
        Real.log (cascadeRec k ms (siteGaussianMarks (Fin N × J) k vs)
          (pairHamG N k c H lam b K₀ K z₀)).toReal ≤ replicaSiteFieldDistance a b :=
    log_cascadeRec_sub_le_of_exp_mul_le ms (siteGaussianMarks (Fin N × J) k vs) hpos
      (measurable_pairHamG' N k c H lam a K₀ K z₀) (measurable_pairHamG' N k c H lam b K₀ K z₀)
      (fun x => pairHamG_pos N k hc hcpos H lam a K₀ K z₀ x)
      (fun x => pairHamG_pos N k hc hcpos H lam b K₀ K z₀ x)
      (cascadeRec_pairHamG_ne_top N k ms vs hpos hle hc H lam a K₀ K z₀)
      (cascadeRec_pairHamG_ne_top N k ms vs hpos hle hc H lam b K₀ K z₀)
      (replicaSiteFieldDistance a b) (pairHamG_field_le_exp_mul hc H lam a b K₀ K z₀)
  exact abs_le.2 ⟨by have hh := hupper b a; rw [replicaSiteFieldDistance_comm] at hh; linarith,
    hupper a b⟩

/-- Conditional Gaussian integrability of the actual constrained
logarithmic cascade for every fixed realized site field. -/
theorem integrable_log_cascadeRec_coupledG {N κ : ℕ} {Ω J : Type}
    [MeasurableSpace Ω] [Fintype J] [DecidableEq J]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ) (u : ℝ)
    (hu : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u)
    (G₀ : GaussianField (α := Config N) Pm (fun σ τ => overlapCovMatrix N ξ σ τ))
    (ns : Fin κ → ℝ) (hpos : ∀ i, 0 < ns i) (hle : ∀ i, ns i ≤ 1)
    (v₀ : ℝ≥0) (vs : Fin κ → ℝ≥0) (L₀ L₀' : Fin 2 → J → ℝ)
    (L L' : Fin κ → Fin 2 → J → ℝ) (a : Fin N × Fin 2 → ℝ) :
    Integrable (fun θ => Real.log (cascadeRec κ ns (siteGaussianMarks (Fin N × J) κ vs)
      (coupledG N u a L₀ L₀' L L' ξ G₀ 1 θ)).toReal) (Pm.prod (rootMarksLaw N v₀)) := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := hu
  have hcσ₀ : constraintR N u σ₀ = 1 := by unfold constraintR; rw [ite_eq_left hσ₀]
  have hHf : Measurable (fun ω => Real.sqrt 1 • G₀.U ω) :=
    G₀.measU.const_smul (Real.sqrt 1)
  have hGm : Measurable (Function.uncurry (coupledG N u a L₀ L₀' L L' ξ G₀ 1)) :=
    measurable_pairHamG_branchParam N κ (constraintR N u) hHf 0 a
      (Real.sqrt (1 - 1) • L₀ + L₀') (fun p => Real.sqrt (1 - 1) • L p + L' p)
  have hint : ∫⁻ θ, ∫⁻ x, coupledG N u a L₀ L₀' L L' ξ G₀ 1 θ x
      ∂Measure.pi (siteGaussianMarks (Fin N × J) κ vs) ∂Pm.prod (rootMarksLaw N v₀) ≠ ∞ :=
    lintegral_lintegral_pairHamG_ne_top N (constraintR_nonneg N u)
      (fun ω => Real.sqrt 1 • G₀.U ω) hHf
      (fun σ => G₀.lintegral_ofReal_exp_neg_smul_add_ne_top (Real.sqrt 1) (σ 0) (σ 1)) 0 a
      (Real.sqrt (1 - 1) • L₀ + L₀') (fun p => Real.sqrt (1 - 1) • L p + L' p) v₀ vs
  have hlog : ∫⁻ θ, ∫⁻ x, ‖Real.log (coupledG N u a L₀ L₀' L L' ξ G₀ 1 θ x).toReal‖ₑ
      ∂Measure.pi (siteGaussianMarks (Fin N × J) κ vs) ∂Pm.prod (rootMarksLaw N v₀) ≠ ∞ :=
    lintegral_lintegral_enorm_log_pairHamG_ne_top N (constraintR_nonneg N u)
      (constraintR_le_one N u) hcσ₀ hHf
      (fun τ => integrable_smul_apply_disorder N ξ G₀ (Real.sqrt 1) τ) 0 a
      (Real.sqrt (1 - 1) • L₀ + L₀') (fun p => Real.sqrt (1 - 1) • L p + L' p) v₀ vs
  exact integrable_log_cascadeRec κ (Pm.prod (rootMarksLaw N v₀)) ns
    (siteGaussianMarks (Fin N × J) κ vs) _ hpos hle hGm
    (fun θ x => coupledG_pos N u ⟨σ₀, hσ₀⟩ a L₀ L₀' L L' ξ G₀ 1 θ x)
    (fun θ x => ENNReal.ofReal_ne_top) hint hlog

/-- Averaging the actual logarithmic cascade over disorder and root
marks retains the deterministic field bound, with the pressure normalization. -/
theorem abs_parisiSplitPressure_sub_field_le {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t u : ℝ)
    (hm : ParisiMAdmissible ms)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (es : Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u)
    (a b : Fin N × Fin 2 → ℝ) :
    |parisiSplitPressure ξ ms qs p t u G₀ es a - parisiSplitPressure ξ ms qs p t u G₀ es b| ≤
      (1 / (N : ℝ)) * replicaSiteFieldDistance a b := by
  let ns := halveBelow (p.val + 1) (parisiResponseSplitMasses ms p)
  let vs := fun i => parisiDrivenSplitVars ξ qs p t u i + es i
  let L₀ := coupledDrivenVarianceFactor (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
    (couplingFactorSgn 1 (p.val + 2) 0)
  let L₀' := coupledAuxVarianceFactor (parisiDrivenRootVar ξ qs t) (parisiAuxRootVar ξ qs t)
    (couplingFactorSgn 1 (p.val + 2) 0)
  let L := fun i => coupledDrivenVarianceFactor (parisiDrivenSplitVars ξ qs p t u i) (es i)
    (couplingFactorSgn 1 (p.val + 2) (i.val + 1))
  let L' := fun i => coupledAuxVarianceFactor (parisiDrivenSplitVars ξ qs p t u i) (es i)
    (couplingFactorSgn 1 (p.val + 2) (i.val + 1))
  have hpos : ∀ i, 0 < ns i := halveBelow_pos (parisiResponseSplitMasses_pos ms p hm) _
  have hle : ∀ i, ns i ≤ 1 := halveBelow_le_one (parisiResponseSplitMasses_le_one ms p hm) _
  have hi (a : Fin N × Fin 2 → ℝ) := integrable_log_cascadeRec_coupledG (parisiTimeProfile ξ t)
    u hreach G₀ ns hpos hle (parisiVar ξ qs 0) vs L₀ L₀' L L' a
  unfold parisiSplitPressure
  change |(1 / (N : ℝ)) * (∫ θ, Real.log (cascadeRec _ ns _
      (coupledG N u a L₀ L₀' L L' (parisiTimeProfile ξ t) G₀ 1 θ)).toReal
      ∂Pm.prod (rootMarksLaw N (parisiVar ξ qs 0))) -
    (1 / (N : ℝ)) * (∫ θ, Real.log (cascadeRec _ ns _
      (coupledG N u b L₀ L₀' L L' (parisiTimeProfile ξ t) G₀ 1 θ)).toReal
      ∂Pm.prod (rootMarksLaw N (parisiVar ξ qs 0)))| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (N : ℝ))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← integral_sub (hi a) (hi b)]
  have hb := norm_integral_le_of_norm_le_const (μ := Pm.prod (rootMarksLaw N (parisiVar ξ qs 0)))
    (f := fun θ => Real.log (cascadeRec _ ns
        (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) ((p.val + 1) + ((k - p.val) + 1)) vs)
        (coupledG N u a L₀ L₀' L L' (parisiTimeProfile ξ t) G₀ 1 θ)).toReal -
      Real.log (cascadeRec _ ns
        (siteGaussianMarks (Fin N × (Fin 2 ⊕ Fin 2)) ((p.val + 1) + ((k - p.val) + 1)) vs)
        (coupledG N u b L₀ L₀' L L' (parisiTimeProfile ξ t) G₀ 1 θ)).toReal)
    (C := replicaSiteFieldDistance a b) (.of_forall fun θ => ?_)
  · simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hb
  · rw [Real.norm_eq_abs]
    obtain ⟨σ, hσ⟩ := hreach
    have hcpos : ∃ σ, 0 < constraintR N u σ := ⟨σ, by simp [constraintR, hσ]⟩
    unfold coupledG
    simp only [Real.sqrt_one, sub_self, Real.sqrt_zero, zero_smul, zero_add, one_smul]
    exact abs_log_cascadeRec_pairHamG_sub_field_le
      (constraintR_nonneg N u) hcpos ns vs hpos hle (G₀.U θ.1) 0 a b L₀' L' θ.2

/-- The pressure is continuous in every realized replica field. This
follows from the deterministic coordinate bound, without differentiating
under the disorder or field integrals. -/
theorem continuous_parisiSplitPressure_siteField {N k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {Pm : Measure Ω} [IsProbabilityMeasure Pm] (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t u : ℝ)
    (hm : ParisiMAdmissible ms)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (es : Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    Continuous (parisiSplitPressure ξ ms qs p t u G₀ es) := by
  apply continuous_iff_continuousAt.2
  intro b
  have hcont : Continuous (fun a : Fin N × Fin 2 → ℝ =>
      (1 / (N : ℝ)) * replicaSiteFieldDistance a b) := by
    unfold replicaSiteFieldDistance
    fun_prop
  have hzero : (1 / (N : ℝ)) * replicaSiteFieldDistance b b = 0 := by
    simp [replicaSiteFieldDistance]
  have hlim : Tendsto (fun a : Fin N × Fin 2 → ℝ =>
      (1 / (N : ℝ)) * replicaSiteFieldDistance a b) (𝓝 b) (𝓝 0) := by
    simpa only [hzero] using hcont.tendsto b
  have hnorm := squeeze_zero (fun a => abs_nonneg _)
    (fun a => abs_parisiSplitPressure_sub_field_le ξ ms qs p t u hm G₀ es hreach a b) hlim
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  simpa only [Real.norm_eq_abs] using hnorm

/-- Shared replicas count each coordinate field difference twice. -/
theorem replicaSiteFieldDistance_shared_zero {N : ℕ} (hVec : Fin N → ℝ) :
    replicaSiteFieldDistance (sharedReplicaSiteField hVec) 0 = 2 * ∑ i, |hVec i| := by
  simp only [replicaSiteFieldDistance, sharedReplicaSiteField, Pi.zero_apply,
    sub_zero, Fin.sum_univ_two]
  ring

/-- The actual quenched coupled pressure is integrable under the i.i.d.
field-vector law. A finite first moment suffices, irrespective of exponential
moments of the site law. -/
theorem integrable_parisiSplitPressure_externalField {N k : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {μh : Measure ℝ} [IsProbabilityMeasure μh] (hμ : Integrable id μh) (ξ : ℝ → ℝ)
    (ms : Fin k → ℝ) (qs : Fin (k + 1) → ℝ) (p : Fin (k + 1)) (t u : ℝ)
    (hm : ParisiMAdmissible ms)
    (G₀ : GaussianField (α := Config N) Pm
      (fun σ τ => overlapCovMatrix N (parisiTimeProfile ξ t) σ τ))
    (es : Fin ((p.val + 1) + ((k - p.val) + 1)) → ℝ≥0)
    (hreach : ∃ σ : Fin 2 → Config N, overlap N (σ 0) (σ 1) = u) :
    Integrable (fun hVec : Fin N → ℝ => parisiSplitPressure ξ ms qs p t u G₀ es
      (sharedReplicaSiteField hVec)) (externalFieldVecLaw N μh) := by
  have hmeas := (continuous_parisiSplitPressure_siteField ξ ms qs p t u hm G₀ es hreach).measurable
    |>.comp (measurable_sharedReplicaSiteField N)
  have hsum : Integrable (fun hVec : Fin N → ℝ => ∑ i, |hVec i|) (externalFieldVecLaw N μh) := by
    apply integrable_finsetSum
    intro i _
    have hi := ((measurePreserving_externalFieldVec_apply N μh i).integrable_comp
      hμ.aestronglyMeasurable).2 hμ
    simpa only [Function.comp_def, id_eq] using hi.abs
  let F₀ := parisiSplitPressure ξ ms qs p t u G₀ es 0
  have hbound : Integrable (fun hVec : Fin N → ℝ =>
      |F₀| + (1 / (N : ℝ)) * (2 * ∑ i, |hVec i|)) (externalFieldVecLaw N μh) :=
    (integrable_const |F₀|).add ((hsum.const_mul 2).const_mul _)
  apply hbound.mono' hmeas.aestronglyMeasurable (.of_forall fun hVec => ?_)
  rw [Real.norm_eq_abs]
  dsimp only [Function.comp_def]
  have hh := abs_parisiSplitPressure_sub_field_le ξ ms qs p t u hm G₀ es hreach
    (sharedReplicaSiteField hVec) 0
  rw [replicaSiteFieldDistance_shared_zero] at hh
  apply abs_le.2
  constructor <;> dsimp only [F₀]
  · linarith [(abs_le.1 hh).1, neg_abs_le (parisiSplitPressure ξ ms qs p t u G₀ es 0)]
  · linarith [(abs_le.1 hh).2, le_abs_self (parisiSplitPressure ξ ms qs p t u G₀ es 0)]

end SpinGlass
