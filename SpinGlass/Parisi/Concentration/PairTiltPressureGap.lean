import SpinGlass.Parisi.Concentration.PairTiltCombinedConcentration

/-!
# From a pressure gap to a small tilted mass

The actual constrained and unconstrained cascade pressures control the mean
of the actual tilted logarithm. The joint Gaussian/field fluctuation theorem
then yields exponential decay, with explicit volume-independent constants.
The identification with the original branch-meeting observable is separate.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace SpinGlass

open FiniteGibbs

variable {N k : ℕ} {J : Type*} [Fintype J]

/-- The unnormalized cascade log pressure under the same clipped field
and disorder coordinates used for the tilted mass. -/
noncomputable def pairHamClippedLogPressure (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    (c : (Fin 2 → Config N) → ℝ) (lam : ℝ)
    (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (R : ℝ)
    (z : (EnergySpace N × (Fin N × J → ℝ)) × (Fin N → ℝ)) : ℝ :=
  Real.log (cascadeRec k ms (siteGaussianMarks (Fin N × J) k vs)
    (pairHamG N k c z.1.1 lam
      (sharedReplicaSiteField (fun i => Aristotle.clip R (z.2 i))) K₀ K z.1.2)).toReal

theorem measurable_pairHamClippedLogPressure
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (c : (Fin 2 → Config N) → ℝ)
    (lam : ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (R : ℝ) :
    Measurable (pairHamClippedLogPressure ms vs c lam K₀ K R) := by
  apply (measurable_cascadeRec_prod k ms (siteGaussianMarks (Fin N × J) k vs) ?_).ennreal_toReal.log
  unfold Function.uncurry pairHamG pairBranchZX pairBranchHamX pairBranchMark sharedReplicaSiteField
  fun_prop

/-- The constrained pressure is at most the unconstrained pressure. -/
theorem pairHamClippedLogPressure_sub_le_zero
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (lam : ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (R : ℝ)
    (z : (EnergySpace N × (Fin N × J → ℝ)) × (Fin N → ℝ)) :
    pairHamClippedLogPressure ms vs c lam K₀ K R z -
      pairHamClippedLogPressure ms vs (fun _ => 1) lam K₀ K R z ≤ 0 := by
  apply log_cascadeRec_sub_le_of_exp_mul_le ms _ hpos
    (measurable_pairHamG' N k _ _ _ _ _ _ _) (measurable_pairHamG' N k _ _ _ _ _ _ _)
    (fun x => pairHamG_pos N k hc0 hcpos _ _ _ _ _ _ x)
    (fun x => pairHamG_pos N k (fun _ => zero_le_one) ⟨fun _ _ => true, one_pos⟩ _ _ _ _ _ _ x)
    (cascadeRec_pairHamG_ne_top N k ms vs hpos hle hc0 _ _ _ _ _ _)
    (cascadeRec_pairHamG_ne_top N k ms vs hpos hle (fun _ => zero_le_one) _ _ _ _ _ _)
  simpa only [Real.exp_zero, ENNReal.ofReal_one, one_mul] using
    pairHamG_mono_constraint hc1 z.1.1 lam
      (sharedReplicaSiteField (fun i => Aristotle.clip R (z.2 i))) K₀ K z.1.2

/-- The logarithmic recursive comparison supplies both integrability of
the pressure difference and the averaged negative-mean comparison. -/
theorem integrable_pressure_gap_and_integral_pairHamClippedLogTiltMass_le
    {P : Measure ((EnergySpace N × (Fin N × J → ℝ)) × (Fin N → ℝ))}
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hmono : Monotone ms)
    (hpos : ∀ i, 0 < ms i) (hle : ∀ i, ms i ≤ 1)
    (lam : ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ) (R : ℝ)
    (hi : Integrable (pairHamClippedLogTiltMass ms vs c lam K₀ K R) P)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hblower : ∀ i, b ≤ ms i) :
    let G := fun z => pairHamClippedLogPressure ms vs c lam K₀ K R z -
      pairHamClippedLogPressure ms vs (fun _ => 1) lam K₀ K R z
    Integrable G P ∧ (∫ z, pairHamClippedLogTiltMass ms vs c lam K₀ K R z ∂P) ≤
      b * ∫ z, G z ∂P := by
  let F := pairHamClippedLogTiltMass ms vs c lam K₀ K R
  let G := fun z => pairHamClippedLogPressure ms vs c lam K₀ K R z -
    pairHamClippedLogPressure ms vs (fun _ => 1) lam K₀ K R z
  have hg0 (z) : G z ≤ 0 := pairHamClippedLogPressure_sub_le_zero ms vs hc0 hc1 hcpos
    hpos hle lam K₀ K R z
  have hfg (z) : F z ≤ b * G z := pairHamLogTiltMass_le_pressure_gap ms vs hc0 hc1 hcpos
    hmono hpos hle z.1.1 lam _ K₀ K z.1.2 hb hb1 hblower
  have hgm : Measurable G := (measurable_pairHamClippedLogPressure ms vs c lam K₀ K R).sub
    (measurable_pairHamClippedLogPressure ms vs (fun _ => 1) lam K₀ K R)
  have hgi : Integrable G P := by
    refine (hi.abs.div_const b).mono' hgm.aestronglyMeasurable (.of_forall fun z => ?_)
    change ‖G z‖ ≤ |F z| / b
    rw [Real.norm_eq_abs, abs_of_nonpos (hg0 z), le_div_iff₀ hb]
    have hh := hfg z
    nlinarith only [hh, neg_abs_le (F z)]
  refine ⟨hgi, ?_⟩
  calc (∫ z, F z ∂P) ≤ ∫ z, b * G z ∂P := integral_mono hi (hgi.const_mul b) hfg
    _ = b * ∫ z, G z ∂P := integral_const_mul _ _

/-- A positive averaged pressure gap makes the actual clipped tilted
mass exponentially small. All concentration and integrability hypotheses
are derived from the displayed covariance, mass and cutoff conditions. -/
theorem integral_pairHamConstrainedTiltMass_clipped_le_of_pressure_gap
    (hN : 0 < N) (μh : Measure ℝ) [IsProbabilityMeasure μh]
    {S : Matrix (Config N) (Config N) ℝ} (hS : S.PosSemidef)
    (ms : Fin k → ℝ) (vs : Fin k → ℝ≥0) (v₀ : ℝ≥0)
    {c : (Fin 2 → Config N) → ℝ} (hc0 : ∀ σ, 0 ≤ c σ) (hc1 : ∀ σ, c σ ≤ 1)
    (hcpos : ∃ σ, 0 < c σ) (hsm : StrictMono ms)
    (hpos : ∀ i, 0 < ms i) (hlt : ∀ i, ms i < 1)
    (lam : ℝ) (K₀ : Fin 2 → J → ℝ) (K : Fin k → Fin 2 → J → ℝ)
    {D d R : ℝ} (hD : 0 ≤ D) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hdiag : ∀ σ, S σ σ ≤ (N : ℝ) * D) (hK : ∀ l, ∑ j, K₀ l j ^ 2 ≤ d)
    {b ε : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hblower : ∀ i, b ≤ ms i) (hε : 0 < ε) :
    let P := ((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)).prod
      (externalFieldVecLaw N μh)
    let C := 1 + 32 * (D + (v₀ : ℝ) * d) + 16 * R ^ 2
    (∫ z, (pairHamClippedLogPressure ms vs c lam K₀ K R z -
      pairHamClippedLogPressure ms vs (fun _ => 1) lam K₀ K R z) ∂P) ≤ -ε * N →
    (∫ z, (pairHamConstrainedTiltMass ms vs c z.1.1 lam
      (sharedReplicaSiteField (fun i => Aristotle.clip R (z.2 i))) K₀ K z.1.2).toReal ∂P) ≤
      Real.exp (-(b * ε) * N / 2) + Real.exp (-((b * ε) ^ 2 * N) / (8 * C)) := by
  classical
  dsimp only
  intro hgap
  let P := ((multivariateGaussian 0 S).prod (rootMarksLaw N (J := J) v₀)).prod
    (externalFieldVecLaw N μh)
  let F := pairHamClippedLogTiltMass ms vs c lam K₀ K R
  let C := 1 + 32 * (D + (v₀ : ℝ) * d) + 16 * R ^ 2
  have hC : 0 < C := by dsimp only [C]; positivity
  obtain ⟨hi, hmgf⟩ := integrable_and_hasSubgaussianMGF_pairHamClippedLogTiltMass μh hS
    ms vs v₀ hc0 hc1 hcpos hsm hpos hlt lam K₀ K hD hd hR hdiag hK
  have hmean : (∫ z, F z ∂P) ≤ -(b * ε) * N := by
    have hh := (integrable_pressure_gap_and_integral_pairHamClippedLogTiltMass_le
      ms vs hc0 hc1 hcpos hsm.monotone hpos (fun i => (hlt i).le) lam K₀ K R hi hb hb1 hblower).2
    have hh' := mul_le_mul_of_nonneg_left hgap hb.le
    nlinarith only [hh, hh']
  have hc : ((N : ℝ) * (32 * (D + (v₀ : ℝ) * d) + 16 * R ^ 2)).toNNReal ≤
      (C * N).toNNReal := by
    apply Real.toNNReal_mono
    dsimp only [C]
    nlinarith only [Nat.cast_nonneg (α := ℝ) N]
  have hmgf' := hasSubgaussianMGF_mono hmgf hc
  have hout := Aristotle.integral_capped_exp_le_of_mgf
    (continuous_pairHamClippedLogTiltMass ms vs hc0 hc1 hcpos hsm hpos hlt lam K₀ K R).measurable
    hi hN (mul_pos hb hε) hC hmean (fun s => ⟨hmgf'.integrable_exp_mul s, by
      simpa only [mgf, Real.coe_toNNReal _ (mul_nonneg hC.le (Nat.cast_nonneg N))] using
        hmgf'.mgf_le s⟩)
  convert hout using 1
  apply integral_congr_ae
  exact .of_forall fun z => by
    have hle := pairHamConstrainedTiltMass_le_one ms vs hc1 hpos (fun i => (hlt i).le)
      z.1.1 lam (sharedReplicaSiteField (fun i => Aristotle.clip R (z.2 i))) K₀ K z.1.2
    have hp := pairHamConstrainedTiltMass_pos ms vs hc0 hcpos hpos (fun i => (hlt i).le)
      z.1.1 lam (sharedReplicaSiteField (fun i => Aristotle.clip R (z.2 i))) K₀ K z.1.2
    have hfin := ne_top_of_le_ne_top ENNReal.one_ne_top hle
    dsimp only [F, pairHamClippedLogTiltMass, pairHamLogTiltMass]
    rw [Real.exp_log (ENNReal.toReal_pos hp.ne' hfin), min_eq_right]
    exact ENNReal.toReal_mono ENNReal.one_ne_top hle

end SpinGlass
